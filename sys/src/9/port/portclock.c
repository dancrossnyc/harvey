/*
 * This file is part of the UCB release of Plan 9. It is subject to the license
 * terms in the LICENSE file found in the top-level directory of this
 * distribution and at http://akaros.cs.berkeley.edu/files/Plan9License. No
 * part of the UCB release of Plan 9, including this file, may be copied,
 * modified, propagated, or distributed except according to the terms contained
 * in the LICENSE file.
 */

#include "u.h"
#include "../port/lib.h"
#include "mem.h"
#include "dat.h"
#include "fns.h"

#include "ureg.h"

struct Timers {
	Lock l;
	Timer *head;
};

static Timers timers[MACHMAX];

u32 intrcount[MACHMAX];
u32 fcallcount[MACHMAX];

static i64
tadd(Timers *tt, Timer *nt)
{
	i64 when;
	Timer *t, **last;

	/* Called with tt locked */
	assert(nt->tt == nil);
	switch(nt->tmode){
	default:
		panic("timer");
		break;
	case Trelative:
		if(nt->tns <= 0)
			nt->tns = 1;
		nt->twhen = fastticks(nil) + ns2fastticks(nt->tns);
		break;
	case Tperiodic:
		/*
		 * Periodic timers must have a period of at least 100µs.
		 */
		assert(nt->tns >= 100000);
		if(nt->twhen == 0){
			/*
			 * Look for another timer at the
			 * same frequency for combining.
			 */
			for(t = tt->head; t; t = t->tnext){
				if(t->tmode == Tperiodic && t->tns == nt->tns)
					break;
			}
			if(t)
				nt->twhen = t->twhen;
			else
				nt->twhen = fastticks(nil);
		}

		/*
		 * The new time must be in the future.
		 * ns2fastticks() can return 0 if the tod clock
		 * has been adjusted by, e.g. timesync.
		 */
		when = ns2fastticks(nt->tns);
		if(when == 0)
			when = 1;
		nt->twhen += when;
		break;
	}

	for(last = &tt->head; (t = *last) != nil; last = &t->tnext){
		if(t->twhen > nt->twhen)
			break;
	}
	nt->tnext = *last;
	*last = nt;
	nt->tt = tt;
	if(last == &tt->head)
		return nt->twhen;
	return 0;
}

static i64
tdel(Timer *dt)
{
	Timer *t, **last;
	Timers *tt;

	tt = dt->tt;
	if(tt == nil)
		return 0;
	for(last = &tt->head; (t = *last) != nil; last = &t->tnext){
		if(t == dt){
			assert(dt->tt);
			dt->tt = nil;
			*last = t->tnext;
			break;
		}
	}
	if(last == &tt->head && tt->head)
		return tt->head->twhen;
	return 0;
}

/* add or modify a timer */
void
timeradd(Timer *nt)
{
	Timers *tt;
	i64 when;

	/* Must lock Timer struct before Timers struct */
	ilock(&nt->l);
	if((tt = nt->tt) != nil){
		ilock(&tt->l);
		tdel(nt);
		iunlock(&tt->l);
	}
	tt = &timers[machp()->machno];
	ilock(&tt->l);
	when = tadd(tt, nt);
	if(when)
		timerset(when);
	iunlock(&tt->l);
	iunlock(&nt->l);
}

void
timerdel(Timer *dt)
{
	Timers *tt;
	i64 when;

	ilock(&dt->l);
	if((tt = dt->tt) != nil){
		ilock(&tt->l);
		when = tdel(dt);
		if(when && tt == &timers[machp()->machno])
			timerset(tt->head->twhen);
		iunlock(&tt->l);
	}
	iunlock(&dt->l);
}

void
hzclock(Ureg *ur)
{
	Proc *up = externup();
	uintptr pc;

	machp()->ticks++;
	if(machp()->machno == 0)
		sys->ticks = machp()->ticks;

	pc = userpc(ur);
	if(machp()->proc)
		machp()->proc->pc = pc;

	if(machp()->mmuflush){
		if(up)
			mmuflush();
		machp()->mmuflush = 0;
	}

	accounttime();
	kmapinval();

	if(kproftimer != nil)
		kproftimer(pc);
	oprof_alarm_handler(ur);

	if(machp()->online == 0)
		return;

	if(active.exiting){
		print("someone's exiting\n");
		exit(0);
	}

	if(machp()->machno == 0){
		/* since sys->ticks is only updated if machp()->machno == 0 */
		checkalarms();
	}

	if(up && up->state == Running)
		hzsched(); /* in proc.c */
}

void
timerintr(Ureg *u, i64 j)
{
	Timer *t;
	Timers *tt;
	i64 when, now;
	int callhzclock;

	intrcount[machp()->machno]++;
	callhzclock = 0;
	tt = &timers[machp()->machno];
	now = fastticks(nil);
	ilock(&tt->l);
	while((t = tt->head) != nil){
		/*
		 * No need to ilock t here: any manipulation of t
		 * requires tdel(t) and this must be done with a
		 * lock to tt held.  We have tt, so the tdel will
		 * wait until we're done
		 */
		when = t->twhen;
		if(when > now){
			timerset(when);
			iunlock(&tt->l);
			if(callhzclock)
				hzclock(u);
			return;
		}
		tt->head = t->tnext;
		assert(t->tt == tt);
		t->tt = nil;
		fcallcount[machp()->machno]++;
		iunlock(&tt->l);
		if(t->tf)
			(*t->tf)(u, t);
		else
			callhzclock++;
		ilock(&tt->l);
		if(t->tmode == Tperiodic)
			tadd(tt, t);
	}
	iunlock(&tt->l);
}

void
timersinit(void)
{
	Timer *t;

	/*
	 * T->tf == nil means the HZ clock for this processor.
	 */
	todinit();
	t = malloc(sizeof(*t));
	t->tmode = Tperiodic;
	t->tt = nil;
	t->tns = 1000000000 / HZ;
	t->tf = nil;
	timeradd(t);
}

Timer *
addclock0link(void (*f)(void), int ms)
{
	Timer *nt;
	i64 when;

	/* Synchronize to hztimer if ms is 0 */
	nt = malloc(sizeof(Timer));
	if(ms == 0)
		ms = 1000 / HZ;
	nt->tns = (i64)ms * 1000000LL;
	nt->tmode = Tperiodic;
	nt->tt = nil;
	nt->tf = (void (*)(Ureg *, Timer *))f;

	ilock(&timers[0].l);
	when = tadd(&timers[0], nt);
	if(when)
		timerset(when);
	iunlock(&timers[0].l);
	return nt;
}

u64
ms2tk(u64 ms)
{
	/* avoid overflows at the cost of precision */
	if(ms >= 1000000000 / HZ)
		return (ms / 1000) * HZ;
	return (ms * HZ + 500) / 1000;
}
