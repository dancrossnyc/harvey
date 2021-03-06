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

#include "../port/error.h"

#include "sys.h"

#include <tos.h>

#include "ureg.h"

extern int nosmp;

typedef struct {
	uintptr ip;
	Ureg *arg0;
	char *arg1;
	char msg[ERRMAX];
	Ureg *old;
	Ureg ureg;
} NFrame;

/*
 *   Return user to state before notify()
 */
void
noted(Ureg *cur, uintptr arg0)
{
	Proc *up = externup();
	NFrame *nf;
	Note note;
	Ureg *nur;

	qlock(&up->debug);
	if(arg0 != NRSTR && !up->notified){
		qunlock(&up->debug);
		pprint("suicide: call to noted when not notified\n");
		pexit("Suicide", 0);
	}
	up->notified = 0;
	fpunoted();

	nf = up->ureg;

	/* sanity clause */
	if(!okaddr(PTR2UINT(nf), sizeof(NFrame), 0)){
		qunlock(&up->debug);
		pprint("suicide: bad ureg %#p in noted\n", nf);
		pexit("Suicide", 0);
	}

	nur = &nf->ureg;
	/* don't let user change system flags */
#if 0
	nur->flags &= (Of|Df|Sf|Zf|Af|Pf|Cf);
	nur->flags |= cur->flags & ~(Of|Df|Sf|Zf|Af|Pf|Cf);
#endif
	memmove(cur, nur, sizeof(Ureg));

	switch((int)arg0){
	case NCONT:
	case NRSTR:
		if(!okaddr(nur->ip, BY2SE, 0) || !okaddr(nur->sp, BY2SE, 0)){
			qunlock(&up->debug);
			pprint("suicide: trap in noted pc=%#p sp=%#p\n",
			       nur->ip, nur->sp);
			pexit("Suicide", 0);
		}
		up->ureg = nf->old;
		qunlock(&up->debug);
		break;
	case NSAVE:
		if(!okaddr(nur->ip, BY2SE, 0) || !okaddr(nur->sp, BY2SE, 0)){
			qunlock(&up->debug);
			pprint("suicide: trap in noted pc=%#p sp=%#p\n",
			       nur->ip, nur->sp);
			pexit("Suicide", 0);
		}
		qunlock(&up->debug);

		splhi();
		nf->arg1 = nf->msg;
		nf->arg0 = &nf->ureg;
		cur->bp = PTR2UINT(nf->arg0);
		nf->ip = 0;
		cur->sp = PTR2UINT(nf);
		break;
	default:
		memmove(&note, &up->lastnote, sizeof(Note));
		qunlock(&up->debug);
		pprint("suicide: bad arg %#p in noted: %s\n", arg0, note.msg);
		pexit(note.msg, 0);
		break;
	case NDFLT:
		memmove(&note, &up->lastnote, sizeof(Note));
		qunlock(&up->debug);
		if(note.flag == NDebug)
			pprint("suicide: %s\n", note.msg);
		pexit(note.msg, note.flag != NDebug);
		break;
	}
}

/*
 *  Call user, if necessary, with note.
 *  Pass user the Ureg struct and the note on his stack.
 */
int
notify(Ureg *ureg)
{
	Proc *up = externup();
	int l;
	Mpl pl;
	Note note;
	uintptr sp;
	NFrame *nf;

	/*
	 * Calls procctl splhi, see comment in procctl for the reasoning.
	 */
	if(up->procctl)
		procctl(up);
	if(up->nnote == 0)
		return 0;

	fpunotify(ureg);

	pl = spllo();
	qlock(&up->debug);

	up->notepending = 0;
	memmove(&note, &up->note[0], sizeof(Note));
	if(strncmp(note.msg, "sys:", 4) == 0){
		l = strlen(note.msg);
		if(l > ERRMAX - sizeof(" pc=0x0123456789abcdef"))
			l = ERRMAX - sizeof(" pc=0x0123456789abcdef");
		sprint(note.msg + l, " pc=%#p", ureg->ip);
	}

	if(note.flag != NUser && (up->notified || up->notify == nil)){
		qunlock(&up->debug);
		if(note.flag == NDebug)
			pprint("suicide: %s\n", note.msg);
		pexit(note.msg, note.flag != NDebug);
	}

	if(up->notified){
		qunlock(&up->debug);
		splhi();
		return 0;
	}

	if(up->notify == nil){
		qunlock(&up->debug);
		pexit(note.msg, note.flag != NDebug);
	}
	if(!okaddr(PTR2UINT(up->notify), sizeof(ureg->ip), 0)){
		qunlock(&up->debug);
		pprint("suicide: bad function address %#p in notify\n",
		       up->notify);
		pexit("Suicide", 0);
	}

	sp = ureg->sp - ROUNDUP(sizeof(NFrame), 16) - 128;	  // amd64 red zone, also wanted by go stack traces
	if(!okaddr(sp, sizeof(NFrame), 1)){
		qunlock(&up->debug);
		pprint("suicide: bad stack address %#p in notify\n", sp);
		pexit("Suicide", 0);
	}

	nf = UINT2PTR(sp);
	memmove(&nf->ureg, ureg, sizeof(Ureg));
	nf->old = up->ureg;
	up->ureg = nf; /* actually the NFrame, for noted */
	memmove(nf->msg, note.msg, ERRMAX);
	nf->arg1 = nf->msg;
	nf->arg0 = &nf->ureg;
	ureg->a0 = (uintptr)nf->arg0;
	ureg->a1 = (uintptr)nf->arg1;
	//print("Setting di to %p and si to %p\n", ureg->di, ureg->si);
	ureg->bp = PTR2UINT(nf->arg0);
	nf->ip = 0;

	ureg->sp = sp;
	ureg->ip = PTR2UINT(up->notify);
	up->notified = 1;
	up->nnote--;
	memmove(&up->lastnote, &note, sizeof(Note));
	memmove(&up->note[0], &up->note[1], up->nnote * sizeof(Note));

	qunlock(&up->debug);
	splx(pl);

	return 1;
}

void
noerrorsleft(void)
{
	Proc *up = externup();
	int i;

	if(up->nerrlab){
		/* NIX processes will have a waserror in their handler */
		if(up->ac != nil && up->nerrlab == 1)
			return;

		print("bad errstack: %d extra\n", up->nerrlab);
		for(i = 0; i < NERR; i++)
			print("sp=%#p pc=%#p\n",
			      up->errlab[i].sp, up->errlab[i].pc);
		panic("error stack");
	}
}

int printallsyscalls = 0;

void
syscall(unsigned int scallnr, Ureg *ureg)
{
	// can only handle 6 args right now.
	uintptr a0, a1, a2, a3;
	uintptr a4, a5;
	if(0 && printallsyscalls)
		dumpgpr(ureg);

	a0 = ureg->a0;
	a1 = ureg->a1;
	a2 = ureg->a2;
	a3 = ureg->a3;
	a4 = ureg->a4;
	a5 = ureg->a5;
	Proc *up = externup();
	if(1)
		iprint("Syscall %d, %lx, %lx, %lx %lx %lx %lx\n", scallnr, a0, a1, a2, a3, a4, a5);
	char *e;
	uintptr sp;
	int s;
	i64 startns, stopns;
	Ar0 ar0;
	static Ar0 zar0;

	if(!userureg(ureg))
		panic("syscall: userureg is false; ip %#llx\n", ureg->ip);

	cycles(&up->kentry);

	machp()->syscall++;
	up->nsyscall++;
	up->nqsyscall++;
	up->insyscall = 1;
	up->pc = ureg->ip;
	up->dbgreg = ureg;
	sp = ureg->sp;
	//print("ureg -> sp says %p\n", ureg->sp);
	startns = stopns = 0;
	if(0)
		print("so far syscall!\n");
	if(up->pid == 0 || printallsyscalls){
		syscallfmt('E', scallnr, nil, startns, stopns, a0, a1, a2, a3, a4, a5);
		if(up->syscalltrace){
			print("E %s\n", up->syscalltrace);
			//free(up->syscalltrace);
			up->syscalltrace = nil;
		}
	}

	if(up->procctl == Proc_tracesyscall){
		/*
		 * Redundant validaddr.  Do we care?
		 * Tracing syscalls is not exactly a fast path...
		 * Beware, validaddr currently does a pexit rather
		 * than an error if there's a problem; that might
		 * change in the future.
		 */
		if(sp < (USTKTOP - BIGPGSZ) || sp > (USTKTOP - sizeof(up->arg) - BY2SE))
			validaddr(UINT2PTR(sp), sizeof(up->arg) + BY2SE, 0);

		syscallfmt('E', scallnr, &ar0, startns, stopns, a0, a1, a2, a3, a4, a5);
		up->procctl = Proc_stopme;
		procctl(up);
		if(up->syscalltrace)
			free(up->syscalltrace);
		up->syscalltrace = nil;
		startns = todget(nil);
	}
	if(0)
		print("more syscall!\n");
	up->scallnr = scallnr;
	if(scallnr == RFORK)
		fpusysrfork(ureg);
	spllo();

	sp = ureg->sp;
	up->nerrlab = 0;
	ar0 = zar0;
	if(!waserror()){
		if(scallnr >= nsyscall || systab[scallnr].f == nil){
			pprint("bad sys call number %d pc %#llx\n",
			       scallnr, ureg->ip);
			postnote(up, 1, "sys: bad sys call", NDebug);
			error(Ebadarg);
		}

		if(sp < (USTKTOP - BIGPGSZ) || sp > (USTKTOP - sizeof(up->arg) - BY2SE)){
			//print("check it\n");
			validaddr(UINT2PTR(sp), sizeof(up->arg) + BY2SE, 0);
		}

		memmove(up->arg, UINT2PTR(sp + BY2SE), sizeof(up->arg));
		up->psstate = systab[scallnr].n;
		//if (1) hi("call syscall!\n");
		systab[scallnr].f(&ar0, a0, a1, a2, a3, a4, a5);
		//	if (1) hi("it returned!\n");
		poperror();
	} else {
		/* failure: save the error buffer for errstr */
		e = up->syserrstr;
		up->syserrstr = up->errstr;
		up->errstr = e;
		if(DBGFLG && up->pid == 1)
			iprint("%s: syscall %s error %s\n",
			       up->text, systab[scallnr].n, up->syserrstr);
		ar0 = systab[scallnr].r;
	}

	/*
	 * NIX: for the execac() syscall, what follows is done within
	 * the system call, because it never returns.
	 * See acore.c:/^retfromsyscall
	 */

	noerrorsleft();

	/*
	 * Put return value in frame.
	 */
	if(0)
		print("return is %p\n", ar0.p);
	ureg->a0 = ar0.p;
	if(0)
		print("ureg->ip is %p val %p\n", &ureg->ip, ureg->ip);

	if(up->pid == 0 || printallsyscalls){
		stopns = todget(nil);
		syscallfmt('X', scallnr, &ar0, startns, stopns, a0, a1, a2, a3, a4, a5);
		if(up->syscalltrace){
			print("X %s\n", up->syscalltrace);
			free(up->syscalltrace);
			up->syscalltrace = nil;
		}
	}

	if(up->procctl == Proc_tracesyscall){
		u8 what = 'X';
		stopns = todget(nil);
		up->procctl = Proc_stopme;
		if(scallnr == RFORK && a0 & RFPROC && ar0.i > 0)
			what = 'F';
		syscallfmt(what, scallnr, &ar0, startns, stopns, a0, a1, a2, a3, a4, a5);
		s = splhi();
		procctl(up);
		splx(s);
		if(up->syscalltrace)
			free(up->syscalltrace);
		up->syscalltrace = nil;
	} else if(up->procctl == Proc_totc || up->procctl == Proc_toac)
		procctl(up);

	if(0)
		hi("past sysretfmt\n");
	up->insyscall = 0;
	up->psstate = 0;

	if(scallnr == NOTED)
		noted(ureg, a0);

	if(0)
		hi("now to splhi\n");
	splhi();
	if(scallnr != RFORK && (up->procctl || up->nnote))
		notify(ureg);

	/* if we delayed sched because we held a lock, sched now */
	if(up->delaysched){
		sched();
		splhi();
	}
	if(0)
		hi("call kexit\n");
	kexit(ureg);
	if(0)
		hi("done kexit\n");
}

uintptr
sysexecstack(uintptr stack, int argc)
{
	uintptr sp;
	/*
	 * Given a current bottom-of-stack and a count
	 * of pointer arguments to be pushed onto it followed
	 * by an integer argument count, return a suitably
	 * aligned new bottom-of-stack which will satisfy any
	 * hardware stack-alignment contraints.
	 * Rounding the stack down to be aligned with the
	 * natural size of a pointer variable usually suffices,
	 * but some architectures impose further restrictions,
	 * e.g. 32-bit SPARC, where the stack must be 8-byte
	 * aligned although pointers and integers are 32-bits.
	 */
	USED(argc);

	sp = STACKALIGN(stack);
	/* but we need to align the stack to 16 bytes, not 8, once
	 * nil
	 * argv
	 * argc
	 * are pushed. So if we have odd arguments, we need an odd-8-byte
	 * aligned stack; else, an even aligned stack.
	 */
	if(argc & 1)
		sp -= sp & 8 ? 0 : 8;
	else
		sp -= sp & 8 ? 8 : 0;
	//print("For %d args, sp is now %p\n", argc, sp);
	return sp;
}

void *
sysexecregs(uintptr entry, u32 ssize, void *tos)
{
	Proc *up = externup();
	uintptr *sp;
	Ureg *ureg;

	// We made sure it was correctly aligned in sysexecstack, above.
	if(ssize & 0xf){
		print("your stack is wrong: stacksize is not 16-byte aligned: %d\n", ssize);
		panic("misaligned stack in sysexecregs");
	}
	sp = (uintptr *)(USTKTOP - ssize);
	if(0)
		print("sysexecregs: entry %p sp %p tos %p\n", entry, sp, tos);
	ureg = up->dbgreg;
	ureg->sp = PTR2UINT(sp);
	ureg->ip = entry;
	ureg->epc = entry;
	ureg->a2 = USTKTOP - sizeof(Tos);
	if(0)
		print("SET ip @ %p to %p\n", &ureg->ip, entry);

	/*
	 * return the address of kernel/user shared data
	 * (e.g. clock stuff)
	 */
	return UINT2PTR(USTKTOP - sizeof(Tos));
}

void
sysprocsetup(Proc *p)
{
	fpusysprocsetup(p);
}

void
sysrforkchild(Proc *child, Proc *parent)
{
	Ureg *cureg;
// If STACKPAD is 1 things go very bad very quickly.
// But it is the right value ...
#define STACKPAD 0 /* for return PC? */
	/*
	 * Add STACKPAD*BY2SE to the stack to account for
	 *  - the return PC
	 *  (NOT NOW) - trap's arguments (syscallnr, ureg)
	 */
	child->sched.sp = PTR2UINT(child->kstack + KSTACK - ((sizeof(Ureg) + STACKPAD * BY2SE)));
	child->sched.pc = PTR2UINT(sysrforkret);

	cureg = (Ureg *)(child->sched.sp + STACKPAD * BY2SE);
	memmove(cureg, parent->dbgreg, sizeof(Ureg));

	/* Things from bottom of syscall which were never executed */
	child->psstate = 0;
	child->insyscall = 0;
	if(0)
		print("Child SP set to %p\n", (void *)child->sched.sp);
	if(0)
		print("NOTE: UP is wrong, ignoreit\n");
	if(0)
		dumpgpr(cureg);

	fpusysrforkchild(child, parent);
}
