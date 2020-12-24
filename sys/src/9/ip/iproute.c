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

#include "ip.h"

static void walkadd(Fs *, Route **, Route *);
static void addnode(Fs *, Route **, Route *);
static void calcd(Route *);

/* these are used for all instances of IP */
static Route *v4freelist;
static Route *v6freelist;
static RWlock routelock;
static u32 v4routegeneration, v6routegeneration;

static void
freeroute(Route *r)
{
	Route **l;

	r->RouteTree.left = nil;
	r->RouteTree.right = nil;
	if(r->RouteTree.type & Rv4)
		l = &v4freelist;
	else
		l = &v6freelist;
	r->RouteTree.mid = *l;
	*l = r;
}

static Route *
allocroute(int type)
{
	Route *r;
	int n;
	Route **l;

	if(type & Rv4){
		n = sizeof(RouteTree) + sizeof(V4route);
		l = &v4freelist;
	} else {
		n = sizeof(RouteTree) + sizeof(V6route);
		l = &v6freelist;
	}

	r = *l;
	if(r != nil){
		*l = r->RouteTree.mid;
	} else {
		r = malloc(n);
		if(r == nil)
			panic("out of routing nodes");
	}
	memset(r, 0, n);
	r->RouteTree.type = type;
	r->RouteTree.ifc = nil;
	r->RouteTree.ref = 1;

	return r;
}

static void
addqueue(Route **q, Route *r)
{
	Route *l;

	if(r == nil)
		return;

	l = allocroute(r->RouteTree.type);
	l->RouteTree.mid = *q;
	*q = l;
	l->RouteTree.left = r;
}

/*
 *   compare 2 v6 addresses
 */
static int
lcmp(u32 *a, u32 *b)
{
	int i;

	for(i = 0; i < IPllen; i++){
		if(a[i] > b[i])
			return 1;
		if(a[i] < b[i])
			return -1;
	}
	return 0;
}

/*
 *  compare 2 v4 or v6 ranges
 */
enum {
	Rpreceeds,
	Rfollows,
	Requals,
	Rcontains,
	Rcontained,
};

static int
rangecompare(Route *a, Route *b)
{
	if(a->RouteTree.type & Rv4){
		if(a->v4.endaddress < b->v4.address)
			return Rpreceeds;

		if(a->v4.address > b->v4.endaddress)
			return Rfollows;

		if(a->v4.address <= b->v4.address && a->v4.endaddress >= b->v4.endaddress){
			if(a->v4.address == b->v4.address && a->v4.endaddress == b->v4.endaddress)
				return Requals;
			return Rcontains;
		}
		return Rcontained;
	}

	if(lcmp(a->v6.endaddress, b->v6.address) < 0)
		return Rpreceeds;

	if(lcmp(a->v6.address, b->v6.endaddress) > 0)
		return Rfollows;

	if(lcmp(a->v6.address, b->v6.address) <= 0 && lcmp(a->v6.endaddress, b->v6.endaddress) >= 0){
		if(lcmp(a->v6.address, b->v6.address) == 0 && lcmp(a->v6.endaddress, b->v6.endaddress) == 0)
			return Requals;
		return Rcontains;
	}

	return Rcontained;
}

static void
copygate(Route *old, Route *new)
{
	if(new->RouteTree.type & Rv4)
		memmove(old->v4.gate, new->v4.gate, IPv4addrlen);
	else
		memmove(old->v6.gate, new->v6.gate, IPaddrlen);
}

/*
 *  walk down a tree adding nodes back in
 */
static void
walkadd(Fs *f, Route **root, Route *p)
{
	Route *l, *r;

	l = p->RouteTree.left;
	r = p->RouteTree.right;
	p->RouteTree.left = 0;
	p->RouteTree.right = 0;
	addnode(f, root, p);
	if(l)
		walkadd(f, root, l);
	if(r)
		walkadd(f, root, r);
}

/*
 *  calculate depth
 */
static void
calcd(Route *p)
{
	Route *q;
	int d;

	if(p){
		d = 0;
		q = p->RouteTree.left;
		if(q)
			d = q->RouteTree.depth;
		q = p->RouteTree.right;
		if(q && q->RouteTree.depth > d)
			d = q->RouteTree.depth;
		q = p->RouteTree.mid;
		if(q && q->RouteTree.depth > d)
			d = q->RouteTree.depth;
		p->RouteTree.depth = d + 1;
	}
}

/*
 *  balance the tree at the current node
 */
static void
balancetree(Route **cur)
{
	Route *p, *l, *r;
	int dl, dr;

	/*
	 * if left and right are
	 * too out of balance,
	 * rotate tree node
	 */
	p = *cur;
	dl = 0;
	if((l = p->RouteTree.left) != nil)
		dl = l->RouteTree.depth;
	dr = 0;
	if((r = p->RouteTree.right) != nil)
		dr = r->RouteTree.depth;

	if(dl > dr + 1){
		p->RouteTree.left = l->RouteTree.right;
		l->RouteTree.right = p;
		*cur = l;
		calcd(p);
		calcd(l);
	} else if(dr > dl + 1){
		p->RouteTree.right = r->RouteTree.left;
		r->RouteTree.left = p;
		*cur = r;
		calcd(p);
		calcd(r);
	} else
		calcd(p);
}

/*
 *  add a new node to the tree
 */
static void
addnode(Fs *f, Route **cur, Route *new)
{
	Route *p;

	p = *cur;
	if(p == 0){
		*cur = new;
		new->RouteTree.depth = 1;
		return;
	}

	switch(rangecompare(new, p)){
	case Rpreceeds:
		addnode(f, &p->RouteTree.left, new);
		break;
	case Rfollows:
		addnode(f, &p->RouteTree.right, new);
		break;
	case Rcontains:
		/*
		 *  if new node is superset
		 *  of tree node,
		 *  replace tree node and
		 *  queue tree node to be
		 *  merged into root.
		 */
		*cur = new;
		new->RouteTree.depth = 1;
		addqueue(&f->queue, p);
		break;
	case Requals:
		/*
		 *  supercede the old entry if the old one isn't
		 *  a local interface.
		 */
		if((p->RouteTree.type & Rifc) == 0){
			p->RouteTree.type = new->RouteTree.type;
			p->RouteTree.ifcid = -1;
			copygate(p, new);
		} else if(new->RouteTree.type & Rifc)
			p->RouteTree.ref++;
		freeroute(new);
		break;
	case Rcontained:
		addnode(f, &p->RouteTree.mid, new);
		break;
	}

	balancetree(cur);
}

#define V4H(a) ((a & 0x07ffffff) >> (32 - Lroot - 5))

void
v4addroute(Fs *f, char *tag, u8 *a, u8 *mask, u8 *gate, int type)
{
	Route *p;
	u32 sa;
	u32 m;
	u32 ea;
	int h, eh;

	m = nhgetl(mask);
	sa = nhgetl(a) & m;
	ea = sa | ~m;

	eh = V4H(ea);
	for(h = V4H(sa); h <= eh; h++){
		p = allocroute(Rv4 | type);
		p->v4.address = sa;
		p->v4.endaddress = ea;
		memmove(p->v4.gate, gate, sizeof(p->v4.gate));
		memmove(p->RouteTree.tag, tag, sizeof(p->RouteTree.tag));

		wlock(&routelock);
		addnode(f, &f->v4root[h], p);
		while((p = f->queue) != nil){
			f->queue = p->RouteTree.mid;
			walkadd(f, &f->v4root[h], p->RouteTree.left);
			freeroute(p);
		}
		wunlock(&routelock);
	}
	v4routegeneration++;

	ipifcaddroute(f, Rv4, a, mask, gate, type);
}

#define V6H(a) (((a)[IPllen - 1] & 0x07ffffff) >> (32 - Lroot - 5))
#define ISDFLT(a, mask, tag) ((ipcmp((a), v6Unspecified) == 0) && (ipcmp((mask), v6Unspecified) == 0) && (strcmp((tag), "ra") != 0))

void
v6addroute(Fs *f, char *tag, u8 *a, u8 *mask, u8 *gate, int type)
{
	Route *p;
	u32 sa[IPllen], ea[IPllen];
	u32 x, y;
	int h, eh;

	/*
	if(ISDFLT(a, mask, tag))
		f->v6p->cdrouter = -1;
	*/

	for(h = 0; h < IPllen; h++){
		x = nhgetl(a + 4 * h);
		y = nhgetl(mask + 4 * h);
		sa[h] = x & y;
		ea[h] = x | ~y;
	}

	eh = V6H(ea);
	for(h = V6H(sa); h <= eh; h++){
		p = allocroute(type);
		memmove(p->v6.address, sa, IPaddrlen);
		memmove(p->v6.endaddress, ea, IPaddrlen);
		memmove(p->v6.gate, gate, IPaddrlen);
		memmove(p->RouteTree.tag, tag, sizeof(p->RouteTree.tag));

		wlock(&routelock);
		addnode(f, &f->v6root[h], p);
		while((p = f->queue) != nil){
			f->queue = p->RouteTree.mid;
			walkadd(f, &f->v6root[h], p->RouteTree.left);
			freeroute(p);
		}
		wunlock(&routelock);
	}
	v6routegeneration++;

	ipifcaddroute(f, 0, a, mask, gate, type);
}

Route **
looknode(Route **cur, Route *r)
{
	Route *p;

	for(;;){
		p = *cur;
		if(p == 0)
			return 0;

		switch(rangecompare(r, p)){
		case Rcontains:
			return 0;
		case Rpreceeds:
			cur = &p->RouteTree.left;
			break;
		case Rfollows:
			cur = &p->RouteTree.right;
			break;
		case Rcontained:
			cur = &p->RouteTree.mid;
			break;
		case Requals:
			return cur;
		}
	}
}

void
v4delroute(Fs *f, u8 *a, u8 *mask, int dolock)
{
	Route **r, *p;
	Route rt;
	int h, eh;
	u32 m;

	m = nhgetl(mask);
	rt.v4.address = nhgetl(a) & m;
	rt.v4.endaddress = rt.v4.address | ~m;
	rt.RouteTree.type = Rv4;

	eh = V4H(rt.v4.endaddress);
	for(h = V4H(rt.v4.address); h <= eh; h++){
		if(dolock)
			wlock(&routelock);
		r = looknode(&f->v4root[h], &rt);
		if(r){
			p = *r;
			if(--(p->RouteTree.ref) == 0){
				*r = 0;
				addqueue(&f->queue, p->RouteTree.left);
				addqueue(&f->queue, p->RouteTree.mid);
				addqueue(&f->queue, p->RouteTree.right);
				freeroute(p);
				while((p = f->queue) != nil){
					f->queue = p->RouteTree.mid;
					walkadd(f, &f->v4root[h], p->RouteTree.left);
					freeroute(p);
				}
			}
		}
		if(dolock)
			wunlock(&routelock);
	}
	v4routegeneration++;

	ipifcremroute(f, Rv4, a, mask);
}

void
v6delroute(Fs *f, u8 *a, u8 *mask, int dolock)
{
	Route **r, *p;
	Route rt;
	int h, eh;
	u32 x, y;

	for(h = 0; h < IPllen; h++){
		x = nhgetl(a + 4 * h);
		y = nhgetl(mask + 4 * h);
		rt.v6.address[h] = x & y;
		rt.v6.endaddress[h] = x | ~y;
	}
	rt.RouteTree.type = 0;

	eh = V6H(rt.v6.endaddress);
	for(h = V6H(rt.v6.address); h <= eh; h++){
		if(dolock)
			wlock(&routelock);
		r = looknode(&f->v6root[h], &rt);
		if(r){
			p = *r;
			if(--(p->RouteTree.ref) == 0){
				*r = 0;
				addqueue(&f->queue, p->RouteTree.left);
				addqueue(&f->queue, p->RouteTree.mid);
				addqueue(&f->queue, p->RouteTree.right);
				freeroute(p);
				while((p = f->queue) != nil){
					f->queue = p->RouteTree.mid;
					walkadd(f, &f->v6root[h], p->RouteTree.left);
					freeroute(p);
				}
			}
		}
		if(dolock)
			wunlock(&routelock);
	}
	v6routegeneration++;

	ipifcremroute(f, 0, a, mask);
}

Route *
v4lookup(Fs *f, u8 *a, Conv *c)
{
	Route *p, *q;
	u32 la;
	u8 gate[IPaddrlen];
	Ipifc *ifc;

	if(c != nil && c->r != nil && c->r->RouteTree.ifc != nil && c->rgen == v4routegeneration)
		return c->r;

	la = nhgetl(a);
	q = nil;
	for(p = f->v4root[V4H(la)]; p;)
		if(la >= p->v4.address){
			if(la <= p->v4.endaddress){
				q = p;
				p = p->RouteTree.mid;
			} else
				p = p->RouteTree.right;
		} else
			p = p->RouteTree.left;

	if(q && (q->RouteTree.ifc == nil || q->RouteTree.ifcid != q->RouteTree.ifc->ifcid)){
		if(q->RouteTree.type & Rifc){
			hnputl(gate + IPv4off, q->v4.address);
			memmove(gate, v4prefix, IPv4off);
		} else
			v4tov6(gate, q->v4.gate);
		ifc = findipifc(f, gate, q->RouteTree.type);
		if(ifc == nil)
			return nil;
		q->RouteTree.ifc = ifc;
		q->RouteTree.ifcid = ifc->ifcid;
	}

	if(c != nil){
		c->r = q;
		c->rgen = v4routegeneration;
	}

	return q;
}

Route *
v6lookup(Fs *f, u8 *a, Conv *c)
{
	Route *p, *q;
	u32 la[IPllen];
	int h;
	u32 x, y;
	u8 gate[IPaddrlen];
	Ipifc *ifc;

	if(memcmp(a, v4prefix, IPv4off) == 0){
		q = v4lookup(f, a + IPv4off, c);
		if(q != nil)
			return q;
	}

	if(c != nil && c->r != nil && c->r->RouteTree.ifc != nil && c->rgen == v6routegeneration)
		return c->r;

	for(h = 0; h < IPllen; h++)
		la[h] = nhgetl(a + 4 * h);

	q = 0;
	for(p = f->v6root[V6H(la)]; p;){
		for(h = 0; h < IPllen; h++){
			x = la[h];
			y = p->v6.address[h];
			if(x == y)
				continue;
			if(x < y){
				p = p->RouteTree.left;
				goto next;
			}
			break;
		}
		for(h = 0; h < IPllen; h++){
			x = la[h];
			y = p->v6.endaddress[h];
			if(x == y)
				continue;
			if(x > y){
				p = p->RouteTree.right;
				goto next;
			}
			break;
		}
		q = p;
		p = p->RouteTree.mid;
	next:;
	}

	if(q && (q->RouteTree.ifc == nil || q->RouteTree.ifcid != q->RouteTree.ifc->ifcid)){
		if(q->RouteTree.type & Rifc){
			for(h = 0; h < IPllen; h++)
				hnputl(gate + 4 * h, q->v6.address[h]);
			ifc = findipifc(f, gate, q->RouteTree.type);
		} else
			ifc = findipifc(f, q->v6.gate, q->RouteTree.type);
		if(ifc == nil)
			return nil;
		q->RouteTree.ifc = ifc;
		q->RouteTree.ifcid = ifc->ifcid;
	}
	if(c != nil){
		c->r = q;
		c->rgen = v6routegeneration;
	}

	return q;
}

void
routetype(int type, char *p)
{
	memset(p, ' ', 4);
	p[4] = 0;
	if(type & Rv4)
		*p++ = '4';
	else
		*p++ = '6';
	if(type & Rifc)
		*p++ = 'i';
	if(type & Runi)
		*p++ = 'u';
	else if(type & Rbcast)
		*p++ = 'b';
	else if(type & Rmulti)
		*p++ = 'm';
	if(type & Rptpt)
		*p = 'p';
}

static char *rformat = "%-15I %-4M %-15I %4.4s %4.4s %3s\n";

void
convroute(Route *r, u8 *addr, u8 *mask, u8 *gate, char *t, int *nifc)
{
	int i;

	if(r->RouteTree.type & Rv4){
		memmove(addr, v4prefix, IPv4off);
		hnputl(addr + IPv4off, r->v4.address);
		memset(mask, 0xff, IPv4off);
		hnputl(mask + IPv4off, ~(r->v4.endaddress ^ r->v4.address));
		memmove(gate, v4prefix, IPv4off);
		memmove(gate + IPv4off, r->v4.gate, IPv4addrlen);
	} else {
		for(i = 0; i < IPllen; i++){
			hnputl(addr + 4 * i, r->v6.address[i]);
			hnputl(mask + 4 * i, ~(r->v6.endaddress[i] ^ r->v6.address[i]));
		}
		memmove(gate, r->v6.gate, IPaddrlen);
	}

	routetype(r->RouteTree.type, t);

	if(r->RouteTree.ifc)
		*nifc = r->RouteTree.ifc->conv->x;
	else
		*nifc = -1;
}

/*
 *  this code is not in rr to reduce stack size
 */
static void
sprintroute(Route *r, Routewalk *rw)
{
	int nifc, n;
	char t[5], *iname, ifbuf[5];
	u8 addr[IPaddrlen], mask[IPaddrlen], gate[IPaddrlen];
	char *p;

	convroute(r, addr, mask, gate, t, &nifc);
	iname = "-";
	if(nifc != -1){
		iname = ifbuf;
		snprint(ifbuf, sizeof ifbuf, "%d", nifc);
	}
	p = seprint(rw->p, rw->e, rformat, addr, mask, gate, t, r->RouteTree.tag, iname);
	if(rw->o < 0){
		n = p - rw->p;
		if(n > -rw->o){
			memmove(rw->p, rw->p - rw->o, n + rw->o);
			rw->p = p + rw->o;
		}
		rw->o += n;
	} else
		rw->p = p;
}

/*
 *  recurse descending tree, applying the function in Routewalk
 */
static int
rr(Route *r, Routewalk *rw)
{
	int h;

	if(rw->e <= rw->p)
		return 0;
	if(r == nil)
		return 1;

	if(rr(r->RouteTree.left, rw) == 0)
		return 0;

	if(r->RouteTree.type & Rv4)
		h = V4H(r->v4.address);
	else
		h = V6H(r->v6.address);

	if(h == rw->h)
		rw->walk(r, rw);

	if(rr(r->RouteTree.mid, rw) == 0)
		return 0;

	return rr(r->RouteTree.right, rw);
}

void
ipwalkroutes(Fs *f, Routewalk *rw)
{
	rlock(&routelock);
	if(rw->e > rw->p){
		for(rw->h = 0; rw->h < nelem(f->v4root); rw->h++)
			if(rr(f->v4root[rw->h], rw) == 0)
				break;
	}
	if(rw->e > rw->p){
		for(rw->h = 0; rw->h < nelem(f->v6root); rw->h++)
			if(rr(f->v6root[rw->h], rw) == 0)
				break;
	}
	runlock(&routelock);
}

i32
routeread(Fs *f, char *p, u32 offset, int n)
{
	Routewalk rw;

	rw.p = p;
	rw.e = p + n;
	rw.o = -offset;
	rw.walk = sprintroute;

	ipwalkroutes(f, &rw);

	return rw.p - p;
}

/*
 *  this code is not in routeflush to reduce stack size
 */
void
delroute(Fs *f, Route *r, int dolock)
{
	u8 addr[IPaddrlen];
	u8 mask[IPaddrlen];
	u8 gate[IPaddrlen];
	char t[5];
	int nifc;

	convroute(r, addr, mask, gate, t, &nifc);
	if(r->RouteTree.type & Rv4)
		v4delroute(f, addr + IPv4off, mask + IPv4off, dolock);
	else
		v6delroute(f, addr, mask, dolock);
}

/*
 *  recurse until one route is deleted
 *    returns 0 if nothing is deleted, 1 otherwise
 */
int
routeflush(Fs *f, Route *r, char *tag)
{
	if(r == nil)
		return 0;
	if(routeflush(f, r->RouteTree.mid, tag))
		return 1;
	if(routeflush(f, r->RouteTree.left, tag))
		return 1;
	if(routeflush(f, r->RouteTree.right, tag))
		return 1;
	if((r->RouteTree.type & Rifc) == 0){
		if(tag == nil || strncmp(tag, r->RouteTree.tag, sizeof(r->RouteTree.tag)) == 0){
			delroute(f, r, 0);
			return 1;
		}
	}
	return 0;
}

Route *
iproute(Fs *fs, u8 *ip)
{
	if(isv4(ip))
		return v4lookup(fs, ip + IPv4off, nil);
	else
		return v6lookup(fs, ip, nil);
}

static void
printroute(Route *r)
{
	int nifc;
	char t[5], *iname, ifbuf[5];
	u8 addr[IPaddrlen], mask[IPaddrlen], gate[IPaddrlen];

	convroute(r, addr, mask, gate, t, &nifc);
	iname = "-";
	if(nifc != -1){
		iname = ifbuf;
		snprint(ifbuf, sizeof ifbuf, "%d", nifc);
	}
	print(rformat, addr, mask, gate, t, r->RouteTree.tag, iname);
}

i32
routewrite(Fs *f, Chan *c, char *p, int n)
{
	Proc *up = externup();
	int h, changed;
	char *tag;
	Cmdbuf *cb;
	u8 addr[IPaddrlen];
	u8 mask[IPaddrlen];
	u8 gate[IPaddrlen];
	IPaux *a, *na;
	Route *q;

	cb = parsecmd(p, n);
	if(waserror()){
		free(cb);
		nexterror();
	}

	if(strcmp(cb->f[0], "flush") == 0){
		tag = cb->f[1];
		for(h = 0; h < nelem(f->v4root); h++)
			for(changed = 1; changed;){
				wlock(&routelock);
				changed = routeflush(f, f->v4root[h], tag);
				wunlock(&routelock);
			}
		for(h = 0; h < nelem(f->v6root); h++)
			for(changed = 1; changed;){
				wlock(&routelock);
				changed = routeflush(f, f->v6root[h], tag);
				wunlock(&routelock);
			}
	} else if(strcmp(cb->f[0], "remove") == 0){
		if(cb->nf < 3)
			error(Ebadarg);
		if(parseip(addr, cb->f[1]) == -1)
			error(Ebadip);
		parseipmask(mask, cb->f[2]);
		if(memcmp(addr, v4prefix, IPv4off) == 0)
			v4delroute(f, addr + IPv4off, mask + IPv4off, 1);
		else
			v6delroute(f, addr, mask, 1);
	} else if(strcmp(cb->f[0], "add") == 0){
		if(cb->nf < 4)
			error(Ebadarg);
		if(parseip(addr, cb->f[1]) == -1 ||
		   parseip(gate, cb->f[3]) == -1)
			error(Ebadip);
		parseipmask(mask, cb->f[2]);
		tag = "none";
		if(c != nil){
			a = c->aux;
			tag = a->tag;
		}
		if(memcmp(addr, v4prefix, IPv4off) == 0)
			v4addroute(f, tag, addr + IPv4off, mask + IPv4off, gate + IPv4off, 0);
		else
			v6addroute(f, tag, addr, mask, gate, 0);
	} else if(strcmp(cb->f[0], "tag") == 0){
		if(cb->nf < 2)
			error(Ebadarg);

		a = c->aux;
		na = newipaux(a->owner, cb->f[1]);
		c->aux = na;
		free(a);
	} else if(strcmp(cb->f[0], "route") == 0){
		if(cb->nf < 2)
			error(Ebadarg);
		if(parseip(addr, cb->f[1]) == -1)
			error(Ebadip);

		q = iproute(f, addr);
		print("%I: ", addr);
		if(q == nil)
			print("no route\n");
		else
			printroute(q);
	}

	poperror();
	free(cb);
	return n;
}
