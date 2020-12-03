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

#include "amd64.h"

/*
 * To do:
 *	mmukmapsync grot for >1 processor;
 *	mmuptcopy (PteSHARED trick?);
 */

#define	PML4		((uintptr)0xFFFFFFFFFFFFF000ULL)

#define PML4E(va) ((PTE*)((((va)>>39)*sizeof(PTE))|(~0ULL<<12)))
#define PML3E(va) ((PTE*)((((va)>>30)*sizeof(PTE))|(~0ULL<<21)))
#define PML2E(va) ((PTE*)((((va)>>21)*sizeof(PTE))|(~0ULL<<30)))
#define PML1E(va) ((PTE*)((((va)>>12)*sizeof(PTE))|(~0ULL<<39)))

#define PPN(x)		((x)&~(PGSZ-1))

static uintmem
recursive(void)
{
	PTE *pml4 = (PTE*)PML4;
	return PPN(pml4[PTSZ/sizeof(PTE)-1]);
}

void
mmukflushtlb(void)
{
	cr3put(machp()->MMU.pml4->pa);
}

// This actually moves to the kernel page table, clearing the
// user portion.
void
mmuflushtlb(void)
{
	machp()->tlbpurge++;
	cr3put(machp()->MMU.pml4->pa);
}

void
mmuflush(void)
{
	Proc *up = externup();
	Mpl pl;

	pl = splhi();
	up->newtlb = 1;
	mmuswitch(up);
	splx(pl);
}

static void
mmuptpunmap(Proc* proc)
{
	Page *page, *next;

	memset(UINT2PTR(proc->MMU.root->va), 0, PTSZ/2);
	for(next = nil, page = proc->MMU.root->next; page != nil; page = next){
		next = page->next;
		page->daddr = 0;
		memset(UINT2PTR(page->va), 0, PTSZ);
		page->next = proc->MMU.root->prev;
		proc->MMU.root->prev = page;
	}
	proc->MMU.root->next = nil;
}

static void
tabs(int n)
{
	int i;

	for(i = 0; i < n; i++)
		print("  ");
}

void
dumpptepg(int lvl, uintptr_t pa)
{
	PTE *pte;
	int tab, i;

	tab = 4 - lvl;
	pte = KADDR(pa);
	for(i = 0; i < PTSZ/sizeof(PTE); i++)
		if(pte[i] & PteP){
			tabs(tab);
			print("l%d %#p[%#05x]: %#llx\n", lvl, pa, i, pte[i]);

			/* skip kernel mappings */
			if((pte[i]&PteU) == 0){
				tabs(tab+1);
				print("...kern...\n");
				continue;
			}
			if(lvl > 2)
				dumpptepg(lvl-1, PPN(pte[i]));
		}
}

void
dumpmmu(Proc *p)
{
	int i;
	Page *pg;

	print("proc %#p pml4 %#P is pa %#llx\n", p, *(PTE*)PML4, p->MMU.root->pa);
	for(i = 3; i > 0; i--){
		print("page table pages at level %d:\n", i);
		for(pg = p->MMU.root->next; pg != nil; pg = pg->next){
			if(pg->daddr != i)
				continue;
			print("\tpg %#p = va %#llx pa %#llx"
				" daddr %#lx next %#p prev %#p\n",
				pg, pg->va, pg->pa, pg->daddr, pg->next, pg->prev);
		}
	}
	if(0)dumpptepg(4, machp()->MMU.pml4->pa);
}

void
dumpmmuwalk(uint64_t addr)
{
	int l;
	PTE *pte;

	if((l = mmuwalk(addr, 3, &pte)) >= 0)
		print("cpu%d: mmu l%d pte %#p = %llx\n", machp()->machno, l, pte, *pte);
	if((l = mmuwalk(addr, 2, &pte)) >= 0)
		print("cpu%d: mmu l%d pte %#p = %llx\n", machp()->machno, l, pte, *pte);
	if((l = mmuwalk(addr, 1, &pte)) >= 0)
		print("cpu%d: mmu l%d pte %#p = %llx\n", machp()->machno, l, pte, *pte);
	if((l = mmuwalk(addr, 0, &pte)) >= 0)
		print("cpu%d: mmu l%d pte %#p = %llx\n", machp()->machno, l, pte, *pte);
}

static Page mmuptpfreelist;

static Page*
mmuptpalloc(void)
{
	void* va;
	Page *page;

	/*
	 * Do not really need a whole Page structure,
	 * but it makes testing this out a lot easier.
	 * Could keep a cache and free excess.
	 * Have to maintain any fiction for pexit?
	 */
	lock(&mmuptpfreelist.l);
	if((page = mmuptpfreelist.next) != nil){
		mmuptpfreelist.next = page->next;
		mmuptpfreelist.ref--;
		unlock(&mmuptpfreelist.l);

		if(page->ref++ != 0)
			panic("mmuptpalloc ref\n");
		page->prev = page->next = nil;
		memset(UINT2PTR(page->va), 0, PTSZ);

		if(page->pa == 0)
			panic("mmuptpalloc: free page with pa == 0");
		return page;
	}
	unlock(&mmuptpfreelist.l);

	if((page = malloc(sizeof(Page))) == nil){
		print("mmuptpalloc: Page alloc failed\n");

		return nil;
	}
	if((va = mallocalign(PTSZ, PTSZ, 0, 0)) == nil){
		print("mmuptpalloc: page table page alloc failed\n");
		free(page);
		return nil;
	}

	page->va = PTR2UINT(va);
	page->pa = PADDR(va);
	page->ref = 1;

	if(page->pa == 0)
		panic("mmuptpalloc: no pa");
	return page;
}

void
mmuswitch(Proc* proc)
{
	Mpl pl;

	pl = splhi();
	if(proc->newtlb){
		/*
 		 * NIX: We cannot clear our page tables if they are going to
		 * be used in the AC
		 */
		if(proc->ac == nil)
			mmuptpunmap(proc);
		proc->newtlb = 0;
	}

	tssrsp0(machp(), STACKALIGN(PTR2UINT(proc->kstack+KSTACK)));
	cr3put(proc->MMU.root->pa);
	if(recursive()!=proc->MMU.root->pa)
		panic("mmuswitch: proc PML4 pa not recursive (%#P vs %#P)\n",
		    proc->MMU.root->pa, recursive());
	splx(pl);
}

void
mmurelease(Proc* proc)
{
	Page *page, *next;
	int freed = 0;

	mmuptpunmap(proc);
	for(next = nil, page = proc->MMU.root->prev; page != nil; page = next){
		next = page->next;
		if(--page->ref)
			panic("mmurelease: page->ref %d\n", page->ref);
		lock(&mmuptpfreelist.l);
		page->prev = nil;
		page->next = mmuptpfreelist.next;
		mmuptpfreelist.next = page;
		mmuptpfreelist.ref++;
		unlock(&mmuptpfreelist.l);
		freed = 1;
	}

	lock(&mmuptpfreelist.l);
	if(--proc->MMU.root->ref)
		panic("mmurelease: proc->MMU.root->ref %d\n", proc->MMU.root->ref);
	proc->MMU.root->prev = nil;
	proc->MMU.root->next = mmuptpfreelist.next;
	mmuptpfreelist.next = proc->MMU.root;
	mmuptpfreelist.ref++;
	unlock(&mmuptpfreelist.l);

	if(freed && pga.rend.l.p)
		wakeup(&pga.rend);

	tssrsp0(machp(), STACKALIGN(machp()->stack+MACHSTKSZ));
	cr3put(machp()->MMU.pml4->pa);
}

static void
checkpte(uintmem ppn, void *a)
{
	int l;
	PTE *pte;
	uint64_t addr;
	char buf[240], *s;

	addr = PTR2UINT(a);
	pte = 0;
	s = buf;
	*s = 0;
	if((l = mmuwalk(addr, 3, &pte)) < 0 || (*pte&PteP) == 0)
		goto Panic;
	s = seprint(buf, buf+sizeof buf,
		"check3: l%d pte %#p = %llx\n",
		l, pte, pte?*pte:~0);
	if((l = mmuwalk(addr, 2, &pte)) < 0 || (*pte&PteP) == 0)
		goto Panic;
	s = seprint(s, buf+sizeof buf,
		"check2: l%d  pte %#p = %llx\n",
		l, pte, pte?*pte:~0);
	if(*pte&PtePS)
		return;
	if((l = mmuwalk(addr, 1, &pte)) < 0 || (*pte&PteP) == 0)
		goto Panic;
	seprint(s, buf+sizeof buf,
		"check1: l%d  pte %#p = %llx\n",
		l, pte, pte?*pte:~0);
	return;

Panic:
	seprint(s, buf+sizeof buf,
		"checkpte: l%d addr %#p ppn %#llx kaddr %#p pte %#p = %llx",
		l, a, ppn, KADDR(ppn), pte, pte?*pte:~0);
	panic("%s", buf);
}

static uintmem
pteflags(uint attr)
{
	uintmem flags;

	flags = 0;
	if(attr & ~(PTEVALID|PTEWRITE|PTERONLY|PTEUSER|PTEUNCACHED|PTENOEXEC))
		panic("pteflags: wrong attr bits: %#x\n", attr);
	if(attr&PTEVALID)
		flags |= PteP;
	if(attr&PTEWRITE)
		flags |= PteRW;
	if(attr&PTEUSER)
		flags |= PteU;
	if(attr&PTEUNCACHED)
		flags |= PtePCD;
	if(attr&PTENOEXEC)
		flags |= PteNX;
	return flags;
}

static PTE
allocuptpage(Proc *p, int level)
{
	Page *page;

	if(p->MMU.root->prev == nil)
		p->MMU.root->prev = mmuptpalloc();
	if(p->MMU.root->prev == nil)
		panic("mmuput: no free pages");
	page = p->MMU.root->prev;
	p->MMU.root->prev = page->next;
	page->daddr = level;
	page->next = p->MMU.root->next;
	p->MMU.root->next = page;

	return PPN(page->pa)|PteU|PteRW|PteP;
}

/*
 * pg->pgszi indicates the page size in machp()->pgsz[] used for the mapping.
 * For the user, it can be either 2*MiB or 1*GiB pages.
 * For 2*MiB pages, we use three levels, not four.
 * For 1*GiB pages, we use two levels.
 */
void
mmuput(uintptr_t va, Page *pg, uint attr)
{
	Proc *up;
	int pgsz;
	PTE *p4e, *p3e, *p2e, *p1e;
	PTE entry;
	Mpl pl;

	DBG("cpu%d: up %#p mmuput %#p %#P %#x %d\n",
	    machp()->machno, up, va, pg->pa, attr, pgsz);

	pl = splhi();
	up = externup();
	if(up == nil)
		panic("mmuput: no process");
	if(pg->pa == 0)
		panic("mmuput: zero pa");
	if(va >= KZERO)
		panic("mmuput: kernel page\n");
	if(pg->pgszi < 0)
		panic("mmuput: page size index out of bounds (%d)\n", pg->pgszi);
	if(up->MMU.root->pa != cr3get())
		panic("mmuput: not on up's page table (should be %#P but is %#P)\n",
		     up->MMU.root->pa, cr3get());
	if(recursive() != up->MMU.root->pa)
		panic("mmuput: up PML4 pa not recursive (%#P vs %#P)\n",
		    up->MMU.root->pa, recursive());
	pgsz = sys->pgsz[pg->pgszi];
	if(pg->pa & (pgsz-1))
		panic("mmuput: pa offset non zero: %#llx\n", pg->pa);

	entry = pg->pa|pteflags(attr)|PteU;
	p4e = PML4E(va);
	if(p4e == nil)
		panic("mmuput: PML4 is nil");
	if(*p4e == 0)
		*p4e = allocuptpage(up, 3);
	p3e = PML3E(va);
	if(p3e == nil)
		panic("mmuput: PML3 is nil");
	if(pgsz == 1*GiB){
		*p3e = entry|PtePS;
		splx(pl);
		DBG("cpu%d: up %#p new 1GiB pte %#p = %#llx\n",
		    machp()->machno, up, p3e, *p3e);
		return;
	}
	if(*p3e == 0)
		*p3e = allocuptpage(up, 2);
	p2e = PML2E(va);
	if(p2e == nil)
		panic("mmuput: PML2 is nil");
	if(pgsz == 2*MiB){
		*p2e = entry|PtePS;
		splx(pl);
		DBG("cpu%d: up %#p new 2MiB pte %#p = %#llx\n",
		    machp()->machno, up, p2e, *p2e);
		return;
	}
	if(*p2e == 0)
		*p2e = allocuptpage(up, 1);
	p1e = PML1E(va);
	if(p1e == nil)
		panic("mmuput: PML1 is nil");
	*p1e = entry;
	invlpg(va);			/* only if old entry valid? */
	splx(pl);

	DBG("cpu%d: up %#p new pte %#p = %#llx\n",
	    machp()->machno, up, p1e, *p1e);
	if(DBGFLG)
		checkpte(PPN(pg->pa), p1e);
}

static Lock vmaplock;

int
mmukmapsync(uint64_t va)
{
	USED(va);

	return 0;
}

/*
 * Add kernel mappings for pa -> va for a section of size bytes.
 * Called only after the va range is known to be unoccupied.
 */
uintptr
mmukphysmap(uintmem pa, int attr, usize size)
{
	uintptr_t pae;
	PTE *p4e, *p3e, *p2e, *p1e;
	usize pgsz = PGLSZ(1);
	Page *pg;
	uintptr va;

	if (pa >= PHYSADDRSIZE)
		panic("mapping nonexistent physical address");
	va = (uintptr)KADDR(pa);

	p4e = PML4E(va);
	if(p4e == nil || *p4e == 0)
		panic("mmukphysmap: PML4E for va %#P is missing", va);

	for(pae = pa + size; pa < pae; pa += pgsz){
		p3e = PML3E(va);
		if(p3e == nil)
			panic("mmukphysmap: PML3 for va %#P is missing", va);
		if(*p3e == 0){
			pg = mmuptpalloc();
			if(pg == nil || pg->pa == 0)
				panic("mmukphysmap: PML2 alloc failed for va %#P", va);
			*p3e = pg->pa|PteRW|PteP;
		}
		p2e = PML2E(va);
		if(p2e == nil)
			panic("mmukphysmap: PML2 missing for va %#P", va);

		/*
		 * Check if it can be mapped using a big page,
		 * i.e. is big enough and starts on a suitable boundary.
		 * Assume processor can do it.
		 */
		if(ALIGNED(pa, PGLSZ(1)) && ALIGNED(va, PGLSZ(1)) && (pae-pa) >= PGLSZ(1)){
			PTE entry = pa|attr|PtePS|PteP;
			if(*p2e != 0 && ((*p2e)&~(PGLSZ(1)-1)) != pa)
				panic("mmukphysmap: remapping kernel direct address at va %#P (old PMl2E %#P, new %#P)",
				    va, *p2e, entry);
			*p2e = entry;
			pgsz = PGLSZ(1);
		}else{
			if(*p2e == 0){
				pg = mmuptpalloc();
				if(pg == nil || pg->pa == 0)
					panic("mmukphysmap: PML1 alloc failed for va %#P", va);
				*p2e = pg->pa|PteRW|PteP;
			}
			p1e = PML1E(va);
			if(p1e == nil)
				panic("mmukphysmap: no PML1 for va %#P", va);
			PTE entry = pa|attr|PteP;
			if(*p1e != 0 && ((*p1e)&~(PGLSZ(0)-1)) != pa)
				panic("mmukphysmap: remapping kernel direct address at va %#P (old PMl2E %#P, new %#P)",
				    va, *p2e, entry);
			*p1e = entry;
			pgsz = PGLSZ(0);
		}
		va += pgsz;
	}

	return va;
}

/*
 * KZERO maps low memory.
 * Thus, almost everything in physical memory is already mapped, but
 * there are things that fall in the gap, mostly MMIO regions, where
 * in particular we would like to disable caching.
 * vmap() is required to access them.
 */
void*
vmap(uintptr_t pa, usize size)
{
	uintptr_t va;
	usize o, sz;

	DBG("vmap(%#p, %lu) pc=%#p\n", pa, size, getcallerpc());

	if(machp()->machno != 0 && DBGFLG)
		print("vmap: machp()->machno != 0\n");
	/*
	 * This is incomplete; the checks are not comprehensive
	 * enough.
	 * Sometimes the request is for an already-mapped piece
	 * of low memory, in which case just return a good value
	 * and hope that a corresponding vunmap of the address
	 * will have the same address.
	 * To do this properly will require keeping track of the
	 * mappings; perhaps something like kmap, but kmap probably
	 * can't be used early enough for some of the uses.
	 */
	if(pa+size < 1ull*MiB)
		return KADDR(pa);
	if(pa < 1ull*MiB)
		return nil;

	/*
	 * Might be asking for less than a page.
	 * This should have a smaller granularity if
	 * the page size is large.
	 */
	o = pa & ((1<<PGSHFT)-1);
	pa -= o;
	sz = ROUNDUP(size+o, PGSZ);

	if(pa == 0){
		print("vmap(0, %lu) pc=%#p\n", size, getcallerpc());
		return nil;
	}
	ilock(&vmaplock);
	va = (uintptr)KADDR(pa);
	if(mmukphysmap(pa, PtePCD|PteRW, sz) < 0){
		iunlock(&vmaplock);
		return nil;
	}
	iunlock(&vmaplock);

	DBG("vmap(%#p, %lu) => %#p\n", pa+o, size, va+o);

	return UINT2PTR(va + o);
}

void
vunmap(void* v, usize size)
{
	uintptr_t va;

	DBG("vunmap(%#p, %lu)\n", v, size);

	if(machp()->machno != 0)
		DBG("vmap: machp()->machno != 0\n");

	/*
	 * See the comments above in vmap.
	 */
	va = PTR2UINT(v);
	if(va >= KZERO && va+size < KZERO+1ull*MiB)
		return;

	/*
	 * Here will have to deal with releasing any
	 * resources used for the allocation (e.g. page table
	 * pages).
	 */
	DBG("vunmap(%#p, %lu)\n", v, size);
}

int
mmuwalk(uintptr_t va, int level, PTE** ret)
{
	PTE *pte;
	Mpl pl;

	pl = splhi();
	if(DBGFLG > 1)
		DBG("mmuwalk%d: va %#p level %d\n", machp()->machno, va, level);
	pte = (PTE *)PML4E(va);
	assert(pte != nil);
	if (level == 3 || !(*pte & PteP)){
		*ret = pte;
		splx(pl);
		return 3;
	}
	pte = (PTE *)PML3E(va);
	if (level == 2 || (!(*pte & PteP) || (*pte & PtePS))){
		*ret = pte;
		splx(pl);
		return 2;
	}
	pte = (PTE *)PML2E(va);
	if (level == 1 || (!(*pte & PteP) || (*pte & PtePS))){
		*ret = pte;
		splx(pl);
		return 1;
	}
	pte = (PTE *)PML1E(va);
	if (level == 0 || (*pte & PteP)){
		*ret = pte;
		splx(pl);
		return 1;
	}
	*ret = nil;
	splx(pl);

	return -1;
}

uintmem
mmuphysaddr(uintptr_t va)
{
	int l;
	PTE *pte;
	uintmem mask, pa;

	/*
	 * Given a VA, find the PA.
	 * This is probably not the right interface,
	 * but will do as an experiment. Usual
	 * question, should va be void* or uintptr?
	 */
	l = mmuwalk(va, 0, &pte);
	DBG("physaddr: va %#p l %d\n", va, l);
	if(l < 0)
		return ~0;

	mask = PGLSZ(l)-1;
	pa = (*pte & ~mask) + (va & mask);

	DBG("physaddr: l %d va %#p pa %#llx\n", l, va, pa);

	return pa;
}

Page mach0pml4;

void
mmuinit(void)
{
	uint8_t *p;
	PTE *rp;
	Page *page;
	uint64_t r;

	archmmu();
	DBG("mach%d: %#p pml4 %#p npgsz %d\n", machp()->machno, machp(), machp()->MMU.pml4, sys->npgsz);

	if(machp()->machno != 0){
		/* NIX: KLUDGE: Has to go when each mach is using
		 * its own page table
		 */
		p = UINT2PTR(machp()->stack);
		p += MACHSTKSZ;

		usize half = PTSZ/(2*sizeof(PTE));
		rp = (PTE*)p;
		memmove(&rp[half], &sys->pml4[half], PTSZ/4 + PTSZ/8);
		rp[PTSZ/sizeof(PTE)-1] = PADDR(p)|PteRW|PteP;
		machp()->MMU.pml4 = &machp()->MMU.pml4kludge;
		machp()->MMU.pml4->va = PTR2UINT(p);
		machp()->MMU.pml4->pa = PADDR(p);
		machp()->MMU.pml4->daddr = 0;

		r = rdmsr(Efer);
		r |= Nxe;
		wrmsr(Efer, r);
		cr3put(machp()->MMU.pml4->pa);
		DBG("m %#p pml4 %#p\n", machp(), machp()->MMU.pml4);
		return;
	}

	page = &mach0pml4;
	page->va = PTR2UINT(sys->pml4);
	page->pa = PADDR(sys->pml4);
	machp()->MMU.pml4 = page;
	rp = (PTE*)page->va;
	if(rp[PTSZ/sizeof(PTE)-1] != (page->pa|PteRW|PteP))
		panic("mmuinit: self-referential pointer for sys->pml4 wrong");
	cr3put(cr3get());

	r = rdmsr(Efer);
	r |= Nxe;
	wrmsr(Efer, r);

	print("mmuinit: KZERO %#p end %#p\n", KZERO, end);
}

void
mmuprocinit(Proc *p)
{
	Page *pg = mmuptpalloc();
	if(pg==nil)
		panic("mmuprocinit: cannot allocate page table for process");
	memmove(UINT2PTR(pg->va+PTSZ/2), UINT2PTR(PML4+PTSZ/2), PTSZ/4+PTSZ/8);
	PTE *ptes = UINT2PTR(pg->va);
	ptes[PTSZ/sizeof(PTE)-1] = pg->pa|PteRW|PteP;
	p->MMU.root = pg;
}
