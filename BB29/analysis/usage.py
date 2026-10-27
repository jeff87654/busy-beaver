# usage.py MACH : which TM transitions (state,read) are used by the blank-tape run and by random height<=E hydra runs
import sys, random
import family
from family import CFG, PT, build, pm_events
from tm import load, parse, nm
from macro2 import SYM
from hydra import rp_len, height
name=sys.argv[1]; m=load(name); n,T=parse(m)
used=set()
def mark_pair(q,side,p):
    cells=list(SYM[p]); h=0 if side=='>' else 1; qi=ord(q)-65
    while 0<=h<=1:
        used.add((qi,cells[h])); tr=T[(qi,cells[h])]
        if tr is None: return
        cells[h]=tr[0]; h+=tr[1]; qi=tr[2]
orig=family.PT(name)
def run(t,head,q,maxs):
    pos=head
    for _ in range(maxs):
        a=t.get(pos,'0'); mark_pair(q[0],q[1],a); e=orig[q][a]
        if e is None or e=='HALT': return
        w,dr,nq=e; t[pos]=w; pos+=1 if dr=='R' else -1; q=nq
run({},0,CFG[name]['start'],3_000_000)
blank=set(used)
random.seed(5)
def rtree(h):
    if h==0: return ()
    return tuple(rtree(h-1) for _ in range(random.choice([0,0,1,1,2,3])))
E=CFG[name]['E']
for _ in range(150):
    h=tuple(rtree(random.randint(0,E-1)) for _ in range(random.randint(0,3))); d=random.randint(0,rp_len(h))
    t,hp=build(random.randint(0,2),random.randint(0,2),h,d); run(t,hp,CFG[name]['P'],300_000)
allt={(i,s) for i in range(n) for s in (0,1)}
f=lambda S: ' '.join(sorted('%s%d'%(nm(i),s) for i,s in S))
print(name,'unused in blank run (3M pair steps):',f(allt-blank))
print(name,'unused in blank run AND random hydra runs:',f(allt-used))
