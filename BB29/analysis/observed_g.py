# observed_g.py MACH steps align : observed pair-level transitions (pair i = cells (2i+al', ...)), al=0: (2i,2i+1); al=1: (2i-1,2i)
import sys, collections
from tm import load, parse, nm
from macro2 import run
name=sys.argv[1]; m=load(name); n,T=parse(m); maxs=int(sys.argv[2]); al=int(sys.argv[3])
tape={}; pos=0; q=0; st=0; obs={}
SY='0cxy'
def pidx(p): return (p+al)>>1
def pair(p):
    b=2*pidx(p)-al
    return SY[tape.get(b,0)*2+tape.get(b+1,0)]
first=(nm(0)+('>' if (pos+al)%2==0 else '<'),pair(0)); obs[first]=1
while st<maxs:
    s=tape.get(pos,0); tr=T[(q,s)]
    if tr is None: break
    old=pos
    tape[pos]=tr[0]; pos+=tr[1]; q=tr[2]; st+=1
    if pidx(old)!=pidx(pos):
        e=(nm(q)+('>' if pos>old else '<'), pair(pos)); obs[e]=obs.get(e,0)+1
by=collections.defaultdict(dict)
for (e,p),c in obs.items(): by[e][p]=c
print('initial entry',first)
for e in sorted(by,key=lambda s:(s[1],s[0])):
    print(e, ' | '.join('%s:%s (%d)'%(p,' '.join(run(T,ord(e[0])-65,e[1],p)),by[e][p]) for p in '0cxy' if p in by[e]))
