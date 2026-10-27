# record which (entry, pair symbol) combos occur in a real run (pairs = (even,odd))
import sys
from tm import load, parse, nm
from macro2 import run as run0
run=lambda q,s,p: run0(T,q,s,p)
m=load(sys.argv[1]); n,T=parse(m); maxs=int(sys.argv[2])
tape={}; pos=0; q=0; st=0; obs={}
SY='0cxy'
def pair(p): b=p-(p%2); return SY[tape.get(b,0)*2+tape.get(b+1,0)]
ent=('A>',pair(0))
obs[ent]=1
while st<maxs:
    s=tape.get(pos,0); tr=T[(q,s)]
    if tr is None: break
    old=pos
    tape[pos]=tr[0]; pos+=tr[1]; q=tr[2]; st+=1
    if (old>>1)!=(pos>>1):
        e=(nm(q)+('>' if pos>old else '<'), pair(pos))
        obs[e]=obs.get(e,0)+1
import collections
byent=collections.defaultdict(dict)
for (e,p),c in obs.items(): byent[e][p]=c
for e in sorted(byent,key=lambda s:(s[1],s[0])):
    print(e, ' | '.join('%s:%s (%d)'%(p,' '.join(run(ord(e[0])-65,e[1],p)),byent[e][p]) for p in '0cxy' if p in byent[e]))
