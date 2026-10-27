# rand_family.py MACH seed ntests maxheight : model vs exact pair machine, from random K(a,b,h,d) until halt (or caps)
import random, sys
from family import *
from hydra import ordinal, cmp
name=sys.argv[1]; random.seed(int(sys.argv[2])); ntest=int(sys.argv[3]); maxh=int(sys.argv[4])
from functools import cmp_to_key
def rtree(h):
    if h==0: return ()
    k=random.choice([0,0,1,1,2,3])
    return tuple(rtree(h-1) for _ in range(k))
def srt(t):
    cs=[srt(c) for c in t]; cs.sort(key=cmp_to_key(lambda x,y:-cmp(ordinal(x),ordinal(y)))); return tuple(cs)
stats=dict(ok=0,halt=0,cap=0,bad=0,undef=0)
for it in range(ntest):
    h=tuple(rtree(random.randint(0,maxh-1)) for _ in range(random.randint(0,3)))
    if random.random()<0.8: h=srt(h)
    if height(h)>maxh: continue
    d=random.randint(0,rp_len(h)); a=random.randint(0,3); b=random.randint(0,3)
    t,hp=build(a,b,h,d)
    pe,st=pm_events(name,t,hp,CFG[name]['P'],3_000_000,2000)
    me=model(a,b,h,d,len(pe))
    bad=None
    for i,(x,y) in enumerate(zip(pe,me)):
        if x!=y: bad=(i,x,y); break
    if bad:
        stats['bad']+=1
        if pe[-1] is None or pe[-1][0]=='UNDEF': stats['undef']+=1
        if stats['bad']<=5: print('MISMATCH',(a,b,h,d),'height',height(h),'event',bad[0],'\n   machine',str(bad[1])[:150],'\n   model  ',str(bad[2])[:150])
    elif pe and pe[-1][0]=='HALT': stats['halt']+=1; stats['ok']+=1
    else: stats['cap']+=1; stats['ok']+=1
print(name,'maxheight',maxh,stats)
