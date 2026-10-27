# random tests: hydra model vs pair machine vs TM, from K(a,b,h,d) to halt
import random, sys
from hydra import *
from check_hydra import pm_events, model, same
from tmrun import tm_events
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
def rtree(h, size):
    if h==0 or size<=0: return ()
    k=random.randint(0,3)
    return tuple(rtree(h-1, size//2) for _ in range(k))
def sortedtree(t):  # children in non-increasing ordinal order (as the machine keeps them)
    cs=[sortedtree(c) for c in t]
    from functools import cmp_to_key
    cs.sort(key=cmp_to_key(lambda x,y: -cmp(ordinal(x),ordinal(y))))
    return tuple(cs)
ntest=int(sys.argv[2]) if len(sys.argv)>2 else 200
maxh=int(sys.argv[3]) if len(sys.argv)>3 else 3
okc=0; halts=0
for it in range(ntest):
    h=tuple(rtree(maxh-1,6) for _ in range(random.randint(0,3)))
    if random.random()<0.7: h=sortedtree(h)
    if height(h)>maxh: continue
    d=random.randint(0,rp_len(h))
    a=random.randint(0,3); b=random.randint(0,3)
    pt,hp=build(a,b,h,d)
    pe=pm_events(dict(pt),hp,'P<',2000000,3000)
    me=model(a,b,h,d,len(pe))
    good=True
    for i,(x,y) in enumerate(zip(pe,me)):
        if not same(x,y):
            print('MISMATCH',a,b,h,d,'event',i,'\n  pm',x,'\n  model',y); good=False; break
    if good and len(pe)!=len(me) and not (pe[-1][0]!='HALT' and len(pe)==3000):
        print('LENGTH',a,b,h,d,len(pe),len(me),pe[-1]); good=False
    # TM level: compare decoded events
    te=tm_events(pt,hp,'P','<',20000000,len(pe)+1)
    for i,(x,y) in enumerate(zip(te,pe)):
        if x[0]=='HALT' or y[0]=='HALT':
            if not(x[0]=='HALT' and y[0]=='HALT' and x[1]==y[1]): print('TM HALT MISMATCH',a,b,h,d,x[:2],y); good=False
            break
        dx=decode(x[0],x[1])
        if dx!=y: print('TM MISMATCH',a,b,h,d,i,dx,y); good=False; break
    if pe and pe[-1][0]=='HALT': halts+=1
    okc+=good
print('tests ok:',okc,'halted:',halts)
