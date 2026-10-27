# ordinal_rand.py seed n maxh : random (unsorted allowed) hydras; over model rounds C(m)->C(m+1) compare ordinary-sum ordinal with o[m+3] / o-1
import random, sys
from family import model_step
from hydra import ordinal as osum, cmp, height
from ordinal_check import fs, is_succ
random.seed(int(sys.argv[1])); n=int(sys.argv[2]); maxh=int(sys.argv[3])
def rtree(h):
    if h==0: return ()
    return tuple(rtree(h-1) for _ in range(random.choice([0,0,1,1,2,3])))
eq=gt=lt=0
for _ in range(n):
    h=tuple(rtree(random.randint(0,maxh-1)) for _ in range(random.randint(1,3))); m=random.randint(0,3); d=0
    c=(m,0,h,d)
    for r in range(int(sys.argv[4]) if len(sys.argv)>4 else 12):
        a=osum(c[2]); mm=c[0]
        c=model_step(*c)
        if c[0]=='HALT': break
        while c[1]>0: c=model_step(*c)
        exp=a[:-1] if is_succ(a) else fs(a,mm+3)
        k=cmp(osum(c[2]),exp); eq+=k==0; gt+=k>0; lt+=k<0
        if k<0: print('SMALLER',h)
print('rounds: equal',eq,'larger',gt,'smaller',lt)
