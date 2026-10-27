# ordinal_check.py MACH maxsteps : at successive chop configurations C(m)=K(m,0,h,d) check the hydra is sorted and
#   o(h_next) == o(h)[m+3]  (o(h) limit)     or     o(h_next) == o(h)-1  (o(h) successor)
# with standard fundamental sequences ( (b+w^(g+1))[n]=b+w^g*n ; (b+w^l)[n]=b+w^(l[n]) ).
import sys, random
from family import *
from hydra import cmp
# CNF ordinal: tuple of exponents (each a CNF ordinal), non-increasing
def o_of(node):  # node sorted -> CNF
    return tuple(o_of(c) for c in node)
def is_sorted(node):
    es=[o_of(c) for c in node]
    return all(cmp(es[i],es[i+1])>=0 for i in range(len(es)-1)) and all(is_sorted(c) for c in node)
def is_succ(a): return len(a)>0 and a[-1]==()
def fs(a,n):
    *b,last=a; b=tuple(b)
    if is_succ(last): return b+(last[:-1],)*n          # w^(g+1)[n]=w^g*n
    return b+(fs(last,n),)                              # w^l[n]=w^(l[n])
def check(name, maxsteps, verbose=True):
    pe,_=pm_events(name,{},0,CFG[name]['start'],maxsteps,10**6)
    C=[e for e in pe if e is not None and e[0]!='HALT' and e[1]==0]
    bad=0
    for (m,_,h,d),(m2,_,h2,d2) in zip(C[1:],C[2:]):
        assert m2==m+1
        a=o_of(h); a2=o_of(h2)
        if not (is_sorted(h) and is_sorted(h2)): bad+=1; print('unsorted at m',m); continue
        exp=a[:-1] if is_succ(a) else fs(a,m+3)
        if exp!=a2: bad+=1; print('ordinal step mismatch at m',m)
    print(name,'checked',len(C)-2,'consecutive chop configs C(1)..; bad =',bad)
if __name__=="__main__":
  for name in sys.argv[1].split(','): check(name,int(sys.argv[2]))
# ---- unsorted variant (BB31/BB33): ordinary-sum ordinal; report equal / strictly-larger-by-absorbed-term counts
from hydra import ordinal as osum, oshow
def check_osum(name,maxsteps):
    pe,_=pm_events(name,{},0,CFG[name]['start'],maxsteps,10**6)
    C=[e for e in pe if e is not None and e[0]!='HALT' and e[1]==0]
    eq=gt=lt=0
    for (m,_,h,d),(m2,_,h2,d2) in zip(C[1:],C[2:]):
        a=osum(h); a2=osum(h2); exp=a[:-1] if is_succ(a) else fs(a,m+3)
        c=cmp(a2,exp); eq+=c==0; gt+=c>0; lt+=c<0
    print(name,'ordinary-sum check over',len(C)-2,'rounds: equal',eq,'larger',gt,'SMALLER',lt, ' C(1) ordinal', oshow(osum(C[1][2])))
if __name__=='__main__' and len(sys.argv)>3:
    for name in sys.argv[3].split(','): check_osum(name,int(sys.argv[2]))
