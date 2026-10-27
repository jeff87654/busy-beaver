# check_hydra.py : run the pair machine from K(a,b,h,d) and compare the sequence of Y->P events with the hydra model
import sys, random
from pm_full import full_table
PT=full_table('BB29')
from hydra import *
def pm_events(t, head, q, maxsteps, maxev):
    """run pair machine, yield decoded configs at Y< --0--> P< events; or ('HALT',...)"""
    pos=head; st=0; evs=[]
    while st<maxsteps and len(evs)<maxev:
        a=t.get(pos,'0'); e=PT[q].get(a)
        if e is None: evs.append(('UNDEF',q,a)); return evs
        if e=='HALT':
            ones=sum({'0':0,'c':1,'x':1,'y':2}[v] for v in t.values())
            evs.append(('HALT',ones)); return evs
        w,dr,nq=e
        if q=='Y<' and a=='0': ev=True
        else: ev=False
        t[pos]=w; pos+=1 if dr=='R' else -1; q=nq; st+=1
        if ev:
            evs.append(decode(t,pos))
    return evs
def model(a,b,h,d,maxev):
    """predicted Y->P events: K(a,b) b>=1 -> K(a+1,b-1) with one copy of M (if M != root) ;
       K(a,0) -> chop with n=a+1 ; then (limit) one copy, K(0,a+1) ; (successor) K(0,a+1) no copy"""
    evs=[]
    def addcopy(h,d):
        if d==0: return h
        def rec(node,depth):
            if depth==d-1: return node+(node[-1],)
            return node[:-1]+(rec(node[-1],depth+1),)
        return rec(h,0)
    while len(evs)<maxev:
        if b>=1:
            a,b,h=a+1,b-1,addcopy(h,d)
        else:
            if h==(): 
                evs.append(('HALT',None)); return evs
            n=a+1
            h,d=chop(h,0)    # remove leaf; p' kept (N=0 copies here; copies come from addcopy)
            h=addcopy(h,d)
            a,b=0,n
        evs.append((a,b,h,d))
    return evs
def same(x,y):
    if x[0]=='HALT' and y[0]=='HALT': return True
    return x==y
if __name__=='__main__':
    pass
