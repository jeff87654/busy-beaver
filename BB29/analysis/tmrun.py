# TM-level runner from a pair tape; events = TM enters P from A (pair-level Y< --0--> P<)
from tm import load, parse
M29=load('BB29'); N29,T29=parse(M29)
BITS={'0':(0,0),'c':(0,1),'x':(1,0),'y':(1,1)}; LET={v:k for k,v in BITS.items()}
def tm_events(pt, headpair, state, side, maxsteps, maxev, T=T29):
    tape={}
    for i,v in pt.items():
        b=BITS[v]; 
        if b[0]: tape[2*i]=1
        if b[1]: tape[2*i+1]=1
    pos=2*headpair+(1 if side=='<' else 0); q=ord(state)-65; st=0; evs=[]
    A=0; P=ord('P')-65; Y=ord('Y')-65; prev=-1
    while st<maxsteps and len(evs)<maxev:
        s=tape.get(pos,0); tr=T[(q,s)]
        if tr is None:
            evs.append(('HALT',sum(tape.values()),st)); return evs
        w,dr,nq=tr
        ev=(q==A and nq==P and prev==Y and s==0)
        prev=q
        if w: tape[pos]=1
        else: tape.pop(pos,None)
        pos+=dr; q=nq; st+=1
        if ev:
            assert pos%2==1
            # pair tape
            ps={}
            for k in tape: ps[k//2]=1
            pt2={i:LET[(tape.get(2*i,0),tape.get(2*i+1,0))] for i in ps}
            evs.append((pt2,pos//2,st))
    return evs
