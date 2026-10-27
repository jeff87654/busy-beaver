# tmcross.py MACH maxsteps evlist : pair machine from blank with TM-step accounting; at chosen macro events run the real TM
# (tmat.exe) to the same TM step count and compare state, head position and the whole tape.
import sys, subprocess, os
from family import CFG, PT, decode
from tm import load, parse
from macro2 import SYM
name=sys.argv[1]; maxs=int(sys.argv[2]); want=[int(x) for x in sys.argv[3].split(',')]
m=load(name); n,T=parse(m); al=CFG[name]['al']; PQ=CFG[name]['P']
def steps_in_pair(q,side,p):
    cells=list(SYM[p]); h=0 if side=='>' else 1; k=0
    while 0<=h<=1:
        tr=T[(q,cells[h])]; cells[h]=tr[0]; h+=tr[1]; q=tr[2]; k+=1
    return k
P=PT(name); t={}; pos=0; q=CFG[name]['start']; tmst=0; ev=0; out=[]
for st in range(maxs):
    a=t.get(pos,'0'); e=P[q][a]
    if e=='HALT' or e is None: break
    tmst+=steps_in_pair(ord(q[0])-65,q[1],a)
    w,dr,nq=e; isev=(nq==PQ and q!=PQ)
    t[pos]=w; pos+=1 if dr=='R' else -1; q=nq
    if isev:
        if ev in want: out.append((ev,tmst,dict(t),pos,q,decode(t,pos)))
        ev+=1
        if ev>max(want): break
exe=os.path.join(os.path.dirname(os.path.abspath(__file__)),'tmat.exe' if os.name=='nt' else 'tmat')   # build: g++ -O2 -o tmat tmat.cpp
res=subprocess.run([exe,m]+[str(o[1]) for o in out],capture_output=True,text=True,creationflags=0x08000000|0x40).stdout.split('\n')
for o,line in zip(out,res):
    ev,tmst,tp,hp,qq,dec=o
    s,qs,tpos,lo,bits=line.split()
    tape={int(lo)+i:int(c) for i,c in enumerate(bits) if c=='1'}
    # pair i = cells (2i-al, 2i+1-al)
    exp={}
    for i,v in tp.items():
        b=SYM[v]
        if b[0]: exp[2*i-al]=1
        if b[1]: exp[2*i+1-al]=1
    exppos=2*hp-al+(1 if qq[1]=='<' else 0)
    ok= tape==exp and int(tpos)==exppos and qs==qq[0]
    a,b,h,d=dec if dec else (-1,-1,None,-1)
    print('%s event %d at TM step %d: K(a=%d,b=%d,d=%d) state %s head %d  TM-literal-match=%s'%(name,ev,tmst,a,b,d,qs,int(tpos),ok))
