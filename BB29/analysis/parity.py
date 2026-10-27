import sys
from tm import load, parse, nm
m=load(sys.argv[1]); n,T=parse(m); maxs=int(sys.argv[2])
tape={}; pos=0; q=0; st=0; par={}
while st<maxs:
    s=tape.get(pos,0); tr=T[(q,s)]
    if tr is None: break
    tape[pos]=tr[0]; pos+=tr[1]; q=tr[2]; st+=1
    par.setdefault(q,[0,0])[pos&1]+=1
for k in sorted(par): print(nm(k),par[k])
