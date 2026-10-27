# view2.py MACH steps snapstates maxsnaps [align] : tape in pairs (cells 2k+align,2k+1+align), head pair marked
import sys
from tm import load, parse, nm
m=load(sys.argv[1]); n,T=parse(m)
maxs=int(sys.argv[2]); snaps=set(ord(c)-65 for c in sys.argv[3]); maxsn=int(sys.argv[4]); al=int(sys.argv[5]) if len(sys.argv)>5 else 1
tape={}; pos=0; q=0; st=0; sn=0
while st<maxs:
    s=tape.get(pos,0); tr=T[(q,s)]
    if tr is None: print('HALT',st); break
    tape[pos]=tr[0]; pos+=tr[1]; q=tr[2]; st+=1
    if q in snaps and sn<maxsn:
        sn+=1
        ks=[k for k in tape if tape[k]] or [pos]
        lo=min(min(ks),pos)-2; hi=max(max(ks),pos)+2
        lo-= (lo-al)%2
        out=[]
        for i in range(lo,hi+1,2):
            p=str(tape.get(i,0))+str(tape.get(i+1,0))
            if i==pos: p='['+nm(q)+']'+p
            elif i+1==pos: p=p[0]+'['+nm(q)+']'+p[1]
            out.append(p)
        print(st,' '.join(out))
