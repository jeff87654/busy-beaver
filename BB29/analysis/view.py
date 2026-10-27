# view.py MACH steps snapstates maxsnaps : print tape on entry to snap states, with absolute head pos
import sys, re
from tm import load, parse, nm
m=load(sys.argv[1]); n,T=parse(m)
maxs=int(sys.argv[2]); snaps=set(ord(c)-65 for c in sys.argv[3]); maxsn=int(sys.argv[4])
tape={}; pos=0; q=0; st=0; sn=0
def rle(s):
    return re.sub(r'((?:[01]{1,6}?))\1{2,}', lambda mm: '(%s)^%d'%(mm.group(1),len(mm.group(0))//len(mm.group(1))), s)
while st<maxs:
    s=tape.get(pos,0); tr=T[(q,s)]
    if tr is None: print('HALT',st); break
    tape[pos]=tr[0]; pos+=tr[1]; q=tr[2]; st+=1
    if q in snaps and sn<maxsn:
        sn+=1
        ks=[k for k in tape if tape[k]] or [pos]
        lo=min(min(ks),pos); hi=max(max(ks),pos)
        L=''.join(str(tape.get(i,0)) for i in range(lo,pos)); R=''.join(str(tape.get(i,0)) for i in range(pos,hi+1))
        print(st, 'lo=%d pos=%d'%(lo,pos), rle(L),'<%s>'%nm(q),rle(R))
