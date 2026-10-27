# view3.py MACH steps snapstates maxsnaps [align] : tape as pair-letters 00=0 01=c 10=x 11=y; head shown as <Q> before pair (or inside: <Q:2nd>)
import sys,re
from tm import load, parse, nm
m=load(sys.argv[1]); n,T=parse(m)
maxs=int(sys.argv[2]); snaps=set(ord(c)-65 for c in sys.argv[3]); maxsn=int(sys.argv[4]); al=int(sys.argv[5]) if len(sys.argv)>5 else 1
mp={'00':'0','01':'c','10':'x','11':'y'}
tape={}; pos=0; q=0; st=0; sn=0
def blocks(s):
    s=re.sub(r'xx((?:yx)*)yy', lambda mm:'[%d]'%(len(mm.group(1))//2), s)
    s=re.sub(r'(\[\d+\])\1+', lambda mm: '%s^%d'%(mm.group(1),len(mm.group(0))//len(mm.group(1))), s)
    s=re.sub(r'x{3,}', lambda mm:'x^%d'%len(mm.group(0)), s)
    return s
while st<maxs:
    s=tape.get(pos,0); tr=T[(q,s)]
    if tr is None: print('HALT',st); break
    tape[pos]=tr[0]; pos+=tr[1]; q=tr[2]; st+=1
    if q in snaps and sn<maxsn:
        sn+=1
        ks=[k for k in tape if tape[k]] or [pos]
        lo=min(min(ks),pos)-2; hi=max(max(ks),pos)+2
        lo-= (lo-al)%2
        L='';R=''
        for i in range(lo,hi+1,2):
            p=mp[str(tape.get(i,0))+str(tape.get(i+1,0))]
            if i<pos-1: L+=p
            elif i==pos-1: L+=p; R='<%s:2>'%nm(q)
            elif i==pos: R+='<%s>'%nm(q)+p
            else: R+=p
        print(st,blocks(L.strip('0') if False else L),R)
