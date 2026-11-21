import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine
from bcfg import classify, _runs
ALPHA='ABCDEFGHIJKLMNOPQRSTUVWXYZ'
OURS='1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC'
K=int(sys.argv[1]); Ml=int(sys.argv[2]); LIMIT=int(sys.argv[3])
m=parse_machine(OURS)
def fmt(cells): return ' '.join('%d:%s^%d'%(s,v,n) for (s,v,n) in _runs(cells))
cells={}
for i in range(K): cells[-1-i]=2
for i in range(Ml): cells[-1-K-i]=3
p=0; cells[0]=2; state='A'
out=open('seq_k%d.log'%K,'w')
for n in range(1,LIMIT+1):
    i=ALPHA.index(state); cur=cells.get(p,0); t=m.table[(i,cur)]
    if t is None or t[2] is None:
        out.write('HALT after %d steps; tape: %s\n'%(n-1,fmt(cells))); out.flush(); break
    w,d,q=t; cells[p]=w; p+= 1 if d=='R' else -1; state='ABC'[q]
    c=classify(cells,p,state)
    if c is not None:
        out.write('step %d  B(%d,%d,%d) head %d   tape: %s\n'%(n,c[0],c[1],c[2],c[3],fmt(cells)))
        out.flush()
