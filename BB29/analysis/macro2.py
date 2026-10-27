# block-2 macro table (pairs = (even, odd) cells; letters 0=00 c=01 x=10 y=11).
# Entry (q,'>'): head on first cell (came from left); (q,'<'): head on second cell (came from right).
import sys
from tm import load, parse, nm
SYM={'0':(0,0),'c':(0,1),'x':(1,0),'y':(1,1)}; INV={v:k for k,v in SYM.items()}
def run(T,q,side,p):
    cells=list(SYM[p]); h=0 if side=='>' else 1; steps=0
    while 0<=h<=1:
        tr=T[(q,cells[h])]
        if tr is None: return ('HALT',INV[tuple(cells)])
        cells[h]=tr[0]; h+=tr[1]; q=tr[2]; steps+=1
        if steps>100: return ('LOOP',)
    return (INV[tuple(cells)], 'R' if h==2 else 'L', nm(q)+('>' if h==2 else '<'))
if __name__=="__main__":
    m=load(sys.argv[1]); n,T=parse(m)
    for i in range(n):
        for side in '><':
            print(nm(i)+side,' | '.join('%s:%s'%(p,' '.join(run(T,i,side,p))) for p in '0cxy'))
