import sys
from pm import PT, SH, runpm
from tree import tt
maxs=int(sys.argv[1]); snaps=sys.argv[2].split(','); maxsn=int(sys.argv[3])
cnt=[0]
def show(tape,pos,q):
    lo=min(min(tape),pos); hi=max(max(tape),pos)
    L=''.join(SH[tape.get(i,'0')] for i in range(lo,pos)); R=''.join(SH[tape.get(i,'0')] for i in range(pos,hi+1))
    return tt(L)+'  |'+q+'|  '+tt(R)
def cb(t,p,q,st):
    if q in snaps and cnt[0]<maxsn:
        cnt[0]+=1; print(st,show(t,p,q))
print(runpm({},0,'A>',maxs,cb))
