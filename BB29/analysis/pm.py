# pair-level machine for BB29 (derived from macro2/observed); alphabet 0 c x y ; prints as _ ( X )
import sys
# entry -> {sym: (write, dir, next)}
PT={
 'A>':{'0':('0','L','P<')},
 'B<':{'c':('x','L','R<'),'y':('0','L','B<'),'0':'HALT','x':'HALT'},
 'D<':{'0':('c','R','F>'),'c':('c','L','D<'),'x':('y','R','F>'),'y':('y','L','D<')},
 'P<':{'0':('c','R','[>'),'c':('c','L','P<')},
 'R<':{'c':('0','R','H>'),'y':('y','L','T<')},
 'T<':{'c':('c','L','R<'),'y':('y','L','\<')},
 'Y<':{'0':('0','L','P<'),'c':('c','L','Y<'),'x':('x','L','D<'),'y':('y','L','Y<')},
 '\<':{'c':('c','L','T<')},
 ']<':{'0':('c','R','H>'),'c':('c','L','Y<'),'y':('y','L','Y<')},
 'F>':{'c':('0','R','H>'),'x':('y','R','N>'),'y':('x','R','K>')},
 'H>':{'0':('c','L','Y<'),'c':('c','R','H>'),'x':('x','R','H>'),'y':('y','R','H>')},
 'K>':{'0':('y','L',']<'),'c':('c','R','K>'),'x':('x','R','K>'),'y':('y','R','K>')},
 'N>':{'0':('x','L',']<'),'c':('c','R','N>'),'x':('x','L','R<'),'y':('y','R','N>')},
 'V>':{'0':('0','R','N>'),'c':('c','R','V>'),'x':('0','L','B<'),'y':('y','R','V>')},
 '[>':{'0':('0','R','V>'),'c':('0','R','V>')},
}
SH={'0':'_','c':'(','x':'X','y':')'}
def show(tape,pos,q):
    lo=min(min(tape),pos); hi=max(max(tape),pos)
    s=''
    for i in range(lo,hi+1):
        if i==pos: s+='{'+q+'}'
        s+=SH[tape.get(i,'0')]
    return s
def runpm(tape,pos,q,maxs,cb=None):
    st=0
    while st<maxs:
        a=tape.get(pos,'0'); e=PT[q].get(a)
        if e is None: return ('UNDEF',q,a,pos,st)
        if e=='HALT': return ('HALT',q,a,pos,st)
        w,d,nq=e; tape[pos]=w; pos+=1 if d=='R' else -1; q=nq; st+=1
        if cb: cb(tape,pos,q,st)
    return ('MAX',q,None,pos,st)
if __name__=='__main__':
    maxs=int(sys.argv[1]); snaps=sys.argv[2].split(','); maxsn=int(sys.argv[3])
    cnt=[0]
    def cb(t,p,q,st):
        if q in snaps and cnt[0]<maxsn:
            cnt[0]+=1; print(st,show(t,p,q))
    print(runpm({},0,'A>',maxs,cb))
