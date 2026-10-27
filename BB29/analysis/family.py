# family.py : generic pair-level harness for BB29/BB31/BB33 (same program up to relabeling)
# pair letters: '0'=00 '_' blank/marked '(' ; 'c'=01 '(' ; 'y'=11 ')' ; 'x'=10 marked ')' (X)
from pm_full import full_table
from hydra import enc, chop, parse_string, rp_len, height
import re
# roles: Y = left scan that ends a round at the H-separator; P = counter walk; start = initial entry; E = escape depth
CFG={
 'BB29':dict(al=0, Y='Y<', P='P<', start='A>', E=3),
 'BB31':dict(al=1, Y='Z<', P='O<', start='A<', E=5),
 'BB33':dict(al=1, Y=']<', P='P<', start='A<', E=7),
}
_PT={}
def PT(name):
    if name not in _PT: _PT[name]=full_table(name)
    return _PT[name]
def build(a,b,h,d):
    t={}; i=1
    for _ in range(a): t[i]='c'; i+=1
    i+=1
    for _ in range(b): t[i]='c'; i+=1
    head=i-1; i+=1
    for ch in enc(h,d): t[i]={'(':'c',')':'y','X':'x'}[ch]; i+=1
    return t,head
def decode(t, head):
    keys=[k for k,v in t.items() if v!='0']
    hi=max(keys+[head]); lo=min(keys+[head])
    sep=head+1
    if t.get(sep,'0')!='0': return None
    H=''.join(t.get(i,'0') for i in range(sep+1,hi+1))
    if '0' in H: return None
    H=H.replace('c','(').replace('y',')').replace('x','X')
    left=''.join(t.get(i,'0') for i in range(lo,sep))
    mm=re.fullmatch(r'0*(c*)0(c*)','0'+left)
    if not mm: return None
    try: h,d=parse_string(H)
    except Exception: return None
    return (len(mm.group(1)),len(mm.group(2)),h,d)
def ones(t): return sum({'0':0,'c':1,'x':1,'y':2}[v] for v in t.values())
def pm_events(name, t, head, q, maxsteps, maxev, decode_events=True):
    P=PT(name); PQ=CFG[name]['P']; pos=head; st=0; evs=[]
    while st<maxsteps and len(evs)<maxev:
        a=t.get(pos,'0'); e=P[q][a]
        if e is None: evs.append(('UNDEF',q,a)); return evs,st
        if e=='HALT': evs.append(('HALT',ones(t))); return evs,st
        w,dr,nq=e; ev=(nq==PQ and q!=PQ)   # event: first entry into the counter walk P<
        t[pos]=w; pos+=1 if dr=='R' else -1; q=nq; st+=1
        if ev: evs.append(decode(t,pos) if decode_events else (dict(t),pos))
    return evs,st
def addcopy(h,d):
    if d==0: return h
    def rec(node,depth):
        if depth==d-1: return node+(node[-1],)
        return node[:-1]+(rec(node[-1],depth+1),)
    return rec(h,0)
def model_step(a,b,h,d):
    """one Y->P event of the model.  Returns new (a,b,h,d) or ('HALT', ones)."""
    if b>=1: return (a+1,b-1,addcopy(h,d),d)
    if h==(): return ('HALT',a+1)
    h2,d2=chop(h,0); h2=addcopy(h2,d2)
    return (0,a+1,h2,d2)
def model(a,b,h,d,maxev):
    evs=[]; c=(a,b,h,d)
    while len(evs)<maxev:
        c=model_step(*c); evs.append(c)
        if c[0]=='HALT': break
    return evs
