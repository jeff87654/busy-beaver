# hydra.py : hydra-level model of BB29 and encoders/decoders for the pair tape.
# A hydra is the tuple of the (implicit) root's children; each node is a tuple of children; leaf = ().
# The marked node M lies on the rightmost path at depth d (d=0: root).
def s(node): return '(' + ''.join(s(c) for c in node) + ')'
def enc(node, d):
    """bracket string of node's children with the rightmost path open down to depth d; M's close is X."""
    if d == 0: return ''.join(s(c) for c in node) + 'X'
    return ''.join(s(c) for c in node[:-1]) + '(' + enc(node[-1], d-1)
def height(node): return 0 if not node else 1+max(height(c) for c in node)
def rp_len(node):  # depth of the rightmost leaf below node (number of edges on the rightmost path)
    k=0
    while node: node=node[-1]; k+=1
    return k
def chop(h, N):
    """KP hydra step: remove the rightmost head; if its parent p is not the root, append N copies of p' to p's parent.
    returns (new hydra, depth of new marked node = depth of p)"""
    k = rp_len(h)
    assert k >= 1
    def rec(node, depth):
        # node at depth 'depth' on rightmost path; leaf is at depth k
        if depth == k-1:          # node is p
            return node[:-1]
        if depth == k-2:          # node is g
            p2 = rec(node[-1], depth+1)
            return node[:-1] + (p2,)*(N+1)
        return node[:-1] + (rec(node[-1], depth+1),)
    if k == 1: return h[:-1], 0
    return rec(h, 0), k-1
# ---- ordinal of a hydra (CNF as nested tuple of exponents, decreasing): o(node)=sum omega^o(child) in tape order (ordinary sum)
def ordinal(node):
    terms=[ordinal(c) for c in node]
    # ordinary sum: a term omega^e absorbs earlier smaller terms
    out=[]
    for e in terms:
        while out and cmp(out[-1],e)<0: out.pop()
        out.append(e)
    return tuple(out)
def cmp(a,b):
    for x,y in zip(a,b):
        c=cmp(x,y)
        if c: return c
    return (len(a)>len(b))-(len(a)<len(b))
def oshow(a):
    if a==(): return '0'
    parts=[]; i=0
    while i<len(a):
        j=i
        while j<len(a) and a[j]==a[i]: j+=1
        e=a[i]; k=j-i
        t='1' if e==() else ('w' if e==((),) else 'w^'+('('+oshow(e)+')' if len(e)>1 or (e and e[0]!=()) else oshow(e)))
        parts.append(t if k==1 else (t+'*%d'%k if t!='1' else str(k)))
        i=j
    return '+'.join(parts)
# ---- pair tape <-> configuration
# pair letters: '0'=00 'c'=01 '(' ; 'y'=11 ')' ; 'x'=10 X ; tape dict index->letter
def build(a, b, h, d):
    """K(a,b,h,d) at the Y->P event: pairs  c^a 0 c^b [P<] 0 H ; returns (tape, headpair).
    The a-block starts at pair 1 (pair 0 is blank, left of it all blank)."""
    t={}; i=1
    for _ in range(a): t[i]='c'; i+=1
    i+=1                      # a/b separator
    for _ in range(b): t[i]='c'; i+=1
    head=i-1                  # P< reads pair left of H-separator
    i+=1                      # H separator
    for ch in enc(h,d):
        t[i]={'(':'c',')':'y','X':'x'}[ch]; i+=1
    return t, head
def parse_string(st):
    """bracket string (with exactly one X, at the end) -> (hydra, d)"""
    assert st.endswith('X') and st.count('X')==1, st
    stack=[[]]
    for ch in st[:-1]:
        if ch=='(': stack.append([])
        elif ch==')':
            n=stack.pop(); stack[-1].append(tuple(n))
        else: raise ValueError(st)
    d=len(stack)-1
    # close M (X) and the open ancestors
    while len(stack)>1:
        n=stack.pop(); stack[-1].append(tuple(n))
    return tuple(stack[0]), d
def decode(t, head):
    """decode a pair tape at a Y->P event into (a,b,h,d). Returns None if not clean."""
    keys=[k for k,v in t.items() if v!='0']
    lo=min(keys+[head]); hi=max(keys+[head])
    S=''.join(t.get(i,'0') for i in range(lo-1,hi+2))
    off=lo-1
    # head must be left of the H separator
    sep=head+1
    if t.get(sep,'0')!='0': return None
    H=''.join(t.get(i,'0') for i in range(sep+1,hi+1))
    if '0' in H: return None
    H=H.replace('c','(').replace('y',')').replace('x','X')
    left=''.join(t.get(i,'0') for i in range(lo,sep))
    # left = c^a 0 c^b  (with possibly a=0: then just c^b, preceded by blanks)
    left=left.lstrip('0') if False else left
    import re
    mm=re.fullmatch(r'0*(c*)0(c*)',  '0'+left)
    if not mm: return None
    a=len(mm.group(1)); b=len(mm.group(2))
    try: h,d=parse_string(H)
    except Exception: return None
    return a,b,h,d
