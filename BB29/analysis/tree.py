# tree.py: pretty-print pair-machine tapes as trees.  '(' ')' brackets; '_' blank-marker; 'X' marked ')'.
import re
def tt(s):
    # s: string of brackets possibly unbalanced and with markers; output nested compressed notation
    out=[]; stack=[[]]
    def emit(tok): stack[-1].append(tok)
    for ch in s:
        if ch=='(':
            stack.append([])
        elif ch==')':
            if len(stack)>1:
                ch_=stack.pop(); emit(node(ch_))
            else: emit(')')
        else:
            emit(ch)
    # unclosed opens
    res=''
    for i,lvl in enumerate(stack):
        if i>0: res+='('
        res+=comp(lvl)
    return res
def node(ch):
    if not ch: return '0'
    return '{'+comp(ch)+'}'
def comp(toks):
    out=[]; i=0
    while i<len(toks):
        j=i
        while j<len(toks) and toks[j]==toks[i]: j+=1
        k=j-i
        out.append(toks[i] if k==1 else '%s^%d'%(toks[i],k)); i=j
    return ' '.join(out)
