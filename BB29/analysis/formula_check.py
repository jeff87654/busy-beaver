# formula_check.py : closed-form final counter for BB29 height-3 hydras vs the hydra model run to HALT.
#   W([])=S ; W(A0++[k]) = T_k(W(A0)) ;  T_0(phi)(m)=phi^(m+3)(m+1) ; T_(k+1)(phi)(m) = (T_k)^(m+3)(phi)(m+1)
#   C(m, root=[A_1..A_r], d) halts with sigma = W(A_1)(...W(A_r)(m)) + 1
from family import model_step
def it(n,f,x):
    for _ in range(n): x=f(x)
    return x
def T(k,phi):
    if k==0: return lambda m: it(m+3,phi,m+1)
    return lambda m: it(m+3, lambda g: T(k-1,g), phi)(m+1)
def W(A):
    f=lambda m: m+1
    for k in A: f=T(k,f)
    return f
def sigma_formula(root,m):
    for A in reversed(root): m=W(A)(m)
    return m+1
def hyd(root): return tuple(tuple(tuple(() for _ in range(k)) for k in A) for A in root)
def run_model(root,m,cap=10**7):
    c=(m,0,hyd(root),0); n=0
    while c[0]!='HALT' and n<cap: c=model_step(*c); n+=1
    return c[1] if c[0]=='HALT' else None
cases=[([],0),([],5),([[]],0),([[]],3),([[],[]],1),([[],[],[]],2),([[0]],0),([[0]],2),([[0],[]],1),([[],[0]],1),([[0,0]],0),([[0,0]],1),([[0],[0]],0)]
import sys
for root,m in cases:
    a=run_model(root,m); b=sigma_formula(root,m)
    print(root,flush=True) if False else print(root,'m=%d'%m,'model sigma',a,'formula',b,'OK' if a==b else 'DIFF')
