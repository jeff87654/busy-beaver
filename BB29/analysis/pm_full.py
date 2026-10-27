# exact pair-level table for all (state,side,symbol), computed from the TM (macro2.run)
from tm import load, parse, nm
from macro2 import run
def full_table(name):
    m=load(name); n,T=parse(m); PT={}
    for i in range(n):
        for side in '><':
            e=nm(i)+side; PT[e]={}
            for p in '0cxy':
                r=run(T,i,side,p)
                PT[e][p]='HALT' if r[0]=='HALT' else (r if len(r)==3 else None)
    return PT
