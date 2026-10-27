import sys
from pm_full import full_table
name=sys.argv[1]; d0=sys.argv[2]
PT=full_table(name)
chain=[d0]
for k in range(8):
    e=PT[chain[-1]]['y']
    print('depth',k,chain[-1],' c->',PT[chain[-1]]['c'],' y->',e,' 0->',PT[chain[-1]]['0'],' x->',PT[chain[-1]]['x'])
    if not e or e=='HALT' or e[2] in chain: break
    chain.append(e[2])
