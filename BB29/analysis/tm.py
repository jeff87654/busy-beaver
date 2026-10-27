# shared parser / simulator for the BB29 / BB31 / BB33 hydra machines (machines.txt in this directory)
import sys
def load(name):
    import os
    for line in open(os.path.join(os.path.dirname(os.path.abspath(__file__)),"machines.txt")):
        p=line.split()
        if p and p[0]==name: return p[1]
    raise KeyError(name)
def parse(m):
    n=(len(m)+1)//7; T={}
    for i in range(n):
        row=m[7*i:7*i+6]
        for s in (0,1):
            t=row[3*s:3*s+3]
            T[(i,s)]=None if t=='---' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
    return n,T
def nm(i): return chr(65+i)
if __name__=='__main__':
    m=load(sys.argv[1]); n,T=parse(m)
    for i in range(n):
        print(nm(i), ' '.join('---' if T[(i,s)] is None else '%d%s%s'%(T[(i,s)][0],'R' if T[(i,s)][1]>0 else 'L',nm(T[(i,s)][2])) for s in (0,1)))
