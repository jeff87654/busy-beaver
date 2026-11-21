#!/usr/bin/env python3
"""For each start marker, find the step where the machine (in state B) first
sits on the rightmost 2 of the 2^k block with the new marker written on the right."""
BB64 = "1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ"
S = "ABCDEF"


def parse(st):
    tr=[]
    for g in st.split("_"):
        row=[]
        for i in range(len(g)//3):
            e=g[3*i:3*i+3]
            row.append(None if e=="---" else (int(e[0]),e[1],-1 if e[2]=="Z" else ord(e[2])-65))
        tr.append(row)
    return tr


def step(tr,q,tape,head):
    e=tr[q][tape.get(head,0)]
    if e is None:return None
    w,mv,nx=e;tape[head]=w;head+= 1 if mv=="R" else -1
    return nx,head


def bcfg(k,m,right):
    tape={};pos=-1
    for _ in range(k):tape[pos]=2;pos-=1
    for _ in range(2*m+1):tape[pos]=3;pos-=1
    for i,s in enumerate(right):tape[i]=s
    return tape


def marker(tape, n=5):
    return [tape.get(i,0) for i in range(n)]


def go(k,m,right):
    tr=parse(BB64);tape=bcfg(k,m,right);q,head=0,0
    print(f"\n Bcfg({k},0,{m},{right}) start marker={marker(tape)}")
    for t in range(60):
        # detect: state B, head reads 2, head<0 (on the 2^k block), and to the far left only 2s/3s
        if q==1 and tape.get(head,0)==2 and head<0:
            # check that head is the rightmost 2 of the block (head+1 is a marker cell >=0 or 2)
            leftall2 = all(tape.get(j,0)==2 for j in range(head-k,head+1))
            if leftall2:
                print(f"   setup done at t={t}: q=B head={head}, right marker={marker(tape)}")
                return t, marker(tape)
        r=step(tr,q,tape,head)
        if r is None or r[0]==-1:
            print(f"   HALT at t={t+1}, marker={marker(tape)}")
            return t+1,None
        q,head=r


if __name__=="__main__":
    for right in ([0],[0,1,1],[0,3,1],[0,0,1],[0,1,3,1]):
        go(5,0,right)
