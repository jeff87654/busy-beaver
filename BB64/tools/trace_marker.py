#!/usr/bin/env python3
"""Trace BB64 from Bcfg(k,0,m,marker) and report each visit to state A,
so we can see the marker evolution and reservoir creation."""
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
    w,mv,nx=e
    tape[head]=w; head+= 1 if mv=="R" else -1
    return nx,head


def bcfg(k,m,right):
    tape={};pos=-1
    for _ in range(k):tape[pos]=2;pos-=1
    for _ in range(2*m+1):tape[pos]=3;pos-=1
    for i,s in enumerate(right):tape[i]=s
    return tape


def show(tape,head,lo=-14,hi=20):
    out=""
    for i in range(lo,hi+1):
        c=str(tape.get(i,0));out+=f"[{c}]" if i==head else c
    return out


def context(tape,head,n=8):
    return [tape.get(head+i,0) for i in range(n)]


def twos_left(tape,head):
    p=head-1;n=0
    while tape.get(p,0)==2:n+=1;p-=1
    return n


def go(k,m,right,maxsteps=4000):
    tr=parse(BB64);tape=bcfg(k,m,right);q,head=0,0
    print(f"\n===== Bcfg({k},0,{m},{right}) =====")
    visits=0
    for t in range(maxsteps):
        # detect A-state visit with right context starting in 2s (fresh reservoir)
        if q==0 and tape.get(head,0)==2 and head>=0:
            visits+=1
            ctx=context(tape,head)
            print(f"  A-visit t={t:4d} h={head:3d} left2={twos_left(tape,head)} ctx={ctx}")
            if visits>=6:break
        r=step(tr,q,tape,head)
        if r is None or r[0]==-1:
            print(f"  HALT t={t+1} {show(tape,head)}")
            return
        q,head=r


if __name__=="__main__":
    import sys
    for right in ([0],[0,1,1],[0,3,1],[0,0,1],[0,1,3,1]):
        go(1,0,right)
