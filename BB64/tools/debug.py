#!/usr/bin/env python3
"""Step-by-step debug of BB64 from Bcfg(5,0,m,0^inf)."""
BB64 = "1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ"
BB54L = "1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE"
S = "ABCDEF"


def parse(st):
    tr = []
    for g in st.split("_"):
        row = []
        for i in range(len(g)//3):
            e = g[3*i:3*i+3]
            row.append(None if e=="---" else (int(e[0]), e[1], -1 if e[2]=="Z" else ord(e[2])-65))
        tr.append(row)
    return tr


def step(tr, q, tape, head):
    e = tr[q][tape.get(head,0)]
    if e is None: return None
    w,mv,nx = e
    tape[head]=w; head += 1 if mv=="R" else -1
    return nx,head


def show(tape, head, lo=-18, hi=18):
    out=""
    for i in range(lo,hi+1):
        c=str(tape.get(i,0)); out += f"[{c}]" if i==head else c
    return out


def bcfg(k,m,right):
    tape={}; pos=-1
    for _ in range(k): tape[pos]=2; pos-=1
    for _ in range(2*m+1): tape[pos]=3; pos-=1
    for i,s in enumerate(right): tape[i]=s
    return tape


def go(which, k, m, right, nsteps):
    tr = parse(BB64 if which=="64" else BB54L)
    tape=bcfg(k,m,right); q,head=0,0
    print(f"--- BB{which} Bcfg({k},0,{m}, {right}), head={head} ---")
    print(f" t=0  q={S[q]} {show(tape,head)}")
    for t in range(nsteps):
        r=step(tr,q,tape,head)
        if r is None or r[0]==-1:
            print(f" t={t+1:3d} HALT q={r[0] if r else 'undef'} {show(tape,head)}")
            return
        q,head=r
        print(f" t={t+1:3d} q={S[q]} h={head:3d} {show(tape,head)}")


if __name__=="__main__":
    import sys
    go("64", 5, 1, [0], int(sys.argv[1]) if len(sys.argv)>1 else 45)
