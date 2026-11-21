#!/usr/bin/env python3
"""Verify the 5 macro rules the task states for BB64, on small parameters.

Rules (Bcfg(k,0,m,R) = 0^inf 3^(2m+1) 2^k A> R, head on R[0]):
 R=0^inf        -> B(1,0,1) 2^(k+2m) 0 1 1 0^inf
 R=0 1 1 ...    -> B(1,0,1) 2^(k+2m) 0 3 1 0^inf
 R=0 3 1 ...    -> B(1,0,1) 2^(k+2m) 0 0 1 0^inf
 R=0 0 1 ...    -> B(1,0,1) 2^(k+2m) 0 1 3 1 0^inf
 R=0 1 3 1 ...  -> halt
"""
BB64 = "1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ"
SNAME = "ABCDEF"


def parse(s):
    trans = []
    for g in s.split("_"):
        row = []
        for k in range(len(g)//3):
            e = g[3*k:3*k+3]
            row.append(None if e == "---" else (int(e[0]), e[1], -1 if e[2]=="Z" else ord(e[2])-65))
        trans.append(row)
    return trans


def step(trans, q, tape, head):
    e = trans[q][tape.get(head, 0)]
    if e is None:
        return None
    w, mv, nx = e
    tape[head] = w
    head += 1 if mv == "R" else -1
    return nx, head


def bcfg(k, m, right):
    tape = {}
    pos = -1
    for _ in range(k):
        tape[pos] = 2; pos -= 1
    for _ in range(2*m+1):
        tape[pos] = 3; pos -= 1
    for i, s in enumerate(right):
        tape[i] = s
    return tape


def window(tape, head, lo=None, hi=None):
    if lo is None: lo = min(list(tape)+[head])-2
    if hi is None: hi = max(list(tape)+[head])+2
    out = ""
    for i in range(lo, hi+1):
        c = str(tape.get(i,0))
        out += f"[{c}]" if i == head else c
    return out


def is_reservoir_start(q, tape, head, t):
    """A-state at start of a 2-reservoir: head>=0, reads 2, and to the left
    (nearest-first) there are exactly one 2 then the 3-stack then blank."""
    if q != 0 or t < 4 or head < 0 or tape.get(head,0) != 2:
        return False
    # head reads first reservoir 2; the Bcfg(1,0,1) left stream is one 2 then 3s
    if tape.get(head-1, 0) != 2:
        return False
    if tape.get(head-2, 0) != 3:
        return False
    return True


def run(trans, q, tape, head, maxsteps=500000):
    for t in range(maxsteps):
        if is_reservoir_start(q, tape, head, t):
            return t, q, head, "reservoir"
        r = step(trans, q, tape, head)
        if r is None or r[0] == -1:
            return t+1, -1, head, "halt"
        q, head = r
    return maxsteps, q, head, "max"


def left_profile(tape, head):
    """Return (num twos immediately left, then num threes)."""
    n2 = 0; p = head-1
    while tape.get(p,0) == 2:
        n2 += 1; p -= 1
    n3 = 0
    while tape.get(p,0) == 3:
        n3 += 1; p -= 1
    return n2, n3


def main():
    trans = parse(BB64)
    cases = [
        ("0^inf",        [0],       "0 1 1"),
        ("0 1 1",        [0,1,1],   "0 3 1"),
        ("0 3 1",        [0,3,1],   "0 0 1"),
        ("0 0 1",        [0,0,1],   "0 1 3 1"),
        ("0 1 3 1",      [0,1,3,1], "HALT"),
    ]
    for k in [1, 2, 3]:
        for m in [0, 1]:
            print(f"\n##### k={k} m={m} (expect reservoir 2^(k+2m)=2^{k+2*m}) #####")
            for name, right, expect in cases:
                tape = bcfg(k, m, right)
                q, head = 0, 0
                t, q, head, status = run(trans, q, tape, head)
                if status == "reservoir":
                    n2, n3 = left_profile(tape, head)
                    ctx = [tape.get(head+i,0) for i in range(6)]
                    okk = (n2 == 1 and n3 == 3)
                    print(f"  R={name:8s}: t={t:5d} left=(2^{n2},3^{n3}) ctx={ctx} {'OK' if okk else '??'} exp_marker={expect}")
                elif status == "halt":
                    print(f"  R={name:8s}: t={t:5d} HALT  {window(tape,head,head-8,head+6)}")
                else:
                    print(f"  R={name:8s}: NO RESULT (q={SNAME[q] if q>=0 else q}) {window(tape,head)}")


if __name__ == "__main__":
    main()
