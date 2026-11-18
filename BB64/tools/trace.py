#!/usr/bin/env python3
"""Trace the BB64 machine phase by phase with small parameters to uncover
the macro-rule structure.  Absolute tape coordinates are printed."""
import sys

BB64 = "1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ"
SNAME = "ABCDEF"


def parse(s):
    groups = s.split("_")
    trans = []
    for g in groups:
        row = []
        for k in range(len(g) // 3):
            e = g[3*k:3*k+3]
            row.append(None if e == "---" else (int(e[0]), e[1], -1 if e[2] == "Z" else ord(e[2]) - 65))
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


def win(tape, head, pad=3):
    """Window string with absolute coords around head."""
    lo, hi = head - 14, head + 14
    parts = []
    for i in range(lo, hi + 1):
        c = str(tape.get(i, 0))
        parts.append(f"[{c}]" if i == head else c)
    return f"@{head:4d} q=" + "".join(parts)


def bcfg(k, m, right):
    """0^inf 3^(2m+1) 2^k A> right ; head=0 reads right[0]."""
    tape = {}
    pos = -1
    for _ in range(k):
        tape[pos] = 2; pos -= 1
    for _ in range(2*m + 1):
        tape[pos] = 3; pos -= 1
    for i, s in enumerate(right):
        tape[i] = s
    return tape


def run_until(trans, q, tape, head, pred, maxsteps=200000, trace=False, tag=""):
    for t in range(maxsteps):
        if trace and t < 20:
            print(f"   {tag} t={t:3d} {win(tape, head)}")
        if pred(q, tape, head, t):
            return t, q, head, True
        r = step(trans, q, tape, head)
        if r is None or r[0] == -1:
            return t + 1, -1, head, False
        q, head = r
    return maxsteps, q, head, False


def main():
    trans = parse(BB64)
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 5

    print(f"=== Round 1: Bcfg({k},0,{m}, 0^inf), the B_sweep ===")
    tape = bcfg(k, m, [0])
    q, head = 0, 0
    # B_sweep ends when A (q=0) reads a 2 (the reservoir) after the marker was planted.
    # Detect: q==0 and tape[head]==2 and we've moved right past original position.
    def at_reservoir(q, tape, head, t):
        return t > 5 and q == 0 and tape.get(head, 0) == 2 and head > 0
    t, q, head, ok = run_until(trans, q, tape, head, at_reservoir, trace=True, tag="sweep")
    print(f" B_sweep end t={t} q={SNAME[q] if q>=0 else 'H'} {win(tape,head)}")

    print(f"\n=== D_chain: eat the reservoir until A reads a non-2 (marker) ===")
    def at_marker(q, tape, head, t):
        return t > 0 and q == 0 and tape.get(head, 0) != 2
    t2, q, head, ok2 = run_until(trans, q, tape, head, at_marker, trace=False, tag="dchain")
    print(f" D_chain end t={t2} q={SNAME[q] if q>=0 else 'H'} {win(tape,head)}")
    # right context from head
    ctx = [tape.get(head + i, 0) for i in range(8)]
    print(f" right context after D_chain: {ctx}")
    # count twos left of head before the 3-block
    n2 = 0; p = head - 1
    while p in tape and tape[p] == 2:
        n2 += 1; p -= 1
    print(f" twos immediately left of head: {n2}")

    print(f"\n=== F-phase: A reads 0 of marker; trace until A reads a fresh reservoir again ===")
    def at_newres(q, tape, head, t):
        return t > 3 and q == 0 and tape.get(head, 0) == 2
    t3, q, head, ok3 = run_until(trans, q, tape, head, at_newres, trace=True, tag="F")
    print(f" F-phase end t={t3} q={SNAME[q] if q>=0 else 'H'} {win(tape,head)}")
    ctx = [tape.get(head + i, 0) for i in range(10)]
    print(f" right context now: {ctx}")


if __name__ == "__main__":
    main()
