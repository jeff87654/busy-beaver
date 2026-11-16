#!/usr/bin/env python3
"""Explore the BB64 machine and check the macro rules claimed in the task.

BB64 = 54-L with B1: 1RZ -> 1RF and an extra state F:
    1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ
"""
import sys

BB64 = "1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ"
BB54L = "1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE"


def parse(s):
    groups = s.split("_")
    trans = []
    for g in groups:
        row = []
        for k in range(len(g) // 3):
            e = g[3*k:3*k+3]
            if e == "---":
                row.append(None)
            else:
                w, mv, nx = e[0], e[1], e[2]
                row.append((int(w), mv, -1 if nx == "Z" else ord(nx) - ord("A")))
        trans.append(row)
    return trans


def step(trans, q, tape, head):
    """One step. tape is a dict {int: sym}. Returns (newq, newhead) or None if halt."""
    e = trans[q][tape.get(head, 0)]
    if e is None:
        return None
    w, mv, nx = e
    tape[head] = w
    head += 1 if mv == "R" else -1
    return nx, head


def render(tape, head, lo=None, hi=None):
    if lo is None:
        lo = min(list(tape) + [head]) - 2
    if hi is None:
        hi = max(list(tape) + [head]) + 2
    s = ""
    for i in range(lo, hi + 1):
        c = str(tape.get(i, 0))
        if i == head:
            c = "[" + c + "]"
        s += c
    return s


def mk_bcfg(k, n, m, right, head_at_right=True):
    """Build tape for Bcfg(k,n,m,right): 0^inf 3^(2m+1) 2^k A> 1^n right.
    Head is placed on the first symbol of `right` (in state A)."""
    tape = {}
    pos = -1
    for _ in range(k):
        tape[pos] = 2
        pos -= 1
    for _ in range(2*m + 1):
        tape[pos] = 3
        pos -= 1
    # right context starts at head=0
    for i, sym in enumerate(right):
        tape[i] = sym
    for i in range(n):
        # n ones placed before `right`; shift right context
        pass
    return tape


def mk_bcfg2(k, n, m, right):
    """0^inf 3^(2m+1) 2^k A> 1^n right ; head on the first 1 of the 1^n block."""
    tape = {}
    pos = -1
    for _ in range(k):
        tape[pos] = 2
        pos -= 1
    for _ in range(2*m + 1):
        tape[pos] = 3
        pos -= 1
    h = 0
    for _ in range(n):
        tape[h] = 1
        h += 1
    for i, sym in enumerate(right):
        tape[h + i] = sym
    return tape, 0


def run(trans, q, tape, head, maxsteps, stop_q=None, verbose=False):
    for t in range(maxsteps):
        if verbose and t < 40:
            print(f"  t={t:3d} q={q} {render(tape, head)}")
        r = step(trans, q, tape, head)
        if r is None:
            return t, q, tape, head, "halt"
        q, head = r
        if q == -1:
            return t + 1, q, tape, head, "halt"
        if stop_q is not None and q == stop_q:
            return t + 1, q, tape, head, "stopq"
    return maxsteps, q, tape, head, "max"


def main():
    t64 = parse(BB64)
    t54 = parse(BB54L)
    print("BB64 states:", len(t64), "BB54L states:", len(t54))
    print("B row BB64:", t64[1], " B row BB54:", t54[1])
    print("F row BB64:", t64[5])

    # 1. first 25 steps from blank tape: compare with BB54L (should match up to B(5,1,0))
    print("\n=== startup: blank tape, first 30 steps ===")
    tape = {}
    q, head = 0, 0
    for t in range(30):
        r = step(t64, q, tape, head)
        if r is None or r[0] == -1:
            print(f" t={t} halted"); break
        q, head = r
        if t in (24, 25, 26):
            print(f" t={t+1} q={q} {render(tape, head)}")

    # 2. F-phase: start at Bcfg(k,0,m, 0 1 1 0^inf), i.e. the halt_enter pre-config
    #    with k=1,m=1 (small), run and watch it re-enter B / halt.
    for (k, m) in [(1, 1), (2, 1), (1, 2), (3, 1)]:
        print(f"\n=== F-phase from Bcfg({k},0,{m},0 1 1 0^inf) ===")
        right = [0, 1, 1]
        tape, head = mk_bcfg2(k, 0, m, right)
        q = 0  # A
        # run 200 steps or until state A repeats with a fresh context
        for t in range(300):
            r = step(t64, q, tape, head)
            if r is None or r[0] == -1:
                print(f" HALT at t={t+1}, q={r[0] if r else 'undef'}")
                print(f"   tape={render(tape, head, head-6, head+10)}")
                break
            q, head = r
            if t < 12:
                print(f"  t={t+1} q={q} {render(tape, head, head-8, head+10)}")
        else:
            print("  (300 steps, no halt yet)")
            print(f"   tape={render(tape, head, head-6, head+12)}")


if __name__ == "__main__":
    main()
