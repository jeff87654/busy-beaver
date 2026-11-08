"""Explore the BB54 machine: compare with the wiki champion, simulate, dump traces."""

import itertools
import os
import sys

sys.path.insert(0, ".")
from sim import Machine, fmt, parse

OURS = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "bb54.txt")).read().strip()
WIKI = "1LD2RA3RB1LC_1LD2LA3RB---_2RA1LA3RC2LC_2RA---2LD2LE_------1RZ1LD"
BB34 = "1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC"


def relabel(m, sp, st):
    """Relabel symbols by sp and states by st (permutations given as lists)."""
    tr, ns, nsy = m.trans, m.nstates, m.nsyms
    new = [[None] * nsy for _ in range(ns)]
    for q in range(ns):
        for s in range(nsy):
            e = tr[q][s]
            if e is None:
                continue
            w, mv, nx = e
            nq = -1 if nx == 25 else st[nx]
            new[st[q]][sp[s]] = (sp[w], mv, nq if nq == -1 else nq)
    return new


def same(a, b):
    return a == b


def equivalent(m1, m2):
    """Is m1 equal to m2 up to a relabelling of states and symbols?"""
    ns, nsy = m1.nstates, m1.nsyms
    if (ns, nsy) != (m2.nstates, m2.nsyms):
        return False
    for sp in itertools.permutations(range(nsy)):
        for st in itertools.permutations(range(ns)):
            r = relabel(m1, list(sp), list(st))
            # r is in m2's alphabet; compare with m2
            t2 = m2.trans
            ok = True
            for q in range(ns):
                for s in range(nsy):
                    e = r[q][s]
                    f = t2[q][s]
                    if (e is None) != (f is None):
                        ok = False
                        break
                    if e is None:
                        continue
                    w1, mv1, n1 = e
                    w2, mv2, n2 = f
                    n2 = -1 if n2 == 25 else n2
                    if (w1, mv1, n1) != (w2, mv2, n2):
                        ok = False
                        break
                if not ok:
                    break
            if ok:
                return (sp, st)
    return None


def show(m, name):
    print(f"=== {name}: {m.string}")
    for q, row in enumerate(m.trans):
        cells = []
        for e in row:
            if e is None:
                cells.append("  ---  ")
            else:
                w, mv, nx = e
                t = "H" if nx == 25 else chr(ord("A") + nx)
                cells.append(f" {w}{mv}{t}  ")
        print(f"  {chr(ord('A') + q)}: " + "".join(cells))


def trace(m, n=60):
    tape = {}
    head = 0
    state = 0
    for i in range(n):
        sym = tape.get(head, 0)
        r = m.step(state, sym)
        if r is None:
            print(f"  step {i}: state {chr(ord('A')+state)} reads {sym} -> UNDEFINED")
            return
        nq, w, mv = r
        lo, hi = min(head, 0), max(head, 0)
        tape[head] = w
        head += 1 if mv == "R" else -1
        state = nq
        lo = min(lo, head)
        hi = max(hi, head)
        cfg = "".join(str(tape.get(j, 0)) for j in range(lo, hi + 1))
        st = "H" if state == -1 else chr(ord("A") + state)
        print(f"  step {i+1}: state {st} head {head} [{cfg}]")
        if state == -1:
            return


if __name__ == "__main__":
    m1 = Machine(OURS)
    m2 = Machine(WIKI)
    m3 = Machine(BB34)
    show(m1, "ours (bb54.txt)")
    show(m2, "wiki BB(5,4) champion")
    show(m3, "BB(3,4) champion")

    print()
    print("ours == wiki under relabelling?", equivalent(m1, m2))
    print("ours == BB34 under relabelling?", equivalent(m1, m3))
    print()
    print("--- trace of ours ---")
    trace(m1, 60)
    print()
    print("--- trace of wiki champion ---")
    trace(m2, 60)
