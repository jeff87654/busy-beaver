#!/usr/bin/env python3
"""Macro-transition scanner for the BB(3,5) champion.

Recognises the shape

    0^inf 3^(2m+1) 2^k  A>  1^n  s        (head in state A, reading s)

and reports, for a given starting (k, m) and head symbol, the first
configuration of the same shape that the machine reaches, together with the
number of steps needed.

Usage:  macro35.py <two|four> <k> <m> [limit]
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from tm_lib import parse_machine

OURS = "1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC"
STATES = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


class TM:
    def __init__(self, spec):
        self.m = parse_machine(spec)
        self.tape = {}
        self.pos = 0
        self.state = "A"

    def get(self, p):
        return self.tape.get(p, 0)

    def put(self, p, s):
        if s:
            self.tape[p] = s
        else:
            self.tape.pop(p, None)

    def step(self):
        i = STATES.index(self.state)
        t = self.m.table[(i, self.get(self.pos))]
        if t is None or t[2] is None:
            return False
        w, d, q = t
        self.put(self.pos, w)
        self.pos += 1 if d == "R" else -1
        self.state = STATES[q]
        return True

    def word(self):
        if not self.tape:
            return "(blank)"
        lo, hi = min(self.tape), max(self.tape)
        out = []
        for p in range(lo, hi + 1):
            out.append("[%d]" % self.get(p) if p == self.pos else str(self.get(p)))
        return " ".join(out)


def classify(t):
    """(k, n, m, s) for  0^inf 3^(2m+1) 2^k A> 1^n s,  else None."""
    if t.state != "A":
        return None
    lo = min(t.tape) if t.tape else t.pos
    left = []
    p = t.pos - 1
    while p >= lo and t.get(p) != 0:
        left.append(t.get(p))
        p -= 1
    left.reverse()
    i = 0
    while i < len(left) and left[i] == 3:
        i += 1
    a = i
    while i < len(left) and left[i] == 2:
        i += 1
    k = i - a
    if i != len(left) or a == 0 or a % 2 == 0:
        return None
    n = 0
    p = t.pos + 1
    while t.get(p) == 1:
        n += 1
        p += 1
    return (k, n, (a - 1) // 2, t.get(t.pos))


def build(k, m, s):
    t = TM(OURS)
    p = 0
    for _ in range(2 * m + 1):
        t.tape[p] = 3
        p += 1
    for _ in range(k):
        t.tape[p] = 2
        p += 1
    t.pos = p
    t.tape[p] = s
    return t


def main():
    mode = sys.argv[1]
    k = int(sys.argv[2])
    m = int(sys.argv[3])
    limit = int(sys.argv[4]) if len(sys.argv) > 4 else 3000000
    s = 2 if mode == "two" else 4
    t = build(k, m, s)
    start = classify(t)
    print("start B(k=%d,n=%d,m=%d) head on %d : %s" % (start[0], start[1], start[2], start[3], t.word()))
    for step in range(limit + 1):
        got = classify(t)
        if got is not None and got[:3] != start[:3]:
            print("  step %8d : B(k=%d,n=%d,m=%d) head on %d : %s"
                  % (step, got[0], got[1], got[2], got[3], t.word()))
            return
        if not t.step():
            print("  HALT at step %d : %s" % (step, t.word()))
            return
    print("  no macro transition within %d steps" % limit)


if __name__ == "__main__":
    main()
