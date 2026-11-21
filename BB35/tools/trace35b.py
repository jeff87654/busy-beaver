#!/usr/bin/env python3
"""Exact physical trace tool for the BB(3,5) champion.

The tape is a dict {position: symbol}; the head is at an absolute position.
The physical tape is printed from the left, with the head cell in brackets.

Recognised macro shape (head in state A):

    0^inf  3^(2m+1)  2^k  A>  1^n  s  ...

where [s] is the cell under the head, and the n ones are the cells
immediately to the right of the head.

Usage:  trace35b.py <mode> <k> <m> [limit]
        mode = four : start from 0^inf 3^(2m+1) 2^k A> [4]
        mode = two  : start from 0^inf 3^(2m+1) 2^k A> [2]
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
        cur = self.get(self.pos)
        t = self.m.table[(i, cur)]
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

    def rle(self):
        if not self.tape:
            return "(blank)"
        lo, hi = min(self.tape), max(self.tape)
        out = []
        i = lo
        while i <= hi:
            j = i
            while j <= hi and self.get(j) == self.get(i):
                j += 1
            n = j - i
            s = self.get(i)
            out.append("%d^%d" % (s, n) if n > 1 else str(s))
            i = j
        return " ".join(out)


def shape(t):
    """Return (k, n, m) if the tape has the shape

           0^inf 3^(2m+1) 2^k [head] 1^n ...
    (ignoring the state), else None.
    """
    lo = min(t.tape) if t.tape else t.pos
    left = []
    p = t.pos - 1
    while p >= lo and t.get(p) != 0:
        left.append(t.get(p))
        p -= 1
    left.reverse()                       # far -> near
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
    return (k, n, (a - 1) // 2)


def build(k, m, headsym):
    t = TM(OURS)
    p = 0
    for _ in range(2 * m + 1):
        t.tape[p] = 3
        p += 1
    for _ in range(k):
        t.tape[p] = 2
        p += 1
    t.pos = p
    t.tape[p] = headsym
    return t


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "four"
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    m = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    limit = int(sys.argv[4]) if len(sys.argv) > 4 else 200000
    verbose = os.environ.get("VERBOSE") == "1"

    t = build(k, m, 2 if mode == "two" else 4)

    print("start : %s  %s" % (t.state, t.rle()))
    for step in range(limit + 1):
        if verbose:
            print("  %6d %s  %s" % (step, t.state, t.word()))
        sh = shape(t)
        if sh is not None:
            print("  step %7d : state %s  B(k=%d, n=%d, m=%d)  head on %d   [%s]"
                  % (step, t.state, sh[0], sh[1], sh[2], t.get(t.pos), t.rle()))
        if not t.step():
            print("  HALT at step %d : %s" % (step, t.word()))
            return
    print("  limit reached")


if __name__ == "__main__":
    main()
