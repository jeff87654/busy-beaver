#!/usr/bin/env python3
"""Trace the BB(4,4) startup phase in detail.

Prints, for a step range, each step at which the head is in state A (the
"reading" state) or in state D, with the tape run-length encoded.
Left stream is printed nearest-first (busycoq convention).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine

OURS = '0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA'
ALPHA = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'


class Tape:
    __slots__ = ('cells', 'p', 'state')

    def __init__(self):
        self.cells = {}
        self.p = 0
        self.state = 'A'

    def read(self):
        return self.cells.get(self.p, 0)

    def write(self, s):
        if s == 0:
            self.cells.pop(self.p, None)
        else:
            self.cells[self.p] = s

    def span(self):
        if not self.cells:
            return 0, 0
        return min(self.cells), max(self.cells)

    def step(self, m):
        i = ALPHA.index(self.state)
        cur = self.read()
        t = m.table[(i, cur)]
        if t is None or t[2] is None:
            return False
        w, d, q = t
        self.write(w)
        self.p += 1 if d == 'R' else -1
        self.state = ALPHA[q]
        return True


def rle(seq):
    out = []
    for x in seq:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return ' '.join('%d^%d' % (a, b) for a, b in out)


def describe(t):
    lo, hi = t.span()
    lo = min(lo, t.p)
    hi = max(hi, t.p)
    # left stream nearest-first
    left = [t.cells.get(i, 0) for i in range(t.p - 1, lo - 1, -1)]
    right = [t.cells.get(i, 0) for i in range(t.p + 1, hi + 1)]
    return 'L[%s] [%d] R[%s]' % (rle(left), t.read(), rle(right))


def main():
    lo_s = int(sys.argv[1])
    hi_s = int(sys.argv[2])
    every = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    m = parse_machine(OURS)
    t = Tape()
    for n in range(hi_s + 1):
        if n >= lo_s and (n % every == 0):
            print('%8d %s  %s' % (n, t.state, describe(t)))
        if not t.step(m):
            print('HALT at', n)
            break


if __name__ == '__main__':
    main()
