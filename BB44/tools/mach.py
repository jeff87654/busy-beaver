#!/usr/bin/env python3
"""Fast simulator + macro-shape detector for the BB(4,4) champion."""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine

MACHINE = '0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA'
CHAMP = '1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC'


class Tape:
    __slots__ = ('cells', 'p', 'state')

    def __init__(self):
        self.cells = {}
        self.p = 0
        self.state = 'A'

    def read(self):
        return self.cells.get(self.p, 0)

    def write(self, s):
        self.cells[self.p] = s

    def span(self):
        if not self.cells:
            return 0, 0
        return min(self.cells), max(self.cells)

    def step(self, m):
        r = m.get((self.state, self.read()))
        if r is None:
            return False
        w, d, ns = r
        self.cells[self.p] = w
        self.p += 1 if d == 'R' else -1
        self.state = ns
        return True


def rle(seq):
    out = []
    for x in seq:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return ' '.join('%d^%d' % (a, b) for a, b in out)


def tape_str(t, width=40):
    lo, hi = t.span()
    lo = min(lo, t.p)
    hi = max(hi, t.p)
    left = [t.cells.get(i, 0) for i in range(t.p - 1, lo - 1, -1)]
    right = [t.cells.get(i, 0) for i in range(t.p + 1, hi + 1)]
    return '%s@%d  L[%s]  [%d]  R[%s]' % (
        t.state, t.p, rle(left[:width]), t.read(), rle(right[:width]))


def bcfg_of(t):
    """Ligocki B(k,n,m) shape: left = 2^k 3^(2m+1) 0^inf ; head A on 1^n.
    Returns (k, n, m) or None."""
    if t.state != 'A':
        return None
    lo, hi = t.span()
    lo = min(lo, t.p)
    left = [t.cells.get(i, 0) for i in range(t.p - 1, lo - 1, -1)]
    k = 0
    while k < len(left) and left[k] == 2:
        k += 1
    if k == 0:
        return None
    j = k
    while j < len(left) and left[j] == 3:
        j += 1
    m3 = j - k
    if m3 == 0 or m3 % 2 == 0:
        return None
    for x in left[j:]:
        if x != 0:
            return None
    right = [t.cells.get(i, 0) for i in range(t.p + 1, hi + 1)]
    n = 0
    while n < len(right) and right[n] == 1:
        n += 1
    return (k, n, (m3 - 1) // 2)


def main():
    machine = sys.argv[1] if len(sys.argv) > 1 else MACHINE
    limit = int(sys.argv[2]) if len(sys.argv) > 2 else 5000000
    m = parse_machine(machine)
    t = Tape()
    n = 0
    prev = None
    while n < limit:
        b = bcfg_of(t)
        if b != prev:
            print('step %-10d Bcfg k=%-3d n=%-3d m=%-4d   %s' % (n, b[0], b[1], b[2], tape_str(t, 12)) if b else 'step %-10d (no Bcfg)' % n)
            prev = b
        if not t.step(m):
            print('HALT at step', n, tape_str(t))
            break
        n += 1


if __name__ == '__main__':
    main()
