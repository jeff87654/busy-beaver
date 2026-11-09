#!/usr/bin/env python3
"""Extract the full macro-config sequence of the BB(4,4) startup phase.

A 'canonical' config is one of Ligocki form
    0^inf  3^(2m+1)  2^k  <A>  [1^n]  R
i.e. reading the LEFT stream from the head outwards it is 2^k, then 3^(2m+1),
then all blanks; the head is in state A.  n is the number of consecutive 1's
starting at the head (the head's own cell included), so n >= 1 iff the head
reads a 1.

Prints one line per canonical config, plus the macro rule (transition) between
successive ones.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine

OURS = '0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA'


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
        i = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'.index(self.state)
        cur = self.read()
        t = m.table[(i, cur)]
        if t is None or t[2] is None:
            return False
        w, d, q = t
        self.write(w)
        self.p += 1 if d == 'R' else -1
        self.state = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'[q]
        return True


def rle(seq):
    out = []
    for x in seq:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return ' '.join('%d^%d' % (a, b) for a, b in out)


def canon(t):
    """Return (k, m, n, right_rle) if the config is canonical, else None."""
    if t.state != 'A':
        return None
    k = 0
    i = t.p - 1
    while t.cells.get(i, 0) == 2:
        k += 1
        i -= 1
    if k == 0:
        return None
    j = 0
    while t.cells.get(i, 0) == 3:
        j += 1
        i -= 1
    if j < 1 or j % 2 == 0:
        return None
    # everything further left must be blank
    while i >= t.p - 4000:
        if t.cells.get(i, 0) != 0:
            return None
        i -= 1
    m = (j - 1) // 2
    # count the 1's starting at the head
    n = 0
    x = t.p
    while t.cells.get(x, 0) == 1:
        n += 1
        x += 1
    if n == 0 and t.read() != 0:
        return None
    lo, hi = t.span()
    right = [t.cells.get(y, 0) for y in range(t.p + 1, hi + 1)]
    return (k, m, n, rle(right))


def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 360000
    m = parse_machine(OURS)
    t = Tape()
    prev = None
    for n in range(limit + 1):
        c = canon(t)
        if c is not None and c != prev:
            print('step %-8d  B(k=%-4d m=%-4d n=%-4d)  R[%s]' % (n, c[0], c[1], c[2], c[3]))
            prev = c
        if not t.step(m):
            print('HALT at step', n)
            break


if __name__ == '__main__':
    main()
