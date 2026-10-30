#!/usr/bin/env python3
"""Compact summary of the BB(4,4) startup's canonical (Ligocki-shaped) configs.

Prints: step, (k, n, m) in Ligocki's order, the right stream, and the number
of steps since the previous canonical config.
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
    """Ligocki shape: left stream from the head outwards = 2^k, 3^(2m+1), 0^inf."""
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
    # everything further left must be blank: the 3-block must end exactly at
    # the leftmost non-blank cell
    lo, hi = t.span()
    if lo < t.p and i != lo - 1:
        return None
    m = (j - 1) // 2
    n = 0
    x = t.p
    while t.cells.get(x, 0) == 1:
        n += 1
        x += 1
    if n == 0 and t.read() != 0:
        return None
    right = [t.cells.get(y, 0) for y in range(t.p + 1, hi + 1)]
    return (k, n, m, rle(right))


def main():
    lo_s = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    hi_s = int(sys.argv[2]) if len(sys.argv) > 2 else 360000
    m = parse_machine(OURS)
    t = Tape()
    prev = None
    prev_step = 0
    for n in range(hi_s + 1):
        c = canon(t)
        if c is not None and c != prev:
            if n >= lo_s:
                print('%8d  (+%6d)  B(k=%-4d n=%-4d m=%-4d)  R[%s]'
                      % (n, n - prev_step, c[0], c[1], c[2], c[3]))
            prev = c
            prev_step = n
        if not t.step(m):
            print('HALT at step', n)
            break


if __name__ == '__main__':
    main()
