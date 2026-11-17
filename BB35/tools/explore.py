#!/usr/bin/env python3
"""Exploration helper for the BB(3,5) champion.

Prints the tape in compressed form ("0^inf 3^7 2^3 A> 1^2 0^inf") at
regular intervals, so that the shape of the configuration family can be read
off directly.
"""
import argparse, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from tm_lib import parse_machine

ALPHA = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'

OURS = '1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC'


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

    def side(self, right):
        """Nonzero symbols of one side, nearest first (0s inside are kept)."""
        out = []
        i = self.p + 1 if right else self.p - 1
        while True:
            v = self.cells.get(i, 0)
            if v == 0:
                # stop at the first blank unless a nonblank follows later
                j = i + 1 if right else i - 1
                if not any(self.cells.get(j + d, 0) != 0 for d in range(-1, 2)):
                    break
                out.append(v)
                i += 1 if right else -1
                continue
            out.append(v)
            i += 1 if right else -1
            if len(out) > 4000:
                break
        return out

    def left(self):
        return self.side(False)

    def right(self):
        return self.side(True)


def compress(xs):
    """["0","0","3","3"] -> "0^2 3^2"."""
    parts = []
    i = 0
    while i < len(xs):
        j = i
        while j < len(xs) and xs[j] == xs[i]:
            j += 1
        parts.append('%s^%d' % (xs[i], j - i))
        i = j
    return ' '.join(parts) if parts else '-'


def show(t):
    left = compress([str(x) for x in reversed(t.left())])   # outermost first
    right = compress([str(x) for x in t.right()])
    return '0^inf %s <%s %s^%d %s> %s 0^inf' % (left, t.state, t.read(), 1,
                                                 '', right) if False else \
        '0^inf %s  %s>%d  %s  0^inf' % (left, t.state, t.read(), right)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--machine', default=OURS)
    ap.add_argument('--steps', type=int, default=100)
    ap.add_argument('--every', type=int, default=1)
    ap.add_argument('--trace', type=int, default=0)
    args = ap.parse_args()
    m = parse_machine(args.machine)
    t = Tape()
    n = 0
    while n < args.steps:
        if not t.step(m):
            print('HALT after %d steps (state %s, symbol %d)' % (n, t.state, t.read()))
            break
        n += 1
        if n <= args.trace or (args.every and n % args.every == 0):
            print('step %4d  %s' % (n, show(t)))
    print('steps %d  state %s  symbol %d  nonblank %d'
          % (n, t.state, t.read(), sum(1 for v in t.cells.values() if v)))


if __name__ == '__main__':
    main()
