#!/usr/bin/env python3
"""Fast, dict-tape simulator for a TNF machine string.

Usage:
    python sim.py --machine <STR> [--steps N] [--every K] [--start "state,left,cur,right"]
    python sim.py --machine <STR> --trace N            # print first N steps
"""
import argparse, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine


class Tape:
    """Sparse tape: dict position -> symbol; head at position p."""
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

    def word(self, k=200):
        lo = self.p - k
        hi = self.p + k
        out = []
        for i in range(lo, hi):
            out.append(str(self.cells.get(i, 0)))
        return ''.join(out)

    def span(self):
        if not self.cells:
            return (0, 0)
        return (min(self.cells), max(self.cells))

    def nonblank(self):
        return sum(1 for v in self.cells.values() if v != 0)

    def left(self):
        lo, hi = self.span()
        return [self.cells.get(i, 0) for i in range(self.p - 1, lo - 1, -1)]

    def right(self):
        lo, hi = self.span()
        return [self.cells.get(i, 0) for i in range(self.p + 1, hi + 1)]

    def snapshot(self):
        """(state, left list, cur, right list) with left/right truncated to nonblank."""
        return (self.state, tuple(self.left()), self.read(), tuple(self.right()))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--machine', required=True)
    ap.add_argument('--steps', type=int, default=0)
    ap.add_argument('--every', type=int, default=0)
    ap.add_argument('--trace', type=int, default=0)
    ap.add_argument('--start', default=None)
    ap.add_argument('--k', type=int, default=120)
    args = ap.parse_args()
    m = parse_machine(args.machine)
    t = Tape()
    if args.start:
        parts = args.start.split(',')
        t.state = parts[0]
        for i, ch in enumerate(parts[1]):
            if ch != '0':
                t.cells[-1 - i] = int(ch)
        t.p = 0
        t.write(int(parts[2]))
        for i, ch in enumerate(parts[3]):
            if ch != '0':
                t.cells[1 + i] = int(ch)
    n = 0
    if args.trace:
        print('step 0 state %s : %s' % (t.state, t.word(args.k)))
    while n < args.steps:
        if not t.step(m):
            print('halted after %d steps' % n)
            break
        n += 1
        if args.trace and n <= args.trace:
            print('step %d state %s : %s' % (n, t.state, t.word(args.k)))
        if args.every and n % args.every == 0:
            lo, hi = t.span()
            print('step %d state %s head@%d span[%d,%d] nb=%d : %s'
                  % (n, t.state, t.p, lo, hi, t.nonblank(), t.word(args.k)))
    print('steps: %d' % n)
    print('state: %s head sym %d' % (t.state, t.read()))
    print('nonblank: %d' % t.nonblank())
    print('word: %s' % t.word(args.k))


if __name__ == '__main__':
    main()
