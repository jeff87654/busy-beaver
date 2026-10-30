#!/usr/bin/env python3
"""Compact trace: run-length of the tape with the head cell marked.

  step  95  C@-7  span[-6..3]   3^3 [0] 1^7
"""
import argparse, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine
from sim import Tape


def rl(seq):
    out = []
    cur = None
    cnt = 0
    for v in seq:
        if v == cur:
            cnt += 1
        else:
            if cur is not None:
                out.append('%d^%d' % (cur, cnt))
            cur, cnt = v, 1
    if cur is not None:
        out.append('%d^%d' % (cur, cnt))
    return ' '.join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--machine', required=True)
    ap.add_argument('--steps', type=int, default=0)
    ap.add_argument('--every', type=int, default=1)
    ap.add_argument('--filter', default=None)
    ap.add_argument('--start', default=None)
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
    while n < args.steps:
        if not t.step(m):
            print('HALTED after %d steps' % n)
            break
        n += 1
        if n % args.every == 0 and (args.filter is None or t.state == args.filter):
            lo, hi = t.span()
            left = [t.cells.get(i, 0) for i in range(t.p - 1, lo - 1, -1)]
            right = [t.cells.get(i, 0) for i in range(t.p + 1, hi + 1)]
            print('step %6d %s@%-5d span[%d..%d]  %s [%d] %s'
                  % (n, t.state, t.p, lo, hi, rl(left), t.read(), rl(right)))
    print('steps: %d  state %s  nb %d' % (n, t.state, t.nonblank()))


if __name__ == '__main__':
    main()
