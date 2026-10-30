#!/usr/bin/env python3
"""Run-length view of the tape, relative to the head.

Prints:  step  N  state S  head=H  | L: runs(nearest-first)  | head=sym | R: runs |
"""
import argparse, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine
from sim import Tape


def runs(seq):
    out = []
    cur = None
    cnt = 0
    for v in seq:
        if v == cur:
            cnt += 1
        else:
            if cur is not None:
                out.append((cur, cnt))
            cur, cnt = v, 1
    if cur is not None:
        out.append((cur, cnt))
    return ' '.join('%d^%d' % (s, c) for s, c in out)


def fmt(t):
    return '| L: %-28s | head=%d | R: %-28s |' % (runs(t.left()), t.read(), runs(t.right()))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--machine', required=True)
    ap.add_argument('--steps', type=int, default=0)
    ap.add_argument('--every', type=int, default=1)
    ap.add_argument('--filter', default=None)
    args = ap.parse_args()
    m = parse_machine(args.machine)
    t = Tape()
    n = 0
    while n < args.steps:
        if not t.step(m):
            print('HALTED after %d steps' % n)
            break
        n += 1
        if n % args.every == 0 and (args.filter is None or t.state == args.filter):
            print('step %5d state %s head@%d %s' % (n, t.state, t.p, fmt(t)))
    print('steps: %d  state %s  nb %d' % (n, t.state, t.nonblank()))


if __name__ == '__main__':
    main()
