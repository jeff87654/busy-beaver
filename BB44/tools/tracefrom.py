#!/usr/bin/env python3
"""Trace a machine starting from the configuration reached after N steps."""
import argparse, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine
from sim import Tape
from trace import rl


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--machine', required=True)
    ap.add_argument('--fromstep', type=int, required=True)
    ap.add_argument('--steps', type=int, default=100)
    ap.add_argument('--every', type=int, default=1)
    args = ap.parse_args()
    m = parse_machine(args.machine)
    t = Tape()
    n = 0
    while n < args.fromstep:
        if not t.step(m):
            print('HALTED after %d steps' % n); return
        n += 1
    print('--- start at step %d ---' % n)
    for k in range(args.steps):
        lo, hi = t.span()
        left = [t.cells.get(i, 0) for i in range(t.p - 1, lo - 1, -1)]
        right = [t.cells.get(i, 0) for i in range(t.p + 1, hi + 1)]
        s = rl(left) + ' [' + str(t.read()) + '] ' + rl(right)
        print('%8d %s@%-5d %s' % (n + k, t.state, t.p, s))
        if not t.step(m):
            print('HALTED after %d steps' % (n + k + 1)); return
    print('steps: %d' % (n + args.steps))


if __name__ == '__main__':
    main()
