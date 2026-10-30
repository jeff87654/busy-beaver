#!/usr/bin/env python3
"""Collect the 'canonical' configurations of a machine: state X with the head on a blank."""
import argparse, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine
from sim import Tape
from trace import rl


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--machine', required=True)
    ap.add_argument('--steps', type=int, default=0)
    ap.add_argument('--state', default='C')
    ap.add_argument('--sym', type=int, default=0)
    ap.add_argument('--every', type=int, default=1)
    args = ap.parse_args()
    m = parse_machine(args.machine)
    t = Tape()
    n = 0
    while n < args.steps:
        if not t.step(m):
            print('HALTED after %d steps' % n)
            break
        n += 1
        if t.state == args.state and t.read() == args.sym:
            lo, hi = t.span()
            left = [t.cells.get(i, 0) for i in range(t.p - 1, lo - 1, -1)]
            right = [t.cells.get(i, 0) for i in range(t.p + 1, hi + 1)]
            print('step %6d %s@%-6d span[%d..%d]  %s [%d] %s'
                  % (n, t.state, t.p, lo, hi, rl(left), t.read(), rl(right)))
    print('steps: %d' % n)


if __name__ == '__main__':
    main()
