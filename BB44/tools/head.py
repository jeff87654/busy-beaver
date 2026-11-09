#!/usr/bin/env python3
"""Print the tape with the head cell marked, e.g.  3333[3]331  (span of nonblank cells)."""
import argparse, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine
from sim import Tape


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--machine', required=True)
    ap.add_argument('--steps', type=int, default=0)
    ap.add_argument('--every', type=int, default=1)
    ap.add_argument('--filter', default=None)
    ap.add_argument('--pad', type=int, default=3)
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
            lo, hi = t.span()
            lo -= args.pad
            hi += args.pad
            s = []
            for i in range(lo, hi + 1):
                v = t.cells.get(i, 0)
                s.append('[%d]' % v if i == t.p else str(v))
            print('step %5d state %s head@%d  %s' % (n, t.state, t.p, ''.join(s)))
    print('steps: %d  state %s  nb %d' % (n, t.state, t.nonblank()))


if __name__ == '__main__':
    main()
