#!/usr/bin/env python3
"""Locate the macro (Bcfg-shaped) configurations of the BB(4,4) startup phase.

A config is 'Bcfg-shaped' when its LEFT stream, read from the head outwards, is
    [2]^k *> [3]^j        (j >= 1, odd)
i.e. the tape to the left of the head is  0^inf 3^j 2^k  <head>.
We report (step, k, j, state, head symbol, right stream) for every such config.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine
from mach import Tape, OURS


def rle(seq):
    out = []
    for x in seq:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return ' '.join('%d^%d' % (a, b) for a, b in out)


def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 360000
    m = parse_machine(OURS)
    t = Tape()
    for n in range(limit + 1):
        if t.state == 'A' and t.read() in (0, 1):
            # walk left from the head: twos then threes
            k = 0
            i = t.p - 1
            while t.cells.get(i, 0) == 2:
                k += 1
                i -= 1
            if k > 0:
                j = 0
                while t.cells.get(i, 0) == 3:
                    j += 1
                    i -= 1
                if j >= 1 and j % 2 == 1:
                    lo, hi = t.span()
                    right = [t.cells.get(x, 0) for x in range(t.p + 1, hi + 1)]
                    print('step %-8d k=%-4d j=%-4d m=%-4d state=%s sym=%d  R[%s]'
                          % (n, k, j, (j - 1) // 2, t.state, t.read(), rle(right)))
        if not t.step(m):
            print('HALT at step', n)
            break


if __name__ == '__main__':
    main()
