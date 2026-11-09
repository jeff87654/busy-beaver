#!/usr/bin/env python3
"""Landmarks inside a step range: every config in state A or B, with a compact
shape of the left stream, the head symbol, and the right stream.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine
from trace2 import Tape, rle, describe

OURS = '0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA'


def main():
    lo_s = int(sys.argv[1])
    hi_s = int(sys.argv[2])
    states = sys.argv[3] if len(sys.argv) > 3 else 'AB'
    m = parse_machine(OURS)
    t = Tape()
    prev = None
    for n in range(hi_s + 1):
        if n >= lo_s and t.state in states:
            d = describe(t)
            if d != prev:
                print('%8d %s' % (n, d))
                prev = d
        if not t.step(m):
            print('HALT at', n)
            break


if __name__ == '__main__':
    main()
