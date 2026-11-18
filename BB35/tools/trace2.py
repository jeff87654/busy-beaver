#!/usr/bin/env python3
"""Trace helper: prints the tape as explicit cell positions."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine

ALPHA = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
OURS = '1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC'


def runs(cells):
    """[(start_pos, symbol, count), ...] sorted by position, zeros omitted."""
    out = []
    for p in sorted(cells):
        v = cells[p]
        if v == 0:
            continue
        if out and out[-1][1] == v and out[-1][0] + out[-1][2] == p:
            out[-1][2] += 1
        else:
            out.append([p, v, 1])
    return out


def fmt(cells, p):
    s = []
    for (start, v, n) in runs(cells):
        s.append('%d:%s^%d' % (start, v, n))
    return ' '.join(s)


def step(m, cells, p, state):
    i = ALPHA.index(state)
    cur = cells.get(p, 0)
    t = m.table[(i, cur)]
    if t is None or t[2] is None:
        return None
    w, d, q = t
    cells[p] = w
    p += 1 if d == 'R' else -1
    return p, ALPHA[q]


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--machine', default=OURS)
    ap.add_argument('--m', type=int, default=3, help='length of the 3-block')
    ap.add_argument('--k', type=int, default=16, help='length of the 2-block')
    ap.add_argument('--steps', type=int, default=300)
    ap.add_argument('--from', dest='frm', type=int, default=1)
    ap.add_argument('--to', dest='to', type=int, default=100000)
    args = ap.parse_args()
    m = parse_machine(args.machine)
    cells = {}
    for i in range(args.k):
        cells[-1 - i] = 2
    for i in range(args.m):
        cells[-1 - args.k - i] = 3
    p = 0
    cells[0] = 2
    state = 'A'
    for n in range(1, args.steps + 1):
        r = step(m, cells, p, state)
        if r is None:
            print('HALT after %d steps: state %s sym %d' % (n - 1, state, cells.get(p, 0)))
            break
        p, state = r
        if args.frm <= n <= args.to:
            print('step %4d  head@%d state %s   %s' % (n, p, state, fmt(cells, p)))


if __name__ == '__main__':
    main()
