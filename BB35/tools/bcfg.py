#!/usr/bin/env python3
"""Identify the BB(3,5) 'B(k,n,m)' configuration family along a run.

The family is  B(k,n,m) R = 0^inf 3^(2m+1) 2^k  A>  1^n  R
(left-to-right on the tape:  3^(2m+1)  2^k  [head]  1^n  R).

Whenever the head is in state A and the tape has this shape, the triple
(k,n,m) is printed, together with the symbol the head reads.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine

ALPHA = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'
OURS = '1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC'


def classify(cells, p, state):
    """Return (k, n, m, head_symbol) if the configuration is a B-config, else None."""
    if state != 'A':
        return None
    # left stream: cells p-1, p-2, ...  (nearest first); must be  2*k then 3*(2m+1) then blanks
    left = []
    i = p - 1
    while i > -10 ** 7 and cells.get(i, 0) != 0:
        left.append(cells[i])
        i -= 1
    k = 0
    while k < len(left) and left[k] == 2:
        k += 1
    rest = left[k:]
    # rest must be 3s (odd count) then blanks
    j = 0
    while j < len(rest) and rest[j] == 3:
        j += 1
    if j != len(rest) or j == 0 or j % 2 == 0:
        return None
    m = (j - 1) // 2
    # right stream: cells p+1, p+2, ...
    right = []
    i = p + 1
    while i <= p + 10000 and cells.get(i, 0) != 0:
        right.append(cells[i])
        i += 1
    head = cells.get(p, 0)
    # In Bcfg k n m r = ... {{A}}> ([1]^^n *> r) the head sits on the FIRST 1 of
    # the 1^n block, so n counts the 1s *including* the head cell.
    n = 0
    if head == 1:
        n = 1
        while n - 1 < len(right) and right[n - 1] == 1:
            n += 1
    if head not in (1, 4, 2):
        return None
    if head == 1 and n == 0:
        return None
    return (k, n, m, head)


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--machine', default=OURS)
    ap.add_argument('--m', type=int, default=1)
    ap.add_argument('--k', type=int, default=1)
    ap.add_argument('--steps', type=int, default=100000)
    ap.add_argument('--all', action='store_true')
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
        i = ALPHA.index(state)
        cur = cells.get(p, 0)
        t = m.table[(i, cur)]
        if t is None or t[2] is None:
            print('HALT after %d steps; state %s sym %d' % (n - 1, state, cur))
            lo = min(cells) if cells else 0
            print('   tape: %s' % ' '.join(
                '%d:%s^%d' % (s, v, c) for (s, v, c) in _runs(cells)))
            break
        w, d, q = t
        cells[p] = w
        p += 1 if d == 'R' else -1
        state = ALPHA[q]
        c = classify(cells, p, state)
        if c is not None and (args.all or True):
            print('step %8d  B(%d,%d,%d)  head reads %d' % (n, c[0], c[1], c[2], c[3]))
    else:
        print('no halt in %d steps' % args.steps)


def _runs(cells):
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


if __name__ == '__main__':
    main()
