#!/usr/bin/env python3
"""Search OUR BB(4,4) machine's run for macro-configuration shapes."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import parse_machine

MACHINE = '0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA'


class Tape:
    def __init__(self):
        self.cells = {}
        self.p = 0
        self.state = 'A'

    def read(self):
        return self.cells.get(self.p, 0)

    def write(self, s):
        self.cells[self.p] = s

    def span(self):
        if not self.cells:
            return 0, 0
        return min(self.cells), max(self.cells)

    def step(self, m):
        cur = self.read()
        r = m.get((self.state, cur))
        if r is None:
            return False
        w, d, ns = r
        self.cells[self.p] = w
        self.p += 1 if d == 'R' else -1
        self.state = ns
        return True


def rl(seq):
    out = []
    for x in seq:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return ' '.join('%d^%d' % (a, b) for a, b in out)


def dump(t, lo=None, hi=None):
    if lo is None:
        lo, hi = t.span()
    lo = min(lo, t.p)
    hi = max(hi, t.p)
    left = [t.cells.get(i, 0) for i in range(t.p - 1, lo - 1, -1)]
    right = [t.cells.get(i, 0) for i in range(t.p + 1, hi + 1)]
    return '%s@%d L[%s] [%d] R[%s]' % (t.state, t.p, rl(left), t.read(), rl(right))


def main():
    m = parse_machine(MACHINE)
    t = Tape()
    n = 0
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 2000000
    while n < limit:
        lo, hi = t.span()
        left = [t.cells.get(i, 0) for i in range(t.p - 1, lo - 1, -1)]
        right = [t.cells.get(i, 0) for i in range(t.p + 1, hi + 1)]
        # Bcfg shape: left = 2^k then 3^(2m+1) then 0s; head in A on 1^n
        if t.state == 'A':
            k = 0
            while k < len(left) and left[k] == 2:
                k += 1
            j = k
            while j < len(left) and left[j] == 3:
                j += 1
            m3 = j - k
            okleft = True
            for x in left[j:]:
                if x != 0:
                    okleft = False
                    break
            if k >= 1 and m3 >= 1 and m3 % 2 == 1 and okleft:
                n1 = 0
                while n1 < len(right) and right[n1] == 1:
                    n1 += 1
                print('Bcfg  step=%d k=%d m=%d n=%d  tail=%s' %
                      (n, k, (m3 - 1) // 2, n1, rl(right[n1:n1 + 6])))
        if not t.step(m):
            print('HALT at step', n, dump(t))
            break
        n += 1


if __name__ == '__main__':
    main()
