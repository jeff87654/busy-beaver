#!/usr/bin/env python3
"""Cross-check of the BB(4,4) macro rules used by the Coq development.

The Coq development proves three things about the champion
0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA:

  * the 98-step start reaches B(2, 6, 0) 0^inf;
  * phase B:   B(2, 0, m) 0^inf      -->  B(1, 2m+2, 0) 0^inf;
  * phase D:   B(1, 0, m) 0^inf      -->  B(2m+2, 1, 0) 2 1 3 0^inf;

and then Ligocki's rule B_rule (proved in BB34_rules.v, unchanged) does the
rest.  This script simulates the machine directly and checks all of that for
small parameters, independently of Coq.
"""
import sys, os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from tm_lib import parse_machine

OURS = '0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA'
ALPHA = 'ABCDEFGHIJKLMNOPQRSTUVWXYZ'


class Tape:
    __slots__ = ('cells', 'p', 'state')

    def __init__(self):
        self.cells = {}
        self.p = 0
        self.state = 'A'

    def read(self):
        return self.cells.get(self.p, 0)

    def write(self, s):
        if s == 0:
            self.cells.pop(self.p, None)
        else:
            self.cells[self.p] = s

    def step(self, m):
        i = ALPHA.index(self.state)
        cur = self.read()
        t = m.table[(i, cur)]
        if t is None or t[2] is None:
            return False
        w, d, q = t
        self.write(w)
        self.p += 1 if d == 'R' else -1
        self.state = ALPHA[q]
        return True

    def set(self, p, v):
        if v == 0:
            self.cells.pop(p, None)
        else:
            self.cells[p] = v

    def left(self, n):
        return [self.cells.get(self.p - i, 0) for i in range(1, n + 1)]

    def right(self, n):
        return [self.cells.get(self.p + i, 0) for i in range(1, n + 1)]

    def run_of(self, v):
        """Number of consecutive v's immediately to the left of the head."""
        n = 0
        i = self.p - 1
        while self.cells.get(i, 0) == v:
            n += 1
            i -= 1
        return n


def build_B(k, n, m, tail):
    """The Ligocki configuration B(k,n,m) R = 0^inf 3^(2m+1) 2^k A> 1^n R.

    The head is on cell 0; the k 2s occupy the cells -1..-k, the 2m+1 3s the
    cells -(k+1)..-(k+2m+1); the n 1s the cells 1..n, then the tail R.
    """
    t = Tape()
    for i in range(1, k + 1):
        t.set(-i, 2)
    for i in range(k + 1, k + 2 * m + 2):
        t.set(-i, 3)
    for i in range(1, n + 1):
        t.set(i, 1)
    for i, v in enumerate(tail):
        t.set(n + 1 + i, v)
    t.p = 0
    t.state = 'A'
    return t


def rle(seq):
    out = []
    for x in seq:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return ' '.join('%d^%d' % (a, b) for a, b in out)


def describe(t):
    lo = min(list(t.cells) + [t.p])
    hi = max(list(t.cells) + [t.p])
    left = [t.cells.get(i, 0) for i in range(t.p - 1, lo - 1, -1)]
    right = [t.cells.get(i, 0) for i in range(t.p + 1, hi + 1)]
    return '%s L[%s] [%d] R[%s]' % (t.state, rle(left), t.read(), rle(right))


def search(t, m, pred, limit):
    """Run until pred(t) holds; return the number of steps, or None."""
    for n in range(limit + 1):
        if pred(t):
            return n
        if not t.step(m):
            return None
    return None


def check_start(m):
    t = Tape()

    def pred(t):
        return (t.state == 'A' and t.read() == 1
                and t.left(3) == [2, 2, 3] and t.right(5) == [1] * 5)

    n = search(t, m, pred, 500)
    ok = (n == 98)
    print('start: %s steps -> %s   %s'
          % (n, describe(t), 'OK' if ok else 'FAIL'))
    return ok


def check_phase_B(m, k):
    """B(2,0,k) 0^inf  -->  B(1, 2k+2, 0) 0^inf."""
    t = build_B(2, 0, k, [])

    def pred(t):
        return (t.state == 'A' and t.read() == 1
                and t.left(2) == [2, 3]
                and t.right(2 * k + 1) == [1] * (2 * k + 1)
                and t.right(2 * k + 2)[-1] == 0)

    n = search(t, m, pred, 10 * k + 10 + 5)
    ok = (n == 10 * k + 10)
    print('phase B (m=%d): %s steps -> %s   %s'
          % (k, n, describe(t), 'OK' if ok else 'FAIL'))
    return ok


def check_phase_D(m, k):
    """B(1,0,k) 0^inf  -->  B(2k+2, 1, 0) 2 1 3 0^inf."""
    t = build_B(1, 0, k, [])

    def pred(t):
        return (t.state == 'A' and t.read() == 1
                and t.run_of(2) == 2 * k + 2
                and t.right(3) == [2, 1, 3])

    n = search(t, m, pred, 20 * k + 35 + 5)
    ok = (n == 20 * k + 35)
    print('phase D (m=%d): %s steps -> %s   %s'
          % (k, n, describe(t), 'OK' if ok else 'FAIL'))
    return ok


def main():
    m = parse_machine(OURS)
    ok = True
    ok &= check_start(m)
    for k in (0, 1, 2, 3):
        ok &= check_phase_B(m, k)
    for k in (0, 1, 2):
        ok &= check_phase_D(m, k)
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
