#!/usr/bin/env python3
"""Symbolic macro model of the BB(5,4) run.

The macro model is validated against the step-level simulator (tools/
extract.py): the macro state (k, n, m, tail) is exactly the Ligocki
configuration

    B(k, n, m) r  =  0^inf 3^(2m+1) 2^k  A> 1^n r

in busycoq's convention (the head sits on the first of the n ones, the right
context is 1^(n-1) :: r).

The macro cycle is

    descent   B(k,n,m,r) -->* B(k-1, 2m+2, 0) (3 1^(n-1) r)
    b1        B(1,n,m,r) -->* B(1, 0, m+n) r
    a3        B(k,0,m,r) -->* B(k+a, b, m) r'      (a = leading 3's,
                                                      b = the following run
                                                      of ones)

and the D/E phase (BB(5,4)-specific) is

    B(k, 0, m) [] -->* B(2m+1, 1, 0) (3 1)^(k/2)      for even k,
    B(k, 0, m) [] -->* halt                          for odd k.

The numbers explode, so they are kept symbolically: a number is either an
exact integer or an expression built from 2^e + c.
"""

import sys
from collections import deque


# ------------------------------------------------------------------ numbers
class Num(object):
    """A natural number, possibly symbolic.

    kind 'n' : an exact integer, value v
    kind 'p' : 2^e + c
    kind 's' : a sum of several Nums
    kind 'm' : a product of two Nums
    """

    __slots__ = ("kind", "e", "c", "v", "t")

    def __init__(self, kind, e=None, c=None, v=None, t=None):
        self.kind = kind
        self.e = e
        self.c = c
        self.v = v
        self.t = t

    # -- constructors
    @staticmethod
    def num(v):
        return Num("n", v=v)

    @staticmethod
    def pow(e, c=0):
        """2^e + c"""
        if e.kind == "n" and e.v < 4096:
            return Num.num((1 << e.v) + c)
        return Num("p", e=e, c=c)

    # -- tests
    def is_exact(self):
        return self.kind == "n"

    def is_zero(self):
        return self.kind == "n" and self.v == 0

    def is_pos(self):
        """definitely > 0"""
        if self.kind == "n":
            return self.v > 0
        if self.kind == "p":
            if self.e.kind == "n":
                if self.e.v < 4096:
                    return (1 << self.e.v) + self.c > 0
                return self.e.v >= 1
            return True
        return True

    def is_gt1(self):
        """definitely > 1"""
        if self.kind == "n":
            return self.v > 1
        if self.kind == "p":
            if self.e.kind == "n":
                if self.e.v < 4096:
                    return (1 << self.e.v) + self.c > 1
                return self.e.v >= 2
            return True
        return True

    # -- arithmetic
    def add(self, o):
        if o.kind == "n" and o.v == 0:
            return self
        if self.kind == "n" and self.v == 0:
            return o
        if self.kind == "n" and o.kind == "n":
            return Num.num(self.v + o.v)
        if self.kind == "p" and o.kind == "n":
            return Num("p", e=self.e, c=self.c + o.v)
        if self.kind == "p" and o.kind == "p" and self.e == o.e:
            return Num("p", e=self.e, c=self.c + o.c)
        return Num("s", t=[self, o])

    def sub(self, d):
        """self - d, d a plain int."""
        if self.kind == "n":
            return Num.num(self.v - d)
        if self.kind == "p":
            return Num("p", e=self.e, c=self.c - d)
        terms = list(self.t)
        terms[0] = terms[0].sub(d)
        return Num("s", t=terms)

    def mul(self, k):
        """self * k, k an int or a Num."""
        if isinstance(k, int):
            if self.kind == "n":
                return Num.num(self.v * k)
            if k == 1:
                return self
            if k == 0:
                return Num.num(0)
            if k > 0 and (k & (k - 1)) == 0:
                sh = k.bit_length() - 1
                if self.kind == "p":
                    return Num("p", e=self.e.add(Num.num(sh)), c=self.c * k)
                return Num("m", e=self, c=Num.num(k))
            if self.kind == "p":
                return Num("m", e=Num.num(k), c=self)
            return Num("m", e=self, c=Num.num(k))
        # k is a Num
        if k.kind == "n":
            return self.mul(k.v)
        return Num("m", e=self, c=k)

    # -- printing
    def __str__(self):
        return self._str(0)

    def _str(self, depth):
        if depth > 12:
            return "..."
        if self.kind == "n":
            return str(self.v)
        if self.kind == "p":
            if self.c:
                return "2^%s%+d" % (self.e._str(depth + 1), self.c)
            return "2^%s" % (self.e._str(depth + 1))
        if self.kind == "s":
            return "(" + "+".join(x._str(depth + 1) for x in self.t) + ")"
        return "(%s*%s)" % (self.e._str(depth + 1), self.c._str(depth + 1))

    def short(self, lim=46):
        t = str(self)
        return t if len(t) <= lim else t[:lim] + "..."

    def __eq__(self, o):
        if self.kind == "n" and o.kind == "n":
            return self.v == o.v
        if self.kind == "p" and o.kind == "p":
            return self.e == o.e and self.c == o.c
        return self is o

    def __hash__(self):
        return id(self)


N0 = Num.num(0)
N1 = Num.num(1)
N2 = Num.num(2)
N3 = Num.num(3)


def nmul2plus2(m):
    return m.mul(2).add(N2)


# --------------------------------------------------------------------- tail
def tl_push_front(tl, sym, cnt):
    if cnt.is_zero():
        return tl
    if tl and tl[0][0] == sym:
        tl[0][1] = tl[0][1].add(cnt)
    else:
        tl.appendleft([sym, cnt])
    return tl


def tl_str(tl):
    out = []
    for s, c in tl:
        cs = c.short()
        out.append("%d^%s" % (s, cs) if not (c.is_exact() and c.v == 1) else "%d" % s)
    return " ".join(out)


# -------------------------------------------------------------------- model
def descent(k, n, m, tl):
    """B(k,n,m,r) -->* B(k-1, 2m+2, 0) (3 1^(n-1) r)   (one level down)."""
    tl = tl_push_front(tl, 1, n.sub(1))
    tl = tl_push_front(tl, 3, N1)
    return k - 1, nmul2plus2(m), N0, tl


def b1_steps(k, n, m, tl):
    """B(1,n,m,r) -->* B(1,0,m+n) r."""
    return k, N0, m.add(n), tl


def a3_phase(k, n, m, tl):
    """Consume the leading 3's (they join the 2-block), then read the 1-run.

    Returns (k', b, m, tl'); b = None means the head reached a blank, i.e.
    the D/E phase starts."""
    a = N0
    while tl and tl[0][0] == 3:
        a = a.add(tl[0][1])
        tl.popleft()
    assert a.is_exact(), "the leading run of threes must be short"
    k = k + a.v
    if not tl:
        return k, None, m, tl
    b = N0
    if tl[0][0] == 1:
        b = tl[0][1]
        tl.popleft()
    return k, b, m, tl


def d_phase(k, m):
    """The D/E phase.

    k even: B(k,0,m) [] -->* B(2m+1,1,0) (3 1)^(k/2)
    k odd : the machine halts (E3 = 1RZ)."""
    if k % 2 == 1:
        return ("HALT", None, None, None, None)
    tl = deque()
    for _ in range(k // 2):
        tl.append([3, N1])
        tl.append([1, N1])
    nk = m.mul(2).add(N1)
    assert nk.is_exact()
    return ("CONT", nk.v, N1, N0, tl)


def cycle(state):
    """One macro cycle."""
    k, n, m, tl = state
    while k >= 2 and n.is_pos():
        k, n, m, tl = descent(k, n, m, tl)
    if k == 1 and n.is_pos():
        k, n, m, tl = b1_steps(k, n, m, tl)
    k, b, m, tl = a3_phase(k, n, m, tl)
    if b is None:
        return ("PHASE", (k, n, m, tl))
    return ("OK", (k, b, m, tl))


def chain_jump(state):
    """Fast-forward the long chain  B(2,N,M,r) -> B(2,N-1,2M+2,r) -> ...

    The macro cycle maps (2,N,M,r) to (2,N-1,2M+2,r) as long as the tail does
    not start with a one.  The chain therefore ends in
    B(2, 1, 2^(N-1)(M+2)-2, r) after N-1 cycles."""
    k, n, m, tl = state
    if k != 2 or not n.is_gt1():
        return None, None
    if tl and tl[0][0] == 1:
        return None, None
    e = n.sub(1)                       # N-1
    mm = m.add(N2)                     # M+2
    if mm.is_exact() and mm.v > 0 and (mm.v & (mm.v - 1)) == 0:
        mp = Num.pow(e.add(Num.num(mm.v.bit_length() - 1)), 0).sub(2)
    else:
        mp = Num.pow(e, 0).mul(mm).sub(2)
    return (2, N1, mp, tl), n.sub(1)


def super_cycle(state):
    """One super-cycle of the main regime, done atomically.

    For the state  B(2, N, M) [3 1^j] S   (j >= 1, N > 1) the macro run
    goes through the long chain (N-1 cycles), then two more cycles, and
    ends in

        B(2, 2^(N+3)-3, 2) [3 1^(j-1)] S .

    The counter j therefore decreases by one per super-cycle, while N
    grows like 2^(N+3).  Returns (state, None) when the pattern does not
    match."""
    k, n, m, tl = state
    if k != 2 or not m.is_exact() or m.v != 2:
        return None, None
    if len(tl) < 2:
        return None, None
    if not (tl[0][0] == 3 and tl[0][1].is_exact() and tl[0][1].v == 1):
        return None, None
    if not (tl[1][0] == 1 and tl[1][1].is_exact()):
        return None, None
    j = tl[1][1].v
    if j < 1 or not n.is_gt1():
        return None, None
    # N' = 2^(N+3) - 3
    if n.kind == "p":
        e, c = n.e, n.c + 3
    elif n.kind == "n" and n.v < 4096:
        e, c = Num.num(n.v + 3), 0
    else:
        return None, None
    np_ = Num("p", e=Num("p", e=e, c=c), c=-3)
    ntl = deque([[3, N1], [1, Num.num(j - 1)]])
    for r in list(tl)[2:]:
        ntl.append(r)
    return (2, np_, N2, ntl), Num.num(1)


def show(state):
    k, n, m, tl = state
    return "B(k=%s n=%s m=%s) tail[%s]" % (k, n.short(), m.short(), tl_str(tl))


def main():
    maxit = int(sys.argv[1]) if len(sys.argv) > 1 else 1000000
    k, n, m, tl = 2, N1, N0, deque()
    print("start  %s" % show((k, n, m, tl)), flush=True)
    i = 0
    while i < maxit:
        st, skipped = super_cycle((k, n, m, tl))
        if st is not None:
            k, n, m, tl = st
            i += 1
            print("%8d  SUPER-CYCLE %s" % (i, show((k, n, m, tl))), flush=True)
            continue
        st, skipped = chain_jump((k, n, m, tl))
        if st is not None:
            k, n, m, tl = st
            i += 1
            print("%8d  (chain jump)  %s" % (i, show((k, n, m, tl))), flush=True)
            continue
        kind, r = cycle((k, n, m, tl))
        i += 1
        if kind == "PHASE":
            k, n, m, tl = r
            st, nk, nn, nm, ntl = d_phase(k, m)
            print("%8d  PHASE k=%d -> %s %s" % (i, k, st, show((nk, nn, nm, ntl))), flush=True)
            if st == "HALT":
                print("MACHINE HALTS with m = %s" % m.short())
                return
            k, n, m, tl = nk, nn, nm, ntl
            continue
        k, n, m, tl = r
        print("%8d  %s" % (i, show((k, n, m, tl))), flush=True)


if __name__ == '__main__':
    main()
