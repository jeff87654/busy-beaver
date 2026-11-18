#!/usr/bin/env python3
"""Precise analyser for the BB(3,5) champion.

Prints the tape with the head marked (^s) and recognises the clean
configurations of the form

    0^inf 3^(2m+1) 2^k  A>  1^n  s  R

which are the macro-states of the analysis.

Usage:  analyze.py <two|four> <k> <m> <from> <to>
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from tm_lib import parse_machine

OURS = "1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC"
STATES = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


class TM:
    def __init__(self, spec):
        self.m = parse_machine(spec)
        self.tape = {}
        self.pos = 0
        self.state = "A"

    def get(self, p):
        return self.tape.get(p, 0)

    def put(self, p, s):
        if s:
            self.tape[p] = s
        else:
            self.tape.pop(p, None)

    def step(self):
        i = STATES.index(self.state)
        t = self.m.table[(i, self.get(self.pos))]
        if t is None or t[2] is None:
            return False
        w, d, q = t
        self.put(self.pos, w)
        self.pos += 1 if d == "R" else -1
        self.state = STATES[q]
        return True

    def word(self):
        if not self.tape:
            return "(blank)"
        lo, hi = min(self.tape), max(self.tape)
        out = []
        for p in range(lo, hi + 1):
            out.append("^%d" % self.get(p) if p == self.pos else str(self.get(p)))
        return " ".join(out)


def classify(t):
    """(k, n, m, s, r) for  0^inf 3^(2m+1) 2^k A> 1^n s R, else None.

    Only the part of R up to the first non-1/non-4 symbol is reported.
    """
    if t.state != "A":
        return None
    lo = min(t.tape) if t.tape else t.pos
    left = []
    p = t.pos - 1
    while p >= lo and t.get(p) != 0:
        left.append(t.get(p))
        p -= 1
    left.reverse()
    i = 0
    while i < len(left) and left[i] == 3:
        i += 1
    a = i
    while i < len(left) and left[i] == 2:
        i += 1
    k = i - a
    if i != len(left) or a == 0 or a % 2 == 0:
        return None
    n = 0
    p = t.pos + 1
    while t.get(p) == 1:
        n += 1
        p += 1
    r = []
    while t.get(p) in (1, 2, 3, 4):
        r.append(t.get(p))
        p += 1
    return (k, n, (a - 1) // 2, t.get(t.pos), "".join(str(x) for x in r))


def build(k, m, s):
    t = TM(OURS)
    p = 0
    for _ in range(2 * m + 1):
        t.tape[p] = 3
        p += 1
    for _ in range(k):
        t.tape[p] = 2
        p += 1
    t.pos = p
    t.tape[p] = s
    return t


def main():
    mode = sys.argv[1]
    k = int(sys.argv[2])
    m = int(sys.argv[3])
    lo = int(sys.argv[4])
    hi = int(sys.argv[5])
    s = 2 if mode == "two" else 4
    t = build(k, m, s)
    for step in range(hi + 1):
        c = classify(t)
        if lo <= step <= hi:
            tag = ""
            if c is not None:
                tag = "   B(k=%d,n=%d,m=%d) s=%d R=%s" % (c[0], c[1], c[2], c[3], c[4])
            print("%6d %s  %s%s" % (step, t.state, t.word(), tag))
        if not t.step():
            print("%6d %s  %s   HALT" % (hi + 1, t.state, t.word()))
            return


if __name__ == "__main__":
    main()
