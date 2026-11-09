#!/usr/bin/env python3
"""Check the macro model against the step-level simulator.

For every step of the real run we extract the Ligocki parameters (k, n, m)
and the tail of the configuration, and compare them with the state the
macro model predicts.  The model must agree at every "cycle boundary"
(i.e. whenever the model state is one the model can be in).

The extraction works in the busycoq convention verified against Coq:

    Bcfg k n m r  =  (A, 2^k :: 3^(2m+1) :: 0^inf , head on the first of
                     n ones, right context 1^(n-1) :: r)

so, with the head at position 0:
    * the cells -1, -2, ... are the twos (k of them),
    * then the threes (2m+1 of them),
    * the head sits on a 1, with n-1 more ones to the right,
    * then the tail r.
"""

import os
import sys
from collections import deque

sys.path.insert(0, ".")
from sim import Machine

MACHINE = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "bb54.txt")).read().strip()


def extract(state, tape, head):
    """Return (k, n, m, tail) or None if the configuration is not a Bcfg."""
    if state != 0:            # must be state A
        return None
    sym = tape.get(head, 0)
    if sym == 0:
        return None
    if sym != 1:
        return None
    # left: twos then threes
    k = 0
    p = head - 1
    while tape.get(p, 0) == 2:
        k += 1
        p -= 1
    threes = 0
    while tape.get(p, 0) == 3:
        threes += 1
        p -= 1
    if tape.get(p, 0) != 0:
        return None
    if threes == 0 or (threes - 1) % 2 != 0:
        return None
    m = (threes - 1) // 2
    # right: the run of ones starting at the head
    n = 0
    q = head
    while tape.get(q, 0) == 1:
        n += 1
        q += 1
    # the tail after the ones
    tail = []
    while True:
        s = tape.get(q, 0)
        if s == 0:
            break
        tail.append(s)
        q += 1
    return k, n, m, tail


def rl_of(lst):
    out = deque()
    for s in lst:
        if out and out[-1][0] == s:
            out[-1][1] += 1
        else:
            out.append([s, 1])
    return out


def rl_str(rl):
    return " ".join("%d^%d" % (s, c) if c > 1 else "%d" % s for s, c in rl)


def main():
    steps = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    verbose = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    m = Machine(MACHINE)
    tape = {}
    head = 0
    state = 0
    prev = None
    for i in range(steps):
        sym = tape.get(head, 0)
        r = m.step(state, sym)
        if r is None:
            print("step %d: HALT (state %s reads %d)" % (i + 1, chr(65 + state), sym))
            break
        nq, w, mv = r
        tape[head] = w
        head += 1 if mv == "R" else -1
        state = nq
        e = extract(state, tape, head)
        if e is None:
            continue
        k, n, mm, tail = e
        cur = (k, n, mm, rl_str(rl_of(tail)))
        if cur != prev:
            if verbose:
                print("step %4d  state %s  B(k=%d n=%s m=%s) tail[%s]" % (
                    i + 1, chr(65 + state), k,
                    n if n.bit_length() < 64 else "2^%d" % n.bit_length(),
                    mm if mm.bit_length() < 64 else "2^%d" % mm.bit_length(),
                    rl_str(rl_of(tail))[:60]))
            prev = cur


if __name__ == '__main__':
    main()
