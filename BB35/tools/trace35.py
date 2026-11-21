#!/usr/bin/env python3
"""Trace the BB(3,5) champion on the configurations that appear in the proof.

Usage:  python trace35.py [k] [m]

Prints step-by-step traces so that the Coq statements can be checked against
the real dynamics.  The tape is printed left-to-right with the head cell in
brackets.
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from tm_lib import parse_machine, Config

OURS = "1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC"


def show(cfg, width=16):
    l = list(reversed(cfg.left[:width]))
    r = cfg.right[:width]
    s = "".join(str(x) for x in l) + "[" + str(cfg.cur) + "]" + "".join(str(x) for x in r)
    return "%s %s" % (cfg.state, s)


def trace(m, cfg, n, label):
    print("=== %s ===" % label)
    for k in range(n):
        print("  %3d  %s" % (k, show(cfg)))
        if not cfg.step(m):
            print("  HALT")
            return
    print("  %3d  %s" % (n, show(cfg)))


def cfg_C_final(A, rlen=0):
    """([2]^^(S A) *> const 0) <{{C}} (4 >> r):  head C on the rightmost 2."""
    return Config([2] * A + [0] * 8, 2, [4] + [0] * rlen, "C")


def cfg_rule1(k, mlen):
    """Bcfg k 0 m (2 >> r): head A on the 2 that follows the 2-block."""
    return Config([2] * k + [3] * (2 * mlen + 1) + [0] * 8, 2, [2] + [0] * 6, "A")


def cfg_B(k, n, m, rlen=0, state="A", head=None):
    """Bcfg k n m r."""
    right = [1] * n + [0] * rlen
    if head is None:
        head = 0
    return Config([2] * k + [3] * (2 * m + 1) + [0] * 8, head, right, state)


def main():
    m = parse_machine(OURS)
    for A in (1, 2, 3):
        trace(m, cfg_C_final(A), 26, "C_final with A=%d" % A)

    for k, mlen in ((1, 0), (2, 0), (3, 1)):
        trace(m, cfg_rule1(k, mlen), 30, "rule1 k=%d m=%d" % (k, mlen))


if __name__ == "__main__":
    main()
