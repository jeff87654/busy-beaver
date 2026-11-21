#!/usr/bin/env python3
"""Explore the BB(3,5) champion's dynamics after Ligocki's descent.

The champion is 1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC.

This script explores the configurations that appear after the descent
(the "B(k,n,m)" family of Ligocki), in particular the phase that follows
rule 1 (B(k,0,m) 2 -->* B(k+2m+1,0,0) 4).
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from tm_lib import parse_machine, Config

OURS = "1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC"


def Bcfg(k, n, m, right=None, state="A"):
    """Ligocki's B(k,n,m) R  =  0^inf 3^(2m+1) 2^k A> 1^n R.

    The head sits on the first 1 of the right block (or on the first cell
    of R when n = 0)."""
    if right is None:
        right = [0] * 40
    left = [2] * k + [3] * (2 * m + 1) + [0] * 40
    ones = [1] * n
    if n > 0:
        cur = 1
        r = ones[1:] + right
    else:
        cur = right[0] if right else 0
        r = right[1:]
    return Config(left, cur, r, state)


def show(cfg, width=26):
    l = list(reversed(cfg.left[:width]))
    r = cfg.right[:width]
    s = "".join(str(x) for x in l) + "[" + str(cfg.cur) + "]" + "".join(str(x) for x in r)
    return "%s %s" % (cfg.state, s)


def run(m, cfg, n, every=1, label=""):
    if label:
        print("=== %s ===" % label)
    for k in range(n):
        if k % every == 0:
            print("  %5d  %s" % (k, show(cfg)))
        if not cfg.step(m):
            print("  HALT at step %d" % k)
            return k
    print("  %5d  %s" % (n, show(cfg)))
    return n


def main():
    m = parse_machine(OURS)
    # after the descent the machine is in B(16,0,g15) with the head on a 2;
    # rule 1 turns that into B(16+2g15+1, 0, 0) with the head on a 4.
    for k, mm in ((1, 0), (2, 0), (3, 0), (4, 0), (5, 1)):
        cfg = Bcfg(k, 0, mm, [4] + [0] * 40, "A")
        run(m, cfg, 30, 1, "B(%d,0,%d) 4" % (k, mm))


if __name__ == "__main__":
    main()
