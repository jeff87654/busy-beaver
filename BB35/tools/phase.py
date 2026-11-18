#!/usr/bin/env python3
"""Precise step-by-step traces of the BB(3,5) champion after the Ligocki descent.

The descent of BB34 reaches the configuration

    0^inf 3^(2m+1) 2^k  A>  2  0^inf        (state A, head on a 2)

In the BB(3,5) champion the transition A2 = 4LC does not halt; it writes a 4,
moves left into state C and the machine keeps running.  This script traces
what happens, in a compact run-length notation.
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from tm_lib import parse_machine, Config

OURS = "1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC"


def rle(cells):
    out = []
    i = 0
    while i < len(cells):
        j = i
        while j < len(cells) and cells[j] == cells[i]:
            j += 1
        n = j - i
        out.append(str(cells[i]) if n == 1 else "%d^%d" % (cells[i], n))
        i = j
    return " ".join(out)


def show(cfg):
    left = list(reversed(cfg.left))          # far -> near
    n = 0
    while n < len(left) and left[n] == 0:     # drop far blanks
        n += 1
    left = left[n:]
    right = list(cfg.right)                   # near -> far
    n = len(right)
    while n > 0 and right[n - 1] == 0:        # drop far blanks
        n -= 1
    right = right[:n]
    l = rle(left) if left else ""
    r = rle(right) if right else ""
    return "%-46s [%s] %s" % (l, cfg.cur, r)


def descent_cfg(k, m, pad=40):
    """0^inf 3^(2m+1) 2^k A> 2 0^inf  (state A on the 2 right of the 2-block)."""
    left = [2] * k + [3] * (2 * m + 1) + [0] * pad
    return Config(left, 2, [0] * pad, "A")


def main():
    m = parse_machine(OURS)
    k = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    mm = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    cfg = descent_cfg(k, mm)
    print("=== descent-final: 0^inf 3^%d 2^%d A> 2 0^inf ===" % (2 * mm + 1, k))
    for i in range(steps):
        print("  %4d %s %s" % (i, cfg.state, show(cfg)))
        if not cfg.step(m):
            print("  %4d %s %s   <== HALT" % (i + 1, cfg.state, show(cfg)))
            return
    print("  %4d %s %s" % (steps, cfg.state, show(cfg)))


if __name__ == "__main__":
    main()
