#!/usr/bin/env python3
"""Compact (run-length) traces of the BB(3,5) champion.

Prints the tape in run-length form, e.g.  0^26 3 2 2 [1] 4 0^30
so that the structure of the machine's configurations can be read off
reliably.
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


def tape_rle(cfg, pad=30):
    """Tape as run-length, with the head cell in brackets."""
    left = list(reversed(cfg.left))
    # trim leading/trailing blanks of the left part
    n = len(left)
    while n > 0 and left[n - 1] == 0:
        n -= 1
    left = left[:n]
    right = list(cfg.right)
    n = len(right)
    while n > 0 and right[n - 1] == 0:
        n -= 1
    right = right[:n]
    parts = []
    if left:
        parts.append(rle(left))
    parts.append("[%d]" % cfg.cur)
    if right:
        parts.append(rle(right))
    return " ".join(parts)


def Bcfg(k, n, m, right=None, state="A"):
    """Ligocki's B(k,n,m) R  =  0^inf 3^(2m+1) 2^k A> 1^n R."""
    if right is None:
        right = [0] * 60
    left = [2] * k + [3] * (2 * m + 1) + [0] * 60
    if n > 0:
        cur = 1
        r = [1] * (n - 1) + right
    else:
        cur = right[0] if right else 0
        r = right[1:]
    return Config(left, cur, r, state)


def run(m, cfg, n, every=1, label=""):
    if label:
        print("=== %s ===" % label)
    for k in range(n):
        if k % every == 0:
            print("  %5d  %-2s %s" % (k, cfg.state, tape_rle(cfg)))
        if not cfg.step(m):
            print("  %5d  %-2s %s   <-- HALT" % (k, cfg.state, tape_rle(cfg)))
            return k
    print("  %5d  %-2s %s" % (n, cfg.state, tape_rle(cfg)))
    return n


def main():
    m = parse_machine(OURS)
    for k, mm in ((1, 0), (2, 0), (3, 0)):
        cfg = Bcfg(k, 0, mm, [4] + [0] * 60, "A")
        run(m, cfg, 40, 1, "B(%d,0,%d) 4" % (k, mm))
    for k, mm in ((1, 1), (2, 1)):
        cfg = Bcfg(k, 0, mm, [4] + [0] * 60, "A")
        run(m, cfg, 40, 1, "B(%d,0,%d) 4" % (k, mm))


if __name__ == "__main__":
    main()
