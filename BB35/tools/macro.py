#!/usr/bin/env python3
"""Find the macro-transitions of the BB(3,5) champion after rule 1.

Starting from B(k,0,m) 4 (the head in state A on a 4), the machine runs a
long phase; we look for the next configuration of the same shape
B(k',0,m') 4, and report the number of steps in between.
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from tm_lib import parse_machine, Config

OURS = "1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC"


def Bcfg(k, n, m, right=None, state="A"):
    if right is None:
        right = [0] * 80
    left = [2] * k + [3] * (2 * m + 1) + [0] * 80
    if n > 0:
        cur = 1
        r = [1] * (n - 1) + right
    else:
        cur = right[0] if right else 0
        r = right[1:]
    return Config(left, cur, r, state)


def is_B_shape(cfg):
    """Is the configuration 0^inf 3^(2m+1) 2^k A> 4 0^inf ?"""
    if cfg.state != "A" or cfg.cur != 4:
        return None
    # right stream must be all blanks
    if any(x != 0 for x in cfg.right[:4]):
        return None
    left = list(reversed(cfg.left))
    i = 0
    while i < len(left) and left[i] == 0:
        i += 1
    body = left[i:]
    # body must be 3^(2m+1) 2^k
    j = 0
    while j < len(body) and body[j] == 3:
        j += 1
    n3 = j
    while j < len(body) and body[j] == 2:
        j += 1
    n2 = j - n3
    if j != len(body):
        return None
    if n3 == 0 or n3 % 2 == 0:
        return None
    return (n2, (n3 - 1) // 2)


def macro(m, k, mm, limit=200000, verbose=False):
    cfg = Bcfg(k, 0, mm, [4] + [0] * 80, "A")
    for step in range(limit):
        if step > 0:
            got = is_B_shape(cfg)
            if got is not None:
                return step, got
        if not cfg.step(m):
            return step, ("HALT", cfg.cur)
    return None, None


def main():
    m = parse_machine(OURS)
    print("%-12s %-14s %-10s" % ("from", "steps", "to"))
    for k, mm in ((2, 0), (3, 0), (4, 0), (5, 0), (2, 1), (3, 1), (6, 0), (7, 0)):
        steps, got = macro(m, k, mm)
        print("B(%d,0,%-2d) -> %-14s steps=%s" % (k, mm, got, steps))


if __name__ == "__main__":
    main()
