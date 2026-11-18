#!/usr/bin/env python3
"""Find the first configuration of Ligocki's B-family after a phase.

A B-configuration looks like   0^inf 3^(2m+1) 2^k A> 1^n R
(the head is in state A).  We scan the run and report every B-configuration
that occurs, together with the step at which it occurs.
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


def classify(cfg):
    """Return (k, n, m, rest) if the configuration is 0^inf 3^(2m+1) 2^k A> 1^n R."""
    if cfg.state != "A":
        return None
    left = list(reversed(cfg.left))
    i = 0
    while i < len(left) and left[i] == 0:
        i += 1
    body = left[i:]
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
    # right stream: n ones then the rest
    r = list(cfg.right)
    n = 0
    while n < len(r) and r[n] == 1:
        n += 1
    if n > 0:
        if cfg.cur != 1:
            return None
    else:
        # head sits on the first symbol of the rest
        pass
    rest = r[n:]
    return (n2, n, (n3 - 1) // 2, rest[:6])


def main():
    m = parse_machine(OURS)
    for k, mm in ((2, 0), (3, 0), (4, 0), (2, 1), (3, 1), (4, 1), (5, 2)):
        cfg = Bcfg(k, 0, mm, [4] + [0] * 80, "A")
        seen = []
        limit = 300000
        for step in range(limit):
            if step > 0:
                got = classify(cfg)
                if got is not None:
                    seen.append((step, got[:3]))
                    if len(seen) >= 4:
                        break
            if not cfg.step(m):
                seen.append((step, "HALT"))
                break
        print("B(%d,0,%d) 4 ->" % (k, mm), seen[:4])


if __name__ == "__main__":
    main()
