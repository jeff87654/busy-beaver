#!/usr/bin/env python3
"""Simulate a Turing machine given by a TNF machine string.

Used to cross-check a Coq proof: the simulator is an independent
implementation of the same transition table, so agreement on the run and on
the final tape is evidence that the Coq side encodes the right machine.

Usage
-----
    python tm_sim.py --machine 1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC --steps 241
    python tm_sim.py --machine ... --steps 241 --word
    python tm_sim.py --machine ... --steps 241 --coq
    python tm_sim.py --machine ... --table
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tm_lib import blank, coq_config, parse_machine, run  # noqa: E402


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--machine", required=True, help="TNF machine string")
    ap.add_argument("--steps", type=int, default=0, help="steps to run from the blank tape")
    ap.add_argument("--start", default=None,
                    help="start configuration as 'state,left,cur,right' (digits, no spaces)")
    ap.add_argument("--word", action="store_true", help="print the tape word around the head")
    ap.add_argument("--coq", action="store_true", help="print the Coq term of the final configuration")
    ap.add_argument("--table", action="store_true", help="print the transition table")
    ap.add_argument("--nonblank", action="store_true", help="print the number of nonzero cells")
    args = ap.parse_args()

    m = parse_machine(args.machine)

    if args.table:
        print("machine: %s" % m.spec)
        for i in range(m.nstates):
            row = []
            for j in range(m.nsyms):
                w, d, q = m.table[(i, j)]
                row.append("%d%s%s" % (w, d, "Z" if q is None else "ABCDEFGHIJKLMNOPQRSTUVWXYZ"[q]))
            print("  %s: %s" % ("ABCDEFGHIJKLMNOPQRSTUVWXYZ"[i], " ".join(row)))
        h = m.halt_entry()
        print("  halting entry: %s%s" % (h[0], h[1]) if h else "  no halting entry")
        return

    if args.start:
        parts = [p.strip() for p in args.start.split(",")]
        if len(parts) != 4:
            raise SystemExit("--start needs 'state,left,cur,right'")
        state = parts[0]
        left = [int(c) for c in parts[1]] if parts[1] else []
        cur = int(parts[2])
        right = [int(c) for c in parts[3]] if parts[3] else []
        from tm_lib import Config
        cfg = Config(left, cur, right, state)
    else:
        cfg = blank(m)

    steps = 0
    while steps < args.steps:
        if not cfg.step(m):
            print("halted after %d steps" % steps)
            break
        steps += 1

    print("steps: %d" % steps)
    print("state: %s   head symbol: %d" % (cfg.state, cfg.cur))
    print("left (nearest first) : %s" % cfg.left)
    print("right (nearest first): %s" % cfg.right)
    if args.word:
        print("word  : %s" % cfg.word())
    if args.nonblank:
        nb = sum(1 for x in cfg.left + [cfg.cur] + cfg.right if x != 0)
        print("nonblank cells: %d" % nb)
    if args.coq:
        print("coq   : %s" % coq_config(cfg))


if __name__ == "__main__":
    main()
