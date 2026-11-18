#!/usr/bin/env python3
"""Find the exact configuration where a sweep variant ends: state A, head on
the first 2 of the reservoir, with the new marker just to the right."""
import trace_marker as T


def find(k, m, right, limit=200000):
    tr = T.parse(T.BB64)
    tape = T.bcfg(k, m, right)
    q, head = 0, 0
    for t in range(limit):
        if q == 0 and tape.get(head, 0) == 2:
            ctx = T.context(tape, head, 9)
            # reservoir: a run of 2s then marker; marker ends with a 1 then zeros
            n2 = 0; p = head
            while tape.get(p, 0) == 2: n2 += 1; p += 1
            # marker starts at p
            mark = [tape.get(p+i, 0) for i in range(5)]
            if mark[0] == 0 and mark[1] in (1, 3, 0) and n2 >= 1:
                left2 = T.twos_left(tape, head)
                print(f"  Bcfg({k},0,{m},{right}): A at t={t}, n2res={n2}, mark={mark}, "
                      f"left-of-head 2s={left2}, 3s-after={T.twos_left(tape,head-0)} ")
                # count 3s immediately left of the single left 2
                p2 = head - 1
                while tape.get(p2, 0) == 2: p2 -= 1
                n3 = 0
                while tape.get(p2, 0) == 3: n3 += 1; p2 -= 1
                print(f"      left structure: 2^{left2} then 3^{n3}; expect 2^1 3^3")
                return t
        r = T.step(tr, q, tape, head)
        if r is None or r[0] == -1:
            print(f"  Bcfg({k},0,{m},{right}): HALT at t={t+1}")
            return
        q, head = r
    print(f"  Bcfg({k},0,{m},{right}): no sweep end found in {limit}")


if __name__ == "__main__":
    for k in [1, 2, 3]:
        for m in [0, 1]:
            find(k, m, [0, 1, 1])
