"""Independent literal simulator for P12 (bb12-p2 agent, 2026-11-15). Written from scratch.
Tape: Python list with offset; RLE printing with units (10) and 1 and 0."""
import sys

P12 = "1RB1RA_1RI1RC_0LD1LG_0RE1LD_---1RF_0LL0RA_1RA0LH_1LG1LH_1RK0LJ_1LH1LI_0LL0RD_0LH1LK"


def parse(s):
    tm = {}
    for i, part in enumerate(s.split('_')):
        q = chr(ord('A') + i)
        for r in (0, 1):
            t = part[3 * r:3 * r + 3]
            if t[0] == '-':
                tm[(q, r)] = None
            else:
                tm[(q, r)] = (int(t[0]), 1 if t[1] == 'R' else -1, t[2])
    return tm


class Tape:
    def __init__(self, cells=None, head=0):
        self.t = dict(cells or {})
        self.h = head

    def get(self, p=None):
        return self.t.get(self.h if p is None else p, 0)


def run(tm, q, tape, maxsteps, stop=None):
    """run until halt / maxsteps / stop(q, tape, prev) true. returns (q, steps, halted)"""
    n = 0
    t = tape.t
    h = tape.h
    while n < maxsteps:
        s = t.get(h, 0)
        tr = tm[(q, s)]
        if tr is None:
            tape.h = h
            return q, n, True
        w, d, nq = tr
        if w:
            t[h] = 1
        elif h in t:
            del t[h]
        h += d
        n += 1
        pq = q
        q = nq
        if stop is not None:
            tape.h = h
            if stop(pq, q, d, tape):
                return q, n, False
    tape.h = h
    return q, n, False


def rle(tape, q, dirright=True):
    t = tape.t
    if not t:
        return f"{q}> blank"
    lo = min(min(t), tape.h)
    hi = max(max(t), tape.h)
    left = ''.join(str(t.get(i, 0)) for i in range(lo, tape.h))
    right = ''.join(str(t.get(i, 0)) for i in range(tape.h, hi + 1))
    return f"{comp(left)}  [{q}]  {comp(right)}"


def comp(s):
    # greedy compression into tokens: runs of '10', '1', '0'
    out = []
    i = 0
    while i < len(s):
        # count (10) repeats
        k = 0
        while s.startswith('10', i + 2 * k):
            k += 1
        if k >= 3:
            out.append(f"(10)^{k}")
            i += 2 * k
            continue
        c = s[i]
        j = i
        while j < len(s) and s[j] == c:
            j += 1
        out.append(c if j - i == 1 else f"{c}^{j - i}")
        i = j
    return ' '.join(out)


if __name__ == '__main__':
    tm = parse(P12)
    tape = Tape()
    q = 'A'
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    total = 0
    # print each time we enter I moving right (Y configs) or H moving left with a 1^b block (Ch)
    def stop(pq, q, d, tp):
        return q == 'I' and d == 1
    while total < N:
        q, n, halted = run(tm, q, tape, N - total, stop)
        total += n
        print(total, rle(tape, q))
        if halted:
            print('HALT', total, 'ones', sum(tape.t.values()))
            break
