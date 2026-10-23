"""Independent literal check of the rules in BB7/1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB.md.

A plain cell-by-cell simulator (no macros). For both machines it checks
  - the start: from the blank tape, the first K configuration is K(8; 0, 1^19), at step 3897 (champ_231) / 3959 (champ_232);
  - D, Bk and E on a grid of small cases, including the exact step counts and the ones count 6a+7 at the halt;
  - that Bk and E fail (no K configuration / no halt within a step limit) just past their precondition (k = 3a+1).
K(a; d1, ..., dn) = 0^inf E> 0 100 (11)^a 00 (11)^d1 00 ... (11)^dn 00 1 0^inf   (head on the first cell, state E).
Usage: python3 c231_chk.py        (about a minute)"""
import sys

MACHINES = {'champ_231': "1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB",
            'champ_232': "1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_1LC0RB"}

def parse(m):
    t = {}
    for i, g in enumerate(m.split('_')):
        for s in (0, 1):
            e = g[3 * s:3 * s + 3]
            t[(i, s)] = None if e == '---' else (int(e[0]), 1 if e[1] == 'R' else -1, ord(e[2]) - 65)
    return t

def ktape(a, ds):
    r = [0, 1, 0, 0] + [1, 1] * a + [0, 0]
    for d in ds:
        r += [1, 1] * d + [0, 0]
    return r + [1]

def kparse(cells):
    """cells from the head to the last 1; returns (a, ds) if they form a K configuration."""
    if cells[:4] != [0, 1, 0, 0]:
        return None
    i, vals, n = 4, [], len(cells)
    while True:
        c = 0
        while i + 1 < n and cells[i] == 1 and cells[i + 1] == 1:
            c += 1; i += 2
        if i == n - 1 and cells[i] == 1 and c == 0:
            break
        if i + 1 < n and cells[i] == 0 and cells[i + 1] == 0:
            vals.append(c); i += 2
        else:
            return None
    return (vals[0], vals[1:]) if vals else None

def run(m, tape, pos=0, q=4, limit=10**6, skip_first=True):
    """Run until the next K configuration (state E on a 0 with only blanks to its left) or the halt."""
    T = parse(m); t = dict(enumerate(tape)); n = 0
    while n < limit:
        s = t.get(pos, 0)
        if q == 4 and s == 0 and (n > 0 or not skip_first) and all(v == 0 for k, v in t.items() if k < pos):
            hi = max(k for k, v in t.items() if v) if any(t.values()) else pos
            k = kparse([t.get(i, 0) for i in range(pos, hi + 1)])
            if k is not None:
                return ('K', n, k)
        tr = T[(q, s)]
        if tr is None:
            return ('H', n, sum(t.values()), 'ABCDEFG'[q], s)
        w, d, q = tr
        t[pos] = w; pos += d; n += 1
    return ('T', n)

def run_blank(m, limit=10**5):
    T = parse(m); t = {}; pos = 0; q = 0; n = 0
    while n < limit:
        s = t.get(pos, 0)
        if q == 4 and s == 0 and all(v == 0 for k, v in t.items() if k < pos) and any(t.values()):
            hi = max(k for k, v in t.items() if v)
            k = kparse([t.get(i, 0) for i in range(pos, hi + 1)])
            if k is not None:
                return n, k
        w, d, q = T[(q, s)]; t[pos] = w; pos += d; n += 1

def main():
    bad = 0
    for name, m in MACHINES.items():
        x = 2 if name == 'champ_232' else 0
        n, k = run_blank(m)
        ok = k == (8, [0] + [1] * 19) and n == {'champ_231': 3897, 'champ_232': 3959}[name]
        bad += not ok
        print(f'{name}: first K configuration at step {n}: K({k[0]}; {k[1][:3]}...{len(k[1])} digits)', 'OK' if ok else 'MISMATCH')
        cnt = 0
        for a in range(1, 7):
            for ds in ([1], [2, 0], [3, 1, 2]):                             # D
                r = run(m, ktape(a, ds))
                exp = ('K', 12 * a * a + 66 * a + 56 + x, (3 * a + 3, [ds[0] - 1] + ds[1:]))
                bad += r != exp; cnt += 1
            for k in range(1, 3 * a + 2):                                  # Bk, and k = 3a+1 must fail
                for y, rest in ((0, []), (2, [1])):
                    r = run(m, ktape(a, [0] * k + [y + 1] + rest), limit=4 * 10**5)
                    if k <= 3 * a:
                        st = 12 * a * a + (24 * k + 66) * a + 74 + 10 * (k - 1) - 4 * (k - 1) * (k - 2) + (2 * (k + 1) if x else 0)
                        exp = ('K', st, (1, [1] * (k - 1) + [3 * a + 3 - k, y] + rest))
                        bad += r != exp
                    else:
                        bad += r[0] == 'K' and r[2][0] == 1
                    cnt += 1
            for k in range(1, 3 * a + 2):                                  # E, and k = 3a+1 must not halt
                r = run(m, ktape(a, [0] * k), limit=4 * 10**5)
                if k <= 3 * a:
                    st = 48 * a * a + 192 * a + 137 - 28 * k if not x else 48 * a * a + 198 * a + 143 - 30 * k
                    bad += r != ('H', st, 6 * a + 7, 'C', 1)
                else:
                    bad += r[0] == 'H'
                cnt += 1
        print(f'{name}: {cnt} rule instances checked')
    print('ALL OK' if bad == 0 else f'{bad} MISMATCHES')
    return bad

if __name__ == '__main__':
    sys.exit(1 if main() else 0)
