"""Literal re-check of the rules in the M13b and M14b write-ups (BB13/, BB14/) on concrete instances.

    python m13b_m14b_writeup_chk.py

Independent of the Coq files: it simulates the machine strings below cell by cell and checks, for each rule
`X ->+ Y` of the write-ups, that the run from X reaches Y exactly (same state, head cell and tape, up to
translation) after at least one step and before halting.  Rules whose instances need levels W_j with j >= 3 are
checked for the small instances that fit; init_352 is checked at its exact step count.
"""
from __future__ import annotations

M13b = '1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_1RZ0LH'
M14b = '1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LN0LL_0LH1LK_1RZ0LH_0RJ0LI'


def table(s):
    t = {}
    for i, row in enumerate(s.split('_')):
        for b in (0, 1):
            c = row[3 * b:3 * b + 3]
            t['ABCDEFGHIJKLMNOP'[i], b] = None if c[2] == 'Z' or c == '---' else (int(c[0]), c[1], c[2])
    return t


CAP = 10 ** 6


def W(j, b):
    """W_0(b) = b + 3, W_(j+1)(b) = W_j^(b+1)(2); any value above CAP is returned as CAP + 1."""
    if b > CAP:
        return CAP + 1
    if j == 0:
        return b + 3
    x = 2
    for _ in range(b + 1):
        x = W(j - 1, x)
        if x > CAP:
            return CAP + 1
    return x


# A configuration is (state, left, head, right): left/right are lists read outward from the head, 0s beyond.
def step(t, c):
    q, l, h, r = c
    a = t[q, h]
    if a is None:
        return None
    w, d, n = a
    if d == 'R':
        return n, [w] + l, (r[0] if r else 0), r[1:]
    return n, l[1:], (l[0] if l else 0), [w] + r


def cells(c):
    """The set of offsets (relative to the head) holding a 1."""
    q, l, h, r = c
    s = {-1 - i for i, v in enumerate(l) if v} | {1 + i for i, v in enumerate(r) if v}
    return s | {0} if h else s


def reaches(t, x, y, limit=10 ** 6):
    """Steps from x until the configuration equals y (at least 1), or None if x halts or the limit is hit."""
    yq, ys = y[0], frozenset(cells(y))
    q, tape, pos = x[0], {}, 0
    for o in cells(x):
        tape[o] = 1
    n1 = len(tape)
    for k in range(1, limit + 1):
        a = t[q, tape.get(pos, 0)]
        if a is None:
            return None
        w, d, q = a
        old = tape.get(pos, 0)
        if w:
            tape[pos] = 1
        else:
            tape.pop(pos, None)
        n1 += w - old
        pos += 1 if d == 'R' else -1
        if q == yq and n1 == len(ys) and (pos in tape) == (0 in ys):
            if frozenset(o - pos for o in tape) == ys:
                return k
    return None


def rep(xs, n):
    return list(xs) * n


# The tape families of the write-ups (left side outward from the head = right-to-left in the written tape).
def side(*parts):
    out = []
    for p in parts:
        out += p
    return out


def Ca(j, b, z):          # 0^inf (10)^j 1^b A> 0 z
    return 'A', side(rep([1], b), rep([0, 1], j)), 0, list(z)


def Ch(j, b, z):          # 0^inf (10)^j <H 1^(b+1) 0 z
    l = rep([0, 1], j)
    return 'H', l[1:], (l[0] if l else 0), side([1], rep([1], b), [0], z)


def Ce(p, a, c, d):       # 0^inf (10)^p 1^(a+2) I> (10)^c 0 (10)^d 0^inf
    r = side(rep([1, 0], c), [0], rep([1, 0], d))
    return 'I', side(rep([1], a + 2), rep([0, 1], p)), r[0], r[1:]


def Cd(p, b, d):          # 0^inf (10)^p 1^(b+2) I> (10)^d 0^inf
    r = rep([1, 0], d) or [0]
    return 'I', side(rep([1], b + 2), rep([0, 1], p)), r[0], r[1:]


def c_end(p, a):          # 0^inf (10)^p 1^(a+5) M> 0^inf
    return 'M', side(rep([1], a + 5), rep([0, 1], p)), 0, []


def ones(c):
    q, l, h, r = c
    return sum(l) + h + sum(r)


fails = 0


def check(name, t, x, y):
    global fails
    k = reaches(t, x, y)
    if k is None:
        fails += 1
        print(f'FAIL {name}')
    return k


def common(label, s):
    t = table(s)
    z = [1, 1, 0, 1, 0]
    n = 0
    for j in range(3):
        for b in range(3):
            if j == 2 and b > 1:
                continue
            check(f'{label} CH_CA j={j} b={b}', t, Ch(j, b, z), Ca(j, W(j, b), z)); n += 1
    for j in range(3):
        for b in range(2):
            for a in range(3):
                x = b
                for _ in range(a):
                    x = W(j, x)
                if x > 400:
                    continue
                check(f'{label} BLK j={j} b={b} a={a}', t, Ca(j, b, side([1], rep([1], a), [0], z)), Ca(j + 1, x, z)); n += 1
    for p in range(3):
        for k in range(3):
            for c in range(2):
                for d in range(2):
                    check(f'{label} CE_EVEN', t, Ce(p + 1, 2 * k, c + 1, d), Ce(p + k + 1, W(p, 1), c, d)); n += 1
    for p in range(4):
        for k in range(3):
            check(f'{label} D_REL', t, Ce(p + 1, 2 * k, 0, 0), Cd(p, W(p, 0), k + 2)); n += 1
    for p in range(3):
        for m in range(3):
            for d in range(2):
                check(f'{label} C_REL', t, Cd(p + 1, 2 * m + 1, d + 1), Ce(p, W(p, 3), m, d)); n += 1
    for p in range(3):
        for a in range(4):
            for d in range(2):
                if W(p, a + 4) > 500:        # larger instances exceed the step limit
                    continue
                check(f'{label} D_STEP', t, Ce(p, a, 0, d + 2), Cd(p, W(p, a + 4), d)); n += 1
    for p in range(4):
        for a in range(4):
            y = c_end(p, a)
            k = check(f'{label} HALT', t, Ce(p, a, 0, 1), y)
            if k is not None and step(t, y) is not None:
                print(f'FAIL {label} c_end does not halt'); fails_inc()
            n += 1
    k = check(f'{label} init_352', t, ('A', [], 0, []), Ce(8, 4, 0, 0))
    if k != 352:
        print(f'FAIL {label} init_352 took {k} steps'); fails_inc()
    n += 1
    return t, n


def fails_inc():
    global fails
    fails += 1


t13, n13 = common('M13b', M13b)
for p in range(1, 6):
    for m in range(4):
        # K reload, first part: Cd p (2m+1) 0 ->+ Cd 2 3 (p+m+2); then C_REL, CE_EVEN and D_STEP give Cd 8 W_8(8) (p+m-1).
        check('M13b K_REL', t13, Cd(p, 2 * m + 1, 0), Cd(2, 3, p + m + 2)); n13 += 1
print(f'M13b: {n13} instances checked')

t14, n14 = common('M14b', M14b)
for q in range(3):
    for m in range(4):
        check('M14b K_REL_odd', t14, Cd(2 * q + 1, 2 * m + 1, 0), Cd(2, 3, 2 * q + m + 3)); n14 += 1
        if q >= 1:
            check('M14b K_REL_even', t14, Cd(2 * q, 2 * m + 1, 0), Ce(2 * q + m + 2, 4, 0, 0)); n14 += 1
print(f'M14b: {n14} instances checked')

# The tail of the K reload: Cd 2 3 (d+3) ->C_REL-> Ce 1 14 1 (d+2) ->CE_EVEN-> Ce 8 4 0 (d+2) ->D_STEP-> Cd 8 W_8(8) d.
for t, label in ((t13, 'M13b'), (t14, 'M14b')):
    for d in range(3):
        check(f'{label} reload tail', t, Cd(2, 3, d + 3), Ce(8, 4, 0, d + 2))
print('ALL PASS' if fails == 0 else f'{fails} FAILURES')
