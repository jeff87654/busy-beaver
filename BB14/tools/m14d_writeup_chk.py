"""Literal re-check of the rules in the M14d_18 write-up (BB14/) on concrete instances.

    python m14d_writeup_chk.py

Independent of the Coq files.  Part 1 simulates the machine string below cell by cell and checks, for each rule
`X ->+ Y` of the write-up, that the run from X reaches Y exactly (same state, head cell and tape, up to
translation) after at least one step and before halting.  Rules whose instances need levels W_j with j >= 3 are
checked for the small instances that fit; init_160 is checked at its exact step count.

Part 2 re-derives the order of the rounds (section 2 of the write-up) from the closed form of W alone:
2 W_2(y) + 5 = 3^(y+3) (checked on instances here), so every accumulator value W_p(b) with p >= 3 is known modulo
3^13.  From that it computes the residue of the level p at every round and the class (K0, K1, K2 = halt, D) of
each round.  The Coq file's residue constants are listed only to compare with at the end.
"""
from __future__ import annotations

M14d = '1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LN1LK_1RZ0LH_0LG1LJ'


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


def side(*parts):
    out = []
    for p in parts:
        out += p
    return out


# The tape families of the write-up (left side outward from the head = right-to-left in the written tape).
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


def fail(msg):
    global fails
    fails += 1
    print(f'FAIL {msg}')


def check(name, t, x, y):
    k = reaches(t, x, y)
    if k is None:
        fail(name)
    return k


# ---------------------------------------------------------------------------------------------------------------
# Part 1: the rules of section 1, literally.
t = table(M14d)
z = [1, 1, 0, 1, 0]
n = 0
for j in range(3):
    for b in range(3):
        if j == 2 and b > 1:
            continue
        check(f'CH_CA j={j} b={b}', t, Ch(j, b, z), Ca(j, W(j, b), z)); n += 1
for j in range(3):
    for b in range(2):
        for a in range(3):
            x = b
            for _ in range(a):
                x = W(j, x)
            if x > 400:
                continue
            # a block 1^(a+1) 0 to the right (a = 0 is the shift CA_SH)
            check(f'BLK j={j} b={b} a={a}', t, Ca(j, b, side([1], rep([1], a), [0], z)), Ca(j + 1, x, z)); n += 1
for p in range(3):
    for k in range(3):
        for c in range(2):
            for d in range(2):
                check('CE_EVEN', t, Ce(p + 1, 2 * k, c + 1, d), Ce(p + k + 1, W(p, 1), c, d)); n += 1
for p in range(3):
    for m in range(3):
        for d in range(2):
            check('C_REL', t, Cd(p + 1, 2 * m + 1, d + 1), Ce(p, W(p, 3), m, d)); n += 1
for p in range(3):
    for a in range(4):
        for d in range(2):
            if W(p, a + 4) > 500:        # larger instances exceed the step limit
                continue
            check('D_STEP', t, Ce(p, a, 0, d + 2), Cd(p, W(p, a + 4), d)); n += 1
# new in M14d_18: D_REL drops two level cells and starts the accumulator at W_p(2)
for p in range(3):
    for k in range(3):
        if W(p, 2) > 500:
            continue
        check('D_REL', t, Ce(p + 2, 2 * k, 0, 0), Cd(p, W(p, 2), k + 2)); n += 1
# new in M14d_18: the reload
for p in range(0, 6):
    for m in range(4):
        check('K_REL_step1+2', t, Cd(p, 2 * m + 1, 0), Ce(0, 1, 0, p + m + 3)); n += 1
for d in range(4):
    check('K_REL_step3', t, Ce(0, 1, 0, d + 3), Cd(5, 3, d)); n += 1
for p in range(1, 6):
    for m in range(4):
        check('K_REL_to_5_3', t, Cd(p, 2 * m + 1, 0), Cd(5, 3, p + m)); n += 1
for p in range(4):
    for a in range(4):
        y = c_end(p, a)
        k = check('HALT', t, Ce(p, a, 0, 1), y)
        if k is not None and step(t, y) is not None:
            fail('c_end does not halt')
        if ones(y) != p + a + 5:
            fail('c_end ones')
        n += 1
k = check('init_160', t, ('A', [], 0, []), Cd(5, 3, 3))
if k != 160:
    fail(f'init_160 took {k} steps')
n += 1
print(f'part 1: {n} rule instances checked')

# ---------------------------------------------------------------------------------------------------------------
# Part 2: the order of the rounds, from the closed form of W.
# W_1(b) = 3b + 5 and 2 W_2(b) + 5 = 3^(b+3); W_3(1) = W_2(W_2(2)) = W_2(119).
for b in range(40):
    if W(1, b) != 3 * b + 5:
        fail(f'W_1({b})')
for b in range(8):
    if 2 * W(2, b) + 5 != 3 ** (b + 3):
        fail(f'W_2({b}) closed form')


def W2(y):
    return (3 ** (y + 3) - 5) // 2


for y in range(61):          # W_2(y) = W_1^(y+1)(2), by direct iteration
    x = 2
    for _ in range(y + 1):
        x = 3 * x + 5
    if x != W2(y):
        fail(f'W_2({y}) by iteration')
if W2(W2(2)) != W2(119):
    fail('W_3(1) = W_2(119)')

# For p >= 3 every W_p(b) (b >= 1) is a value W_2(y) with y >= 29 (Coq: W_ge3_S_is_W2), so 2 W_p(b) + 5 is
# divisible by 3^13.  Even values (b odd) have a/2 = -5/4 and odd values (b even) have floor(b/2) = -7/4 mod 3^13.
Q = 3 ** 13
inv = lambda v, mod: pow(v, -1, mod)
h_even = (-5 * inv(4, Q)) % Q
h_odd = (-7 * inv(4, Q)) % Q
for y in range(29, 45):
    a = W2(y)
    h = a // 2
    if (h - (h_even if a % 2 == 0 else h_odd)) % Q:
        fail(f'W_2({y}) residue')

# Level changes mod 3^13 (section 2 of the write-up):
#   Kc adds a/2 = -5/4; Kc_full(p, b) = Kc^(b/2)(p - 1, .) adds -1 + (-7/4)(-5/4) = 19/16, and so does Kd_step;
#   the reload restarts at p_K0 = 4 + W_4(3)/2 = 4 - 5/4 = 11/4 with d = p + b/2 - 3 tokens;
#   a D round from Ce p a 0 0 goes to level p - 2 with a/2 + 2 = 3/4 tokens, i.e. (a/2 + 2)/3 = 1/4 Kd_steps.
step16 = (19 * inv(16, Q)) % Q
pK0 = (11 * inv(4, Q)) % Q

rounds = []
resid = []                # (kind of configuration, residue of p, modulus)
p, mod, kind = pK0, Q, 'Cd'           # pb1 = pb_K0 (after init_160 and one reload tail with 3 tokens)
resid.append(('Cd', p, mod))
while True:
    if kind == 'Cd':
        d = (p + h_odd - 3) % mod
        r = d % 3
        nst = ((d - r) // 3) % (mod // 3)
        mod //= 3
        if r == 2:
            rounds.append('K2')
            break
        if r == 0:
            rounds.append('K0')
            p, kind = (pK0 + nst * step16) % mod, 'Cd'
        else:
            rounds.append('K1')
            p, kind = (pK0 + (nst + 1) * step16) % mod, 'Ce'
    else:
        mod = min(mod, 3 ** 12)
        # a/2 + 2 = 3/4 mod 3^13, so the number of Kd_steps (a/2 + 2)/3 is 1/4 mod 3^12
        if (h_even + 2) % 3:
            fail('D round token count not divisible by 3')
        nst = (h_even + 2) // 3
        if (nst - inv(4, 3 ** 12)) % (3 ** 12):
            fail('D round count is not 1/4')
        rounds.append('D')
        p, kind = (p - 2 + nst * step16) % mod, 'Cd'
    resid.append((kind, p, mod))

expected = ['K1', 'D', 'K0', 'K0', 'K0', 'K0', 'K0', 'K0', 'K1', 'D', 'K1', 'D', 'K1', 'D', 'K0', 'K1', 'D', 'K2']
print('part 2: rounds 2-19 =', ' '.join(rounds))
if rounds != expected:
    fail('round order')
print(f'        {len(rounds)} rounds after pb1, each one f_(omega+2) in the bound')

# Compare with the residues proved in the Coq file (run_pb1 ... run_pb18).
coq = [(1195745, 3 ** 13), (132863, 3 ** 12), (107950, 3 ** 12), (45499, 3 ** 11), (2326, 3 ** 10),
       (13531, 3 ** 9), (2794, 3 ** 8), (1141, 3 ** 7), (350, 3 ** 6), (144, 3 ** 5), (17, 3 ** 5), (78, 3 ** 4),
       (32, 3 ** 4), (8, 27), (16, 27), (2, 9), (1, 3), (0, 3)]
mine = [(r, m) for (_, r, m) in resid]
if mine != coq:
    fail('residues differ from the Coq file')
    for a, b in zip(mine, coq):
        print('  ', a, b)
else:
    print('        residues of p agree with the 18 run_* lemmas of the Coq file')
# and the Coq constants themselves
for name, mine_c, coq_c, m in [('Kd_step', step16, 1494679, Q), ('p_K0', pK0, 1195745, Q),
                               ('K1 offset', (pK0 + step16) % Q, 2690424, Q),
                               ('D offset', (-2 + inv(4, 3 ** 12) * step16) % 3 ** 12, 506528, 3 ** 12),
                               ('a/2 even', h_even, 1195741, Q), ('b/2 odd', h_odd, 398579, Q)]:
    if (mine_c - coq_c) % m:
        fail(f'constant {name}')

print('ALL PASS' if fails == 0 else f'{fails} FAILURES')
