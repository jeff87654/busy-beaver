"""Independent check of the J20 write-up's rules on the machine string (no Coq files used).

    python j20_writeup_chk.py [macro_steps]      (default 2,000,000 macro steps of the blank-tape run; about 2 minutes)

J20 = Jacobzheng's BB(20) champion (bbchallenge wiki). The simulator below is exact: it runs the transition table
parsed from the string, and only jumps over a run of equal cells when the machine stays in the same state and
direction over it (a same-state run). Lists are blocks of 1s separated by single 0s; [a, b, c] is 1^a 0 1^b 0 1^c.
Inner boundary:  0^inf <H 1^x 0 1^d2 ... 0 1^dn 00 [outer list]        (H reads the blank left of the inner list)
Outer boundary:  0^inf 1 00 F> 1^a 0 1^o2 ... 0 1^om 0^inf             (marker 1 and two 0s at the far left)
Checks:
  1. inner engine steps on 600 random inner lists with random outer lists (E0, E1, exit into the outer head);
  2. outer rounds on random outer lists (R0 = expansion + whole inner run, for heads a <= 5; R1 for any head);
  3. the expansion of the outer head a = 1..199 (the first inner boundary after it);
  4. exhaustion + refill for [a, 1^n], a = 1..39, n = 0..5: the merged block has N = a + 2n + 4 ones; N = 3j halts
     with 2j + 1 ones on the tape when the halting slot is read (so sigma = 2j + 2), N = 3k + 1 gives the outer list
     [1, 1, 2^(k-1), 3] and N = 3k + 2 gives [1, 2^k, 3];
  5. the mod-3 residue law of the inner engine on 3000 random small lists, and G(1..5);
  6. the run from the blank tape against the model, boundary by boundary (inner and outer), for the given number
     of macro steps.
"""
import random
import sys

J20 = ('1LH0LG_0LI1RC_0LD1LA_0RE1LD_1RQ1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0RF0LO_'
       '0RF1LP_0RF1LN_1LR1RQ_1RZ1LS_0LF1LT_0LF0LR')


def parse(s):
    T = {}
    for i, part in enumerate(s.split('_')):
        for r in range(2):
            t = part[3 * r:3 * r + 3]
            T[(chr(65 + i), r)] = None if t == '---' or t[2] == 'Z' else (int(t[0]), t[1], t[2])
    return T


class Sim:
    """Tape = two stacks of [symbol, count] runs (top = next to the head). face 'R': the head reads R's top."""
    def __init__(self, s):
        self.T = parse(s); self.L = []; self.R = []; self.face = 'R'; self.st = 'A'
        self.steps = 0; self.halted = False

    @staticmethod
    def push(stk, sym, n):
        if n <= 0:
            return
        if stk and stk[-1][0] == sym:
            stk[-1][1] += n
        elif not stk and sym == 0:
            return
        else:
            stk.append([sym, n])

    @staticmethod
    def pop1(stk):
        if not stk:
            return 0
        s = stk[-1][0]; stk[-1][1] -= 1
        if stk[-1][1] == 0:
            stk.pop()
        return s

    def sym(self):
        src = self.R if self.face == 'R' else self.L
        return src[-1][0] if src else 0

    def step(self):
        src = self.R if self.face == 'R' else self.L
        dst = self.L if self.face == 'R' else self.R
        sym = src[-1][0] if src else 0
        tr = self.T[(self.st, sym)]
        if tr is None:
            self.halted = True; return
        w, d, ns = tr
        if d == self.face and ns == self.st:
            if not src:
                raise RuntimeError('same-state run into the blank: never halts')
            n = src.pop()[1]; self.push(dst, w, n); self.steps += n
        elif d == self.face:
            self.pop1(src); self.push(dst, w, 1); self.steps += 1
        else:
            self.pop1(src); self.push(src, w, 1); self.face = d; self.steps += 1
        self.st = ns

    def ones(self):
        return sum(n for s, n in self.L + self.R if s == 1)


def build(left, st, right, face):
    s = Sim(J20)
    for ch in left:
        Sim.push(s.L, int(ch), 1)
    for ch in reversed(right):
        Sim.push(s.R, int(ch), 1)
    s.st = st; s.face = face
    return s


def blocks(ds):
    return '0'.join('1' * d for d in ds)


def parse_R(s):
    runs = list(reversed(s.R))
    return [n for sy, n in runs if sy == 1], [n for sy, n in runs if sy == 0]


def inner_of(s):
    """inner list (up to the first 00) and the 1-blocks after it"""
    runs = list(reversed(s.R)); inn = []; i = 0
    while i < len(runs):
        sy, n = runs[i]
        if sy == 1:
            inn.append(n)
        elif n >= 2:
            break
        i += 1
    return inn, [n for sy, n in runs[i:] if sy == 1], (runs[i][1] if i < len(runs) else None), \
        [n for sy, n in runs[i + 1:] if sy == 0]


def at_inner(s):
    return s.st == 'H' and s.face == 'L' and not s.L and s.sym() == 0


def at_outer(s):
    return s.st == 'F' and s.face == 'R' and len(s.L) == 2 and s.L[0] == [1, 1] and s.L[1] == [0, 2]


# ---- the model of the write-up ----
class Big(Exception):
    pass


def eng_step(l):
    """E0 [x,e,r] -> [x+4,e-1,r];  E1 [x,1^p,e,r] -> [2,1^(p-1),x+3,e-1,r];  exit [x,1^n] -> outer head x+2n+2"""
    i = 1
    while i < len(l) and l[i] == 1:
        i += 1
    if i == len(l):
        return ('X', l[0] + 2 * (len(l) - 1) + 2)
    p, x, e = i - 1, l[0], l[i]
    if p == 0:
        return [x + 4, e - 1] + l[i + 1:]
    return [2] + [1] * (p - 1) + [x + 3, e - 1] + l[i + 1:]


def eng(l, cap=None):
    l = list(l)
    while True:
        r = eng_step(l)
        if isinstance(r, tuple):
            return r[1]
        if cap and r[0] > cap:
            raise Big()
        l = r


def expand(a):
    """T = a + 4:  T = 3k+1 -> [-1,2^k],  T = 3k+2 -> [0,2^k],  T = 3k -> [1,2^(k-1)]  (x = -1, 0: mid-sweep start)"""
    T = a + 4
    if T % 3 == 1:
        return [-1] + [2] * ((T - 1) // 3)
    if T % 3 == 2:
        return [0] + [2] * ((T - 2) // 3)
    return [1] + [2] * (T // 3 - 1)


def G(a, cap=None):
    return eng(expand(a), cap)


def oround(O, cap=None):
    """R0 [a,e,r] -> [G a,e-1,r];  R1 [a,1^p,e,r] -> [3,1^(p-1),a+2,e-1,r];  EX [a,1^n] -> block N = a+2n+4"""
    i = 1
    while i < len(O) and O[i] == 1:
        i += 1
    if i == len(O):
        return ('N', O[0] + 2 * (len(O) - 1) + 4)
    p, a, e = i - 1, O[0], O[i]
    if p == 0:
        return [G(a, cap), e - 1] + O[i + 1:]
    return [3] + [1] * (p - 1) + [a + 2, e - 1] + O[i + 1:]


def refill(N):
    """N = 3j: halt with 2j+1 ones;  N = 3k+1: [1,1,2^(k-1),3];  N = 3k+2: [1,2^k,3]"""
    if N % 3 == 0:
        return ('HALT', 2 * (N // 3) + 1)
    if N % 3 == 1:
        return [1, 1] + [2] * (N // 3 - 1) + [3]
    return [1] + [2] * (N // 3) + [3]


fails = 0


def report(name, ok, bad):
    global fails
    fails += bad
    print(f'{name}: {ok} ok, {bad} bad', flush=True)


def run_outer(O, through_refill):
    """from an outer boundary, run to the next outer boundary (or halt)"""
    s = build('100', 'F', blocks(O), 'R'); first = True; sawQ = False
    for _ in range(10 ** 7):
        if s.halted:
            return ('HALT', s.ones())
        if s.st == 'QQ' or s.st == 'Q':
            sawQ = True
        if not first and at_outer(s):
            o, g = parse_R(s)
            return ('RF' if sawQ else 'O', o, g)
        first = False; s.step()
    return ('TIMEOUT',)


# 1. inner engine steps
random.seed(1); ok = bad = 0
for _ in range(600):
    n = random.randint(1, 6)
    l = [random.randint(1, 12)] + [random.choice([1, 1, 1, 2, 3, 4, 7]) for _ in range(n - 1)]
    outer = [random.randint(1, 9) for _ in range(random.randint(1, 4))]
    s = build('', 'H', blocks(l) + '00' + blocks(outer), 'L'); first = True; got = None
    for _ in range(10 ** 6):
        if s.halted:
            got = ('HALT',); break
        if not first and at_inner(s):
            inn, rest, sep, gaps = inner_of(s); got = ('I', inn, rest, gaps, sep); break
        if not first and at_outer(s):
            o, g = parse_R(s); got = ('O', o, g); break
        first = False; s.step()
    m = eng_step(l)
    exp = ('O', [m[1]] + outer, [1] * len(outer)) if isinstance(m, tuple) else \
        ('I', m, outer, [1] * (len(outer) - 1), 2)
    if got == exp:
        ok += 1
    else:
        bad += 1; print('  INNER MISMATCH', l, outer, got, exp)
report('inner engine steps (E0, E1, exit)', ok, bad)

# 2. outer rounds
ok = bad = 0
for _ in range(400):
    n = random.randint(2, 6)
    O = [random.randint(1, 30)] + [random.choice([1, 1, 1, 2, 3, 5, 9]) for _ in range(n - 1)]
    i = 1
    while i < len(O) and O[i] == 1:
        i += 1
    if i == len(O):
        continue
    if i == 1 and O[0] > 5:
        O[0] = random.randint(1, 5)
    r = run_outer(O, False)
    if r[0] == 'O' and r[1] == oround(O) and all(g == 1 for g in r[2]):
        ok += 1
    else:
        bad += 1; print('  OUTER MISMATCH', O, r, oround(O))
report('outer rounds (R0 with a <= 5, R1 with any a)', ok, bad)

# 3. expansion
ok = bad = 0
for a in range(1, 200):
    O = [a, random.randint(2, 6), random.randint(1, 5)]
    s = build('100', 'F', blocks(O), 'R')
    while not at_inner(s):
        s.step()
    inn, rest, sep, gaps = inner_of(s)
    if inn == eng_step(expand(a)) and rest == [O[1] - 1, O[2]] and sep == 2 and all(g == 1 for g in gaps):
        ok += 1
    else:
        bad += 1; print('  EXPANSION MISMATCH', a, inn, rest)
report('expansion of the outer head a = 1..199 (first inner boundary)', ok, bad)

# 4. exhaustion + refill
ok = bad = 0
for a in range(1, 40):
    for n in range(0, 6):
        O = [a] + [1] * n; r = run_outer(O, True); m = refill(a + 2 * n + 4)
        if isinstance(m, tuple):
            good = r == ('HALT', m[1])
        else:
            good = r[0] == 'RF' and r[1] == m and all(g == 1 for g in r[2])
        ok += good; bad += not good
        if not good:
            print('  REFILL MISMATCH', O, r, m)
report('exhaustion + refill of [a,1^n] (N = a+2n+4; halt iff N = 3j, with 2j+1 ones)', ok, bad)

# 5. residue law
random.seed(5); ok = bad = 0
for _ in range(3000):
    n = random.randint(1, 5)
    l = [random.randint(-1, 9)] + [random.choice([1, 1, 2, 3]) for _ in range(n - 1)]
    try:
        v = eng(l, cap=10 ** 6)
    except Big:
        continue
    pred = (l[0] + sum(d - 1 for d in l[1:]) + 2 * (len(l) - 1) + 2) % 3
    ok += v % 3 == pred; bad += v % 3 != pred
report('inner residue law (exit = x + sum(d-1) + 2(n-1) + 2 mod 3)', ok, bad)
g = [G(a) for a in range(1, 6)]
good = g == [8, 9, 28, 32, 36] and all(G(a) % 3 == (a + 1) % 3 for a in range(1, 6))
print(f'G(1..5) = {g}, each = a+1 mod 3:', 'ok' if good else 'BAD')
fails += not good


# 6. the blank-tape run, boundary by boundary
def model_events():
    O = [3]; yield ('O', O)
    while True:
        i = 1
        while i < len(O) and O[i] == 1:
            i += 1
        if i == len(O):
            rf = refill(O[0] + 2 * (len(O) - 1) + 4)
            if isinstance(rf, tuple):
                yield ('HALT', rf); return
            O = rf; yield ('O', O); continue
        if i > 1:
            O = [3] + [1] * (i - 2) + [O[0] + 2, O[i] - 1] + O[i + 1:]; yield ('O', O); continue
        l = expand(O[0]); rest = [O[1] - 1] + O[2:]
        while True:
            l = eng_step(l)
            if isinstance(l, tuple):
                O = [l[1]] + rest; yield ('O', O); break
            yield ('I', l, rest)


maxmacro = int(sys.argv[1]) if len(sys.argv) > 1 else 2 * 10 ** 6
s = Sim(J20); me = model_events(); n = 0; mism = False; first_outer = []
for _ in range(maxmacro):
    if s.halted:
        print('  the machine halted early (not expected)'); mism = True; break
    ev = None
    if at_outer(s):
        ev = ('O', parse_R(s)[0])
    elif at_inner(s) and s.R and s.steps > 13:
        inn, rest, _, _ = inner_of(s); ev = ('I', inn, rest)
    if ev:
        m = next(me)
        if ev != m:
            print('  BLANK-RUN MISMATCH at step', s.steps, ev, m); mism = True; break
        n += 1
        if ev[0] == 'O' and len(first_outer) < 5:
            first_outer.append(ev[1])
    s.step()
print(f'blank tape: {n} consecutive boundaries agree with the model ({s.steps} steps); first outer lists:',
      ' '.join(str(o) for o in first_outer), flush=True)
fails += mism or n < 100

print('ALL CHECKS PASSED' if fails == 0 else f'{fails} FAILURES')
sys.exit(1 if fails else 0)
