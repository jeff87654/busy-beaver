"""Independent check of the R18a write-up's rules on the machine string (no Coq files used).

    python r18a_writeup_chk.py          (about 10 seconds)

R18a is this project's 18-state machine, derived from Jacobzheng's J20 (BB20/). The simulator below is exact: it
runs the transition table parsed from the string, and only jumps over a run of equal cells when the machine stays in
the same state and direction over it (a same-state run). Lists are blocks of 1s separated by single 0s.
Outer boundary (the Coq file's CO a ds):   0^inf 1 0 0 F> 1^a 0 1^d1 0 1^d2 ... 0 1^dm 0^inf
Checks:
  1. exhaustion + refill of CO a [1^n], a = 0..79, n = 0..6: the merged block has T = a + 2n + 2 cells;
     T = 3c+1 halts with 2c+2 ones (R reads the marker 1; R1 = 1RZ writes 1 on a 1, so sigma = 2c+2),
     T = 3k+2 gives CO 0 [1, 1, 2^k], T = 3k gives CO 0 [1, 2^k];
  2. R1 on 400 random lists: CO a [1^(p+1), e+2, rest] -> CO 3 [1^p, a+2, e+1, rest];
  3. R0 for a = 0..5: CO a [e+2, rest] -> CO (G a) [e+1, rest], with G computed from the Coq file's recursion
     (h, hc, Gcy, G, typed in again below); G(a) = a+1 mod 3 for a = 0..8;
  4. the run from the blank tape: its outer boundaries are CO 3 [] (after 13 steps), CO 0 [1,1,2], CO 3 [1,2,1],
     CO 3 [5,1,1], CO 28 [4,1,1] (the next one needs G(28)), and it does not halt in the next 3,000,000 macro steps.
"""
import random
import sys

R18A = ('1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0LQ0LO_'
        '1LR1LP_0LQ1LN_0RO1LB_0LL1RZ')


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


def blocks(ds):
    return '0'.join('1' * d for d in ds)


def co(a, ds):
    s = Sim(R18A)
    for ch in '100':
        Sim.push(s.L, int(ch), 1)
    for ch in reversed('1' * a + '0' + blocks(ds)):
        Sim.push(s.R, int(ch), 1)
    s.st = 'F'; s.face = 'R'
    return s


def at_outer(s):
    return s.st == 'F' and s.face == 'R' and s.L == [[1, 1], [0, 2]]


def read_co(s):
    """(a, ds) of an outer boundary, or None if the right side is not 1^a 0 (list with single 0 gaps)"""
    cells = ''.join(str(sy) * n for sy, n in reversed(s.R)).rstrip('0')
    a = len(cells) - len(cells.lstrip('1'))
    rest = cells[a + 1:]
    if '00' in rest:
        return None
    return a, ([len(b) for b in rest.split('0')] if rest else [])


def next_event(s, cap=10 ** 7):
    first = True
    for _ in range(cap):
        if s.halted:
            return ('HALT', s.ones())
        if not first and at_outer(s):
            return ('CO',) + read_co(s)
        first = False; s.step()
    return ('TIMEOUT',)


# ---- the Coq file's recursion (BB18_R18a.v: h, hc, Gcy, G) ----
def h(m, x, closed=True):
    if m == 0:
        return x + 4
    if m == 1 and closed:
        return 4 * x + 10          # = (x -> x+4)^(x+2) (2); checked against the iteration below
    y = 2
    for _ in range(x + 2):
        y = h(m - 1, y)
    return y


def hc(m, n, x):
    for i in range(n):
        x = h(m + i, x)
    return x


def G(a):
    c, y = divmod(a, 3)
    return hc(1, c, y + 3) + 2 * c + 4


def model(a, ds):
    """one outer round in the write-up's rules"""
    i = 0
    while i < len(ds) and ds[i] == 1:
        i += 1
    if i == len(ds):
        T = a + 2 * len(ds) + 2; c, r = divmod(T, 3)
        return ('HALT', 2 * c + 2) if r == 1 else ('CO', 0, [1, 1] + [2] * c) if r == 2 else ('CO', 0, [1] + [2] * c)
    e = ds[i]
    if i == 0:
        return ('CO', G(a), [e - 1] + ds[1:])
    return ('CO', 3, [1] * (i - 1) + [a + 2, e - 1] + ds[i + 1:])


fails = 0


def report(name, ok, bad):
    global fails
    fails += bad
    print(f'{name}: {ok} ok, {bad} bad', flush=True)


# 1. exhaustion + refill
ok = bad = 0
for a in range(80):
    for n in range(7):
        got, exp = next_event(co(a, [1] * n)), model(a, [1] * n)
        if got == exp:
            ok += 1
        else:
            bad += 1; print('  REFILL MISMATCH', a, n, got, exp)
report('exhaustion + refill of CO a [1^n] (T = a+2n+2; halt iff T = 3c+1, with 2c+2 ones)', ok, bad)

# 2. R1
random.seed(7); ok = bad = 0
for _ in range(400):
    a = random.randint(0, 60); p = random.randint(0, 4); e = random.randint(0, 5)
    rest = [random.randint(1, 4) for _ in range(random.randint(0, 3))]
    ds = [1] * (p + 1) + [e + 2] + rest
    got, exp = next_event(co(a, ds)), model(a, ds)
    if got == exp and exp == ('CO', 3, [1] * p + [a + 2, e + 1] + rest):
        ok += 1
    else:
        bad += 1; print('  R1 MISMATCH', a, ds, got, exp)
report('R1: CO a [1^(p+1),e+2,rest] -> CO 3 [1^p,a+2,e+1,rest]', ok, bad)

# 3. R0 and G
ok = bad = 0
for a in range(6):
    for ds in ([3, 2], [2], [5, 1, 3]):
        got, exp = next_event(co(a, ds)), model(a, ds)
        ok += got == exp; bad += got != exp
        if got != exp:
            print('  R0 MISMATCH', a, ds, got, exp)
report('R0 for a = 0..5: CO a [e+2,rest] -> CO (G a) [e+1,rest]', ok, bad)
g = [G(a) for a in range(9)]
good = all(h(1, x) == h(1, x, False) for x in range(60)) and g[:6] == [7, 8, 9, 28, 32, 36] and all(G(a) % 3 == (a + 1) % 3 for a in range(9))
print(f'G(0..5) = {g[:6]}, G(a) = a+1 mod 3 for a = 0..8:', 'ok' if good else 'BAD')
fails += not good

# 4. the blank-tape run
s = Sim(R18A); evs = []; first13 = None
for _ in range(10 ** 7):
    if at_outer(s):
        if first13 is None:
            first13 = s.steps
        evs.append(('CO',) + read_co(s))
        if len(evs) == 5:
            break
    if s.halted:
        break
    s.step()
want = [('CO', 3, []), ('CO', 0, [1, 1, 2]), ('CO', 3, [1, 2, 1]), ('CO', 3, [5, 1, 1]), ('CO', 28, [4, 1, 1])]
model_ok = all(model(*want[i][1:]) == want[i + 1] for i in range(4))
s.step(); n = 0
while n < 3 * 10 ** 6 and not s.halted:
    s.step(); n += 1
good = evs == want and first13 == 13 and model_ok and not s.halted
print('blank tape: outer boundaries', ' '.join(f'CO {e[1]} {e[2]}' for e in evs), f'(first after {first13} steps);',
      'model agrees' if model_ok else 'MODEL DISAGREES', f'; no halt in the next {n} macro steps ({s.steps} steps):',
      'ok' if good else 'BAD')
fails += not good

print('ALL CHECKS PASSED' if fails == 0 else f'{fails} FAILURES')
sys.exit(1 if fails else 0)
