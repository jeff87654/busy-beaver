"""Independent check of the J19 write-up's rules on the machine string (no Coq files used).

    python j19_writeup_chk.py          (well under a minute)

J19 = Jacobzheng's BB(19) champion (bbchallenge wiki). The simulator below is exact: it runs the transition table
parsed from the string, and only jumps over a run of equal cells when the machine stays in the same state and
direction over it (a same-state run). Lists are blocks of 1s separated by single 0s; [a, b, c] is 1^a 0 1^b 0 1^c.
Checks:
  1. the boot: from the blank tape the machine reaches the outer boundary Kbnd [2,2] (K on the 0 left of the list);
  2. engine sweeps on 400 random level-1 lists with random outer tails (E0, E1 and the exit rule);
  3. the expansion of the outer head a = 1..30 into a level-1 list (three tails each);
  4. the refill for M = 1..59 (M odd: the new outer list [2,1^((M+1)/2),2]; M even: halt with M/2 + 2 ones
     on the tape when the halting slot is read, so sigma = M/2 + 3);
  5. the outer-round model (R0 via G, R1, exhaustion, refill) against the machine on 159 crafted outer lists,
     up to 12 rounds each, and on the first rounds from the blank tape.
"""
import random
import sys

J19 = ('1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_'
       '1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR')


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


def build(left, st, right, face):
    s = Sim(J19)
    for ch in left:
        Sim.push(s.L, int(ch), 1)
    for ch in reversed(right):
        Sim.push(s.R, int(ch), 1)
    s.st = st; s.face = face
    return s


def lst(ds):
    return '0'.join('1' * d for d in ds)


# ---- the model of the write-up ----
def eng_step(ds):
    """E0 [x,e,r] -> [x+4,e-1,r];  E1 [x,1^p,e,r] -> [2,1^(p-1),x+3,e-1,r];  exit [x,1^n] -> x+2n+3"""
    x = ds[0]; i = 1
    while i < len(ds) and ds[i] == 1:
        i += 1
    if i == len(ds):
        return ('K', x + 2 * (len(ds) - 1) + 3)
    p, e, r = i - 1, ds[i], ds[i + 1:]
    return ('H', [x + 4, e - 1] + r) if p == 0 else ('H', [2] + [1] * (p - 1) + [x + 3, e - 1] + r)


def expand(a):
    """the level-1 list the outer head a expands into: [4,1,2^q] (a = 1 mod 3) or [7,1,2^q], q = (a-1) div 3"""
    q = (a - 1) // 3
    return ([4] if a % 3 == 1 else [7]) + [1] + [2] * q


class Big(Exception):
    pass


def G(a, cap):
    l = expand(a)
    while True:
        r = eng_step(l)
        if r[0] == 'K':
            return r[1]
        l = r[1]
        if l[0] > cap:
            raise Big()


def oround(O, cap):
    """R0 [a,e,r] -> [G a,e-1,r];  R1 [a,1^p,e,r] -> [6,1^(p-1),a+1,e-1,r];  EX [a,1^n] -> M = a+2n+1"""
    i = 1
    while i < len(O) and O[i] == 1:
        i += 1
    if i == len(O):
        return ('M', O[0] + 2 * (len(O) - 1) + 1)
    p, a, e = i - 1, O[0], O[i]
    if p == 0:
        return [G(a, cap), e - 1] + O[i + 1:]
    return [6] + [1] * (p - 1) + [a + 1, e - 1] + O[i + 1:]


def refill(M):
    return ('HALT', M // 2 + 2) if M % 2 == 0 else [2] + [1] * ((M + 1) // 2) + [2]


def strip0(l):
    return [d for d in l if d > 0]


fails = 0


def report(name, ok, bad):
    global fails
    fails += bad
    print(f'{name}: {ok} ok, {bad} bad', flush=True)


# 1. boot
s = Sim(J19)
while s.st != 'K' and not s.halted:
    s.step()
boot = [n for sy, n in reversed(s.R) if sy == 1]
gaps = [n for sy, n in reversed(s.R) if sy == 0]
good = s.face == 'L' and not s.L and boot == [2, 2] and gaps == [1, 1]
print(f'boot: K boundary after {s.steps} steps, list {boot}:', 'ok' if good else 'BAD')
fails += not good

# 2. engine sweeps
random.seed(11); ok = bad = 0
for _ in range(400):
    n = random.randint(1, 6)
    ds = [random.choice([1, 2, 3, 5, 6, 7, 9, 10, 14])] + [random.choice([1, 1, 1, 2, 3, 4, 5]) for _ in range(n - 1)]
    outer = [random.randint(1, 7) for _ in range(random.randint(1, 4))]
    exp = eng_step(ds)
    s = build('', 'H', lst(ds) + '00' + lst(outer), 'L'); first = True; got = None
    for _ in range(10 ** 6):
        if s.halted:
            got = ('HALT',); break
        if not first and s.st == 'H' and s.face == 'L' and not s.L:
            runs = list(reversed(s.R)); bl = [n for sy, n in runs if sy == 1]; gp = [n for sy, n in runs if sy == 0]
            k = gp.index(2)
            got = ('H', bl[:k + 1], bl[k + 1:]) if all(g == 1 for i, g in enumerate(gp) if i != k) else ('GAP',)
            break
        if s.st == 'K':
            runs = list(reversed(s.R)); bl = [n for sy, n in runs if sy == 1]; gp = [n for sy, n in runs if sy == 0]
            got = ('K', bl[0], bl[1:]) if not s.L and all(g == 1 for g in gp) else ('KBAD',)
            break
        first = False; s.step()
    if got == (exp[0], exp[1], outer):
        ok += 1
    else:
        bad += 1; print('  MISMATCH', ds, outer, exp, got)
report('engine sweeps (E0, E1, exit)', ok, bad)

# 3. expansion
ok = bad = 0
for a in range(1, 31):
    for tail in ([3], [2, 1], [5, 2, 1]):
        s = build('', 'K', '0' + lst([a] + tail), 'L'); first = True; got = None
        for _ in range(10 ** 6):
            if not first and s.st == 'H' and s.face == 'L' and not s.L:
                runs = list(reversed(s.R)); bl = [n for sy, n in runs if sy == 1]; gp = [n for sy, n in runs if sy == 0]
                k = gp.index(2)
                if all(g == 1 for i, g in enumerate(gp) if i != k):
                    got = (bl[:k + 1], bl[k + 1:])
                break
            first = False; s.step()
        if got == (expand(a), strip0([tail[0] - 1] + tail[1:])):
            ok += 1
        else:
            bad += 1; print('  EXPANSION MISMATCH', a, tail, got)
report('expansion of the outer head a = 1..30', ok, bad)

# 4. refill
ok = bad = 0
for M in range(1, 60):
    s = build('1', 'K', '0' + lst([M]), 'L'); first = True
    for _ in range(10 ** 6):
        if s.halted or (not first and s.st == 'K'):
            break
        first = False; s.step()
    exp = refill(M)
    if isinstance(exp, tuple):
        good = s.halted and s.ones() == exp[1]
    else:
        bl = [n for sy, n in reversed(s.R) if sy == 1]; gp = [n for sy, n in reversed(s.R) if sy == 0]
        good = not s.halted and not s.L and bl == exp and all(g == 1 for g in gp)
    ok += good; bad += not good
    if not good:
        print('  REFILL MISMATCH', M)
report('refill M = 1..59 (halt iff M even, with M/2 + 2 ones)', ok, bad)


# 5. outer rounds, model vs machine
def machine_rounds(s, nrounds):
    out = []; first = True
    for _ in range(3 * 10 ** 6):
        if s.halted:
            out.append(('HALT', s.ones())); return out
        if s.st == 'K' and not first:
            R = [n for sy, n in reversed(s.R) if sy == 1]
            out.append(('M', R) if s.L else ('L', R))
            if len(out) >= nrounds:
                return out
        first = False; s.step()
    out.append(('TIMEOUT',)); return out


def model_rounds(O, nrounds):
    out = []
    for _ in range(nrounds):
        try:
            r = oround(O, cap=200)
        except Big:
            return out
        if isinstance(r, tuple):
            out.append(('M', [r[1]])); r2 = refill(r[1])
            if isinstance(r2, tuple):
                out.append(('HALT', r2[1])); return out
            O = r2
        else:
            O = r
        out.append(('L', O))
    return out


random.seed(7); ok = bad = 0
cases = [[2, 2], [1, 1], [3], [2, 1, 2], [4, 2], [6, 2, 1], [2, 1, 1, 2], [5, 1, 3], [3, 2, 2]]
for _ in range(150):
    n = random.randint(1, 4)
    cases.append([random.randint(1, 6)] + [random.choice([1, 1, 2, 3]) for _ in range(n - 1)])
for O in cases:
    mo = model_rounds(O, 12)
    if not mo:
        continue
    ma = machine_rounds(build('', 'K', '0' + lst(O), 'L'), len(mo))
    if ma[:len(mo)] == mo:
        ok += 1
    else:
        bad += 1; print('  ROUND MISMATCH', O, mo, ma)
report('outer rounds on crafted lists (up to 12 rounds each)', ok, bad)
# from the blank tape: the model runs until a head value passes the cap (then G is too large to evaluate)
mo = [('L', [2, 2])] + model_rounds([2, 2], 40)
ma = machine_rounds(Sim(J19), len(mo))
agree = sum(1 for x, y in zip(ma, mo) if x == y)
print(f'blank tape: {agree} of the first {len(mo)} K boundaries agree with the model:',
      ' '.join(f'{x[0]}{x[1]}' for x in ma[:5]), '...', flush=True)
fails += agree != len(mo) or len(mo) < 10

print('ALL CHECKS PASSED' if fails == 0 else f'{fails} FAILURES')
sys.exit(1 if fails else 0)
