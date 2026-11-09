"""Independent check of the B21 write-up's rules on the machine string (no Coq files used).

    python b21_writeup_chk.py          (about 30 seconds)

B21 = Racheline's BB(21) champion (bbchallenge wiki). The simulator below is exact: it runs the transition table
parsed from the string, and only jumps over a run of equal cells when the machine stays in the same state and
direction over it (a same-state run).
A boundary:  0^inf <A B0 00 B1 00 B2 ...   (state A at the left end, facing left). A block is a list of digits
written as runs of 1s separated by single 0s: [3,1,2] is 111 0 1 0 11. E = an all-1-digit block of length >= 2,
P = the lone block [1].  J configuration: 0^inf (left part) 1^x 0 J> (right part), x = the J accumulator.
Checks (the rules of BB21/README.md; the Coq file BB21_B21_absdef.v transcribes the same rules):
  1. 1200 random sweeps (J configuration -> next A boundary): strip one digit of each E passed (acc + 2 each),
     then act on the first non-E block T: decrement with X(acc) merged into the block on its left, one in-block
     engine step, or P -> X(acc+2) when the next block is [2];
  2. the level-1 engine on 300 random B0 lists: J leaves B0 with exit accumulator A + 3, A from the H recursion;
  3. the final sweep + refill on 24 cases: acc = 0 mod 4 halts, acc = 2 mod 4 appends ",4,1" to the last block
     and (acc-2)/4 lone [2] blocks;
  4. 9 large cases: refill, then the next phase sweep by sweep until its first deep engine run;
  5. the boot: the blank tape reaches the A boundary [1,1,4,1,2] 00 [1] after 162 steps;
  6. the residue schedule of the write-up (2-adic, mod 2^64): the deep exit accumulator is d = -4/3, the refill at
     the end of phase p has acc d + 2 N_p, N_(p+1) = N_p - 1 + (acc - 2)/4: refills #3 to #5 continue, #6 halts.
"""
import random
import re
import sys

B21 = ('0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_'
       '0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LR')


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


def cells_of(spec):
    """'3,1|2' -> 111 0 1 00 11"""
    out = ''
    for t in re.findall(r'\d+|,|\|', spec):
        out += '0' if t == ',' else '00' if t == '|' else '1' * int(t)
    return out


def spec(bs):
    return '|'.join(','.join(str(d) for d in b) for b in bs)


def build(left, st, right, face):
    s = Sim(B21)
    for ch in left:
        Sim.push(s.L, int(ch), 1)
    for ch in reversed(right):
        Sim.push(s.R, int(ch), 1)
    s.st = st; s.face = face
    return s


def jconfig(m, x, R):
    return build('10' * m + '1' * x + '0', 'J', cells_of(spec(R)), 'R')


def atA(s):
    return s.st == 'A' and s.face == 'L' and not s.L


def right_cells(s):
    return ''.join(str(a) * n for a, n in reversed(s.R)).rstrip('0')


def episode(s, cap=10 ** 8):
    """run to the next A boundary (or the halt)"""
    for _ in range(cap):
        if s.halted:
            return 'HALT'
        if atA(s):
            return 'A'
        s.step()
    return 'TIMEOUT'


# ---- the write-up's block rules ----
def X(x):
    if x == 4:
        return [5]
    if x == 6:
        return [4, 2]
    k = (x - 2) // 2
    return [4] + [1] * (k - 2) + [2]


def estep(L):
    x = L[0]; i = 1
    while L[i] == 1:
        i += 1
    p, e = i - 1, L[i]
    if p == 0:
        return [x + 4, e - 1] + L[i + 1:]
    return [1] * p + [x + 4, e - 1] + L[i + 1:]


def is_E(b):
    return len(b) >= 2 and all(d == 1 for d in b)


def sweep(m, x, R):
    """J configuration with m passed B0 digits and acc x, blocks R on the right -> ('A', blocks) or ('REFILL_P', ...)"""
    i = 0
    while i < len(R) and is_E(R[i]):
        i += 1
    xp = x + 2 * i
    out = [[1] * m] + [[1] * (len(e) - 1) for e in R[:i]]
    T, rest = R[i], R[i + 1:]
    if T[0] >= 2:
        out[-1] = out[-1] + X(xp)
        return ('A', out + [[T[0] - 1] + T[1:]] + rest)
    if len(T) > 1:
        return ('A', out + [estep([xp - 1] + T[1:])] + rest)
    if not rest:
        return ('REFILL_P', out, xp + 2)
    assert rest[0] == [2]
    return ('A', out + [X(xp + 2), [1]] + rest[1:])


def refill_P(out, x):
    if x % 4 == 0:
        return ('HALT',)
    return ('A', out[:-1] + [out[-1] + [4, 1]] + [[2]] * ((x - 2) // 4))


def bstep(bs):
    if not all(d == 1 for d in bs[0]):
        return ('ENGINE',)
    r = sweep(len(bs[0]) - 1, 4, bs[1:])
    return r if r[0] == 'A' else refill_P(r[1], r[2])


def H(i, x):
    """engine level maps: H_2(x) = x+4, H_i(x) = H_(i-1)^(x+3)(1)"""
    if i == 2:
        return x + 4
    y = 1
    for _ in range(x + 3):
        y = H(i - 1, y)
        if y > 10 ** 6:
            raise OverflowError
    return y


def eng(L):
    x = L[0]
    for k, d in enumerate(L[1:], start=2):
        for _ in range(d - 1):
            x = H(k, x)
            if x > 10 ** 6:
                raise OverflowError
    return x


fails = 0


def report(name, ok, bad):
    global fails
    fails += bad
    print(f'{name}: {ok} ok, {bad} bad', flush=True)


# 1. sweeps
random.seed(1); ok = bad = 0
while ok + bad < 1200:
    m = random.randint(1, 40); Es = [random.randint(2, 30) for _ in range(random.choice([0, 0, 1, 2, 3, 5]))]
    x = 2 * random.randint(2, 60); typ = random.choice(['dec', 'dec_tail', 'w1', 'P2'])
    if typ == 'dec':
        T = [random.randint(2, 9)]
    elif typ == 'dec_tail':
        T = [random.randint(2, 9)] + [random.choice([1, 1, 2, 3, 7]) for _ in range(random.randint(1, 6))]
    elif typ == 'w1':
        T = [1] + [random.choice([1, 1, 2, 3, 7]) for _ in range(random.randint(1, 6))]
        if all(d == 1 for d in T):
            T[-1] = 2
    else:
        T = [1]
    rest = [[2]] + random.choice([[], [[2]], [[2], [2]]]) if typ == 'P2' else [[2], [1, 3, 1]][:random.randint(0, 2)]
    R = [[1] * e for e in Es] + [T] + rest
    pred = sweep(m, x, R)
    s = jconfig(m, x, R); k = episode(s)
    if k == 'A' and right_cells(s) == cells_of(spec(pred[1])).rstrip('0'):
        ok += 1
    else:
        bad += 1; print('  SWEEP MISMATCH', typ, m, x, spec(R)[:120])
report('sweeps (E strips, decrement + X(acc), in-block engine step, P -> X(acc+2))', ok, bad)

# 2. level-1 engine
random.seed(2); ok = bad = 0
while ok + bad < 300:
    n = random.randint(1, 6)
    L = [random.randint(1, 12)] + [random.choice([1, 1, 1, 2, 2, 3]) for _ in range(n - 1)]
    rest = random.choice(['', '|2', '|1|2', '|1,1,1|3,1'])
    try:
        A = eng(L)
    except OverflowError:
        continue
    s = build('', 'A', cells_of(spec([L]) + rest), 'L')
    for _ in range(10 ** 7):
        if s.st == 'J' and s.face == 'R':
            break
        s.step()
    left = ''.join(str(a) * c for a, c in s.L)
    if left == '10' * (n - 1) + '1' * (A + 3) + '0' and right_cells(s) == cells_of(rest[1:]):
        ok += 1
    else:
        bad += 1; print('  ENGINE MISMATCH', L, rest, A)
report('level-1 engine (exit accumulator A + 3, B0 left as n-1 single digits)', ok, bad)

# 3. final sweep + refill
ok = bad = 0
for x in (40, 42, 44, 46, 48, 50):
    for Es in ([], [9], [9, 7], [12, 9, 7, 5]):
        R = [[1] * e for e in Es] + [[1]]
        r = sweep(20, x, R); pr = refill_P(r[1], r[2])
        s = jconfig(20, x, R); k = episode(s)
        good = (k == 'HALT') if pr[0] == 'HALT' else (k == 'A' and right_cells(s) == cells_of(spec(pr[1])).rstrip('0'))
        ok += good; bad += not good
        if not good:
            print('  REFILL MISMATCH', x, Es, k)
report('final sweep + refill (halt iff acc = 0 mod 4)', ok, bad)

# 4. refill and the next phase, sweep by sweep, until the first deep engine run
ok = bad = 0
for m0, x, Es in [(200, 40, [80, 40, 20]), (200, 42, [80, 40, 20]), (300, 60, [120, 60, 30, 15, 8]),
                  (300, 62, [120, 60, 30, 15, 8]), (150, 44, [60]), (400, 100, [150, 90, 50, 25, 12, 6]),
                  (400, 98, [150, 90, 50, 25, 12, 6]), (100, 40, []), (30, 40, [20, 10])]:
    R = [[1] * e for e in Es] + [[1]]
    r = sweep(m0, x, R); pr = refill_P(r[1], r[2]); s = jconfig(m0, x, R); nsw = 0
    if pr[0] == 'HALT':
        good = episode(s) == 'HALT'
    else:
        bs = pr[1]; good = False
        while True:
            if episode(s) != 'A' or right_cells(s) != cells_of(spec(bs)).rstrip('0'):
                break
            nsw += 1; nb = bstep(bs)
            if nb[0] == 'ENGINE':
                good = True; break
            bs = nb[1]; s.step()
    ok += good; bad += not good
    print(f'  m0={m0} x={x} Es={Es}: {"halt" if pr[0] == "HALT" else f"{nsw} A boundaries agree"}',
          'ok' if good else 'MISMATCH', flush=True)
report('refill + next phase until its first deep engine run', ok, bad)

# 5. boot
s = Sim(B21); want = cells_of('1,1,4,1,2|1'); at = None
while s.steps < 10 ** 4 and not s.halted:
    if atA(s) and right_cells(s) == want:
        at = s.steps; break
    s.step()
print('boot: A boundary [1,1,4,1,2] 00 [1] after', at, 'steps:', 'ok' if at == 162 else 'BAD')
fails += at != 162

# 6. residue schedule
M = 1 << 64
d = (-4 * pow(3, -1, M)) % M
N, p, res = 1, 3, None
while p < 30:
    x = (d + 2 * N) % M
    if x % 4 == 0:
        res = p; break
    N = (N - 1 + ((x - 2) % M >> 2)) % (M >> 2); p += 1
print('residue schedule: refills #3 ..', res - 1 if res else '?', 'continue, the machine halts at refill #', res, ':',
      'ok' if res == 6 else 'BAD')
fails += res != 6

print('ALL CHECKS PASSED' if fails == 0 else f'{fails} FAILURES')
sys.exit(1 if fails else 0)
