"""Independent literal checks for the BB(4,3) write-up (own cell-by-cell simulator, standard library only,
   nothing imported from the Coq files).
   Run: python bb43_chk.py   (a few seconds). Prints one PASS/FAIL line per check, ALL PASS at the end, and exits 1
   on any failure.

   Notation (as in ../1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD.md): words are written left to right; "x <Q" = state Q
   with the head on the cell x just left of the marker; "Q> x" = state Q with the head on the cell x just right of it.
     D(a,b,c)  = 0^inf   (11)^a (12)^b 2 2 1 <D (11)^c 0^inf
     D1(a,b,c) = 0^inf 1 (11)^a (12)^b 2 2 1 <D (11)^c 0^inf
   A rule whose left (or right) end is written "L" (or "R") holds for every context on that side: the simulator fills
   that side with an "unknown" symbol and fails if the machine ever reads it. A side written 0^inf is blank.
   Checks: the run from blank (D(2,2,1) at step 80, D(2,1,91) at step 11828), the sweeps and the rules
   P6, R10-R18, R20-R23, R21a, Y, R23z on small parameters, the edge rules R25-R27, the halting rule R28 with its
   tape (4c+18 ones, all consecutive, nothing else), the arithmetic of the score recursion, and that every defined
   transition is read."""
import re
import sys

M = '1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD'
TR = {}
for i, row in enumerate(M.split('_')):
    for s in range(3):
        t = row[3 * s:3 * s + 3]
        TR['ABCD'[i], s] = None if t[2] == 'Z' else (int(t[0]), 1 if t[1] == 'R' else -1, t[2])
U = -1          # unknown context symbol
USED = set()
FAILS = []


def report(name, ok, detail=''):
    print(('PASS ' if ok else 'FAIL ') + name + ('  ' + detail if detail else ''))
    if not ok:
        FAILS.append(name)


# ---------------------------------------------------------------- patterns

def parse(pat, env):
    """pattern -> (cells, head index, state, left default, right default).
    Head index -1 means the last cell of the left context, len(cells) the first cell of the right context."""
    toks = pat.split()
    ends = {'L': U, 'R': U, '0^inf': 0}
    assert toks[0] in ends and toks[-1] in ends, pat
    left, right = ends[toks[0]], ends[toks[-1]]
    cells, head, state = [], None, None
    for t in toks[1:-1]:
        m = re.fullmatch(r'<([A-D])', t)
        if m:
            head, state = len(cells) - 1, m.group(1)
            continue
        m = re.fullmatch(r'([A-D])>', t)
        if m:
            head, state = len(cells), m.group(1)
            continue
        m = re.fullmatch(r'\((\d+)\)\^\{?([^}]+)\}?', t) or re.fullmatch(r'(\d)\^\{?([^}]+)\}?', t)
        if m:
            k = eval(m.group(2), {}, env)
            assert k >= 0, (t, k)
            cells += [int(c) for c in m.group(1)] * k
            continue
        m = re.fullmatch(r'\(?(\d+)\)?', t)
        assert m, t
        cells += [int(c) for c in m.group(1)]
    assert state is not None, pat
    return cells, head, state, left, right


class Machine:
    def __init__(self, cells, head, state, left, right):
        self.t = {i: v for i, v in enumerate(cells)}
        self.n, self.left, self.right = len(cells), left, right
        self.pos, self.q, self.steps = head, state, 0
        self.nz = sum(1 for v in cells if v)        # nonzero cells written so far (a cheap pre-test for matches)

    def read(self, p):
        if p in self.t:
            return self.t[p]
        return self.left if p < 0 else (self.right if p >= self.n else 0)

    def step(self):
        """one step; returns 'ok', 'halt' (the halting transition, applied) or 'unknown' (read the context)."""
        s = self.read(self.pos)
        if s == U:
            return 'unknown'
        USED.add((self.q, s))
        tr = TR[self.q, s]
        if tr is None:
            self.nz += self.read(self.pos) == 0
            self.t[self.pos] = 1     # C0 = 1RZ: write 1, then halt
            self.steps += 1
            return 'halt'
        w, d, q = tr
        self.nz += (w != 0) - (s != 0)
        self.t[self.pos] = w
        self.pos += d
        self.q = q
        self.steps += 1
        return 'ok'

    def window(self):
        ps = list(self.t) + [self.pos]
        return min(ps), max(ps)


def canon_blank(m):
    """translation-invariant form of a configuration on a blank-ended tape"""
    lo, hi = m.window()
    cells = [m.read(p) for p in range(lo, hi + 1)]
    h = m.pos - lo
    a, b = 0, len(cells) - 1
    while a < h and cells[a] == 0:
        a += 1
    while b > h and cells[b] == 0:
        b -= 1
    return m.q, tuple(cells[a:b + 1]), h - a


def matches(m, rhs, nz, canon):
    cells, head, state, left, right = rhs
    if m.q != state or m.nz != nz:
        return False
    if left == 0 and right == 0:
        return canon_blank(m) == canon
    if left == U and right == U:
        assert len(cells) == m.n, 'rule changes the word length between two unknown contexts'
        shift = 0
    elif left == U:
        shift = 0                       # anchored at the left context
    else:
        shift = m.n - len(cells)        # anchored at the right context
    if m.pos != head + shift:
        return False
    lo, hi = m.window()
    lo, hi = min(lo, shift), max(hi, shift + len(cells) - 1)
    for p in range(lo, hi + 1):
        i = p - shift
        want = cells[i] if 0 <= i < len(cells) else (left if i < 0 else right)
        if m.read(p) != want:
            return False
    return True


def run_rule(lhs, rhs, env, maxsteps=2 * 10 ** 6):    # the largest instance (R21, b = 4) takes 781,884 steps
    L, R = parse(lhs, env), parse(rhs, env)
    assert (L[3], L[4]) == (R[3], R[4]), (lhs, rhs)
    m = Machine(*L)
    nz = sum(1 for v in R[0] if v)
    canon = canon_blank(Machine(*R)) if (R[3], R[4]) == (0, 0) else None
    while m.steps < maxsteps:
        if matches(m, R, nz, canon):
            return 'OK', m.steps
        r = m.step()
        if r != 'ok':
            return r, m.steps
    return 'no match', m.steps


def check_rule(name, lhs, rhs, envs):
    bad = []
    for env in envs:
        res, n = run_rule(lhs, rhs, env)
        if res != 'OK':
            bad.append(({k: x for k, x in env.items() if isinstance(x, int)}, res, n))
    report(f'{name}: {lhs}  ->  {rhs}', not bad,
           f'{len(envs)} instances' if not bad else f'failures {bad[:3]}')


# ---------------------------------------------------------------- functions of the analysis

def g(b): return 2 * b + 5


def iterate(f, n, x):
    for _ in range(n):
        x = f(x)
    return x


def f1(b): return iterate(g, b + 3, 1)


def D(a, b, c): return f'0^inf (11)^{a} (12)^{b} 2 2 1 <D (11)^{c} 0^inf'


def D1(a, b, c): return f'0^inf 1 (11)^{a} (12)^{b} 2 2 1 <D (11)^{c} 0^inf'


def main():
    # 1. the run from blank
    targets = {80: D(2, 2, 1), 11828: D(2, 1, 91)}
    want = {canon_blank(Machine(*parse(p, {}))): n for n, p in targets.items()}
    m = Machine([], 0, 'A', 0, 0)
    seen = {}
    while m.steps <= 11828:
        c = canon_blank(m)
        if c in want and c not in seen:
            seen[c] = m.steps
        if m.step() != 'ok':
            break
    for c, n in want.items():
        report(f'blank tape, state A reaches {targets[n]} first at step {n}', seen.get(c) == n,
               f'first seen at step {seen.get(c)}')

    # 2. sweeps and basic rules (any left context L; right context R or 0^inf)
    ns = [dict(n=n) for n in range(6)]
    ab = [dict(a=a) for a in range(6)]
    bb = [dict(b=b) for b in range(6)]
    check_rule('D_22', 'L D> 2^n R', 'L 2^n D> R', ns)
    check_rule('D_11', 'L D> (11)^n R', 'L (21)^n D> R', ns)
    check_rule('A_11', 'L A> (11)^n R', 'L (12)^n A> R', ns)
    check_rule('B_11', 'L B> (11)^n R', 'L (11)^n B> R', ns)
    check_rule('C_21', 'L (21)^n <C R', 'L <C (11)^n R', ns)
    check_rule('A_12', 'L (12)^n <A R', 'L <A (11)^n R', ns)
    check_rule('P6', 'L A> (11)^a 0 0 R', 'L <A (11)^{a+1} R', ab)
    check_rule('R10', 'L 2 <D (11)^{a+1} 0 0 R', 'L <D (11)^{a+2} 2 R', ab)
    check_rule('R11', 'L 2 <D (11)^a 2 0 0 R', 'L <D (11)^{a+1} 2 2 R', ab)
    check_rule('R12', 'L 1 <A (11)^b 0 0 R', 'L <A (11)^{b+1} 2 R', bb)
    check_rule('R13', 'L 1 <A (11)^b 2 0 0 R', 'L <A (11)^{b+1} 2 2 R', bb)
    check_rule('R14', 'L 1 2 1 <D (11)^b 0 0 R', 'L 1 <D (11)^{b+2} R', bb)
    check_rule('R15', 'L (12)^a 1 <D (11)^b 0^inf', 'L 1 <D (11)^{b+2*a} 0^inf',
               [dict(a=a, b=b) for a in range(5) for b in range(5)])
    check_rule('R16', 'L 1 2 2 1 <D (11)^b 0^inf', 'L 2 (12)^{b+2} 1 <D (11) 0^inf', bb)
    check_rule('R17', 'L 1 2 2 1 <D (11)^b 0^inf', 'L 2 1 <D (11)^{2*b+5} 0^inf', bb)
    check_rule('R18', 'L (12)^a 2 1 <D (11)^b 0^inf', 'L 2 1 <D (11)^{it(a,b)} 0^inf',
               [dict(a=a, b=b, it=lambda a, b: iterate(g, a, b)) for a in range(5) for b in range(4)])
    check_rule('R20', 'L 1 <D (11)^{b+1} 2 0^inf', 'L 2 1 <D (11)^{2*b+1} 0^inf', bb)
    check_rule('R21a', 'L 2 2 1 <D (11)^b 0^inf', 'L 2 <D (11)^{b+2} 0^inf', bb)
    check_rule('R22', 'L 1 <D (11)^{b+1} 2 2 0^inf', 'L 2 (12)^b 2 1 <D (11) 0^inf', bb)
    check_rule('Y', 'L 1 1 1 <D (11)^b 0^inf', 'L 1 <A (11)^{b+2} 0^inf', bb)
    check_rule('R23z', 'L 1 <A (11)^b 2 2 0^inf', 'L (12)^b 2 2 1 <D (11) 0^inf', bb)

    # 3. the two working rules
    check_rule('R21', 'L (12) 2 2 1 <D (11)^b 0^inf', 'L 2 2 1 <D (11)^{f(b)} 0^inf',
               [dict(b=b, f=f1) for b in range(5)])
    check_rule('R23', 'L (11)^3 2 2 1 <D (11)^b 0^inf', 'L (12)^{2*b+11} 2 2 1 <D (11) 0^inf', bb)

    # 4. the left-edge rules
    cs = range(8)
    check_rule('R25', D(2, 0, 'c'), D1('2*c+8', 3, 1), [dict(c=c) for c in cs])
    check_rule('R26', D1(1, 0, 'c'), D1('2*c+7', 3, 1), [dict(c=c) for c in cs])
    check_rule('R27', D1(0, 0, 'c'), D('2*c+5', 3, 1), [dict(c=c) for c in cs])

    # 5. the halt: D(1,0,c) reaches C on a blank with exactly 1^(4c+17) to its right (blank elsewhere); C0 = 1RZ
    #    writes one more 1, so the final tape is 1^(4c+18) and nothing else.
    bad = []
    for c in range(12):
        m = Machine(*parse(D(1, 0, c), {}))
        r, before = 'ok', None
        while r == 'ok' and m.steps < 10 ** 7:
            if m.q == 'C' and m.read(m.pos) == 0:
                before = canon_blank(m)
            r = m.step()
        lo, hi = m.window()
        cells = [m.read(p) for p in range(lo, hi + 1)]
        word = ''.join(map(str, cells)).strip('0')
        if r != 'halt' or before != ('C', (0,) + (1,) * (4 * c + 17), 0) or word != '1' * (4 * c + 18):
            bad.append((c, r, word[:40]))
    report('R28: D(1,0,c) halts; before the halt C reads 0 with 1^(4c+17) to its right; final tape 1^(4c+18)',
           not bad, 'c = 0..11' if not bad else f'failures {bad[:3]}')

    # 6. arithmetic of the score recursion (no large G-iterate is evaluated)
    ok = all(f1(b) == 3 * 2 ** (b + 4) - 5 for b in range(60))
    report('f1(b) = g^(b+3)(1) = 3*2^(b+4) - 5, b < 60', ok)
    e1 = f1(f1(1))                       # v = f1(e1) is far too large to evaluate; only its residue is used
    report('f1(1) = 91, e1 = f1(91) = 3*2^95 - 5, e1 + 5 = 6*2^94', f1(1) == 91 and e1 == 3 * 2 ** 95 - 5)
    report('k1 = (2 e1 + 7)/3 = 2^96 - 1 and 2 e1 + 8 = 3 k1 + 1',
           (2 * e1 + 7) // 3 == 2 ** 96 - 1 and 2 * e1 + 8 == 3 * (2 ** 96 - 1) + 1)
    report('e1 = 1 (mod 3); f1(b) = 3*2^(b+4) - 5 = 1 (mod 3) for b < 60 (so v = f1(e1) = 1 and G(c) = 1 (mod 3))',
           e1 % 3 == 1 and all(f1(b) % 3 == 1 for b in range(60)))
    report('2^96 = 7.92e28 (to three digits)', f'{2 ** 96:.2e}' == '7.92e+28', f'{2 ** 96:.4e}')
    # if x = 1 (mod 3): 2x+7 = 0 and 2x+5 = 1 (mod 3), so the three cascades are D1(3k+1) -> D1(1), D1(3k) -> D1(0),
    # D(3k+1) -> D(1)
    report('x = 1 (mod 3) => 2x+8 = 1, 2x+7 = 0, 2x+5 = 1 (mod 3)',
           all((2 * x + 8) % 3 == 1 and (2 * x + 7) % 3 == 0 and (2 * x + 5) % 3 == 1 for x in range(1, 300, 3)))

    # 7. coverage
    defined = {k for k, t in TR.items() if t is not None} | {('C', 0)}
    report('every transition (including the halt C0) is read by some check', defined <= USED,
           f'unread: {sorted(defined - USED)}')

    print('ALL PASS' if not FAILS else f'{len(FAILS)} FAILED: {FAILS}')
    sys.exit(1 if FAILS else 0)


if __name__ == '__main__':
    main()
