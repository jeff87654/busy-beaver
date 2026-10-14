"""Independent literal checks for the M13 write-up (own cell-by-cell simulator, nothing imported from the Coq files).
   Run: python m13_writeup_chk.py   (a few seconds). Prints one PASS/FAIL line per check and exits 1 on any failure.

   Configurations (as in BB13_M13.v; "C>" = head on the cell to its right, "<A" = head on the cell to its left):
     Ca(j,b;z)   = 0^inf (10)^j 1^b C> 0 z
     Ch(j,b;z)   = 0^inf (10)^j <A 1^(b+1) 0 z
     Ce(p,a,c,d) = 0^inf (10)^p 1^(a+2) E> (10)^c 0 1^d 0^inf
     end(p,a)    = 0^inf (10)^p 1^(a+5) M> 0^inf          (M reads 0: the halt, M0 = 1RZ)
   z stands for an arbitrary right part; it is instantiated with several finite words followed by 0^inf.
   Checks: the mirrored 1RB form and Argon's core-label form of M13 (search/README.md), the rules CA_SH, CA_SH_iter, CA_EXIT, CA_CH, CH_0, CH_S, CH_CA (= W), BLK_iter, CE_EVEN (= Kc), C_REL,
   D_REL, HALT_step, Kd_step, D_reload, small end-to-end halts with the exact ones count, the start-up
   (steps 116 and 306) and the first two big steps of the real run."""
import random, sys

M = '1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_0LG1RI_1RE0RH_1LF0RC_1RM0LE_1LA1LE_0LL1LB_0RM1LL_1RZ1RH'
TR = {}
for i, row in enumerate(M.split('_')):
    q = 'ABCDEFGHIJKLM'[i]
    for s in (0, 1):
        t = row[3 * s:3 * s + 3]
        TR[(q, s)] = None if t[2] == 'Z' else (int(t[0]), 1 if t[1] == 'R' else -1, t[2])
USED = set()


class Tape:
    def __init__(self, cfg):
        q, left, h, right = cfg
        self.pad = 64
        word = left + h + right
        self.t = bytearray(self.pad) + bytearray(int(x) for x in word) + bytearray(self.pad)
        self.h = self.pad + len(left)
        self.q = q
        self.steps = 0
        self.n1 = sum(self.t)

    def step(self):
        tr = TR[(self.q, self.t[self.h])]
        if tr is None:
            return False
        USED.add((self.q, self.t[self.h]))
        w, d, q = tr
        self.n1 += w - self.t[self.h]
        self.t[self.h] = w
        self.h += d
        self.q = q
        if self.h < 2:
            self.t = bytearray(self.pad) + self.t
            self.h += self.pad
        elif self.h >= len(self.t) - 2:
            self.t += bytearray(self.pad)
        self.steps += 1
        return True

    def canon(self):
        s = ''.join('1' if b else '0' for b in self.t)
        return (self.q, s[:self.h].lstrip('0'), s[self.h], s[self.h + 1:].rstrip('0'))


def canon(cfg):
    q, left, h, right = cfg
    return (q, left.lstrip('0'), h, right.rstrip('0'))


def ones(cfg):
    return sum(x == '1' for x in cfg[1] + cfg[2] + cfg[3])


# ---- configuration builders (cfg = (state, left word, head symbol, right word)) ----
def Ca(j, b, z):
    return ('C', '10' * j + '1' * b, '0', z)


def Ch(j, b, z):
    left = '10' * j
    return ('A', left[:-1], '0', '1' * (b + 1) + '0' + z)


def Er(left, z):           # 0^inf left E> z 0^inf
    z = z or '0'
    return ('E', left, z[0], z[1:])


def Ce(p, a, c, d):
    return Er('10' * p + '1' * (a + 2), '10' * c + '0' + '1' * d)


def End(p, a):
    return ('M', '10' * p + '1' * (a + 5), '0', '')


def blk(a, z):
    return '1' * (a + 1) + '0' + z


# ---- the recursions of BB13_M13.v ----
def W_rec(j, b):
    """W exactly as defined in BB13_M13.v: W 0 b = b + 3, W (j+1) b = (W j)^(b+1) 2."""
    if j == 0:
        return b + 3
    x = 2
    for _ in range(b + 1):
        x = W_rec(j - 1, x)
    return x


def W(j, b):
    """W with closed forms for j <= 2 (checked against W_rec below), so that W 2 of large arguments is cheap."""
    if j == 0:
        return b + 3
    if j == 1:
        return 3 * b + 5
    if j == 2:
        return (27 * 3 ** b - 5) // 2
    x = 2
    for _ in range(b + 1):
        x = W(j - 1, x)
    return x


def Kc(pa):
    p, a = pa
    return (p + a // 2, W(p - 1, 1))


def iterf(n, g, x):
    for _ in range(n):
        x = g(x)
    return x


def Kd_step(pa):
    p, a = pa
    return iterf(a // 2 + 1, Kc, (p - 1, 2))


def D_reload(pa):
    p, a = pa
    return Kc((p - 2, 2))


# ---- driver ----
def reaches(src, dst, plus=True, maxsteps=3 * 10 ** 6):
    """Run from src until the configuration equals dst (relative to the head, blanks trimmed)."""
    T = Tape(src)
    tgt = canon(dst)
    n1 = ones(dst)
    if not plus and T.canon() == tgt:
        return True, 0
    while T.steps < maxsteps:
        if not T.step():
            return False, 'halted at %d' % T.steps
        if T.q == tgt[0] and T.n1 == n1 and T.canon() == tgt:
            return True, T.steps
    return False, 'no match in %d steps' % maxsteps


RES = {}
FAILS = []


def tally(name, ok, info=''):
    a = RES.setdefault(name, [0, 0, 0])
    a[0 if ok else 1] += 1
    if ok and isinstance(info, int):
        a[2] = max(a[2], info)
    if not ok:
        FAILS.append((name, info))


def rule(name, src, dst, plus=True):
    ok, info = reaches(src, dst, plus)
    tally(name, ok, info if not ok else info)


rng = random.Random(13)
ZS = ['', '1', '0', '11', '101', '0110', '1101001', '0011', '111']
for _ in range(6):
    ZS.append(''.join(rng.choice('01') for _ in range(rng.randint(1, 12))))

if __name__ == '__main__':
    # table sanity: 25 defined transitions, M0 is the only halt
    halts = [k for k, v in TR.items() if v is None]
    ok = halts == [('M', 0)] and len(TR) == 26
    print('%s  table: 26 entries, the only undefined/halting one is M0 (1RZ)' % ('PASS' if ok else 'FAIL'))
    if not ok:
        FAILS.append(('table', halts))

    # equivalent forms: the direction mirror (bbchallenge convention A0 = 1RB) and the search's core labels
    def parse(m):
        out = {}
        for i, row in enumerate(m.split('_')):
            for s in (0, 1):
                t = row[3 * s:3 * s + 3]
                out[('ABCDEFGHIJKLM'[i], s)] = None if t[2] == 'Z' else (int(t[0]), t[1], t[2])
        return out
    MIR = '1RB1RA_1LC0RA_1LD1LC_1LE1LK_1LF0RJ_0RG1LI_1LE0LH_1RF0LC_1LM0RE_1RA1RE_0RL1RB_0LM1RL_1RZ1LH'
    CORE = '1RI0LL_1RA1RC_0LD1LG_0RE1LD_1RZ1RF_1LI0RM_1RM0LH_1LG1LH_0LK1RJ_1RE0LA_1RA0RF_1LH1LA_1RB1RM'
    P, PM, PC = parse(M), parse(MIR), parse(CORE)
    okm = all((P[k] is None) == (PM[k] is None) and (P[k] is None or
              PM[k] == (P[k][0], 'L' if P[k][1] == 'R' else 'R', P[k][2])) for k in P)
    t1, t2, h1, h2, q1, q2 = {}, {}, 0, 0, 'A', 'A'          # literal lockstep run of M13 and its mirror
    for _ in range(200000):
        a, b = P[(q1, t1.get(h1, 0))], PM[(q2, t2.get(h2, 0))]
        if a is None or b is None:
            okm = okm and a is None and b is None
            break
        t1[h1], t2[h2] = a[0], b[0]
        h1 += 1 if a[1] == 'R' else -1
        h2 += 1 if b[1] == 'R' else -1
        q1, q2 = a[2], b[2]
        okm = okm and h1 == -h2 and q1 == q2
    okm = okm and {k: v for k, v in t1.items() if v} == {-k: v for k, v in t2.items() if v}
    print('%s  mirror %s: L/R swapped entry by entry; 200000 lockstep steps give the reflected tape'
          % ('PASS' if okm else 'FAIL', MIR))
    rel = dict(zip('ABCDEFGHIJKLM', 'HGMBAIKFJLCDE'))      # M13 state -> core-label state (start state H)
    okc = all((P[k] is None and PC[(rel[k[0]], k[1])] is None) or
              (P[k] is not None and PC[(rel[k[0]], k[1])] == (P[k][0], P[k][1], rel[P[k][2]])) for k in P)
    print('%s  core labels %s (start H) = M13 relabeled A..M -> HGMBAIKFJLCDE' % ('PASS' if okc else 'FAIL', CORE))
    if not (okm and okc):
        FAILS.append(('equivalent forms', (okm, okc)))

    # W closed forms and parity (used in the write-up)
    okW = all(W(0, b) == b + 3 and W(1, b) == 3 * b + 5 for b in range(30)) \
        and all(2 * W(2, b) == 27 * 3 ** b - 5 for b in range(12)) \
        and all(W(j, b) % 2 == (b + 1) % 2 for j in range(3) for b in range(8)) \
        and W(3, 0) == 119 and [W(j, 1) for j in range(3)] == [4, 8, 38]
    print('%s  W: W0 b = b+3, W1 b = 3b+5, 2*W2 b = 27*3^b - 5, W j b = b+1 mod 2, W3 0 = 119, Wj 1 = 4,8,38'
          % ('PASS' if okW else 'FAIL'))
    if not okW:
        FAILS.append(('W', None))

    for z in ZS:
        for j in range(5):
            for b in range(7):
                rule('CA_SH', Ca(j, b, '10' + z), Ca(j + 1, b, z))
                rule('CA_EXIT', Ca(j, b, '0' + z), Er('10' * j + '1' * (b + 2), z))
                rule('CA_CH', Ca(j, b, '11' + z), Ch(j, b, '1' + z))
                rule('CH_S', Ch(j + 1, b, z), Ca(j, 2, blk(b + 1, z)))
            for k in range(5):
                rule('CA_SH_iter', Ca(j, 3, '10' * k + z), Ca(j + k, 3, z), plus=False)
        for b in range(10):
            rule('CH_0', Ch(0, b, z), Ca(0, b + 3, z))
    # CH_CA: Ch j b z ->+ Ca j (W j b) z, for every (j, b) with W j b of moderate size
    for z in ZS[:8]:
        for j, b in [(0, b) for b in range(8)] + [(1, b) for b in range(8)] + [(2, 0), (2, 1), (2, 2), (2, 3), (3, 0)]:
            rule('CH_CA', Ch(j, b, z), Ca(j, W(j, b), z))
        # BLK_iter: Ca j b (blk a z) ->+ Ca (j+1) ((W j)^a b) z
        for j, b, a in [(0, 0, 0), (0, 2, 3), (0, 5, 6), (1, 0, 2), (1, 3, 2), (2, 0, 1), (2, 2, 1), (1, 1, 3)]:
            rule('BLK_iter', Ca(j, b, blk(a, z)), Ca(j + 1, iterf(a, lambda x: W(j, x), b), z))
    # Ce-level rules (right side ends in 0^inf by definition of Ce)
    for pp in range(3):                       # W pp 1 small only for pp <= 2
        for k in range(6):
            for c in range(4):
                for d in range(5):
                    p, a = pp + 1, 2 * k
                    rule('CE_EVEN=Kc', Ce(p, a, c + 1, d), Ce(*Kc((p, a)), c, d))
    for pp in range(6):
        for k in range(6):
            for d in range(5):
                rule('C_REL', Ce(pp + 1, 2 * k, 0, d + 2), Ce(pp, 2, k + 1, d))
        for a in range(12):
            rule('D_REL', Ce(pp + 2, a, 0, 0), Ce(pp, 2, 1, a + 1))
    for p in range(7):
        for a in range(10):
            rule('HALT_step', Ce(p, a, 0, 1), End(p, a))
    for d in range(6):
        rule('Kd_step(2,2)', Ce(2, 2, 0, d + 2), Ce(*Kd_step((2, 2)), 0, d))
    for p in (3, 4, 5):
        for a in (0, 2, 4, 10, 30):
            rule('D_reload', Ce(p, a, 0, 0), Ce(*D_reload((p, a)), 0, a + 1))

    # small end-to-end runs to the halt: exact ones count (before the final write) = p + a + 5 at the end
    e2e = [(Ce(2, 2, 0, 3), Kd_step((2, 2))),            # Kd_step then HALT_step
           (Ce(3, 0, 0, 0), D_reload((3, 0))),           # D_reload (d = a+1 = 1) then HALT_step
           (Ce(4, 0, 0, 0), D_reload((4, 0))),
           (Ce(5, 0, 0, 0), D_reload((5, 0)))]
    for p in range(6):
        for a in range(0, 12, 2):
            e2e.append((Ce(p, a, 0, 1), (p, a)))
    for src, (p, a) in e2e:
        T = Tape(src)
        while T.step():
            if T.steps > 10 ** 7:
                break
        okh = T.q == 'M' and T.t[T.h] == 0 and T.n1 == p + a + 5 and T.canon() == canon(End(p, a))
        tally('halt+ones', okh, T.steps if okh else 'state %s ones %d' % (T.q, T.n1))

    # start-up from the blank tape: init_116, init_306, then C_REL and one Kc of the real run
    T = Tape(('A', '', '0', ''))
    marks = {}
    targets = {canon(Ce(1, 2, 2, 2)): 'Ce(1,2,2,2)', canon(Ce(2, 4, 1, 2)): 'Ce(2,4,1,2)',
               canon(Ce(4, 8, 0, 2)): 'Ce(4,8,0,2)', canon(Ce(3, 2, 5, 0)): 'Ce(3,2,5,0)',
               canon(Ce(4, 38, 4, 0)): 'Ce(4,38,4,0)'}
    while T.steps < 2 * 10 ** 6 and len(marks) < len(targets):
        T.step()
        cn = T.canon() if T.q == 'E' else None
        if cn in targets and targets[cn] not in marks:
            marks[targets[cn]] = T.steps
    print('      start-up landmarks (first time reached):', marks)
    oks = marks.get('Ce(1,2,2,2)') == 116 and marks.get('Ce(4,8,0,2)') == 306 \
        and marks.get('Ce(2,4,1,2)', 10 ** 9) < 306 < marks.get('Ce(3,2,5,0)', 0) < marks.get('Ce(4,38,4,0)', 0)
    tally('start-up', oks, marks.get('Ce(4,38,4,0)', 'missing'))
    print('      next: Ce(23, W3 1, 3, 0) with W3 1 = (27*3^119 - 5)/2 (%d digits): too large to simulate'
          % len(str(W(2, 119))))
    W31 = W(3, 1)                             # = W2(W2 2), with the closed form of W2
    okk = Kc((3, 2)) == (4, 38) and W(2, 2) == 119 and W31 == (27 * 3 ** 119 - 5) // 2 and W31 % 2 == 0
    tally('Kc(3,2)=(4,38),W3 1', okk)

    for nm, (a, b, mx) in RES.items():
        print('%s  %-18s %4d instances ok, %d bad%s' % ('PASS' if b == 0 else 'FAIL', nm, a, b,
                                                         '   (max steps %s)' % mx if mx else ''))
    print('      transitions read during the checks: %d of 25 defined (%s unused)'
          % (len(USED), ', '.join(q + str(s) for (q, s), v in sorted(TR.items()) if v and (q, s) not in USED) or 'none'))
    if FAILS:
        print('FAIL  %d failures, first: %s' % (len(FAILS), FAILS[:5]))
        sys.exit(1)
    print('ALL PASS')
