"""Independent literal checks for the M14 write-up (own cell-by-cell simulator, not derived from the Coq file).

Every configuration family and rule of section 1 of the write-up is instantiated on concrete values (the
arbitrary tails z, r, y with random words) and the machine is run until it reaches the predicted configuration
exactly (same state, same head position, same tape). Also checks the start-up (steps 26 / 578 / 801), the
D_reload instances that are small enough to run, the halting configuration and its ones count, and that the
visit-order (TNF) relabelling of the machine runs in lockstep with it.

Run: python m14_writeup_chk.py   (a few seconds). Prints PASS/FAIL lines; exit code 1 on any failure.
"""
import random
import sys

M = '1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN'
STATES = 'ABCDEFGHIJKLMN'
TR = {}
for i, row in enumerate(M.split('_')):
    for s in (0, 1):
        t = row[3 * s:3 * s + 3]
        TR[(STATES[i], s)] = None if t[2] == 'Z' else (int(t[0]), 1 if t[1] == 'R' else -1, t[2])
HALT_TR = (1, 1)  # J0 = 1RZ: the halting transition writes 1 (on a 0)


class Run:
    """Tape = set of positions holding 1; everything else is 0."""

    def __init__(self, cfg):
        q, ones = cfg
        self.q, self.h, self.t, self.steps = q, 0, set(ones), 0

    def step(self):
        tr = TR[(self.q, 1 if self.h in self.t else 0)]
        if tr is None:
            return False
        w, d, q = tr
        if w:
            self.t.add(self.h)
        else:
            self.t.discard(self.h)
        self.h += d
        self.q = q
        self.steps += 1
        return True

    def cfg(self):
        return self.q, frozenset(p - self.h for p in self.t)


def R(q, left, right):
    """Head on right[0] (state q, about to read it); left/right are finite words, 0 beyond."""
    right = right or '0'
    w = left + right
    h = len(left)
    return q, frozenset(i - h for i, c in enumerate(w) if c == '1')


def Lh(q, left, right):
    """Head on the last cell of left (the '<q' form of busycoq)."""
    left = left or '0'
    return R(q, left[:-1], left[-1] + right)


def reach(src, dst, maxsteps=10 ** 7, exact_steps=None):
    """Run from src until the configuration equals dst (>= 1 step). Returns step count or None."""
    r = Run(src)
    n1 = len(dst[1])
    while r.steps < maxsteps:
        if not r.step():
            return None
        if r.q == dst[0] and len(r.t) == n1 and r.cfg() == dst:
            if exact_steps is not None and r.steps != exact_steps:
                continue
            return r.steps
    return None


# ---- configuration families (write-up section 1.1; Coq names in brackets) ----
def Ca(j, b, z):          # 0^inf (10)^j 1^b  A> 0 z
    return R('A', '10' * j + '1' * b, '0' + z)


def Ch(j, b, z):          # 0^inf (10)^j <H 1^(b+1) 0 z
    return Lh('H', '10' * j, '1' * (b + 1) + '0' + z)


def Ch0(j, c, d):         # 0^inf (10)^j <H 0 0 1^c 0 1^d 0^inf
    return Lh('H', '10' * j, '00' + '1' * c + '0' + '1' * d)


def Ci(p, a, c, d):       # 0^inf (10)^p 1^(a+1)  I> 1^c 0 1^d 0^inf
    return R('I', '10' * p + '1' * (a + 1), '1' * c + '0' + '1' * d)


def blk(a, z):            # 1^(a+1) 0 z
    return '1' * (a + 1) + '0' + z


def c_end(p, a):          # 0^inf (10)^p 1^(a+1) 1 0  J> 0^inf
    return R('J', '10' * p + '1' * (a + 1) + '10', '0')


# ---- the arithmetic of the write-up ----
def W(j, b):
    if j == 0:
        return b + 3
    x = 2
    for _ in range(b + 1):
        x = W(j - 1, x)
    return x


def Kc(p, a):
    return p - 1 + (a + 1) // 2, W(p - 1, 1 - a % 2) + 1


def iterK(n, pa):
    for _ in range(n):
        pa = Kc(*pa)
    return pa


FAIL = []


def report(name, oks, detail=''):
    good = all(oks)
    print('%s %-12s %3d/%-3d %s' % ('PASS' if good else 'FAIL', name, sum(oks), len(oks), detail))
    if not good:
        FAIL.append(name)


def rword(rng):
    return ''.join(rng.choice('01') for _ in range(rng.randint(0, 6)))


if __name__ == '__main__':
    rng = random.Random(14)

    # W values used in the write-up
    report('W-values', [W(1, 0) == 5, W(1, 1) == 8, W(2, 0) == 11, W(2, 1) == 38, W(3, 0) == 119,
                        all(W(1, b) == 3 * b + 5 for b in range(20)), Kc(2, 3) == (3, 6), Kc(3, 6) == (5, 39),
                        5 - 1 + (39 + 1) // 2 == 24, iterK(2, (1, 3)) == (3, 9)])

    # start-up from the blank tape
    blank = ('A', frozenset())
    s26 = reach(blank, Ca(1, 1, blk(2, '')))
    s578 = reach(blank, Ci(2, 30, 0, 0))
    s801 = reach(blank, Ci(3, 6, 0, 32))
    report('start-up', [s26 == 26, s578 == 578, s801 == 801], 'steps %s %s %s' % (s26, s578, s801))

    # CA_SH: Ca j b (1 0 z) -> Ca (j+1) b z
    oks = []
    for j in range(5):
        for b in range(6):
            z = rword(rng)
            oks.append(reach(Ca(j, b, '10' + z), Ca(j + 1, b, z), 10 ** 5) is not None)
    report('CA_SH', oks)

    # CA_EXIT: Ca j b (0 z) -> 0^inf (10)^j 1^(b+2) I> z
    oks = []
    for j in range(5):
        for b in range(6):
            z = rword(rng) or '0'
            oks.append(reach(Ca(j, b, '0' + z), R('I', '10' * j + '1' * (b + 2), z), 10 ** 5) is not None)
    report('CA_EXIT', oks)

    # CA_CH: Ca j b (1 1 y) -> Ch j b (1 y)
    oks = []
    for j in range(5):
        for b in range(6):
            y = rword(rng)
            oks.append(reach(Ca(j, b, '11' + y), Ch(j, b, '1' + y), 10 ** 5) is not None)
    report('CA_CH', oks)

    # CH_0: Ch 0 b z -> Ca 0 (b+3) z ;  CH_S: Ch (j+1) b z -> Ca j 2 (blk (b+1) z)
    oks = []
    for b in range(10):
        z = rword(rng)
        oks.append(reach(Ch(0, b, z), Ca(0, b + 3, z), 10 ** 5) is not None)
    report('CH_0', oks)
    oks = []
    for j in range(5):
        for b in range(6):
            z = rword(rng)
            oks.append(reach(Ch(j + 1, b, z), Ca(j, 2, blk(b + 1, z)), 10 ** 6) is not None)
    report('CH_S', oks)

    # CH_CA: Ch j b z -> Ca j (W j b) z   (the Ackermann-type recursion on the tape)
    oks = []
    for j, bs in [(0, range(8)), (1, range(8)), (2, range(4)), (3, [0])]:
        for b in bs:
            z = rword(rng)
            oks.append(reach(Ch(j, b, z), Ca(j, W(j, b), z), 10 ** 7) is not None)
    report('CH_CA', oks, '(j<=2, and W(3,0)=119)')

    # BLK_iter: Ca j b (blk a z) -> Ca (j+1) (W_j^a b) z
    oks = []
    for j, cases in [(0, [(a, b) for a in range(5) for b in range(4)]), (1, [(a, b) for a in range(3) for b in range(3)]),
                     (2, [(0, 0), (0, 3), (1, 0), (1, 1)])]:
        for a, b in cases:
            z = rword(rng)
            x = b
            for _ in range(a):
                x = W(j, x)
            oks.append(reach(Ca(j, b, blk(a, z)), Ca(j + 1, x, z), 10 ** 7) is not None)
    report('BLK_iter', oks)

    # CH0_CI: Ch0 j c d -> Ci j 3 c d
    oks = []
    for j in range(5):
        for c in range(4):
            for d in range(4):
                oks.append(reach(Ch0(j, c, d), Ci(j, 3, c, d), 10 ** 6) is not None)
    report('CH0_CI', oks)

    # C_REL: Ci (p+1) a 0 (d+2) -> Ci p 3 (a+3) d ;  D_REL: Ci (p+2) a 0 0 -> Ci p 3 2 (a+2)
    oks = []
    for p in range(5):
        for a in range(8):
            for d in range(4):
                oks.append(reach(Ci(p + 1, a, 0, d + 2), Ci(p, 3, a + 3, d), 10 ** 6) is not None)
    report('C_REL', oks)
    oks = []
    for p in range(5):
        for a in range(8):
            oks.append(reach(Ci(p + 2, a, 0, 0), Ci(p, 3, 2, a + 2), 10 ** 6) is not None)
    report('D_REL', oks)

    # Kc_step (CI_EVEN / CI_ODD): Ci p a (c+1) d -> Ci p' a' c d with (p', a') = Kc(p, a), p >= 1;
    # feasible while the new accumulator W(p-1, .) is small, i.e. p <= 3, plus p = 4 with a even (W(3,1) is huge)
    oks = []
    for p in (1, 2, 3):
        for a in range(0, 12):
            for c, d in [(0, 0), (1, 2), (3, 5)]:
                p2, a2 = Kc(p, a)
                oks.append(reach(Ci(p, a, c + 1, d), Ci(p2, a2, c, d), 10 ** 7) is not None)
    report('Kc_step', oks, '(p<=3, both parities of a)')

    # the Kc map does not depend on c, d and decrements c: Ci p a c d -> Ci Kc^c(p,a) 0 d  (two-step chains)
    oks = []
    for (p, a) in [(1, 3), (1, 4), (2, 3), (1, 5)]:
        for d in (0, 3):
            q = iterK(2, (p, a))
            oks.append(reach(Ci(p, a, 2, d), Ci(q[0], q[1], 0, d), 10 ** 7) is not None)
    report('Kc_loop', oks)

    # D_reload: Ci p a 0 0 -> Ci D_reload(p,a) 0 (a+2), D_reload(p,a) = Kc^2(p-2, 3)
    oks = []
    for p in (3, 4):
        for a in range(3, 12):
            q = iterK(2, (p - 2, 3))
            oks.append(reach(Ci(p, a, 0, 0), Ci(q[0], q[1], 0, a + 2), 10 ** 7) is not None)
    report('D_reload', oks, 'D_reload(3,a)=(3,9), D_reload(4,a)=(5,39)')

    # Kd_step with the smallest admissible arguments is already out of reach: Kd_step(2,3) = Kc^6(1,3) passes
    # through Kc(3,9) = (7,12) and then W(6,1). We check only its first stage (C_REL) and the c-loop above.

    # HALT_step: Ci p a 0 1 -> c_end p a ; J reads 0 there (the halting transition); ones = p + a + 2
    oks = []
    for p in range(6):
        for a in range(10):
            ok = reach(Ci(p, a, 0, 1), c_end(p, a), 10 ** 5) is not None
            q, ones = c_end(p, a)
            ok = ok and q == 'J' and 0 not in ones and TR[('J', 0)] is None and len(ones) == p + a + 2
            oks.append(ok)
    report('HALT_step', oks, 'score = ones + 1 = p + a + 3 (J0 = 1RZ writes 1 on a 0)')

    # J0 is the only undefined transition
    report('table', [sum(v is None for v in TR.values()) == 1, TR[('J', 0)] is None, M.split('_')[9][:3] == '1RZ'])

    # the visit-order (TNF) relabelling: states renamed in order of first visit from the blank tape. Check that the
    # relabelled table is TNF_STR, and that both machines run in lockstep (same tape, mapped state) for 10^6 steps,
    # through the start-up events at steps 26, 578 and 801.
    TNF_STR = '1RB1RA_1RC1RJ_1RD0LM_0LE0RG_1LH1RF_1LG0RA_1RZ0LE_0LI1LH_1RA0LL_0LK1LI_0RE1LK_1LI1LL_0LL0LN_1LL1LM'
    order, r = ['A'], Run(blank)
    while r.steps < 10 ** 6 and len(order) < 14:
        r.step()
        if r.q not in order:
            order.append(r.q)
    mp = {q: STATES[i] for i, q in enumerate(order)}

    def fmt(t):
        return '1RZ' if t is None else '%d%s%s' % (t[0], 'R' if t[1] > 0 else 'L', mp[t[2]])

    relab = '_'.join(fmt(TR[(q, 0)]) + fmt(TR[(q, 1)]) for q in order)
    TR2 = {}
    for i, row in enumerate(TNF_STR.split('_')):
        for s in (0, 1):
            t = row[3 * s:3 * s + 3]
            TR2[(STATES[i], s)] = None if t[2] == 'Z' else (int(t[0]), 1 if t[1] == 'R' else -1, t[2])
    TR1, r1, r2, same, ev = TR, Run(blank), Run(blank), True, {}
    while r1.steps < 10 ** 6:
        r1.step()
        TR = TR2
        r2.step()
        TR = TR1
        if mp[r1.q] != r2.q or r1.h != r2.h or r1.t != r2.t:
            same = False
            break
        if r1.steps in (26, 578, 801):
            ev[r1.steps] = (r1.cfg(), r2.cfg())
    evok = (len(ev) == 3 and ev[26][0] == Ca(1, 1, blk(2, '')) and ev[578][0] == Ci(2, 30, 0, 0)
            and ev[801][0] == Ci(3, 6, 0, 32) and all(ev[k][1] == (mp[ev[k][0][0]], ev[k][0][1]) for k in ev))
    report('TNF-form', [relab == TNF_STR, same, evok],
           'lockstep 10^6 steps; renaming ' + ' '.join(q + mp[q] for q in STATES))

    print('ALL PASS' if not FAIL else 'FAILED: ' + ' '.join(FAIL))
    sys.exit(1 if FAIL else 0)
