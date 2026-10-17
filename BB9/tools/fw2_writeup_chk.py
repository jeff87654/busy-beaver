"""Independent literal checks for the fw2 write-up (own cell-by-cell simulator, nothing imported from the Coq files).
   Run: python fw2_writeup_chk.py   (about 90 s). Prints one PASS/FAIL line per check and exits 1 on any failure.

   Configuration family (as in BB9_fw2_1RB0RD.v; "<H" = state H with the head on the 0 just left of the word):
     Kd(ds, a, b) = 0^inf <H 1^(b+1) 0 1^a 0 1^d_1 0 1^d_2 ... 0 1^d_n 0^inf,     ds = [d_1, ..., d_n]
   Rules (Coq: KR1, KR2, KR3, KR4O3, KR4Ex):
     R1   Kd(ds, a+1, b)                    -->+ Kd(ds, a, b+3)
     R2   Kd([y+1] + t, 0, b)                -->+ Kd([y] + t, b+2, 1)
     R3   Kd([0]*(m+1) + [y+1] + t, 0, 2(m+1)+s) -->+ Kd([2]*m + [s+2, y] + t, 2, 1)
     R4O3 Kd([0]*k, 0, 4m+3)                -->+ Kd([2] + trip(m), 0, 1),  trip(m) = (0,1,2)^m (0,1,1)
     R4Ex Kd([0]*k, 0, 2m)                  -->* halt in state I reading 0 with 2m+3 ones (score 2m+4)
   Checks: the two state labellings of the machine, the start-up (Kd([1,1], 0, 1) at step 49), each rule on many
   concrete instances, small end-to-end halts with the exact ones count, the exact values U, X, b1 = 620011 from the
   Coq recursion, and the first 2*10^8 steps of the real run against the rules (every visit to the Kd family)."""
import random, sys

M = '1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA'
# the same machine in the state labels of the BB(9) champion's Coq file, started in state E (Coq file header)
M_CHAMP_LABELS = '1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RH0RA_1LB1LF_1RZ1RE_1LI1LI_0RE0LH'
RELABEL = {'E': 'A', 'H': 'B', 'I': 'C', 'A': 'D', 'B': 'E', 'F': 'F', 'C': 'G', 'D': 'H', 'G': 'I'}
CHAMPION9 = '1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH'   # Jacobzheng 2024
STATES = 'ABCDEFGHI'


def table(m):
    tr = {}
    for i, row in enumerate(m.split('_')):
        for s in (0, 1):
            t = row[3 * s:3 * s + 3]
            tr[(STATES[i], s)] = None if t[2] == 'Z' else (int(t[0]), 1 if t[1] == 'R' else -1, t[2])
    return tr


TR = table(M)
NQ = {q: i for i, q in enumerate(STATES)}
# flat table for the fast loop: index 2*q+s -> (write, move, next) or None
FLAT = [None] * 18
for (q, s), v in TR.items():
    FLAT[2 * NQ[q] + s] = None if v is None else (v[0], v[1], NQ[v[2]])
QH, QI = NQ['H'], NQ['I']

FAILS = []


def check(name, ok, detail=''):
    print(('PASS  ' if ok else 'FAIL  ') + name + (('   ' + detail) if detail else ''))
    if not ok:
        FAILS.append(name)


class Tape:
    """Literal machine. The tape grows on both sides as needed."""

    def __init__(self, q, left, head, right):
        self.pad = 1024
        self.t = bytearray(self.pad) + bytearray(int(x) for x in left + head + right) + bytearray(self.pad)
        self.h = self.pad + len(left)
        self.q = NQ[q]
        self.steps = 0
        self.halted = False

    def grow(self):
        if self.h < 2:
            n = len(self.t)
            self.t = bytearray(n) + self.t
            self.h += n
        elif self.h >= len(self.t) - 2:
            self.t += bytearray(len(self.t))

    def run(self, n, stop=None):
        """Run up to n steps. stop(tape) is called after each step in state H reading 0 with a 1 to its right;
        if it returns True the run stops there. Returns the number of steps taken."""
        t, h, q, flat = self.t, self.h, self.q, FLAT
        done = 0
        while done < n:
            if h < 2 or h >= len(t) - 2:
                self.t, self.h = t, h
                self.grow()
                t, h = self.t, self.h
            tr = flat[2 * q + t[h]]
            if tr is None:
                self.halted = True
                break
            t[h] = tr[0]
            h += tr[1]
            q = tr[2]
            done += 1
            if stop is not None and q == QH and t[h] == 0 and t[h + 1] == 1:
                self.t, self.h, self.q = t, h, q
                self.steps += done
                n -= done
                done = 0
                if stop(self):
                    return
        self.t, self.h, self.q = t, h, q
        self.steps += done

    def left_blank(self):
        return not any(self.t[:self.h])

    def right_word(self):
        return bytes(self.t[self.h + 1:]).rstrip(b'\x00')

    def ones(self):
        return sum(self.t)


def kd_word(ds, a, b):
    return '1' * (b + 1) + '0' + '1' * a + ''.join('0' + '1' * d for d in ds)


def kd_cfg(ds, a, b):
    return ('H', '', '0', kd_word(ds, a, b))


def parse_kd(tape):
    """Kd parameters of the tape (state H on the 0 left of the word, blank to the left), or None. A Kd word has
    trailing digits d_n >= 0 written as 0 1^d_n, so trailing zero digits are invisible; ds is returned without them
    and compared modulo trailing zeros."""
    if tape.q != QH or tape.t[tape.h] != 0 or not tape.left_blank():
        return None
    w = tape.right_word().decode('latin1').replace('\x00', '0').replace('\x01', '1')
    blocks = w.split('0')
    b = len(blocks[0]) - 1
    a = len(blocks[1]) if len(blocks) > 1 else 0
    ds = [len(x) for x in blocks[2:]]
    return ds, a, b


def strip0(ds):
    ds = list(ds)
    while ds and ds[-1] == 0:
        ds.pop()
    return ds


def run_to_kd(cfg, target, limit):
    """Run from cfg until the configuration is Kd target (ds compared modulo trailing zero digits)."""
    tape = Tape(*cfg)
    tds, ta, tb = target
    found = []

    def stop(tp):
        k = parse_kd(tp)
        if k is not None and strip0(k[0]) == strip0(tds) and k[1] == ta and k[2] == tb:
            found.append(tp.steps)
            return True
        return False
    tape.run(limit, stop)
    return found[0] if found else None


def trip(m):
    return [0, 1, 2] * m + [0, 1, 1]


# ---------------------------------------------------------------------------------------------------------------
# 1. the machine labellings
relab = ['' for _ in STATES]
for i, row in enumerate(M_CHAMP_LABELS.split('_')):
    q = STATES[i]
    out = ''
    for s in (0, 1):
        t = row[3 * s:3 * s + 3]
        out += t[:2] + ('Z' if t[2] == 'Z' else RELABEL[t[2]])
    relab[NQ[RELABEL[q]]] = out
check('champion-label form started in E relabels to the TNF string', '_'.join(relab) == M, '_'.join(relab))
shared = [(STATES[i], s) for i, (r1, r2) in enumerate(zip(M_CHAMP_LABELS.split('_'), CHAMPION9.split('_')))
          for s in (0, 1) if r1[3 * s:3 * s + 3] == r2[3 * s:3 * s + 3]]
print('      transitions shared with the BB(9) champion (champion labels): %d of 18: %s'
      % (len(shared), ' '.join('%s%d' % x for x in shared)))

# 2. start-up
tape = Tape('A', '', '0', '')
seen = []


def note_kd(tp):
    k = parse_kd(tp)
    if k is not None:
        seen.append((tp.steps, (strip0(k[0]), k[1], k[2])))
    return False


tape.run(49, note_kd)
k49 = parse_kd(tape)
check('blank tape is Kd([1,1], 0, 1) at step 49', tape.steps == 49 and k49 is not None
      and (strip0(k49[0]), k49[1], k49[2]) == ([1, 1], 0, 1), 'Kd-shaped configurations up to step 49: %s' % seen)
START49 = tape

# 3. the rules on concrete instances
rng = random.Random(9)


def rand_ds(n, hi):
    return [rng.randint(0, hi) for _ in range(n)]


ok, n = True, 0
for _ in range(60):
    ds, a, b = rand_ds(rng.randint(0, 3), 4), rng.randint(1, 12), rng.randint(0, 30)
    if run_to_kd(kd_cfg(ds, a, b), (ds, a - 1, b + 3), 10 ** 6) is None:
        ok = False
    n += 1
check('R1   Kd(ds,a+1,b) -->+ Kd(ds,a,b+3)', ok, '%d instances' % n)

ok, n = True, 0
for _ in range(60):
    y, t, b = rng.randint(0, 6), rand_ds(rng.randint(0, 3), 4), rng.randint(0, 30)
    if run_to_kd(kd_cfg([y + 1] + t, 0, b), ([y] + t, b + 2, 1), 10 ** 6) is None:
        ok = False
    n += 1
check('R2   Kd([y+1]+t,0,b) -->+ Kd([y]+t,b+2,1)', ok, '%d instances' % n)

ok, n = True, 0
for _ in range(80):
    m, y, s, t = rng.randint(0, 5), rng.randint(0, 5), rng.randint(0, 20), rand_ds(rng.randint(0, 2), 4)
    if run_to_kd(kd_cfg([0] * (m + 1) + [y + 1] + t, 0, 2 * (m + 1) + s),
                 ([2] * m + [s + 2, y] + t, 2, 1), 10 ** 7) is None:
        ok = False
    n += 1
check('R3   Kd(0^(m+1) (y+1) t,0,2(m+1)+s) -->+ Kd(2^m (s+2) y t,2,1)', ok, '%d instances' % n)

ok, n = True, 0
for k in range(0, 4):
    for m in range(0, 25):
        if run_to_kd(kd_cfg([0] * k, 0, 4 * m + 3), ([2] + trip(m), 0, 1), 10 ** 7) is None:
            ok = False
        n += 1
check('R4O3 Kd(0^k,0,4m+3) -->+ Kd(2 trip(m),0,1)', ok, '%d instances' % n)

ok, n = True, 0
for k in range(0, 4):
    for m in range(0, 25):
        tp = Tape(*kd_cfg([0] * k, 0, 2 * m))
        tp.run(10 ** 7)
        q = STATES[tp.q]
        if not (tp.halted and q == 'I' and tp.t[tp.h] == 0 and tp.ones() == 2 * m + 3):
            ok = False
        n += 1
check('R4Ex Kd(0^k,0,2m) halts in I reading 0 with 2m+3 ones (score 2m+4)', ok, '%d instances' % n)

# 4. the exact values (the Coq recursion UX, b1)
def U(j, x):
    if j == 0:
        return 3 * x + 7
    v = X(j - 1)
    for _ in range(x - 2 * (j - 1)):
        v = U(j - 1, v)
    return v


def X(j):
    return 7 if j == 0 else U(j - 1, U(j - 1, X(j - 1)))


b1 = U(1, 10)
check('b1 = U 1 10 = 620011 = 4*155002 + 3 (m1 = 155002 even; depth 3*m1+3 = 465009)',
      b1 == 620011 and b1 == 4 * 155002 + 3 and 155002 % 2 == 0 and 3 * 155002 + 3 == 465009, 'b1 = %d' % b1)
check('X 1 = 91', X(1) == 91)

# 5. abstract Kd machine (the four rules + the halt) against the literal machine
def kd_next(ds, a, b):
    """One rule application; returns ('kd', (ds, a, b)), ('halt', ones), or ('stuck', None) where no rule applies."""
    ds = strip0(ds)
    if a > 0:
        return 'kd', (ds, a - 1, b + 3)
    if ds and ds[0] > 0:
        return 'kd', ([ds[0] - 1] + ds[1:], b + 2, 1)
    if ds:          # a run of m+1 leading zero digits, then y+1
        z = 0
        while ds[z] == 0:
            z += 1
        m, y, t = z - 1, ds[z] - 1, ds[z + 1:]
        s = b - 2 * (m + 1)
        if s < 0:
            return 'stuck', None
        return 'kd', ([2] * m + [s + 2, y] + t, 2, 1)
    if b % 4 == 3:
        return 'kd', ([2] + trip((b - 3) // 4), 0, 1)
    if b % 2 == 0:
        return 'halt', b + 3
    return 'stuck', None


FIRST = []


def literal_vs_abstract(tape, start, steps):
    """Literal run from the Kd configuration tape = Kd(start); every later visit to the Kd family must be the next
    configuration given by the rules (and nothing else), and a halt must come where R4Ex predicts it, with its ones.
    Returns (Kd visits matched, mismatch or None, ones at the halt or None, steps run, stuck, last Kd visit)."""
    state = {'pred': None, 'n': 0, 'bad': None, 'stuck': False, 'last': None, 'first': []}

    def advance(k):
        kind, nxt = kd_next(*k)
        if kind == 'stuck':
            state['stuck'] = True
            return True
        state['pred'] = (strip0(nxt[0]), nxt[1], nxt[2]) if kind == 'kd' else ('halt', nxt)
        return False

    def stop(tp):
        k = parse_kd(tp)
        if k is None:
            return False
        k = (strip0(k[0]), k[1], k[2])
        if k != state['pred']:
            state['bad'] = (tp.steps, k, state['pred'])
            return True
        state['n'] += 1
        state['last'] = (tp.steps, k)
        if len(state['first']) < 24:
            state['first'].append((tp.steps, k))
        return advance(k)
    if not advance((strip0(start[0]), start[1], start[2])):
        tape.run(steps, stop)
    ones = tape.ones() if tape.halted else None
    if tape.halted and state['bad'] is None:
        if state['pred'] is None or state['pred'][0] != 'halt':
            state['bad'] = (tape.steps, 'halted', state['pred'])
        elif state['pred'][1] != ones:
            state['bad'] = (tape.steps, 'ones %d' % ones, state['pred'])
    FIRST[:] = state['first']
    return state['n'], state['bad'], ones, tape.steps, state['stuck'], state['last']


ok, n, total, nst = True, 0, 0, 0
for _ in range(60):
    ds, a, b = rand_ds(rng.randint(0, 3), 2), rng.randint(0, 3), rng.choice([2 * rng.randint(0, 6), 4 * rng.randint(0, 3) + 3])
    cnt, bad, ones, st, stuck, _ = literal_vs_abstract(Tape(*kd_cfg(ds, a, b)), (ds, a, b), 3 * 10 ** 6)
    if bad is not None:
        ok = False
        print('      mismatch from', (ds, a, b), bad)
    n += ones is not None
    nst += stuck
    total += cnt
check('small Kd starts: every Kd visit is the next rule; halts where R4Ex says, with its ones count', ok,
      '60 starts: %d halted within the budget, %d reached a Kd where no rule applies, %d Kd visits matched'
      % (n, nst, total))

cnt, bad, ones, st, stuck, last = literal_vs_abstract(START49, ([1, 1], 0, 1), 2 * 10 ** 8)
check('real run from step 49 to step %d: every Kd visit is the next rule' % st,
      bad is None and not stuck and cnt > 0 and not START49.halted,
      '%d Kd visits matched; the last: step %d, Kd(%s, %d, %d)' % (cnt, last[0], last[1][0], last[1][1], last[1][2]))

print('      the first Kd visits of the real run after step 49 (step, (ds, a, b)):')
for i in range(0, len(FIRST), 4):
    print('        ' + '  '.join('%d %s' % (st, k) for st, k in FIRST[i:i + 4]))

# 6. every defined transition is read: the real run (first 10^6 steps) and the R4Ex halts above
used = set()
tp = Tape('A', '', '0', '')
for _ in range(10 ** 6):
    s0 = tp.t[tp.h]
    used.add((STATES[tp.q], s0))
    tp.run(1)
tp = Tape(*kd_cfg([], 0, 4))
while not tp.halted:
    used.add((STATES[tp.q], tp.t[tp.h]))
    tp.run(1)
defined = {k for k, v in TR.items() if v is not None}
check('every defined transition is read (real run, first 10^6 steps, plus one R4Ex halt), and the halt I0 is reached',
      defined <= used and ('I', 0) in used, 'not read: %s' % sorted(defined - used))

print()
print('ALL PASS' if not FAILS else 'FAILED: ' + ', '.join(FAILS))
sys.exit(1 if FAILS else 0)
