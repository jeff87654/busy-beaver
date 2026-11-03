"""Independent literal checks of the BB18 M18_4round write-up (does not use the Coq files).

    python bb18_4round_writeup_chk.py

Simulates the machine string cell by cell and checks, on concrete instances:
  1. the opening: from the blank tape the machine reaches Ce_gen 0 4 0 (1^230) [init_ce0], and in its first 10^7
     steps it never reads the slots that differ from M16_B (N0, O1, P0) or the new states Q and R, so up to there it
     runs exactly as M16_B; it does read N1, O0 and P1 (the Kd2 turnaround, as in M16_B);
  2. the sweeps: from Ce_gen p a 0 (1 0 0 1 u) [SWEEP_1] and from Ce_gen p a 0 (1 0 0 0 0 1 u) [SWEEP_001], a even,
     the machine first reaches state P at the left end of the tape with (1 0)^(p+1) 0 (1 0)^(a/2+2) 0 u, resp.
     (1 0)^(p+1) 0 (1 0)^(a/2+2) 0 1 0 u, to its right, without reading u;
  3. the bounce [bounce_155, P0_bounce]: from P at the left end with (1 0)^3 r to its right, it is in
     Ch 2 1 (0 1 1 0 0 1 0 0 0 r) after 156 steps and then reaches Ce_gen 22 8 1 (0 r), without reading r;
     CE_EVEN, which finishes P0_bounce (Ce_gen 22 8 1 (0 r) -> Ce_gen 26 (W 21 1) 0 (0 r)), is checked on the
     small instances Ce_gen (p'+1) (2k) (c+1) r -> Ce_gen (p'+k+1) (W p' 1) c r with p' <= 2;
  4. the halt [HALT_step]: from Ce_gen p a 0 (1 0 0 0 1^227) the machine makes five steps (E, F, I, N, Q) and then
     R reads 1, with p + a + 233 ones on the tape.
  5. the engine pieces that make up a round, on small instances (p' <= 2, where W p' 1 is small): the reload
     D1_REL (start of a D1 cycle), C_REL_full (start of a Kd1 step) and D2_STEP_full (start of a Kd2 step) reach
     the configurations stated in the Coq file without reading the tail; D1_REL reads no slot of N, O, P, C_REL_full
     and D2_STEP_full read N1, O0 and P1 (the turnaround I0, N1, O0, P1, I1, unchanged from M16_B), and none reads
     N0, O1, P0 or Q and R. So the round's loops are not confined to A..M, but they use only slots shared with M16_B.
Configurations (as in BB18_4round_fw3.v):
  Ce_gen p a c X = 0^inf (1 0)^p 1^(a+2) [E] (1 0)^c 0 X 0^inf    (E on the first cell after the 1s)
  Ch j b z       = 0^inf (1 0)^j [A on the 0 of the last pair] 1 1^b 0 z 0^inf
  W 0 b = b + 3,  W (j+1) b = (W j)^(b+1)(2)
"""
import random

MACHINE = ('1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_'
           '1RQ0LO_1LP1LN_0RB1LI_1RR0LO_0RO1RZ')


def parse(m):
    t = {}
    for i, row in enumerate(m.split('_')):
        for s in (0, 1):
            x = row[3 * s:3 * s + 3]
            t[(chr(65 + i), s)] = None if x == '---' or x[2] == 'Z' else (int(x[0]), 1 if x[1] == 'R' else -1, x[2])
    return t


T = parse(MACHINE)


def step(tape, q, h):
    tr = T[(q, tape.get(h, 0))]
    if tr is None:
        return None
    tape[h] = tr[0]
    return tr[2], h + tr[1]


def config(left_outward, h, right):
    """tape with the head on cell h holding right[0]; left_outward = cells h-1, h-2, ..."""
    tape = {}
    for i, b in enumerate(left_outward):
        tape[h - 1 - i] = b
    for i, b in enumerate(right):
        tape[h + i] = b
    return tape


def same(tape, q, h, want_tape, want_q, want_h):
    if q != want_q or h != want_h:
        return False
    keys = set(k for k, v in tape.items() if v) | set(k for k, v in want_tape.items() if v)
    return all(tape.get(k, 0) == want_tape.get(k, 0) for k in keys)


def ce_left(p, a):
    return [1] * (a + 2) + [0, 1] * p


def W(j, b):
    if j == 0:
        return b + 3
    x = 2
    for _ in range(b + 1):
        x = W(j - 1, x)
    return x


def reach(left0, right0, q0, left1, right1, q1, rlen, cap=10 ** 6):
    """Run from (left0, [q0] right0), head on cell 0, until (left1, [q1] right1) with the last rlen cells (r) in
    place.  Returns (steps or None, slots read, r read?)."""
    tape = config(left0, 0, right0)
    rs = len(right0) - rlen
    hw = rs - (len(right1) - rlen)
    want = config(left1, hw, right1)
    q, h, n, used, rread = q0, 0, 0, set(), False
    while not same(tape, q, h, want, q1, hw):
        if n >= cap:
            return None, used, rread
        used.add((q, tape.get(h, 0)))
        rread |= h >= rs
        q, h = step(tape, q, h)
        n += 1
    return n, used, rread


ok = True
rng = random.Random(18)

# 1. the opening
tape, q, h = {}, 'A', 0
found, used = None, set()
for n in range(10 ** 7):
    s = tape.get(h, 0)
    if found is None and q == 'E' and s == 0 and all(tape.get(h - i, 0) == 1 for i in range(1, 7)) \
            and tape.get(h - 7, 0) == 0 and all(tape.get(h + i, 0) == 1 for i in range(1, 231)) \
            and sum(tape.values()) == 236:
        found = n
    used.add((q, s))
    r = step(tape, q, h)
    if r is None:
        break
    q, h = r
bad = sorted(used & {('N', 0), ('O', 1), ('P', 0), ('Q', 0), ('Q', 1), ('R', 0), ('R', 1)})
read_nop = sorted(x for x in used if x[0] in 'NOP')
c1 = found is not None and not bad and r is not None and read_nop == [('N', 1), ('O', 0), ('P', 1)]
print(f'1. opening: Ce_gen 0 4 0 (1^230) after {found} steps; first 10^7 steps read {read_nop} of N, O, P, '
      f'changed or new slots read: {bad or "none"}: {c1}')
ok &= c1

# 2. the sweeps SWEEP_1 and SWEEP_001
for name, pre, mid_ in (('SWEEP_1', [1, 0, 0, 1], []), ('SWEEP_001', [1, 0, 0, 0, 0, 1], [1, 0])):
    steps_seen, npass = set(), 0
    for p in range(1, 8):
        for a in range(0, 14, 2):
            u = [rng.randint(0, 1) for _ in range(rng.randint(0, 6))]
            x = pre + u
            tape = config(ce_left(p, a), 0, [0] + x)
            q, h, n, hmax = 'E', 0, 0, 0
            while not (q == 'P' and tape.get(h, 0) == 0 and not any(v for k, v in tape.items() if k < h))                     and n < 10 ** 5:
                q, h = step(tape, q, h)
                n += 1
                hmax = max(hmax, h)
            want = [1, 0] * (p + 1) + [0] + [1, 0] * (a // 2 + 2) + [0] + mid_ + u
            uend = len(x)                       # u occupies cells len(pre)+1 .. len(x)
            got = [tape.get(k, 0) for k in range(h + 1, uend + 1)]
            c2 = got == want and not any(v for k, v in tape.items() if k > uend) and hmax <= len(pre)
            steps_seen.add(n - (4 * p + a))
            npass += c2
    c2 = npass == 49 and len(steps_seen) == 1
    print(f'2. {name} on 49 instances (p = 1..7, a = 0..12 even, random u): {npass} of 49 reach the claimed '
          f'configuration without reading u; steps = 4p + a + {sorted(steps_seen)}: {c2}')
    ok &= c2

# 3. the bounce
for _ in range(5):
    rr = [rng.randint(0, 1) for _ in range(rng.randint(0, 6))]
    tape = config([], 0, [0, 1, 0, 1, 0, 1, 0] + rr)      # P on 0 at cell 0, (1 0)^3 on cells 1..6, r from cell 7
    q, h, hmax = 'P', 0, 0
    for _ in range(156):
        q, h = step(tape, q, h)
        hmax = max(hmax, h)
    zz = [0, 1, 1, 0, 0, 1, 0, 0, 0] + rr
    right = [0, 1, 1, 0] + zz                              # A on 0, then 1 1^1 0 z
    hw = 7 - (len(right) - len(rr))                        # r stays on cells 7..
    want = config([1, 0, 1], hw, right)
    c3a = same(tape, q, h, want, 'A', hw)
    # continue to Ce_gen 22 8 1 (0 r): (1 0)^22 1^10 [E on 1] 0 0 0 r
    right2 = [1, 0, 0, 0] + rr
    hw2 = 7 - (len(right2) - len(rr))
    want2 = config(ce_left(22, 8), hw2, right2)
    n2 = 156
    while not same(tape, q, h, want2, 'E', hw2) and n2 < 10 ** 6:
        q, h = step(tape, q, h)
        n2 += 1
        hmax = max(hmax, h)
    c3b = n2 < 10 ** 6 and hmax < 7
    ok &= c3a and c3b
    print(f'3. bounce, r = {rr}: Ch 2 1 (0 1 1 0 0 1 0 0 0 r) after 156 steps: {c3a}; '
          f'Ce_gen 22 8 1 (0 r) after {n2} steps, r not read: {c3b}')

for pp in range(3):
    for k in range(0, 5):
        for c in range(3):
            rr = [rng.randint(0, 1) for _ in range(3)]
            right = [1, 0] * (c + 1) + [0] + rr
            tape = config(ce_left(pp + 1, 2 * k), 0, right)
            rs = len(right) - len(rr)                      # first cell of r
            right2 = [1, 0] * c + [0] + rr
            hw = rs - (len(right2) - len(rr))
            want = config(ce_left(pp + k + 1, W(pp, 1)), hw, right2)
            q, h, n = 'E', 0, 0
            while not same(tape, q, h, want, 'E', hw) and n < 10 ** 6:
                q, h = step(tape, q, h)
                n += 1
            c3c = n < 10 ** 6
            ok &= c3c
            if not c3c:
                print(f'3. CE_EVEN FAIL p\'={pp} k={k} c={c}')
print("3. CE_EVEN on 45 instances (p' = 0..2, k = 0..4, c = 0..2): all reached")

# 4. the halt
for p in (1, 3, 5, 9):
    for a in (0, 4, 6, 10):
        tape = config(ce_left(p, a), 0, [0, 1, 0, 0, 0] + [1] * 227)
        q, h, n = 'E', 0, 0
        while True:
            r = step(tape, q, h)
            if r is None:
                break
            q, h = r
            n += 1
        c4 = q == 'R' and tape.get(h, 0) == 1 and sum(tape.values()) == p + a + 233 and n == 5
        ok &= c4
        print(f'4. halt from Ce_gen {p} {a} 0 (1 0 0 0 1^227): {n} steps, then R reads 1; ones = {sum(tape.values())} '
              f'(want {p + a + 233}): {c4}')

# 5. the engine pieces of a round on small instances: which slots of N, O, P and the new states they read
rx = [1, 0, 1, 1, 0]
nop = {}
for name, cases in (
        ('D1_REL', [(ce_left(pp + 2, a), [0, 0] + rx, ce_left(pp, W(pp, 1)), [0] + [1] * (a + 3) + rx)
                    for pp in range(3) for a in (0, 2, 4, 6)]),
        ('C_REL_full', [(ce_left(pp + 3, 2 * k + 4), [0, 1, 1] + rx,
                         ce_left(pp + W(pp + 1, 1) // 2 + 2, W(pp, 1)), [1, 0] * (k + 2) + [0] + rx)
                        for pp in range(2) for k in range(3)]),
        ('D2_STEP_full', [(ce_left(pp + 3, 2 * k + 2), [0] + [1, 0, 1, 0] + rx,
                           ce_left(pp + W(pp + 1, 1) // 2 + 2, W(pp, 1)), [1, 0] * k + [0] + [1, 1, 0, 0] + rx)
                          for pp in range(2) for k in range(3)])):
    for l0, r0, l1, r1 in cases:
        n, used, rread = reach(l0, r0, 'E', l1, r1, 'E', len(rx))
        c5 = n is not None and not rread
        ok &= c5
        nop.setdefault(name, set()).update(x for x in used if x[0] in 'NOPQR')
        if not c5:
            print(f'5. {name} FAIL on {l0} {r0}')
c5 = not nop['D1_REL'] and nop['C_REL_full'] == nop['D2_STEP_full'] == {('N', 1), ('O', 0), ('P', 1)} \
    and not (set().union(*nop.values()) & {('N', 0), ('O', 1), ('P', 0), ('Q', 0), ('Q', 1), ('R', 0), ('R', 1)})
ok &= c5
print(f"5. D1_REL (12 instances), C_REL_full (6), D2_STEP_full (6) reached; slots of N, O, P, Q, R read: "
      f"D1_REL {sorted(nop['D1_REL']) or 'none'}, C_REL_full {sorted(nop['C_REL_full']) or 'none'}, "
      f"D2_STEP_full {sorted(nop['D2_STEP_full'])}; none reads a changed or new slot: {c5}")

print('ALL CHECKS PASS' if ok else 'SOME CHECK FAILED')
raise SystemExit(0 if ok else 1)
