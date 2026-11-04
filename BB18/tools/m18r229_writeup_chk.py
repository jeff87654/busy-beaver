"""Independent literal checks of the BB18 M18_229round write-up (does not use the Coq files).

    python m18r229_writeup_chk.py

Simulates the machine string cell by cell and checks, on concrete instances:
  1. the opening: from the blank tape the machine reaches Ce_gen 0 4 0 (1^230) [init_ce0], and in its first 10^7
     steps it never reads the slots that differ from M16_B (N0, O1, P0) or the states Q and R, so up to there it
     runs exactly as M16_B; it does read N1, O0 and P1 (the Kd2 turnaround, as in M16_B);
  2. the two sweeps, a even, p >= 1:
       SWEEP_odd:  from Ce_gen p a 0 (1 0 0 1 0 0 1 1 u) the machine first reaches state P at the left end of the
                   tape with (1 0)^(p+1) 0 (1 0)^(a/2+2) 0 1 0 1 0 u to its right, without reading u;
       SWEEP_even: from Ce_gen p a 0 (1 0 0 1 0 1 0 u) it reaches P at the left end with
                   (1 0)^(p+1) 0 (1 0)^(a/2+2) 0 1 0 0 u, without reading u;
     and reports which slots of N, O, P, Q, R each sweep reads;
  3. the bounce [bounce_155, P0_bounce] (unchanged from M18_4round): from P at the left end with (1 0)^3 r to its
     right, it is in Ch 2 1 (0 1 1 0 0 1 0 0 0 r) after 156 steps and then reaches Ce_gen 22 8 1 (0 r), without
     reading r; CE_EVEN, which finishes P0_bounce, on small instances;
  4. the halt [HALT_step, c_end]: from Ce_gen p a 0 (1 0 0 1 0 0) followed by blank tape, the machine makes seven
     steps (E, F, I, N, Q, R, N) and then Q reads 0, in exactly the configuration c_end p a, with p + a + 8 ones;
  5. the engine pieces of a round (D1_REL, C_REL_full, D2_STEP_full) on small instances: they reach the stated
     configurations without reading the tail, and read no slot of N, O, P, Q, R other than N1, O0, P1;
  6. the tail bookkeeping of the run, as words: after the opening and round 1 the tail is 1 0 0 1 0 0 1^228; an
     odd round turns 1 0 0 1 0 0 1 1 u into 1 0 0 1 0 1 0 u and an even round turns that into 1 0 0 1 0 0 u (the
     sweep outputs of check 2 followed by the 1 0 0 that ROUND_after_sweep leaves); 114 odd/even pairs use up the
     228 ones, and the tail left is 1 0 0 1 0 0, which is the halt of check 4: 1 + 228 = 229 rounds.
Configurations (as in BB18_229round_fw3.v):
  Ce_gen p a c X = 0^inf (1 0)^p 1^(a+2) [E] (1 0)^c 0 X 0^inf    (E on the first cell after the 1s)
  Ch j b z       = 0^inf (1 0)^j [A on the 0 of the last pair] 1 1^b 0 z 0^inf
  c_end p a      = 0^inf (1 0)^p 1^(a+2) 1 1 0 1 1 1 1 [Q on 0] 0^inf
  W 0 b = b + 3,  W (j+1) b = (W j)^(b+1)(2)
"""
import random

MACHINE = ('1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_'
           '1RQ0LO_1LP1LR_0RB1LI_1RZ1RR_1RN0LO')


def parse(m):
    t = {}
    for i, row in enumerate(m.split('_')):
        for s in (0, 1):
            x = row[3 * s:3 * s + 3]
            t[(chr(65 + i), s)] = None if x == '---' or x[2] == 'Z' else (int(x[0]), 1 if x[1] == 'R' else -1, x[2])
    return t


T = parse(MACHINE)
assert [k for k, v in T.items() if v is None] == [('Q', 0)]


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
rng = random.Random(229)
CHANGED = {('N', 0), ('O', 1), ('P', 0), ('Q', 0), ('Q', 1), ('R', 0), ('R', 1)}

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
bad = sorted(used & CHANGED)
read_nop = sorted(x for x in used if x[0] in 'NOP')
c1 = found is not None and not bad and r is not None and read_nop == [('N', 1), ('O', 0), ('P', 1)]
print(f'1. opening: Ce_gen 0 4 0 (1^230) after {found} steps; first 10^7 steps read {read_nop} of N, O, P, '
      f'changed or new slots read: {bad or "none"}: {c1}')
ok &= c1

# 2. the sweeps SWEEP_odd and SWEEP_even
for name, pre, mid_ in (('SWEEP_odd', [1, 0, 0, 1, 0, 0, 1, 1], [1, 0, 1, 0]),
                        ('SWEEP_even', [1, 0, 0, 1, 0, 1, 0], [1, 0, 0])):
    steps_seen, npass, slots = set(), 0, set()
    for p in range(1, 8):
        for a in range(0, 14, 2):
            u = [rng.randint(0, 1) for _ in range(rng.randint(0, 6))]
            x = pre + u
            tape = config(ce_left(p, a), 0, [0] + x)
            q, h, n, hmax = 'E', 0, 0, 0
            while not (q == 'P' and tape.get(h, 0) == 0 and not any(v for k, v in tape.items() if k < h)) \
                    and n < 10 ** 5:
                slots.add((q, tape.get(h, 0)))
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
    nopqr = sorted(x for x in slots if x[0] in 'NOPQR')
    print(f'2. {name} on 49 instances (p = 1..7, a = 0..12 even, random u): {npass} of 49 reach the claimed '
          f'configuration without reading u; steps = 4p + a + {sorted(steps_seen)}; slots of N..R read: {nopqr}: '
          f'{c2}')
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

n3 = 0
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
            n3 += c3c
            if not c3c:
                print(f'3. CE_EVEN FAIL p\'={pp} k={k} c={c}')
print(f"3. CE_EVEN on 45 instances (p' = 0..2, k = 0..4, c = 0..2): {n3} of 45 reached: {n3 == 45}")

# 4. the halt
for p in (1, 3, 5, 9):
    for a in (0, 4, 6, 10):
        tape = config(ce_left(p, a), 0, [0, 1, 0, 0, 1, 0, 0])
        q, h, n, path = 'E', 0, 0, ''
        while True:
            path += q
            r = step(tape, q, h)
            if r is None:
                break
            q, h = r
            n += 1
        want = config([1, 1, 1, 1, 0, 1, 1] + ce_left(p, a), h, [0])
        c4 = q == 'Q' and tape.get(h, 0) == 0 and same(tape, q, h, want, 'Q', h) and n == 7 \
            and sum(tape.values()) == p + a + 8
        ok &= c4
        print(f'4. halt from Ce_gen {p} {a} 0 (1 0 0 1 0 0): {n} steps ({path[:-1]}), then Q reads 0 in c_end; '
              f'ones = {sum(tape.values())} (want p + a + 8 = {p + a + 8}): {c4}')

# 5. the engine pieces of a round on small instances: which slots of N, O, P, Q, R they read
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
    and not (set().union(*nop.values()) & CHANGED)
ok &= c5
print(f"5. D1_REL (12 instances), C_REL_full (6), D2_STEP_full (6) reached; slots of N, O, P, Q, R read: "
      f"D1_REL {sorted(nop['D1_REL']) or 'none'}, C_REL_full {sorted(nop['C_REL_full']) or 'none'}, "
      f"D2_STEP_full {sorted(nop['D2_STEP_full'])}; none reads a changed or new slot: {c5}")

# 6. the tail bookkeeping, as words (cells after the 0 that E reads)
ODD_IN, ODD_OUT = '10010011', '1001010'      # sweep output 1 0 1 0 u, then the round leaves 1 0 0 in front
EVEN_IN, EVEN_OUT = '1001010', '100100'      # sweep output 1 0 0 u, then 1 0 0 in front
assert ODD_OUT == '100' + '1010' and EVEN_OUT == '100' + '100'
tail = '10' * 10 + '0100' + '1' * 228          # init_ce: (1 0)^10 0 1 0 0 1^228
tail = tail[18:]                               # round 1: 9 Kd2 steps, (1 0)^9 1 0 X -> 1 0 X
c6 = tail == '100100' + '1' * 228
rounds, kinds = 1, ''
while True:
    if tail.startswith(ODD_IN):
        tail, kinds = ODD_OUT + tail[len(ODD_IN):], kinds + 'o'
    elif tail.startswith(EVEN_IN):
        tail, kinds = EVEN_OUT + tail[len(EVEN_IN):], kinds + 'e'
    else:
        break
    rounds += 1
c6 &= tail == '100100' and rounds == 229 and kinds == 'oe' * 114
ok &= c6
print(f'6. tail after round 1 = 1 0 0 1 0 0 1^228; then {kinds.count("o")} odd and {kinds.count("e")} even rounds, '
      f'alternating; tail left {" ".join(tail)} (the halt of check 4); rounds in all = {rounds}: {c6}')

print('ALL CHECKS PASS' if ok else 'SOME CHECK FAILED')
raise SystemExit(0 if ok else 1)
