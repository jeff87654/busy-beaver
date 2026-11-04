"""Independent literal checks of the BB19 M19_fw4_A write-up (does not use the Coq files).

    python m19a_writeup_chk.py

Simulates the machine string cell by cell and checks, on concrete instances:
  1. the opening: from the blank tape the machine reaches Ce_gen 0 4 0 (1^230) [init_ce0], and in its first 10^7
     steps it never reads the slots that differ from M18_4round (O1, Q0, Q1, R0, R1, S0, S1) or the N0/P0 slots that
     only the sweeps and the bounce read; it does read N1, O0 and P1 (the Kd2 turnaround, as in M16_B);
  2. the sweeps: from Ce_gen p a 0 (1 0 0 1 u) [SWEEP_park] the machine first reaches state P at the left end of the
     tape with (1 0)^(p+1) 0^(a+6) u to its right, and from Ce_gen p a 0 (1 0 0 0 0 u) [SWEEP_cd] with
     (1 0)^(p+1) 1^(a+4) 0 0 0 u, without reading u, after 4p + a + 12 resp. 4p + 3a + 20 steps; it also records
     which slots of N, O, Q, R, S each sweep reads;
  3. the bounce [bounce_155, P0_bounce], unchanged from M17_B/M18_4round: from P at the left end with (1 0)^3 r to
     its right, it is in Ch 2 1 (0 1 1 0 0 1 0 0 0 r) after 156 steps and then reaches Ce_gen 22 8 1 (0 r), without
     reading r; CE_EVEN (which finishes P0_bounce) on small instances;
  4. the halt [HALT_step]: from Ce_gen p a 0 (1 0 0 0 1^228) the machine makes five steps (E, F, I, N, Q) and then S
     reads 1, with p + a + 234 ones on the tape;
  5. the engine pieces (D1_REL, C_REL_full, D2_STEP_full) on small instances: they reach the configurations stated in
     the Coq file without reading the tail, and read no slot of N, O, P, Q, R, S except N1, O0, P1;
  6. the whole right end of the run for small a_R1: the two sweeps and the halt run literally; the rest of each round
     (bounce, alt loop, D1 cycle, Kd1 steps) is replaced by its tape effect from the Coq lemmas, with a fresh small
     level (p, a) at each round. It checks that the park round leaves the header 1 0 0 0 followed by a_R1 + 5 zeros
     before the 1^228 wall, that there are exactly a_R1 + 5 countdown rounds, each moving the boundary 1 cell right,
     and that the machine then halts with S on the first cell of the wall, which never moved.
Configurations (as in BB19_fw4_fw3_9.v):
  Ce_gen p a c X = 0^inf (1 0)^p 1^(a+2) [E] (1 0)^c 0 X 0^inf    (E on the first cell after the 1s)
  Ch j b z       = 0^inf (1 0)^j [A on the 0 of the last pair] 1 1^b 0 z 0^inf
  W 0 b = b + 3,  W (j+1) b = (W j)^(b+1)(2)
"""
import random

MACHINE = ('1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_'
           '1RQ0LO_1LP1RR_0RB1LI_1RS0LQ_1LN0LR_0LR1RZ')
NEW = {('O', 1), ('Q', 0), ('Q', 1), ('R', 0), ('R', 1), ('S', 0), ('S', 1)}


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


def sweep(tape, h, cap=10 ** 5):
    """Run from E at cell h until P stands on a 0 with no 1 to its left.  Returns (h, steps, slots read, max head)."""
    q, n, used, hmax = 'E', 0, set(), h
    while not (q == 'P' and tape.get(h, 0) == 0 and not any(v for k, v in tape.items() if k < h)):
        if n >= cap:
            return None, n, used, hmax
        used.add((q, tape.get(h, 0)))
        q, h = step(tape, q, h)
        n += 1
        hmax = max(hmax, h)
    return h, n, used, hmax


ok = True
rng = random.Random(19)

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
bad = sorted(used & (NEW | {('N', 0), ('P', 0)}))
read_nop = sorted(x for x in used if x[0] in 'NOPQRS')
c1 = found == 21854 and not bad and r is not None and read_nop == [('N', 1), ('O', 0), ('P', 1)]
print(f'1. opening: Ce_gen 0 4 0 (1^230) after {found} steps; first 10^7 steps read {read_nop} of N..S, '
      f'N0, P0 or changed/new slots read: {bad or "none"}: {c1}')
ok &= c1

# 2. the sweeps SWEEP_park and SWEEP_cd
for name, pre, mid, ka in (('SWEEP_park', [1, 0, 0, 1], None, 1), ('SWEEP_cd', [1, 0, 0, 0, 0], [0, 0, 0], 3)):
    steps_seen, npass, slots = set(), 0, set()
    for p in range(1, 8):
        for a in range(0, 14, 2):
            u = [rng.randint(0, 1) for _ in range(rng.randint(0, 6))]
            x = pre + u
            tape = config(ce_left(p, a), 0, [0] + x)
            hh, n, us, hmax = sweep(tape, 0)
            if mid is None:
                want = [1, 0] * (p + 1) + [0] * (a + 6) + u
            else:
                want = [1, 0] * (p + 1) + [1] * (a + 4) + mid + u
            uend = len(x)                       # u occupies cells len(pre)+1 .. len(x)
            got = [tape.get(k, 0) for k in range(hh + 1, uend + 1)] if hh is not None else None
            c2 = got == want and not any(v for k, v in tape.items() if k > uend) and hmax <= len(pre)
            steps_seen.add(n - (4 * p + ka * a))
            slots |= {s for s in us if s[0] in 'NOQRS'}
            npass += c2
    c2 = npass == 49 and len(steps_seen) == 1
    print(f'2. {name} on 49 instances (p = 1..7, a = 0..12 even, random u): {npass} of 49 reach the claimed '
          f'configuration without reading u; steps = 4p + {"" if ka == 1 else ka}a + {sorted(steps_seen)}; slots of N, O, Q, R, S read: '
          f'{sorted(slots)}: {c2}')
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
    right2 = [1, 0, 0, 0] + rr                             # Ce_gen 22 8 1 (0 r)
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

nce = 0
for pp in range(3):
    for k in range(0, 5):
        for c in range(3):
            rr = [rng.randint(0, 1) for _ in range(3)]
            n, _, rread = reach(ce_left(pp + 1, 2 * k), [1, 0] * (c + 1) + [0] + rr, 'E',
                                ce_left(pp + k + 1, W(pp, 1)), [1, 0] * c + [0] + rr, 'E', len(rr))
            c3c = n is not None and not rread
            nce += c3c
            if not c3c:
                print(f'3. CE_EVEN FAIL p\'={pp} k={k} c={c}')
ok &= nce == 45
print(f"3. CE_EVEN on 45 instances (p' = 0..2, k = 0..4, c = 0..2): {nce} of 45 reached, r not read")

# 4. the halt
for p in (1, 3, 5, 9):
    for a in (0, 4, 6, 10):
        tape = config(ce_left(p, a), 0, [0, 1, 0, 0, 0] + [1] * 228)
        q, h, n = 'E', 0, 0
        while True:
            r = step(tape, q, h)
            if r is None:
                break
            q, h = r
            n += 1
        c4 = q == 'S' and tape.get(h, 0) == 1 and h == 5 and sum(tape.values()) == p + a + 234 and n == 5
        ok &= c4
        print(f'4. halt from Ce_gen {p} {a} 0 (1 0 0 0 1^228): {n} steps, then S reads 1 at h + {h}; '
              f'ones = {sum(tape.values())} (want {p + a + 234}): {c4}')

# 5. the engine pieces on small instances: which slots of N..S they read
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
        nop.setdefault(name, set()).update(x for x in used if x[0] in 'NOPQRS')
        if not c5:
            print(f'5. {name} FAIL on {l0} {r0}')
c5 = not nop['D1_REL'] and nop['C_REL_full'] == nop['D2_STEP_full'] == {('N', 1), ('O', 0), ('P', 1)}
ok &= c5
print(f"5. D1_REL (12 instances), C_REL_full (6), D2_STEP_full (6) reached; slots of N..S read: "
      f"D1_REL {sorted(nop['D1_REL']) or 'none'}, C_REL_full {sorted(nop['C_REL_full']) or 'none'}, "
      f"D2_STEP_full {sorted(nop['D2_STEP_full'])}: {c5}")


# 6. the right end of the run, rounds 2 .. end, for small a_R1
def right_word(tape, start):
    end = max(k for k, v in tape.items() if v)
    return [tape.get(k, 0) for k in range(start, end + 1)]


WALL = 228
for aR1 in (4, 6, 8, 10, 20, 40):
    # end of round 1: Ce_gen p a 0 (1 0 0 1 0 0 1^228), boundary h = 0, wall from cell 7
    p, a = 5, aR1
    tape = config(ce_left(p, a), 0, [0, 1, 0, 0, 1, 0, 0] + [1] * WALL)
    wall0 = 7
    rounds, kinds, hs, c6, halted = 0, [], [0], True, None
    h0 = 0
    while rounds < 200:
        x = [tape.get(h0 + i, 0) for i in range(1, 6)]
        if x[:4] == [1, 0, 0, 0] and x[4] == 1:            # the halt
            tape2 = dict(tape)
            q, h, n = 'E', h0, 0
            while True:
                r = step(tape2, q, h)
                if r is None:
                    break
                q, h = r
                n += 1
            halted = (q, h, tape2.get(h, 0), n, sum(tape2.values()), p + a + 234)
            break
        kind = 'park' if x[:4] == [1, 0, 0, 1] else 'cd' if x == [1, 0, 0, 0, 0] else None
        if kind is None:
            c6 = False
            break
        kinds.append(kind)
        hh, n, _, _ = sweep(tape, h0)
        w = right_word(tape, hh + 1)
        if w[:2 * (p + 1)] != [1, 0] * (p + 1):
            c6 = False
            break
        y0 = hh + 1 + 2 * (p + 1)                          # first cell of Y
        # bounce eats (1 0)^3, the alt loop eats (1 0)^(p-2): tail 0 Y, boundary at y0 - 2; D1 cycle: 0 Y -> 1 Y
        tail = [1] + right_word(tape, y0)
        hb = y0 - 2
        while tail[:2] == [1, 1]:                          # Kd1 steps: 1 1 u -> u
            tail = tail[2:]
            hb += 2
        p, a = rng.randint(3, 8), 2 * rng.randint(2, 6)    # a fresh small level for the next sweep
        tape = config(ce_left(p, a), hb, [0] + tail)
        h0 = hb
        rounds += 1
        hs.append(h0)
    gap = None
    if len(kinds) >= 1 and kinds[0] == 'park':
        gap = hs[1]                                        # after park: header at hs[1]+1..+4, zeros, wall at wall0
        zeros = wall0 - (hs[1] + 5)
    ncd = kinds.count('cd')
    moves = [hs[i + 1] - hs[i] for i in range(1, len(hs) - 1)]
    c6 = c6 and kinds[0] == 'park' and kinds[1:] == ['cd'] * ncd and zeros == aR1 + 5 and ncd == aR1 + 5 \
        and all(m == 1 for m in moves) and halted is not None and halted[0] == 'S' and halted[2] == 1 \
        and halted[1] == wall0 and halted[3] == 5 and halted[4] == halted[5]
    ok &= c6
    print(f'6. a_R1 = {aR1}: park round leaves {zeros} zeros before the wall (want {aR1 + 5}); {ncd} countdown rounds, '
          f'boundary moves {sorted(set(moves))}; halt: S reads {halted[2]} at cell {halted[1]} (wall starts at '
          f'{wall0}) after {halted[3]} steps, ones = {halted[4]} (= p + a + 234: {halted[4] == halted[5]}): {c6}')

print('ALL CHECKS PASS' if ok else 'SOME CHECK FAILED')
raise SystemExit(0 if ok else 1)
