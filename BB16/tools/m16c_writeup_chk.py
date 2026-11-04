"""Independent literal checks of the BB16 (M16_C) write-up (does not use the Coq files).

    python m16c_writeup_chk.py

Simulates the machine string cell by cell and checks, on concrete instances:
  1. the opening: from the blank tape the machine reaches Ce_gen 0 4 0 (1^230) [init_ce0], and the halting slot P0
     is not read on the way;
  2. start_38: Ce_gen 0 4 0 (1 1 r) reaches Ca 0 3 (blk 1 (blk 1 (0 1 0 1 0 0 r))) in 38 steps;
  3. the bridge (the only place the changed slot O1 = 0LE is read):
       C_REL_M16C_aux:  Ce_gen (p'+2) (2k+4) 0 (1 0 0 1 r) reaches Ch p' 1 (0 1 1 0 0 (10)^(k+2) 0 0 1 r),
       C_REL_M16C_full: Ce_gen (p''+3) (2k+4) 0 (1 0 0 1 r) reaches
                        Ce_gen (p'' + W_(p''+1)(1)/2 + 2) (W_p''(1)) (k+2) (0 1 r),
     next to the ordinary Kd1 front end C_REL_full (same numbers, tail 1 1 r -> r): the bridge is a Kd1 step that
     leaves 0 1 in front of r. The reason (3e): 11 steps from Ce_gen p a 0 (1 0 0 1 r) give exactly the
     configuration that Ce_gen p a 0 (1 1 0 1 r) reaches after 3 steps, so the bridge reads 1 0 0 1 as 1 1 0 1.
     Under M16_B's O1 = 1RM the same instance does not reach that result (3d);
  4. the other macro steps the run uses, on their smallest instances: CE_EVEN, D1_REL, D2_STEP_full;
  5. the halt (HALT_step): Ce_gen p a 0 (1) halts in state P reading 0, with p + a + 5 ones on the tape.
For every instance it counts how often O1 is read: once in each bridge instance, never elsewhere.
Configurations (as in BB16_M16c_fw3.v; for a side written outward from the head, "left" lists cells h-1, h-2, ...):
  Ce_gen p a c X = 0^inf (1 0)^p 1^(a+2) [E] (1 0)^c 0 X 0^inf      (head on the first cell after the 1s)
  Ca j b z       = 0^inf (1 0)^j 1^b [C on 0] z 0^inf,   blk a z = 1 1^a 0 z
  Ch j b z       = 0^inf (1 0)^j [A on the 0 of the last (1 0), or on a blank if j = 0] 1 1^b 0 z 0^inf
  W 0 b = b + 3,  W (j+1) b = (W j)^(b+1)(2)
"""
MACHINE = '1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP0LE_1RZ1LI'
M16_B = '1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP1RM_1RZ1LI'


def parse(m):
    t = {}
    for i, row in enumerate(m.split('_')):
        for s in (0, 1):
            x = row[3 * s:3 * s + 3]
            t[(chr(65 + i), s)] = None if x == '---' or x[2] == 'Z' else (int(x[0]), 1 if x[1] == 'R' else -1, x[2])
    return t


T = parse(MACHINE)
TB = parse(M16_B)


def W(j, b):
    if j == 0:
        return b + 3
    x = 2
    for _ in range(b + 1):
        x = W(j - 1, x)
    return x


R0 = 10 ** 6          # the tail r always starts at this cell; it is never read, so it must not move


def build(right, left, q, pre_len):
    """right: cells h, h+1, ...; left: cells h-1, h-2, ...; the tail r starts pre_len cells after the head."""
    h = R0 - pre_len
    tape = {}
    for i, b in enumerate(right):
        if b:
            tape[h + i] = 1
    for i, b in enumerate(left):
        if b:
            tape[h - 1 - i] = 1
    return tape, q, h


def CE(p, a, c, pre, r):
    """Ce_gen p a c (pre ++ r)"""
    right = [1, 0] * c + [0] + pre + r
    return build(right, [1] * (a + 2) + [0, 1] * p, 'E', 2 * c + 1 + len(pre))


def CH(j, b, pre, r):
    """Ch j b (pre ++ r): head on the first cell of the left side (01)^j."""
    right = [0, 1] + [1] * b + [0] + pre + r
    left = ([0, 1] * j)[1:]
    return build(right, left, 'A', len(right) - len(r))


def CA(j, b, pre, r):
    """Ca j b (pre ++ r): C on the 0 after 1^b."""
    right = [0] + pre + r
    return build(right, [1] * b + [0, 1] * j, 'C', 1 + len(pre))


def run_to(start, target, table=T, limit=2_000_000):
    """Run from start until the configuration equals target. Returns (steps, O1 reads) or (None, O1 reads)."""
    tape, q, h = dict(start[0]), start[1], start[2]
    ttape, tq, th = target
    want = set(k for k, v in ttape.items() if v)
    o1 = 0
    for n in range(limit + 1):
        if q == tq and h == th and set(k for k, v in tape.items() if v) == want:
            return n, o1
        s = tape.get(h, 0)
        if (q, s) == ('O', 1):
            o1 += 1
        tr = table[(q, s)]
        if tr is None:
            return None, o1
        if tr[0]:
            tape[h] = 1
        else:
            tape.pop(h, None)
        q, h = tr[2], h + tr[1]
    return None, o1


ok = True
TAILS = ([], [1], [1, 0, 1], [0, 1, 1, 0, 1])


def report(label, res, want_o1):
    global ok
    n, o1 = res
    c = n is not None and o1 == want_o1
    ok &= c
    print(f'{label}: {n} steps, O1 read {o1}x: {c}')


# 1. opening to Ce_gen 0 4 0 (1^230): E on 0, 6 ones to the left then blank, 230 ones to the right then blank
tape, q, h = {}, 'A', 0
found, p0, o1 = None, False, 0
for n in range(200000):
    if q == 'E' and tape.get(h, 0) == 0 and all(tape.get(h - i, 0) == 1 for i in range(1, 7)) \
            and tape.get(h - 7, 0) == 0 and all(tape.get(h + i, 0) == 1 for i in range(1, 231)) \
            and sum(tape.values()) == 236:
        found = n
        break
    s = tape.get(h, 0)
    p0 |= (q, s) == ('P', 0)
    o1 += (q, s) == ('O', 1)
    tr = T[(q, s)]
    if tr is None:
        break
    tape[h] = tr[0]
    q, h = tr[2], h + tr[1]
c1 = found is not None and not p0 and o1 == 0
print(f'1. opening reaches Ce_gen 0 4 0 (1^230) after {found} steps, P0 read: {p0}, O1 read {o1}x: {c1}')
ok &= c1

# 2. start_38
for r in TAILS:
    st = CE(0, 4, 0, [1, 1], r)
    tg = CA(0, 3, [1, 1, 0] + [1, 1, 0] + [0, 1, 0, 1, 0, 0], r)
    n, o = run_to(st, tg)
    c2 = n == 38 and o == 0
    ok &= c2
    print(f'2. start_38, r = {r}: {n} steps, O1 read {o}x: {c2}')

# 3. the bridge
for pp in (0, 1, 2):
    for k in (0, 1, 2):
        for r in TAILS[:3]:
            report(f"3a. C_REL_M16C_aux  p'={pp} k={k} r={r}",
                   run_to(CE(pp + 2, 2 * k + 4, 0, [1, 0, 0, 1], r),
                          CH(pp, 1, [0, 1, 1, 0, 0] + [1, 0] * (k + 2) + [0, 0, 1], r)), 1)
for pp in (0, 1):
    for k in (0, 1, 2):
        for r in TAILS[:3]:
            P, A = pp + W(pp + 1, 1) // 2 + 2, W(pp, 1)
            report(f"3b. C_REL_M16C_full p''={pp} k={k} r={r} -> Ce_gen {P} {A} {k + 2} (0 1 r)",
                   run_to(CE(pp + 3, 2 * k + 4, 0, [1, 0, 0, 1], r), CE(P, A, k + 2, [0, 1], r)), 1)
            report(f"3c. C_REL_full      p''={pp} k={k} r={r} -> Ce_gen {P} {A} {k + 2} r      ",
                   run_to(CE(pp + 3, 2 * k + 4, 0, [1, 1], r), CE(P, A, k + 2, [], r)), 0)
# why: 11 steps from Ce_gen p a 0 (1 0 0 1 r) give exactly the configuration that Ce_gen p a 0 (1 1 0 1 r) reaches
# after 3 steps (E on the tail's first 1, the start of the leftward E/J sweep), so from there the runs coincide
def steps(cfg, n):
    tape, q, h = dict(cfg[0]), cfg[1], cfg[2]
    for _ in range(n):
        tr = T[(q, tape.get(h, 0))]
        if tr[0]:
            tape[h] = 1
        else:
            tape.pop(h, None)
        q, h = tr[2], h + tr[1]
    return tape, q, h


for p, a in ((2, 4), (3, 6), (5, 8)):
    for r in TAILS:
        x = steps(CE(p, a, 0, [1, 0, 0, 1], r), 11)
        y = steps(CE(p, a, 0, [1, 1, 0, 1], r), 3)
        c3e = x[1:] == y[1:] == ('E', R0 - 4) and set(x[0]) == set(y[0])
        ok &= c3e
        print(f'3e. p={p} a={a} r={r}: (1 0 0 1 r) after 11 steps = (1 1 0 1 r) after 3 steps, '
              f'state {x[1]} reading {x[0].get(x[2], 0)}: {c3e}')

# in M16_B (O1 = 1RM) the bridge pattern does not produce the Kd1 step with 0 1 left in front of r
nb, _ = run_to(CE(3, 4, 0, [1, 0, 0, 1], [0, 0]), CE(6, 4, 2, [0, 1], [0, 0]), table=TB, limit=200000)
c3 = nb is None
ok &= c3
print(f'3d. same bridge instance under M16_B (O1 = 1RM) does not reach Ce_gen 6 4 2 (0 1 r): {c3}')

# 4. other macro steps on small instances
for pp in (0, 1):
    for k in (2, 3):
        for c in (0, 1):
            for r in TAILS[:2]:
                report(f"4a. CE_EVEN p'={pp} k={k} c={c} r={r}",
                       run_to(CE(pp + 1, 2 * k, c + 1, [], r), CE(pp + k + 1, W(pp, 1), c, [], r)), 0)
for pp in (0, 1):
    for a in (4, 6):
        for r in TAILS[:2]:
            report(f"4b. D1_REL p'={pp} a={a} r={r}",
                   run_to(CE(pp + 2, a, 0, [0], r), CE(pp, W(pp, 1), 0, [1] * (a + 3), r)), 0)
for pp in (0, 1):
    for k in (1, 2):
        for s in TAILS[:2]:
            P, A = pp + W(pp + 1, 1) // 2 + 2, W(pp, 1)
            report(f"4c. D2_STEP_full p''={pp} k={k} s={s}",
                   run_to(CE(pp + 3, 2 * k + 2, 0, [1, 0, 1], s), CE(P, A, k, [1, 1, 0], s)), 0)

# 5. the halt
for p in (3, 5, 9):
    for a in (4, 6, 10):
        tape, q, h = CE(p, a, 0, [1], [])
        tape = dict(tape)
        n = 0
        while True:
            tr = T[(q, tape.get(h, 0))]
            if tr is None:
                break
            tape[h] = tr[0]
            q, h = tr[2], h + tr[1]
            n += 1
        c5 = q == 'P' and tape.get(h, 0) == 0 and sum(tape.values()) == p + a + 5 and n == 5
        ok &= c5
        print(f'5. halt from Ce_gen {p} {a} 0 (1): {n} steps then P reads 0, ones = {sum(tape.values())} '
              f'(want {p + a + 5}): {c5}')

print('ALL CHECKS PASS' if ok else 'SOME CHECK FAILED')
raise SystemExit(0 if ok else 1)
