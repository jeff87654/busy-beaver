"""Independent literal checks of the BB19 write-up's rules (does not use the Coq files).

    python bb19_writeup_chk.py

Simulates the machine string cell by cell and checks, on concrete instances:
  1. the opening: in its first 10^7 steps from the blank tape the machine never reads N0, Q0, Q1, R0, R1, S0 or S1
     (the counter is dormant until the first reflection pass), and never goes right of cell +8;
  2. P_BOOT_141 (the left-end bootstrap of every pass) reads N1 but not N0, and not the tail z;
  3. seed pass start (SEED_c1_raw): from Ce_gen p a 0 (1 0 0 ...) the head reaches the left end of the tape in state
     P with (1 0)^(p-1) 0 0 1^(a+7) to its right; S crosses the a+6 ones of the block (S1 read a+6 times), and the
     head never goes right of h+4;
  4. countdown pass start (CD_DUMP_raw): from Ce_gen p a 0 (1 0 0 1 1 r) the head reaches the left end in state P
     with (1 0)^p 1^(a+6) 0 0 r to its right (two parked 1s erased), and never visits r;
  5. the halt (HALT_step): from Ce_gen p a 0 (1 0 0 1) the machine halts after 6 steps (the 6th is R0), in R reading
     0, with p + a + 6 ones on the tape before the halting transition writes its 1;
  6. the whole run of the right end, for small a_0: literal pass starts (as in 3-5), with the middle of each pass
     replaced by the tape effect of the Coq lemmas (P_BOOT: (1 0)^3 z -> E facing 1^43 z; Kd1_step: 1 1 u -> u;
     the reload D1_REL_gen + Kd1 steps with a even: 0 u -> 1 u). It checks that there are exactly a_0/2 + 4 passes,
     that the halt comes right after the last one, that each countdown pass moves the boundary 2 cells right, and
     that the halt happens at the cell of the first boundary + 5.
Ce_gen p a 0 X is the engine configuration  0^inf (1 0)^p 1^(a+2) [E on 0] X 0^inf.
"""
MACHINE = ('1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_'
           '1RQ0RG_0LG1LP_0LO1LP_1LS0RR_1RZ0LP_0LR1LS')
COUNTER = {('N', 0), ('Q', 0), ('Q', 1), ('R', 0), ('R', 1), ('S', 0), ('S', 1)}


def parse(m):
    t = {}
    for i, row in enumerate(m.split('_')):
        for s in (0, 1):
            x = row[3 * s:3 * s + 3]
            t[(chr(65 + i), s)] = None if x == '---' or x[2] == 'Z' else (int(x[0]), 1 if x[1] == 'R' else -1, x[2])
    return t


T = parse(MACHINE)


def run(tape, q, h, steps, hook=None, stop=None):
    """Run at most `steps` steps. Returns (status, steps done, state, head); a halt counts as one step."""
    for n in range(steps):
        if stop and stop(q, h):
            return 'STOP', n, q, h
        s = tape.get(h, 0)
        if hook:
            hook(q, s, h)
        tr = T[(q, s)]
        if tr is None:
            return 'HALT', n + 1, q, h
        tape[h] = tr[0]
        h += tr[1]
        q = tr[2]
    return 'RUN', steps, q, h


def ce_gen(p, a, x, h=0):
    """Ce_gen p a 0 X with E at cell h. Returns the tape and the blank cell left of (1 0)^p."""
    tape, pos = {}, h - 1
    for _ in range(a + 2):
        tape[pos] = 1
        pos -= 1
    for _ in range(p):
        tape[pos] = 0
        tape[pos - 1] = 1
        pos -= 2
    for i, b in enumerate(x):
        tape[h + 1 + i] = b
    return tape, pos


def word(tape, lo, hi):
    return ''.join(str(tape.get(i, 0)) for i in range(lo, hi + 1))


def to_left_end(p, a, x):
    """Run from Ce_gen p a 0 X until P stands on the blank left of the stack, recording reads."""
    tape, left = ce_gen(p, a, x)
    reads, maxh = [], [0]

    def hook(q, s, h):
        reads.append((q, s))
        maxh[0] = max(maxh[0], h)
    r = run(tape, 'E', 0, 10 ** 5, hook, lambda q, h: q == 'P' and h == left)
    return r, tape, left, reads, maxh[0]


ok = True

# 1. the opening
used, maxh1 = set(), [0]


def hook1(q, s, h):
    used.add((q, s))
    maxh1[0] = max(maxh1[0], h)


r = run({}, 'A', 0, 10 ** 7, hook1)
bad = used & COUNTER
c1 = r[0] == 'RUN' and not bad and maxh1[0] == 8
print(f'1. opening, 10^7 steps: counter slots read: {sorted(bad) or "none"}; rightmost cell {maxh1[0]}: {c1}')
ok &= c1

# 2. P_BOOT_141: (const 0) <{{P}} ((1 0)^3 z), 141 steps, z never read
used2, zread = set(), []
tape = {1 + i: b for i, b in enumerate([1, 0, 1, 0, 1, 0])}
run(tape, 'P', 0, 141, lambda q, s, h: (used2.add((q, s)), h >= 7 and zread.append(h)))
c2 = ('N', 0) not in used2 and ('N', 1) in used2 and not zread and not (used2 & (COUNTER - {('N', 0)}))
print(f'2. P_BOOT_141: reads N1 {("N", 1) in used2}, reads N0 {("N", 0) in used2}, reads Q/R/S '
      f'{bool(used2 & (COUNTER - {("N", 0)}))}, reads z {bool(zread)}: {c2}')
ok &= c2

# 3, 4, 5 on concrete instances
n345 = 0
for p in (3, 4, 5, 8, 11):
    for a in (4, 6, 8, 12):
        # 3. seed pass start
        r3, t3, left, reads, mh = to_left_end(p, a, [1])
        got = word(t3, left + 1, 12)
        want = '10' * (p - 1) + '00' + '1' * (a + 7) + '0' * 8
        c3 = (r3[0] == 'STOP' and got == want and reads.count(('S', 1)) == a + 6 and reads.count(('S', 0)) == 1
              and ('Q', 1) not in reads and ('R', 0) not in reads and mh == 4)
        # 4. countdown pass start, several tails r
        c4 = True
        for tail in ([], [1], [1, 1, 1], [0, 1, 1, 0, 1], [1] * 9):
            r4, t4, left, reads, mh = to_left_end(p, a, [1, 0, 0, 1, 1] + tail)
            got = word(t4, left + 1, 6 + len(tail) + 3)
            want = '10' * p + '1' * (a + 6) + '00' + ''.join(map(str, tail)) + '0000'
            c4 &= (r4[0] == 'STOP' and got == want and mh <= 5 and not any(q == 'S' for q, _ in reads)
                   and ('Q', 0) not in reads)
        # 5. the halt
        t5, _ = ce_gen(p, a, [1, 0, 0, 1])
        r5 = run(t5, 'E', 0, 100)
        c5 = r5 == ('HALT', 6, 'R', 5) and t5.get(5, 0) == 0 and sum(t5.values()) == p + a + 6
        ok &= c3 and c4 and c5
        n345 += 1
        print(f'3-5. p={p:2d} a={a:2d}: seed start (10)^(p-1) 00 1^(a+7): {c3}; '
              f'countdown start (10)^p 1^(a+6) 00 r: {c4}; halt after 6 steps, p+a+6 ones: {c5}')


# 6. the right end over the whole run, small a_0
def right_end_run(a0, p_lit=6, a_even=(4, 6)):
    """Returns (passes, boundary heads, halt cell, halt state). X[i] is at cell xs + i; E's head is at xs - 1."""
    X, xs = [1], 1
    heads, passes = [], 0
    while True:
        while True:  # Kd1 steps and reloads until X starts with 1 0
            x0 = X[0] if X else 0
            x1 = X[1] if len(X) > 1 else 0
            if x0 == 1 and x1 == 1:
                X, xs = X[2:], xs + 2
            elif x0 == 0:
                X = [1] + X[1:]
            else:
                break
        h = xs - 1
        heads.append(h)
        assert X[:3] + [0] * (3 - len(X[:3])) == [1, 0, 0], X[:6]
        a = a0 if passes == 0 else a_even[passes % 2]
        tape, left = ce_gen(p_lit, a, X, h)
        rr = run(tape, 'E', h, 10 ** 5, None, lambda q, hh: q == 'P' and hh == left)
        if rr[0] == 'HALT':
            return passes, heads, rr[3], rr[2], rr[1]
        assert rr[0] == 'STOP'
        passes += 1
        hi = max(i for i, v in tape.items() if v)
        w = [tape.get(i, 0) for i in range(left + 1, hi + 1)]
        assert w[:6] == [1, 0, 1, 0, 1, 0]
        X, xs = [1] * 43 + w[6:], left + 7 - 43  # P_BOOT: E faces 1^41 1 1 z, z unchanged in place


for a0 in (4, 6, 8, 10, 20, 40):
    passes, heads, hcell, hq, hsteps = right_end_run(a0)
    steps_ok = all(heads[k + 1] - heads[k] == 2 for k in range(1, len(heads) - 1))
    c6 = (passes == a0 // 2 + 4 and heads[0] == 0 and heads[1] == -(a0 + 6) and steps_ok and heads[-1] == 0
          and hcell == 5 and hq == 'R' and hsteps == 6)
    ok &= c6
    print(f'6. a_0={a0:2d}: passes {passes} (a_0/2+4 = {a0 // 2 + 4}); boundary after the seed pass at '
          f'{heads[1]} (-(a_0+6)), then +2 per pass, last at {heads[-1]}; halt in {hq} at cell {hcell}: {c6}')

print('ALL CHECKS PASS' if ok else 'SOME CHECK FAILED')
raise SystemExit(0 if ok else 1)
