"""Independent literal checks of the BB18 write-up's rules (does not use the Coq files).

    python bb18_writeup_chk.py

Simulates the machine string cell by cell and checks, on concrete instances:
  1. the opening: in its first 10^7 steps from the blank tape the machine never reads N0, Q0, Q1, R0 or R1 (the
     counter is dormant until the first reflection pass), and never goes right of cell +8;
  2. P_BOOT_141 (the left-end bootstrap of every pass) never reads N0 (it does read N1);
  3. pass start (P_DUMP_raw): from Ce_gen p a 0 (1 0 0 ...) the head reaches the left end of the tape in state P,
     with (1 0)^p 1^(a+4) 0 0 1 to its right: the marker is planted and I's 1 is erased;
  4. the halt (HALT_step): from Ce_gen p a 0 (1 0 0 1) the machine halts after 6 steps, in R reading 0,
     with p + a + 5 ones on the tape.
Ce_gen p a 0 X is the engine configuration  0^inf (1 0)^p 1^(a+2) [E on 0] X 0^inf.
"""
MACHINE = ('1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_'
           '0RQ0RG_0LG1LP_0LO1LP_1LQ0RR_1RZ0LP')


def parse(m):
    t = {}
    for i, row in enumerate(m.split('_')):
        for s in (0, 1):
            x = row[3 * s:3 * s + 3]
            t[(chr(65 + i), s)] = None if x == '---' or x[2] == 'Z' else (int(x[0]), 1 if x[1] == 'R' else -1, x[2])
    return t


T = parse(MACHINE)


def run(tape, q, h, steps, hook=None):
    for n in range(steps):
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


def ce_gen(p, a, x):
    tape, pos = {}, -1
    for _ in range(a + 2):
        tape[pos] = 1
        pos -= 1
    for _ in range(p):
        tape[pos] = 0
        tape[pos - 1] = 1
        pos -= 2
    for i, b in enumerate(x):
        tape[1 + i] = b
    return tape, pos


ok = True

# 1. the opening
used, maxh = set(), [0]


def hook1(q, s, h):
    used.add((q, s))
    maxh[0] = max(maxh[0], h)


r = run({}, 'A', 0, 10 ** 7, hook1)
bad = used & {('N', 0), ('Q', 0), ('Q', 1), ('R', 0), ('R', 1)}
c1 = r[0] == 'RUN' and not bad and maxh[0] == 8
print(f'1. opening, 10^7 steps: counter slots read: {sorted(bad) or "none"}; rightmost cell {maxh[0]}: {c1}')
ok &= c1

# 2. P_BOOT_141: (const 0) <{{P}} ((1 0)^3 z), 141 steps, z never read
used2, zread = set(), []
tape = {1 + i: b for i, b in enumerate([1, 0, 1, 0, 1, 0])}
run(tape, 'P', 0, 141, lambda q, s, h: (used2.add((q, s)), h >= 7 and zread.append(h)))
c2 = ('N', 0) not in used2 and ('N', 1) in used2 and not zread
print(f'2. P_BOOT_141: reads N1 {("N", 1) in used2}, reads N0 {("N", 0) in used2}, reads z {bool(zread)}: {c2}')
ok &= c2

# 3, 4
for p in (3, 4, 5, 8, 11):
    for a in (4, 6, 8, 12):
        tape, left = ce_gen(p, a, [1])
        hit = {}

        def hook3(q, s, h):
            if q == 'P' and h == left and 'n' not in hit:
                hit['t'] = dict(tape)
                hit['n'] = True
        run(tape, 'E', 0, 1000, hook3)
        got = ''.join(str(hit['t'].get(i, 0)) for i in range(left + 1, 7)) if hit else None
        want = '10' * p + '1' * (a + 4) + '001' + '00'
        c3 = got == want
        tape, _ = ce_gen(p, a, [1, 0, 0, 1])
        r = run(tape, 'E', 0, 100)
        c4 = r[:3] == ('HALT', 6, 'R') and tape.get(r[3], 0) == 0 and sum(tape.values()) == p + a + 5
        ok &= c3 and c4
        print(f'3/4. p={p:2d} a={a:2d}: pass start leaves (10)^p 1^(a+4) 001: {c3}; halt after 6 steps with p+a+5 ones: {c4}')

print('ALL CHECKS PASS' if ok else 'SOME CHECK FAILED')
raise SystemExit(0 if ok else 1)
