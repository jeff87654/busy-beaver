"""Independent literal checks of the BB16 (M16_B) write-up (does not use the Coq files).

    python bb16_writeup_chk.py

Simulates the machine string cell by cell and checks, on concrete instances:
  1. the opening: from the blank tape the machine reaches Ce_gen 0 4 0 (1^230) [init_ce0], and the halting slot P0
     is not read on the way;
  2. start_38: Ce_gen 0 4 0 (1 1 r) reaches Ca 0 3 (blk 1 (blk 1 (0 1 0 1 0 0 r))) in 38 steps, for several r;
  3. the halt (HALT_step): Ce_gen p a 0 (1) halts in state P reading 0, with p + a + 5 ones on the tape.
Configurations (as in BB16_halt_fw3.v):
  Ce_gen p a 0 X = 0^inf (1 0)^p 1^(a+2) [E on 0] X 0^inf
  Ca j b z       = 0^inf (1 0)^j 1^b [C on 0] z 0^inf,   blk a z = 1 1^a 0 z
"""
MACHINE = '1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP1RM_1RZ1LI'


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


def config(left_outward, q, h, right):
    """tape with head cell h holding right[0]; left_outward = cells h-1, h-2, ..."""
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


ok = True

# 1. opening to Ce_gen 0 4 0 (1^230): E on 0, 6 ones to the left then blank, 230 ones to the right then blank
tape, q, h = {}, 'A', 0
found, p0 = None, False
for n in range(200000):
    if q == 'E' and tape.get(h, 0) == 0 and all(tape.get(h - i, 0) == 1 for i in range(1, 7)) \
            and tape.get(h - 7, 0) == 0 and all(tape.get(h + i, 0) == 1 for i in range(1, 231)) \
            and sum(tape.values()) == 236:
        found = n
        break
    if (q, tape.get(h, 0)) == ('P', 0):
        p0 = True
    r = step(tape, q, h)
    if r is None:
        break
    q, h = r
c1 = found is not None and not p0
print(f'1. opening reaches Ce_gen 0 4 0 (1^230) after {found} steps, P0 read on the way: {p0}: {c1}')
ok &= c1

# 2. start_38 on several tails r (r is never read: it is followed by blanks and checked unchanged)
for r_tail in ([], [1], [1, 0, 1], [0, 1, 1, 0, 1]):
    tape = config(ce_left(0, 4), 'E', 0, [0, 1, 1] + r_tail)
    q, h = 'E', 0
    for _ in range(38):
        q, h = step(tape, q, h)
    # Ca 0 3 (blk 1 (blk 1 (0 1 0 1 0 0 r))): 1^3 [C on 0] 1 1 0 1 1 0 0 1 0 1 0 0 r
    z = [1, 1, 0] + [1, 1, 0] + [0, 1, 0, 1, 0, 0] + r_tail
    want = config([1, 1, 1], 'C', h, [0] + z)
    # r started at cell 3 and must not move: the 12 cells of z before r end at cell 2, so the head is at -10
    c2 = same(tape, q, h, want, 'C', -10)
    ok &= c2
    print(f'2. start_38, r = {r_tail}: {c2}')

# 3. the halt
for p in (3, 5, 9):
    for a in (4, 6, 10):
        tape = config(ce_left(p, a), 'E', 0, [0, 1])
        q, h, n = 'E', 0, 0
        while True:
            r = step(tape, q, h)
            if r is None:
                break
            q, h = r
            n += 1
        c3 = q == 'P' and tape.get(h, 0) == 0 and sum(tape.values()) == p + a + 5 and n == 5
        ok &= c3
        print(f'3. halt from Ce_gen {p} {a} 0 (1): {n} steps then P reads 0, ones = {sum(tape.values())} '
              f'(want {p + a + 5}): {c3}')

print('ALL CHECKS PASS' if ok else 'SOME CHECK FAILED')
raise SystemExit(0 if ok else 1)
