"""Literal check of the hand-derived P12 macro rules (bb12-p2 agent).  Uses only lit12.py.
Y p u w = [1]^u [0;1]^p 0^inf I> w   (left written nearest-first; on the tape: (10)^p 1^u then head)."""
import random
from lit12 import parse, P12, Tape, run

tm = parse(P12)


def Wx(j, b):
    if j == 0:
        return b + 3
    x = 2
    for _ in range(b + 1):
        x = Wx(j - 1, x)
    return x


def mk(p, u, w):
    """tape cells for Y p u w; w = list of bits starting at the head cell."""
    cells = {}
    pos = -1
    for _ in range(u):
        cells[pos] = 1
        pos -= 1
    for _ in range(p):
        # nearest-first [0;1]: 0 at pos, 1 at pos-1
        cells[pos - 1] = 1
        pos -= 2
    for i, c in enumerate(w):
        if c:
            cells[i] = 1
    return cells


def same(t1, h1, cells2):
    a = {k - h1: v for k, v in t1.items() if v}
    b = {k: v for k, v in cells2.items() if v}
    return a == b


def to_next_Y(cells, maxsteps):
    tape = Tape(dict(cells), 0)

    def stop(pq, q, d, tp):
        return q == 'I' and d == 1
    q, n, halted = run(tm, 'I', tape, maxsteps, stop)
    return q, n, halted, tape


def stock(d):
    return [1, 0] * d


fails = 0
count = 0


def check(name, p, u, w, p2, u2, w2, maxsteps=30_000_000):
    global fails, count
    q, n, halted, tape = to_next_Y(mk(p, u, w), maxsteps)
    ok = (not halted) and q == 'I' and same(tape.t, tape.h, mk(p2, u2, w2))
    count += 1
    if not ok:
        fails += 1
        print('FAIL', name, p, u, w[:12], '->expected', p2, u2, 'got q', q, 'halted', halted, 'steps', n)


rnd = random.Random(1)


def tail():
    return [rnd.randint(0, 1) for _ in range(rnd.randint(0, 6))]


# R_A: X p u ([1;0]^d S) -> Y p (W p u + 2) ([1;0]^(d-1) S),  d >= 2
for p in range(0, 3):
    for u in range(0, 12):
        if Wx(p, u) > 3000:
            continue
        for d in (2, 3, 5):
            S = tail()
            check('R_A', p, u, [0] + stock(d) + S, p, Wx(p, u) + 2, stock(d - 1) + S)
# R_Bo: Y p (2m+1) (1 >> T0) -> Y (p-1) (W(p-1,1)+2) ([1;0]^m >> T0),  p >= 1, m >= 1
for p in range(1, 4):
    for m in range(1, 9):
        for _ in range(3):
            T0 = tail()
            check('R_Bo', p, 2 * m + 1, [1] + T0, p - 1, Wx(p - 1, 1) + 2, stock(m) + T0)
# R_Be: Y p (2m) (1 >> 0 >> T) -> Y (p-1+m) (W(p-1,1)+2) T,  p >= 1, m >= 1
for p in range(1, 4):
    for m in range(1, 9):
        for _ in range(3):
            T = tail()
            check('R_Be', p, 2 * m, [1, 0] + T, p - 1 + m, Wx(p - 1, 1) + 2, T)
# BLANK_E: Y p (2m) 0^inf -> Y 0 4 ([1;0]^(p+m+1) 0^inf),  m >= 1
for p in range(0, 9):
    for m in range(1, 9):
        check('BLANK_E', p, 2 * m, [], 0, 4, stock(p + m + 1))
# BOOT2: Y 0 4 ([1;0]^D S) -> Y 2 5 ([1;0]^(D-1) S),  D >= 1
for D in range(1, 8):
    S = tail()
    check('BOOT2', 0, 4, stock(D) + S, 2, 5, stock(D - 1) + S)
print('rules: %d checks, %d failures' % (count, fails))

# R_H: X p u ([1;0] 0^inf) halts at once with p+u+1 ones
hf = 0
for p in range(0, 6):
    for u in range(0, 10):
        tape = Tape(mk(p, u, [0, 1, 0]), 0)
        q, n, halted = run(tm, 'I', tape, 100)
        if not (halted and q == 'E' and sum(tape.t.values()) == p + u + 1):
            hf += 1
            print('R_H FAIL', p, u, q, halted, n)
print('R_H: 60 checks, %d failures' % hf)

# bootstrap from the blank tape: Ch 4 1 ([1;0]^3 0^inf) = [0;1]^4 <H (H reads the 0) | 1 1 0 (10)^3
cells = {0: 1, 1: 1, 2: 0}
for i in range(3):
    cells[3 + 2 * i] = 1
for i in range(4):
    cells[-1 - 2 * i - 1] = 1
cells2 = {k + 1: v for k, v in cells.items()}   # head one cell left of the block
tape = Tape({}, 0)
q = 'A'
found = None
for n in range(1, 2000):
    q, k, halted = run(tm, q, tape, 1)
    if q == 'H' and same(tape.t, tape.h, cells2):
        found = n
        break
print('bootstrap Ch 4 1 ([1;0]^3 0^inf) reached at literal step', found)
