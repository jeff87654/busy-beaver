import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sim import Machine
PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "bb54.txt")
MACH = Machine(open(PATH).read().strip())

def build(k, n, mv, tail):
    tape = {}
    p = -1
    for _ in range(k): tape[p] = 2; p -= 1
    for _ in range(2*mv+1): tape[p] = 3; p -= 1
    for i in range(n): tape[i] = 1
    for i, c in enumerate(tail): tape[n+i] = c
    return tape, 0, 0

def left_repr(tape, head):
    # nearest-first list of non-zero cells left of the head
    out = []
    j = head-1
    while len(out) < 40:
        s = tape.get(j,0)
        if s != 0: out.append(s)
        j -= 1
        if j < -60: break
    return out

def right_repr(tape, head):
    out = []
    j = head+1
    while len(out) < 40:
        s = tape.get(j,0)
        if s != 0: out.append(s)
        j += 1
        if j > 60: break
    return out

def macro_state(tape, head, state):
    """Try to read off the Ligocki parameters (k,n,m) from the tape."""
    L = left_repr(tape, head); R = right_repr(tape, head)
    # the head is on a 1 (state A, symbol 1) -> count the run of ones to the right
    sym = tape.get(head,0)
    n = 1 if sym == 1 else 0
    # count the twos immediately left
    k = 0; j = head-1
    while tape.get(j,0) == 2: k += 1; j -= 1
    # count the threes after the twos
    m = 0
    while tape.get(j,0) == 3: m += 1; j -= 1
    return k, n, m, L, R, sym

def run(k, n, mv, tail, steps):
    tape, head, state = build(k, n, mv, tail)
    print("INIT  k=%d n=%d m=%d tail=%s" % (k,n,mv,tail))
    prev = None
    for i in range(steps):
        sym = tape.get(head,0)
        r = MACH.step(state, sym)
        if r is None:
            print("%3d HALT state %s sym %d" % (i+1, chr(65+state), sym)); return
        nq, w, mv2 = r
        tape[head] = w
        head += 1 if mv2=='R' else -1
        state = nq
        kk,nn,mm,L,R,s = macro_state(tape, head, state)
        cur = (chr(65+state), head, kk, nn, mm, tuple(R))
        if cur != prev:
            print("%3d state %s head %3d  | k=%d n=%d m=%d | L=%s | R=%s" % (
                i+1, chr(65+state), head, kk, nn, mm, ''.join(map(str,L)), ''.join(map(str,R))))
            prev = cur

if __name__ == "__main__":
    k = int(sys.argv[1]); n = int(sys.argv[2]); mv = int(sys.argv[3])
    tail = [int(c) for c in sys.argv[4]] if len(sys.argv)>4 and sys.argv[4] else []
    steps = int(sys.argv[5]) if len(sys.argv)>5 else 60
    run(k, n, mv, tail, steps)
