import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sim import Machine

PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "bb54.txt")
MACH = Machine(open(PATH).read().strip())

def build(k, n, mv, tail):
    """0^inf 3^(2m+1) 2^k  A> 1^n tail ; head at 0."""
    tape = {}
    p = -1
    for _ in range(k):
        tape[p] = 2; p -= 1
    for _ in range(2*mv+1):
        tape[p] = 3; p -= 1
    for i in range(n):
        tape[i] = 1
    for i, c in enumerate(tail):
        tape[n+i] = c
    return tape, 0, 0   # tape, head, state(A)

def show(tape, head, state, w=12):
    lo, hi = head-w, head+w
    left = ''.join(str(tape.get(j,0)) for j in range(head-1, max(lo,head-w)-1, -1))
    right= ''.join(str(tape.get(j,0)) for j in range(head+1, hi+1))
    return "state %s head %3d | L(nearest-first) %-14s | R(nearest-first) %s" % (
        chr(65+state), head, left, right)

def run(k, n, mv, tail, steps):
    tape, head, state = build(k, n, mv, tail)
    print("INIT  " + show(tape, head, state))
    for i in range(steps):
        sym = tape.get(head,0)
        r = MACH.step(state, sym)
        if r is None:
            print("%3d   HALT  (state %s reads %d)" % (i+1, chr(65+state), sym))
            return
        nq, w, mv2 = r
        tape[head] = w
        head += 1 if mv2=='R' else -1
        state = nq
        print("%3d   %s" % (i+1, show(tape, head, state)))

if __name__ == "__main__":
    k = int(sys.argv[1]); n = int(sys.argv[2]); mv = int(sys.argv[3])
    tail = [int(c) for c in sys.argv[4]] if len(sys.argv)>4 and sys.argv[4] else []
    steps = int(sys.argv[5]) if len(sys.argv)>5 else 40
    run(k, n, mv, tail, steps)
