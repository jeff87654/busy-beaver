"""Parser and simulator for TNF-format Turing machines (bbchallenge notation).

TNF string: states are separated by '_'; inside one state the entries are the
transitions for symbols 0,1,2,... in order, each written as <write><move><next>
where <move> is L or R and <next> is the next state letter ('Z' = halt).
'---' marks an undefined transition (the machine dies there).

State letters are canonical: the i-th group is the state A+i, i.e. group 1 is A,
group 2 is B, and so on.
"""

import os
import sys


def parse(s):
    """Return (transitions, nstates, nsyms).

    transitions[q][sym] = (write, move, next) or None for undefined.
    """
    groups = s.split("_")
    nstates = len(groups)
    trans = []
    nsyms = None
    for gi, g in enumerate(groups):
        assert len(g) % 3 == 0, (gi, g)
        m = len(g) // 3
        if nsyms is None:
            nsyms = m
        assert nsyms == m, (gi, g)
        row = []
        for k in range(m):
            e = g[3 * k : 3 * k + 3]
            if e == "---":
                row.append(None)
                continue
            w, mv, nx = e[0], e[1], e[2]
            assert w.isdigit() and mv in "LR" and nx.isalpha(), (gi, e)
            row.append((int(w), mv, ord(nx) - ord("A")))
        trans.append(row)
    return trans, nstates, nsyms


def fmt(trans):
    """Format a transition table back to TNF notation."""
    out = []
    for row in trans:
        g = ""
        for e in row:
            if e is None:
                g += "---"
            else:
                w, mv, nx = e
                g += f"{w}{mv}{chr(ord('A') + nx)}"
        out.append(g)
    return "_".join(out)


class Machine:
    def __init__(self, s):
        self.trans, self.nstates, self.nsyms = parse(s)
        self.string = s

    def step(self, q, sym):
        """Return (newq, newsym, move) or None if undefined.

        A transition to state 'Z' halts: newq is then -1.
        """
        e = self.trans[q][sym]
        if e is None:
            return None
        w, mv, nx = e
        return (nx - 1 if nx == 25 else nx), w, mv

    def run(self, maxsteps=10**7, tape=None, head=0, state=0):
        """Run from a blank tape.  Returns (steps, state, head, tape, status)."""
        if tape is None:
            tape = {}
        steps = 0
        while steps < maxsteps:
            sym = tape.get(head, 0)
            r = self.step(state, sym)
            if r is None:
                return steps, state, head, tape, "undefined"
            nq, w, mv = r
            tape[head] = w
            head += 1 if mv == "R" else -1
            state = nq
            steps += 1
            if state == -1:
                return steps, state, head, tape, "halt"
        return steps, state, head, tape, "maxsteps"


def render(tape, lo, hi, head=None):
    """Render tape[lo..hi] as a string using digits."""
    s = ""
    for i in range(lo, hi + 1):
        s += str(tape.get(i, 0))
    return s


if __name__ == "__main__":
    import os
    import sys

    default = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                           "..", "..", "bb54.txt")
    s = sys.argv[1] if len(sys.argv) > 1 else open(default).read().strip()
    m = Machine(s)
    print("states", m.nstates, "symbols", m.nsyms)
    for q, row in enumerate(m.trans):
        print(
            chr(ord("A") + q),
            [
            "undef" if e is None else f"{e[0]}{e[1]}{chr(ord('A') + e[2])}"
            for e in row
        ],
        )
