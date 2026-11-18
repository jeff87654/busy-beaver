#!/usr/bin/env python3
"""Shared helpers for proving Turing-machine halting in Coq on top of busycoq.

Provides:
  * a parser for the TNF machine string  ("1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC"),
  * a tape simulator for that machine,
  * emitters that turn a configuration into a busycoq tape term.

The machine string has one row per state, rows separated by "_", and each row
lists the transition for every symbol as three characters:

    <write symbol><direction><next state>          e.g.  "1RB", "3LB", "1RZ"

The next state "Z" means *halt*.  The write symbol and the direction are given
in the order 0, 1, 2, ... and the rows are given in the order A, B, C, ...

The simulator mirrors busycoq's tape representation exactly: a configuration is
a triple (left stream, symbol under the head, right stream); the left stream is
listed from the head outwards, the right stream likewise.
"""

import re

STATE_LETTERS = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"


# --------------------------------------------------------------------------
# machine string
# --------------------------------------------------------------------------

class Machine:
    """A Turing machine given by a TNF machine string."""

    def __init__(self, spec):
        self.spec = spec
        rows = spec.split("_")
        self.nstates = len(rows)
        width = len(rows[0])
        if width % 3 != 0:
            raise ValueError("row %r has length %d, not a multiple of 3" % (rows[0], width))
        self.nsyms = width // 3
        for r in rows:
            if len(r) != width:
                raise ValueError("all rows must have the same length")
        self.table = {}          # (state_index, symbol) -> (write, dir, next) or None
        self.halt = set()        # (state_index, symbol) pairs that halt
        for i, row in enumerate(rows):
            for j in range(self.nsyms):
                entry = row[3 * j:3 * j + 3]
                w, d, n = entry[0], entry[1], entry[2]
                if not w.isdigit():
                    raise ValueError("bad write symbol in %r" % entry)
                if d not in "LR":
                    raise ValueError("bad direction in %r" % entry)
                if n == "Z":
                    self.table[(i, j)] = (int(w), d, None)
                    self.halt.add((i, j))
                else:
                    if n not in STATE_LETTERS[:self.nstates]:
                        raise ValueError("bad next state in %r" % entry)
                    self.table[(i, j)] = (int(w), d, STATE_LETTERS.index(n))

    # -- convenience -------------------------------------------------------
    def state_name(self, i):
        return STATE_LETTERS[i]

    def states(self):
        return [STATE_LETTERS[i] for i in range(self.nstates)]

    def sym_names(self):
        return ["S%d" % j for j in range(self.nsyms)]

    def transition_string(self):
        """The TNF string, regenerated from the parsed table (for round-trip tests)."""
        rows = []
        for i in range(self.nstates):
            row = ""
            for j in range(self.nsyms):
                w, d, q = self.table[(i, j)]
                row += "%d%s%s" % (w, d, "Z" if q is None else STATE_LETTERS[q])
            rows.append(row)
        return "_".join(rows)

    def check_roundtrip(self):
        if self.transition_string() != self.spec:
            raise AssertionError("machine string did not round-trip: %r vs %r"
                                 % (self.transition_string(), self.spec))

    def halt_entry(self):
        """The single halting entry, as (state, symbol index), or None."""
        if len(self.halt) != 1:
            return None
        (i, j) = next(iter(self.halt))
        return STATE_LETTERS[i], j

    def halt_entry_pos(self):
        """The character offset of the halting entry in the machine string, and
        the three characters of the entry."""
        if len(self.halt) != 1:
            return None, None
        (i, j) = next(iter(self.halt))
        width = 3 * self.nsyms + 1
        off = i * width + 3 * j
        return off, self.spec[off:off + 3]


# --------------------------------------------------------------------------
# simulator
# --------------------------------------------------------------------------

class Config:
    """A configuration: left (nearest first), symbol under the head, right (nearest first)."""

    def __init__(self, left, cur, right, state):
        self.left, self.cur, self.right, self.state = left, cur, right, state

    def copy(self):
        return Config(list(self.left), self.cur, list(self.right), self.state)

    def step(self, m):
        """Perform one step; returns False when the machine halts.

        Like busycoq, the halting transition is modelled as "stop without
        writing": busycoq's [tm] returns [None] for the halting entry, so the
        halting configuration is a *configuration*, not a successor.  The
        effect of the halting write on the score is accounted for in the
        proof, not here.
        """
        i = STATE_LETTERS.index(self.state)
        t = m.table[(i, self.cur)]
        if t is None or t[2] is None:
            return False
        w, d, q = t
        if d == "R":
            self.left = [w] + self.left
            self.cur = self.right[0] if self.right else 0
            self.right = self.right[1:]
        else:
            self.right = [w] + self.right
            self.cur = self.left[0] if self.left else 0
            self.left = self.left[1:]
        self.state = STATE_LETTERS[q]
        return True

    def word(self, k=60):
        return "".join(str(x) for x in (list(reversed(self.left)) + [self.cur] + self.right))

    def key(self):
        return (self.state, tuple(self.left), self.cur, tuple(self.right))


def blank(m):
    return Config([], 0, [], "A")


def run(m, cfg, nsteps):
    """Run exactly nsteps steps; returns the resulting configuration."""
    for _ in range(nsteps):
        if not cfg.step(m):
            break
    return cfg


def find_config(m, cfg, target, limit):
    """Run until the configuration equals target (compare state, head symbol and
    both streams) or until limit steps have been taken.  Returns (steps, found)."""
    cur = cfg.copy()
    for k in range(limit + 1):
        if cur.key() == target.key():
            return k, True
        if k == limit:
            return k, False
        if not cur.step(m):
            return k, False
    return limit, False


# --------------------------------------------------------------------------
# Coq term emission
# --------------------------------------------------------------------------

def coq_sym(j):
    return "S%d" % j


def coq_stream(cells):
    """A Coq stream term for a list of cells (nearest first) followed by blanks."""
    if not cells:
        return "Streams.const S0"
    return "[" + ";".join(coq_sym(x) for x in cells) + "] *> Streams.const S0"


def coq_config(cfg):
    """A busycoq configuration term: (state, (left, head symbol, right))."""
    return "(%s, (%s, %s, %s))" % (cfg.state, coq_stream(cfg.left),
                                   coq_sym(cfg.cur), coq_stream(cfg.right))


def coq_states(m):
    """The Coq state constructors, e.g. "Inductive state := A | B | C." """
    return " | ".join(m.states())


def coq_syms(m):
    return " | ".join(coq_syms(m))


def coq_table(m):
    """The busycoq transition table definition [tm] for this machine.

    The halting entry becomes [None], exactly as busycoq models it.
    """
    lines = []
    for i in range(m.nstates):
        cells = []
        for j in range(m.nsyms):
            w, d, q = m.table[(i, j)]
            if q is None:
                cells.append("None")
            else:
                cells.append("Some (%d, %s, %s)" % (w, d, STATE_LETTERS[q]))
        row = "  | %s, %d => %s" % (STATE_LETTERS[i], 0, cells[0])
        for j in range(1, m.nsyms):
            row += "  | %s, %d => %s" % (STATE_LETTERS[i], j, cells[j])
        lines.append(row)
    body = "\n".join(lines)
    return ("Definition tm : TM := fun '(q, s) =>\n  match q, s with\n"
            + body + "\n  end.")


def parse_machine(spec):
    """Parse a machine string, tolerating whitespace and a trailing period."""
    spec = spec.strip().rstrip(".")
    if not re.fullmatch(r"[0-9A-Z]+(_[0-9A-Z]+)*", spec):
        raise ValueError("not a TNF machine string: %r" % spec)
    m = Machine(spec)
    m.check_roundtrip()
    return m
