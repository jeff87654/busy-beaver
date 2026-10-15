#!/usr/bin/env python3
"""Pinned syntax extraction and finite command-model regressions.

Only reads the source as an AST. It never imports TMBuilder or executes the
source's methods. Numeric unpair uses the closed Cantor inverse, cross-checked
against the source's successor walk on the finite range reported below.
The constructor-token interpretation, exact gate-tail syntax, and parsed
Coq program regressions do not prove source execution correspondence.
Source constructor subroutines, the source-unpair/Coq correspondence, command
field/candidate decoding, reach/drain, and Coq kernel checking remain open.
"""
import argparse
import ast
import hashlib
import itertools
import math
from pathlib import Path
import re

PIN = "b489f6f59dfd6af070db18897ca76b275a931f9958941bceb697c6dd3f4d751a"
DEFAULT_SOURCE = Path("/Users/mira/work/mm0-bb/research/"
                      "pa242_zfc257_intake_2026_09_29/package_members/"
                      "layout_core/inputs/pa/source.py")
COQ = Path(__file__).resolve().parents[1] / "coq" / "logic"
ARITY = dict(wim=2, wel=2, wal=2, weq=2, wn=1, wa=2, wex=2)


def app(op, *args):
    if op == "wn":
        return app("wim", args[0], 1)
    if op == "wa":
        return app("wn", app("wim", args[0], app("wn", args[1])))
    if op == "wex":
        return app("wn", app("wal", args[0], app("wn", args[1])))
    return (op, *args)


def parse_formula(text):
    tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_]*|[0-9]+|[()]", text)
    pos = 0

    def atom():
        nonlocal pos
        token = tokens[pos]
        pos += 1
        if token == "(":
            value = atom()
            assert tokens[pos] == ")", tokens[pos:]
            pos += 1
            return value
        if token in ARITY:
            return app(token, *(atom() for _ in range(ARITY[token])))
        assert token != ")"
        return int(token) if token.isdecimal() else token

    result = atom()
    assert pos == len(tokens), tokens[pos:]
    return result


def extract_source(source):
    raw = source.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == PIN, "PA source pin mismatch"
    tree = ast.parse(raw)
    cls, = [node for node in tree.body if isinstance(node, ast.ClassDef)]
    axioms, = [node for node in cls.body
               if isinstance(node, ast.FunctionDef) and node.name == "axioms"]
    assert isinstance(axioms.body[-1], ast.Return)
    source_nodes = axioms.body[-1].value.elts
    # Exact six-node suffix: the last conjunction constructor plus all five
    # register operations of the freshness gate. Syntax equality does not
    # establish the execution semantics of while_decnz or if_eq.
    gate_suffix = ast.parse("""[
        wa,
        self.while_decnz(self.param3, [self.scratch1.inc, self.scratch2.inc]),
        self.if_eq(self.scratch1, self.param2,
                   [self.while_decnz(self.topwff, ())]),
        self.while_decnz(self.scratch2, self.scratch1.inc),
        self.while_decnz(self.param1, self.param2.inc),
        self.if_eq(self.scratch1, self.param2,
                   [self.while_decnz(self.topwff, ())])
    ]""", mode="eval").body.elts
    assert [ast.dump(node) for node in source_nodes[-6:]] == [ast.dump(node) for node in gate_suffix], "source gate-tail AST mismatch"
    current, stack, param2 = "T", ["W"], "h"
    reached_gate = False
    operations = 0
    for index, node in enumerate(source_nodes):
        name = node.id if isinstance(node, ast.Name) else node.func.attr
        if name == "while_decnz" and node.args[0].attr == "param3":
            assert index == len(source_nodes) - 5, "unexpected earlier gate"
            reached_gate = True
            break
        operations += 1
        if name in {"par1", "par2", "par3", "pushwff"}:
            stack.append(current)
            current = {"par1": "a", "par2": param2,
                       "par3": "c", "pushwff": 0}[name]
        elif name == "read":
            assert node.args[0].attr == "param2"
            param2 = "b"  # incoming cache plus the newly read offset
        elif name == "unpair":
            assert node.args[2].attr == "prooflist"
        elif name == "while_decnz":
            register = node.args[0].attr
            if register == "scratch1":
                assert node.args[1].attr == "inc"
                assert node.args[1].value.attr == "topwff"
                current = "u"
            else:
                assert register == "scratch2"
                assert node.args[1].value.attr == "prooflist"
        elif name in ARITY:
            current = app(name, current) if ARITY[name] == 1 else app(name, stack.pop(), current)
        else:
            raise AssertionError(f"unsupported source operation {name}")
    assert reached_gate and stack[0] == "W"
    return current, list(reversed(stack[1:])), operations


def coq_definitions():
    text = (COQ / "Codes238.v").read_text()
    text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    definitions = {}
    for name in [*(f"rho{i}" for i in range(1, 9)), "bundle"]:
        match = re.search(r"Definition\s+" + name + r"\b[^:]*:=\s*(.*?)\.", text, re.S)
        assert match, name
        definitions[name] = parse_formula(match[1])
    return definitions


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n):
    diagonal = (math.isqrt(8 * n + 1) - 1) // 2
    b = n - diagonal * (diagonal + 1) // 2
    return diagonal - b, b


def value(expr, env):
    if isinstance(expr, int):
        return expr
    if isinstance(expr, str):
        return env[expr]
    op, a, b = expr
    return 4 * pair(value(a, env), value(b, env)) + {"wim": 0, "wel": 1, "wal": 2, "weq": 3}[op]


def pack(xs, tail):
    for x in reversed(xs):
        tail = pair(x, tail)
    return tail


def programs():
    # Parse the actual Coq command definitions; no duplicate hand-written
    # instruction lists are used for the compiler regression tests.
    text = (COQ / "Compiler238.v").read_text()
    text = re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)
    bodies = {}
    for name in ["reset", "row_program", "generalize_program", "mp_program", "bundle_program"]:
        match = re.search(r"Definition\s+" + name + r"\b(.*?)\s*:=\s*(.*?)\.", text, re.S)
        assert match, name
        header = match[1].split(":", 1)[0].strip()
        if name == "row_program":
            header = header.strip("()").split(":", 1)[0]
        bodies[name] = (header.split(), match[2])

    def evaluate(name, args=()):
        params, body = bodies[name]
        assert len(args) == len(params), (name, params, args)
        env = dict(zip(params, args))
        tokens = re.findall(r"\+\+|[A-Za-z_][A-Za-z0-9_]*|[0-9]+|[][();-]", body)
        pos = 0

        def atom():
            nonlocal pos
            token = tokens[pos]
            pos += 1
            if token == "(":
                result = expression()
                assert tokens[pos] == ")"
                pos += 1
                return result
            if token == "[":
                result = []
                while tokens[pos] != "]":
                    result.append(atom())
                    if tokens[pos] == ";":
                        pos += 1
                    else:
                        assert tokens[pos] == "]"
                pos += 1
                return result
            if token in {"DROP", "NIP", "MP", "AX"}:
                return (token, *(atom() for _ in range({"DROP": 0, "NIP": 0, "MP": 1, "AX": 4}[token])))
            if token == "repeat":
                command, count = atom(), atom()
                return [command] * count
            if token in bodies:
                return evaluate(token, tuple(atom() for _ in bodies[token][0]))
            if token.isdecimal():
                return int(token)
            return env[token]

        def expression():
            nonlocal pos
            result = atom()
            while pos < len(tokens) and tokens[pos] in {"++", "-"}:
                op = tokens[pos]
                pos += 1
                other = atom()
                result = result + other if op == "++" else max(0, result - other)
            return result

        result = expression()
        assert pos == len(tokens), (name, tokens[pos:])
        return result

    return (evaluate("reset"),
            lambda j, a, b, c, u: evaluate("row_program", (j, a, b, c, u)),
            lambda a, ks: evaluate("generalize_program", (a, ks)),
            lambda b, ks, ls: evaluate("mp_program", (b, ks, ls)),
            lambda a, b, c: evaluate("bundle_program", (a, b, c)))


def run(commands, q, defs):
    t, w, d, h = q
    for command in commands:
        op, *args = command
        if op == "MP":
            d += args[0]
            t, w = (d, pair(0, w)) if 4 * pair(t, d) == h else (0, w)
            h = 0
        elif op == "DROP":
            t, w = h, pair(t, w)
        elif op == "NIP":
            if h == 1:
                return None
            h, w = unpair(w)
        elif op == "AX":
            c, x, y, u = args
            a, b = d + x, h + y
            env = dict(a=a, b=b, c=c, u=u)
            rows = [value(defs[f"rho{i}"], env) for i in range(1, 9)]
            w = pack(rows + [4 * pair(a, h) + 2, t], w)
            # Declared command-model gate. The exact source AST gate suffix
            # was checked above; its source execution equivalence is open.
            t = 0 if c == a or c == b else value(defs["bundle"], env)
            d = h = 0
        else:
            raise AssertionError(command)
    return t, w, d, h


def check(source):
    bundle, stack, operations = extract_source(source)
    defs = coq_definitions()
    assert stack == [*(defs[f"rho{i}"] for i in range(1, 9)), app("wal", "a", "h"), "T"]
    assert bundle == defs["bundle"], "source/Coq bundle mismatch"
    walked = (0, 0)
    for n in range(4096):
        assert unpair(n) == walked
        assert pair(*walked) == n
        a, b = walked
        walked = (a - 1, b + 1) if a else (b + 1, 0)
    reset, leaf, gen, mp, bundle_leaf = programs()
    checks = 0
    for t, w in itertools.product([0, 1, 4], [0, 7]):
        assert run(reset, (t, w, 0, 0), defs) == (0, w, 0, 0)
        checks += 1
        for a, b, c, u in itertools.product(range(2), repeat=4):
            env = dict(a=a, b=b, c=c, u=u)
            for j in range(1, 9):
                assert run(leaf(j, a, b, c, u), (t, w, 0, 0), defs) == (value(defs[f"rho{j}"], env), w, 0, 0)
                checks += 1
        for a, b, c in [(0, 0, 1), (0, 1, 2), (1, 0, 2)]:
            ks = bundle_leaf(a, b, c)
            assert run(ks, (t, w, 0, 0), defs) == (value(defs["bundle"], dict(a=a, b=b, c=c)), w, 0, 0)
            checks += 1
        for a in range(2):
            antecedent = gen(a, reset)
            implication = leaf(2, a, 0, 0, 0)
            A = 4 * pair(a, 0) + 2
            B = 4 * pair(A, A)
            assert run(antecedent, (t, w, 0, 0), defs) == (A, w, 0, 0)
            assert run(mp(B, antecedent, implication), (t, w, 0, 0), defs) == (B, w, 0, 0)
            checks += 2
    assert run([("NIP",)], (0, 0, 0, 1), defs) is None
    print(f"source SHA256 {PIN}")
    print(f"exact AST syntax: {operations} constructor-stream operations and six-node gate suffix")
    print("PA rows 1..8 and bundle match the interpreted source constructor stream")
    print(f"dual Cantor inverse: 4096 source-walk values; command regression checks: {checks + 1}")
    print("Unverified: source constructor execution; source-unpair/Coq correspondence; command fields/candidate decoder; reach/drain; Coq kernel")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=DEFAULT_SOURCE)
    check(parser.parse_args().source)
