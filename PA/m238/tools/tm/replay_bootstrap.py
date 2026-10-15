#!/usr/bin/env python3
"""Reproduce the finite PA238 blank checkpoint from its literal rows.

This is an inspected finite audit, not a Coq proof. No trace or historical
receipt is an input. The full output tape is checked against a separately
specified unary-block representation, not just against decoded registers.
"""

import argparse
import hashlib
import json
from pathlib import Path
import resource
import signal


TABLE_SHA256 = "ffe370842d70bae96688ad5e290073edffe0bb213cf12fe562a75a74bec966de"
STEPS = 799_504
ACTIVE = [0, 2, 0, 0, 0, 0, 6, 0, 0]
EXTRAS = [0] * 5 + [1] + [0] * 318
GRAPH_SHA256 = "124162f14d4b1255ec5dfa0e9fe251a97556926eeaec579ffa6a62f53d67b5a2"
REGISTER_NAMES = ["wffstack", "param1", "axiomcode", "scratch2", "scratch1",
                  "prooflist", "nextproof", "topwff", "param2"]


def parse_table(data):
    """Require the exact start header and complete binary row domain."""
    if hashlib.sha256(data).hexdigest() != TABLE_SHA256:
        raise ValueError("selected PA238 table hash mismatch")
    lines = data.decode("ascii").splitlines()
    if lines[0] != "#! start 0":
        raise ValueError("unexpected start convention")
    rows = {}
    for number, line in enumerate(lines[1:], 2):
        fields = line.split()
        if len(fields) != 5:
            raise ValueError(f"bad transition line {number}")
        q, b, w, direction, target = fields
        if direction not in ("L", "R"):
            raise ValueError(f"bad direction on line {number}")
        q, b, w, target = map(int, (q, b, w, target))
        if b not in (0, 1) or w not in (0, 1) or not 0 <= target <= 238:
            raise ValueError(f"bad symbol/target on line {number}")
        if (q, b) in rows:
            raise ValueError(f"duplicate row on line {number}")
        rows[q, b] = (w, -1 if direction == "L" else 1, target)
    if set(rows) != {(q, b) for q in range(238) for b in (0, 1)}:
        raise ValueError("incomplete or extra transition domain")
    return rows


def blank_replay(rows, steps):
    state = head = 0
    ones = set()
    minimum = maximum = 0
    for clock in range(steps):
        action = rows.get((state, int(head in ones)))
        if action is None:
            raise ValueError(f"early halt at transition {clock}")
        write, move, state = action
        if write:
            ones.add(head)
            if len(ones) > 4096:
                raise ValueError("finite replay exceeds its 4096-cell storage limit")
        else:
            ones.discard(head)
        head += move
        minimum, maximum = min(minimum, head), max(maximum, head)
    return state, head, ones, [minimum, maximum]


def decode_checkpoint(state, head, ones):
    """Locate marker/header and decode every block; reject stray one-cells."""
    ordered = sorted(ones)
    if len(ordered) < 3:
        raise ValueError("missing marker, header, or register file")
    origin, header = ordered[:2]
    if state != 25 or head != origin + 1 or ordered[2] != header + 2:
        raise ValueError("invalid source-boundary shape")
    cursor = header + 1
    values = []
    while cursor < ordered[-1]:
        if cursor in ones or cursor + 1 not in ones:
            raise ValueError(f"invalid separator/block at {cursor}")
        cursor += 1
        length = 0
        while cursor in ones:
            length += 1
            cursor += 1
        values.append(length - 1)
    reconstructed = {origin, header}
    cursor = header + 1
    for value in values:
        reconstructed.update(range(cursor + 1, cursor + value + 2))
        cursor += value + 2
    if reconstructed != ones:
        raise ValueError("whole-tape reconstruction mismatch")
    return origin, header, values


def expected_ones():
    result = {-21, 18}
    cursor = 19
    for value in ACTIVE + EXTRAS:
        result.update(range(cursor + 1, cursor + value + 2))
        cursor += value + 2
    return result


def audit(table):
    rows = parse_table(table.read_bytes())
    state, head, ones, visited = blank_replay(rows, STEPS)
    origin, header, values = decode_checkpoint(state, head, ones)
    expected = expected_ones()
    if (state, head, origin, header, values, ones) != (
        25, -20, -21, 18, ACTIVE + EXTRAS, expected
    ):
        raise ValueError("manuscript checkpoint mismatch")
    # The encoding is explicitly stated so this hash is independently reusable.
    tape_bytes = (json.dumps(sorted(ones), separators=(",", ":")) + "\n").encode("ascii")
    return {
        "status": "PASS_FINITE_RAW_TABLE_BOOTSTRAP",
        "table_sha256": TABLE_SHA256,
        "transitions": STEPS,
        "early_halt": False,
        "state": state,
        "head": head,
        "origin": origin,
        "header": header,
        "H_header_minus_origin": header - origin,
        "D_blank_cells_from_head_to_header": header - head,
        "active_registers": values[:9],
        "blocks": len(values),
        "spare_blocks": len(values) - 9,
        "nonzero_spares_zero_based": [[i, v] for i, v in enumerate(values[9:]) if v],
        "one_cells": len(ones),
        "one_cell_range": [min(ones), max(ones)],
        "visited_head_range": visited,
        "whole_tape_equal_to_expected": True,
        "one_cells_sha256_encoding": "ASCII compact JSON sorted coordinates followed by LF",
        "one_cells_sha256": hashlib.sha256(tape_bytes).hexdigest(),
        "scope": "Finite external replay only; no kernel theorem or unbounded simulation.",
    }


def audit_graph(path):
    """Execute authenticated CFG rows; do not consume any supplied trace."""
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != GRAPH_SHA256:
        raise ValueError("authenticated PA control graph hash mismatch")
    payload = json.loads(data)
    results = []
    for key in ("graph", "source_graph"):
        graph = payload[key]
        if len(graph) != 4409:
            raise ValueError("unexpected PA site count")
        for row in graph:
            opcode = row[0]
            if opcode == "halt":
                arity = 0
            elif opcode == "goto":
                arity = 1
            else:
                family, name, instruction = opcode.split(".")
                if family != "3" or name not in REGISTER_NAMES or instruction not in ("inc", "decnz"):
                    raise ValueError("unexpected PA opcode")
                arity = 1 if instruction == "inc" else 2
            if len(row) != arity + 1 or any(type(j) is not int or not 0 <= j < 4409 for j in row[1:]):
                raise ValueError("invalid PA graph row")
        pc, registers, aliases = 0, [0, 0, 0, 0, 0, 0, 2, 0, 0], 0
        for clock in range(670):
            row = graph[pc]
            if row[0] == "halt":
                raise ValueError(f"CFG {key} early halt at step {clock}")
            if row[0] == "goto":
                aliases += 1
                pc = row[1]
                continue
            _, name, instruction = row[0].split(".")
            register = REGISTER_NAMES.index(name)
            if instruction == "inc":
                registers[register] += 1
                pc = row[1]
            elif registers[register] != 0:
                registers[register] -= 1
                pc = row[1]
            else:
                pc = row[2]
        if (pc, registers, aliases) != (0, ACTIVE, 0):
            raise ValueError(f"CFG {key} does not reach the claimed closed join")
        results.append({"graph": key, "steps": 670, "pc": pc,
                        "active_registers": registers, "early_halt": False,
                        "control_alias_steps": aliases})
    return {"control_graph_sha256": GRAPH_SHA256, "runs": results,
            "scope": "Finite row replay; source-to-graph correspondence is a separate obligation."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--table", type=Path, default=Path(__file__).resolve().parents[2] / "machine/pa_238.tm")
    parser.add_argument("--graph", type=Path, help="authenticated CONTROL_GRAPH.json extracted at the pinned original commit")
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_CPU, (10, 10))
    # The tape's 4096-cell structural bound avoids dependence on Darwin's
    # unsupported/ineffective RLIMIT_AS. Table and graph inputs are hash-pinned.
    signal.alarm(30)
    result = audit(args.table)
    if args.graph:
        result["source_join"] = audit_graph(args.graph)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
