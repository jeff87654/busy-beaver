"""Build and mechanically check the BB(7) holdout non-halting proofs in this directory.

  BUSYCOQ=/path/to/busycoq/verify python3 check.py            # every BB7_*.v here
  BUSYCOQ=/path/to/busycoq/verify python3 check.py BB7_H1_1RB1RE.v ...

BUSYCOQ is the verify/ directory of a busycoq checkout (commit bd2e36f) with Individual.vo and Flip.vo built.
COQC may name a specific coqc (default: coqc on PATH). The logical path of this directory is BB7.

Each proof file must contain a header comment `(* machine: <standard TM string> *)`, a definition
`Definition tm : TM := fun '(q, s) => match q, s with ... end.` and `Theorem nonhalt : ~ halts tm c0.`
For each file the checker:
  1. compiles it (after BB72.v, Individual72.v and the proof files it imports) with coqc;
  2. checks, as text, that the transition table of `tm` equals the declared machine string (`---` is `None`)
     and that the file imports Individual72 (7 states, 2 symbols);
  3. checks, as text, that the theorem is exactly `Theorem nonhalt : ~ halts tm c0.` (c0 = blank tape, state A);
  4. runs a Coq probe that re-checks 2 and 3 inside Coq:
       Check (<file>.nonhalt : ~ halts <file>.tm c0).
       Check (eq_refl : <file>.tm (A, 0) = Some (1, R, B)).   ... one line per transition (14 in all)
       Print Assumptions <file>.nonhalt.
     and requires "Closed under the global context" (no Admitted, no axioms).
It also checks that BB72.v and Individual72.v are byte-identical to ../../verify/ (the BB7 entry's copies), so the
7-state setup (states A..G, start state A, blank symbol 0) is the one already reviewed there.
A reviewer then only has to confirm that each declared machine string is the intended machine.
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
QS = 'ABCDEFG'
COQC = os.environ.get('COQC', 'coqc')
SETUP = ['BB72', 'Individual72']


def flags():
    busy = os.environ.get('BUSYCOQ')
    if not busy:
        sys.exit('set BUSYCOQ to the verify/ directory of a busycoq checkout (commit bd2e36f)')
    return ['-Q', str(Path(busy).resolve()), 'BusyCoq', '-Q', str(HERE), 'BB7']


def coqc(args, **kw):
    return subprocess.run([COQC, *flags(), *args], capture_output=True, text=True, **kw)


def strip_comments(text):
    # Coq comments nest; remove them innermost first.
    prev = None
    while prev != text:
        prev, text = text, re.sub(r'\(\*(?:(?!\(\*|\*\)).)*\*\)', ' ', text, flags=re.S)
    return text


def deps(name):
    code = strip_comments((HERE / f'{name}.v').read_text(encoding='utf-8'))
    out = []
    for names in re.findall(r'From\s+BB7\s+Require\s+(?:Import\s+|Export\s+)?([\w\s.]+?)\.(?:\s|$)', code):
        out += [n for n in names.split() if (HERE / f'{n}.v').exists()]
    return out


def compile_all(names, done):
    for name in names:
        if name in done:
            continue
        compile_all(deps(name), done)
        r = coqc([f'{name}.v'], cwd=HERE)
        if r.returncode:
            raise SystemExit(f'coqc failed on {name}.v:\n{(r.stdout + r.stderr)[-3000:]}')
        print(f'compiled {name}.v', flush=True)
        done.add(name)


def table_from_coq(code):
    m = re.search(r"Definition\s+tm\s*:\s*TM\s*:=\s*fun\s*'\(q,\s*s\)\s*=>\s*match\s+q,\s*s\s+with(.*?)end\.", code, re.S)
    if not m:
        raise ValueError("no `Definition tm : TM := fun '(q, s) => match q, s with ... end.` found")
    table = {}
    for q, s, rhs in re.findall(r'\|\s*([A-G_])\s*,\s*([01_])\s*=>\s*(None|Some\s*\(\s*[01]\s*,\s*[LR]\s*,\s*[A-G]\s*\))',
                                m.group(1)):
        if q == '_' or s == '_':
            raise ValueError('wildcard cases are not supported by the checker')
        if (q, int(s)) in table:
            raise ValueError(f'duplicate case {q}, {s}')
        if rhs == 'None':
            table[(q, int(s))] = '---'
        else:
            w, d, n = re.match(r'Some\s*\(\s*([01])\s*,\s*([LR])\s*,\s*([A-G])\s*\)', rhs).groups()
            table[(q, int(s))] = f'{w}{d}{n}'
    return table


def check(name):
    text = (HERE / f'{name}.v').read_text(encoding='utf-8')
    m = re.search(r'\(\*\s*machine:\s*([01LRA-G_\-]+)\s*\*\)', text)
    if not m:
        raise ValueError('missing header comment (* machine: <TM string> *)')
    machine = m.group(1)
    rows = machine.split('_')
    if len(rows) != 7 or any(len(r) != 6 for r in rows):
        raise ValueError(f'{machine} is not a 7-state 2-symbol machine string')
    code = strip_comments(text)
    if not re.search(r'From\s+BB7\s+Require\s+Import\s+Individual72\.', code):
        raise ValueError('file does not import Individual72')
    table = table_from_coq(code)
    for i, row in enumerate(rows):
        for s in (0, 1):
            want = row[3 * s: 3 * s + 3]
            got = table.get((QS[i], s))
            if got != want:
                raise ValueError(f'transition {QS[i]}{s}: Coq has {got}, machine string has {want}')
    if len(table) != 14:
        raise ValueError('table must have exactly 14 cases')
    if not re.search(r'Theorem\s+nonhalt\s*:\s*~\s*halts\s+tm\s+c0\s*\.', code):
        raise ValueError('need exactly `Theorem nonhalt : ~ halts tm c0.`')
    lines = ['From BB7 Require Import Individual72.', f'From BB7 Require {name}.',
             f'Check ({name}.nonhalt : ~ halts {name}.tm c0).']
    for i, row in enumerate(rows):
        for s in (0, 1):
            t = row[3 * s: 3 * s + 3]
            rhs = 'None' if t == '---' else f'Some ({t[0]}, {t[1]}, {t[2]})'
            lines.append(f'Check (eq_refl : {name}.tm ({QS[i]}, {s}) = {rhs}).')
    lines.append(f'Print Assumptions {name}.nonhalt.')
    with tempfile.TemporaryDirectory() as td:
        probe = Path(td) / 'probe.v'
        probe.write_text('\n'.join(lines) + '\n', encoding='utf-8')
        r = coqc([str(probe)], cwd=td)
    out = (r.stdout + r.stderr).strip()
    if r.returncode:
        raise ValueError(f'Coq rejected the statement/table probe:\n{out[-3000:]}')
    if 'Closed under the global context' not in out or 'Axioms:' in out:
        raise ValueError(f'assumption check failed:\n{out[-3000:]}')
    return machine


def main():
    for f in SETUP:
        ours, theirs = HERE / f'{f}.v', HERE.parent.parent / 'verify' / f'{f}.v'
        if ours.read_bytes() != theirs.read_bytes():
            sys.exit(f'{f}.v differs from {theirs}')
    names = [Path(a).stem for a in sys.argv[1:]] or sorted(p.stem for p in HERE.glob('BB7_*.v'))
    compile_all(SETUP + names, set())
    bad = 0
    for name in names:
        try:
            m = check(name)
            print(f'PASS {name}.v: {m} never halts (machine-checked, no axioms)', flush=True)
        except ValueError as e:
            bad += 1
            print(f'FAIL {name}.v: {e}', flush=True)
    print(f'{len(names) - bad} of {len(names)} passed')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
