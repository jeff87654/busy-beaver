"""Check one of the ZF-machine proofs.

    python check.py 393|361|354|336|335    (run from ZF/verify/)

Environment:
    BUSYCOQ  path to busycoq's verify/ directory with TM.vo compiled (busycoq bd2e36f, Coq 8.20.1)
    COQC     coqc executable (default: coqc on PATH)

Steps:
1. Parse ../machines/<machine>.tm independently and check that `zf2_table` in <N>/ZF2Dag.v is exactly
   its transition table (every row, no extras), with start state 0.boot.A. Inside Coq, ZFTM.v proves
   that the machine `tm` gives the same transition as `zf2_table` for every state and symbol. This
   script ties `zf2_table` to the file.
2. Compile <N>/*.v in dependency order (the list in <N>/FILES).
3. Check the statement of `zf_machine` in Main.v and that `Print Assumptions zf_machine` reports a closed
   proof (no axioms, no Admitted).
"""
from __future__ import annotations
import os, re, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MACHINES = {'393': 'zf2.tm', '361': 'A361.tm', '354': 'B354.tm', '336': 'R3s336.tm', '335': 'R3Y1_335.tm'}
EXPECTED = 'halts tm c0 <-> prov (Wel v0 v0)'


def parse_tm(path: Path):
    start, rows = None, {}
    for line in path.read_text(encoding='utf-8').splitlines():
        line = line.strip()
        if line.startswith('#!'):
            p = line[2:].split()
            if p and p[0] == 'start':
                start = p[1]
        elif line and not line.startswith('#'):
            s, r, w, d, n = line.split()
            assert r in '01' and w in '01' and d in 'LR', line
            assert (s, r) not in rows, f'duplicate row {line}'
            rows[(s, r)] = (w, d, n)
    return start, rows


def parse_coq_table(path: Path):
    text = path.read_text(encoding='utf-8')
    m = re.search(r'Definition zf2_table[^\[]*\[(.*?)\]\.', text, re.S)
    rows = {}
    for s, r, w, d, n in re.findall(
            r'\("([^"]+)",\s*(true|false),\s*(true|false),\s*(true|false),\s*"([^"]+)"\)', m.group(1)):
        key = (s, '1' if r == 'true' else '0')
        assert key not in rows
        rows[key] = ('1' if w == 'true' else '0', 'R' if d == 'true' else 'L', n)
    return rows


def main():
    if len(sys.argv) != 2 or sys.argv[1] not in MACHINES:
        sys.exit('usage: python check.py 393|361|354|336|335')
    n = sys.argv[1]
    d = HERE / n
    tm = HERE.parent / 'machines' / MACHINES[n]
    coqc = os.environ.get('COQC', 'coqc')
    busy = os.environ.get('BUSYCOQ')
    if not busy:
        sys.exit('set BUSYCOQ to busycoq/verify (with TM.vo compiled)')
    flags = ['-Q', busy, 'BusyCoq', '-Q', str(d), 'ZF']

    start, rows = parse_tm(tm)
    assert start == '0.boot.A', start
    assert rows == parse_coq_table(d / 'ZF2Dag.v'), f'{n}/ZF2Dag.v zf2_table differs from {tm.name}'
    states = {s for s, _ in rows} | {x for _, _, x in rows.values()}
    print(f'{tm.name}: {len(rows)} transitions, {len(states) - 1} states + halt; literal table matches')

    for name in (d / 'FILES').read_text().split():
        r = subprocess.run([coqc, *flags, f'{name}.v'], cwd=d, capture_output=True, text=True)
        if r.returncode:
            sys.exit(f'FAILED {name}.v\n{r.stdout}{r.stderr}')
        print(f'compiled {n}/{name}.v', flush=True)

    m = re.search(r'Theorem\s+zf_machine\s*:\s*(.*?)\.\s*\n', (d / 'Main.v').read_text(encoding='utf-8'), re.S)
    stmt = ' '.join(m.group(1).split())
    assert stmt == EXPECTED, f'unexpected statement: {stmt!r}'
    probe = d / 'Probe.v'
    probe.write_text('From ZF Require Import Main.\nPrint Assumptions zf_machine.\n', encoding='utf-8')
    r = subprocess.run([coqc, *flags, 'Probe.v'], cwd=d, capture_output=True, text=True)
    out = r.stdout + r.stderr
    assert r.returncode == 0 and 'Closed under the global context' in out and 'Axioms:' not in out, out
    print(f'Theorem zf_machine : {stmt}')
    print('Print Assumptions zf_machine: Closed under the global context')
    print(f'CHECK PASSED ({tm.name}, {len(states) - 1} states)')


if __name__ == '__main__':
    main()
