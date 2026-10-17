#!/usr/bin/env python3
"""Build and check the formalization of m254tg_wade.tm (portable: Linux / macOS / Windows).

    python3 check.py            # coqc from $COQC, default `coqc` on PATH (Coq 8.20.x)

1. Refuses any of our sources (coq/) containing Admitted / admit / Axiom / Parameter / Conjecture
   outside comments (vendored code is covered by Print Assumptions).
2. Checks that machine/m254tg_wade.tm has the published sha256 and that the literal transition table
   tg_table (coq/tm/TableTG.v) is exactly its table.
3. Checks that the generated files reproduce: Wade's TMBuilder (../generator) compiles
   machine/source_tg.py to machine/m254tg_wade.tm (up to the line terminators of the platform);
   tools/gen_tm_coq.py regenerates coq/tm/{DagTG,TableTG,NamesTG}.v and tools/gen_prog.py the generated
   regions of coq/prog/ProgLibTG.v, byte for byte.
4. Compiles, in dependency order, the closure of coq/e2e/E2E_TG.v.  Load paths: our layers
   coq/tm -> M254TGT, coq/prog -> M254TGP, coq/logic -> M254TGL, coq/settheory -> M254TG,
   coq/ac -> M254TGA; shared with the sibling packages: ../m254/coq/settheory -> M254S,
   ../m254/coq/logic -> M254L, ../stdzf/coq -> ZF, ../stdzf_r3/regcon -> RegCon, ../stdzf_r3/zfc -> ZFC,
   ../stdzf_r3/vendor/undecidability/theories -> Undecidability, ../stdzf_r3/vendor/busycoq -> BusyCoq.
5. Requires the four headline statements, "Closed under the global context" 4 times in E2E_TG.v, and
   the statement of ZFTM.tm_table (the Coq machine tm = the literal table) closed as well.
   Prints CHECK PASS / CHECK FAIL.
"""
import hashlib, os, re, subprocess, sys, tempfile, time
from pathlib import Path
for _s in (sys.stdout, sys.stderr):
    try:
        _s.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass

HERE = Path(__file__).resolve().parent
ZF = HERE.parent
COQC = os.environ.get('COQC', 'coqc')
UNDEC = ZF / 'stdzf_r3' / 'vendor' / 'undecidability' / 'theories'
ROOTS = {'Undecidability': [UNDEC], 'BusyCoq': [ZF / 'stdzf_r3' / 'vendor' / 'busycoq'],
         'ZF': [ZF / 'stdzf' / 'coq'], 'RegCon': [ZF / 'stdzf_r3' / 'regcon'], 'ZFC': [ZF / 'stdzf_r3' / 'zfc'],
         'M254S': [ZF / 'm254' / 'coq' / 'settheory'], 'M254L': [ZF / 'm254' / 'coq' / 'logic'],
         'M254TGT': [HERE / 'coq' / 'tm'], 'M254TGP': [HERE / 'coq' / 'prog'],
         'M254TGL': [HERE / 'coq' / 'logic'], 'M254TG': [HERE / 'coq' / 'settheory'],
         'M254TGA': [HERE / 'coq' / 'ac']}
TOP = HERE / 'coq' / 'e2e' / 'E2E_TG.v'
TM_FILE = HERE / 'machine' / 'm254tg_wade.tm'
TM_SHA256 = 'e9b63d8e07bc505326c8e9ec697890b00cc74e675ce12c451369b208826da071'
WARN = ['-w', '-notation-overridden,-stdlib-vector,-notation-incompatible-prefix,'
              '-postfix-notation-not-level-1,-closed-notation-not-level-0,-deprecated']
LIBFLAGS = ['-set', 'Default Proof Using = Type']     # as in the library's _CoqProject

# The four headline theories: as written in E2E_TG.v (fully qualified), and as coqc prints them.
STATEMENTS = {
    'tg296_halts_iff_ZFGU': ('ZF.Std_iface.ZFc phi \\/ phi = M254TG.SU_gu.GU',
                             'Std_iface.ZFc phi \\/ phi = SU_gu.GU'),
    'tg296_halts_iff_ZFRGU': ("(ZF.Std_iface.ZFc phi \\/ phi = RegCon.MinZF.ax_reg') \\/ phi = M254TG.SU_gu.GU",
                              "(Std_iface.ZFc phi \\/ phi = MinZF.ax_reg') \\/ phi = SU_gu.GU"),
    'tg296_halts_iff_ZFCGU': ('(ZF.Std_iface.ZFc phi \\/ phi = ZFC.Z_wo.ax_ac) \\/ phi = M254TG.SU_gu.GU',
                              '(Std_iface.ZFc phi \\/ phi = Z_wo.ax_ac) \\/ phi = SU_gu.GU'),
    'tg296_halts_iff_ZFCRGU': ("((ZF.Std_iface.ZFc phi \\/ phi = RegCon.MinZF.ax_reg') \\/ phi = ZFC.Z_wo.ax_ac) \\/ "
                               "phi = M254TG.SU_gu.GU",
                               "((Std_iface.ZFc phi \\/ phi = MinZF.ax_reg') \\/ phi = Z_wo.ax_ac) \\/ phi = SU_gu.GU"),
}
TM_TABLE = ('tm_table : (forall (q : state) (b : bool), table_lookup tg_table (name q) b = row_of (tm (q, b))) /\\ '
            '(forall (s : string) (b w mv : bool) (nx : string), In (s, b, w, mv, nx) tg_table -> '
            'exists q : state, name q = s) /\\ NoDup (map name all_states) /\\ NoDup (map row_key tg_table) /\\ '
            'name q0 = "0.boot.A" /\\ s0 = false /\\ Datatypes.length all_states = 297 /\\ '
            'Datatypes.length tg_table = 591')

if os.name == 'nt':                                   # run at Idle priority on Windows
    import ctypes
    ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x40)
else:
    try:
        os.nice(19)
    except Exception:
        pass


def strip_comments(text):
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith('(*', i):
            depth += 1; i += 2
        elif text.startswith('*)', i) and depth:
            depth -= 1; i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    return ''.join(out)


REQ = re.compile(r'(?:From\s+([\w.]+)\s+)?Require\s+(?:Import\s+|Export\s+)?(.*?)\.(?:\s|$)', re.S)


def resolve(roots, prefix, name):
    """Map a (From prefix, module name) pair to a source file below our load paths, or None (stdlib)."""
    full = f'{prefix}.{name}' if prefix else name
    parts = full.split('.')
    if parts[0] not in roots:
        return None
    for root in roots[parts[0]]:
        f = root.joinpath(*parts[1:]).with_suffix('.v')
        if f.exists():
            return f
    # partially qualified name: a suffix of a module path below the prefix directory
    tail = '/' + '/'.join(name.split('.'))
    for root in roots[parts[0]]:
        base = root.joinpath(*prefix.split('.')[1:]) if prefix else root
        cands = sorted(p for p in base.rglob(name.split('.')[-1] + '.v')
                       if p.with_suffix('').as_posix().endswith(tail))
        if cands:
            return cands[0]
    raise SystemExit(f'cannot resolve {full}')


def deps(roots, f):
    out = []
    for prefix, names in REQ.findall(strip_comments(f.read_text(encoding='utf-8'))):
        if prefix and prefix.split('.')[0] not in roots:
            continue
        for n in names.split():
            if not prefix and n.split('.')[0] not in roots:
                continue
            r = resolve(roots, prefix, n)
            if r is not None:
                out.append(r)
    return out


def closure(roots, top):
    order, seen = [], set()
    def visit(f, stack):
        if f in seen:
            return
        if f in stack:
            raise SystemExit(f'dependency cycle at {f}')
        for d in deps(roots, f):
            visit(d, stack | {f})
        seen.add(f)
        order.append(f)
    visit(top, frozenset())
    return order


def parse_tm(path):
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


def check_table():
    if hashlib.sha256(TM_FILE.read_bytes()).hexdigest() != TM_SHA256:
        return 'machine/m254tg_wade.tm: sha256 mismatch'
    start, rows = parse_tm(TM_FILE)
    if start != '0.boot.A':
        return f'm254tg_wade.tm: start state {start}, expected 0.boot.A'
    text = (HERE / 'coq' / 'tm' / 'TableTG.v').read_text(encoding='utf-8')
    m = re.search(r'Definition tg_table[^\[]*\[(.*?)\]\.', text, re.S)
    coq = {}
    for s, r, w, d, n in re.findall(r'\("([^"]+)",\s*(true|false),\s*(true|false),\s*(true|false),\s*"([^"]+)"\)',
                                    m.group(1)):
        key = (s, '1' if r == 'true' else '0')
        if key in coq:
            return f'TableTG.v: duplicate row {key}'
        coq[key] = ('1' if w == 'true' else '0', 'R' if d == 'true' else 'L', n)
    if coq != rows:
        return 'TableTG.v tg_table differs from m254tg_wade.tm'
    states = {s for s, _ in rows} | {n for _, _, n in rows.values()}
    if 'halt' not in states or len(states) != 297 or len(rows) != 591:
        return f'm254tg_wade.tm: {len(states)} states incl. halt, {len(rows)} transitions (expected 297, 591)'
    return None


def check_generated():
    """The .tm from source_tg.py, and the generated Coq files from the .tm, reproduce."""
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        r = subprocess.run([sys.executable, '-I', str(HERE / 'machine' / 'build_tm.py'), str(tmp / 'rebuilt.tm')],
                           capture_output=True, text=True)
        if r.returncode:
            return 'machine/build_tm.py failed\n' + r.stdout + r.stderr
        lf = lambda b: b.replace(b'\r\n', b'\n')
        if lf((tmp / 'rebuilt.tm').read_bytes()) != lf(TM_FILE.read_bytes()):
            return 'TMBuilder does not reproduce machine/m254tg_wade.tm from machine/source_tg.py'
        r = subprocess.run([sys.executable, '-I', str(HERE / 'tools' / 'gen_tm_coq.py'), str(tmp)],
                           capture_output=True, text=True)
        if r.returncode:
            return 'tools/gen_tm_coq.py failed\n' + r.stdout + r.stderr
        for f in ['DagTG.v', 'TableTG.v', 'NamesTG.v']:
            if (tmp / f).read_bytes() != (HERE / 'coq' / 'tm' / f).read_bytes():
                return f'tools/gen_tm_coq.py does not reproduce coq/tm/{f}'
        r = subprocess.run([sys.executable, '-I', str(HERE / 'tools' / 'gen_prog.py'), str(tmp / 'ProgLibTG.v')],
                           capture_output=True, text=True)
        if r.returncode:
            return 'tools/gen_prog.py failed\n' + r.stdout + r.stderr
        if (tmp / 'ProgLibTG.v').read_bytes() != (HERE / 'coq' / 'prog' / 'ProgLibTG.v').read_bytes():
            return 'tools/gen_prog.py does not reproduce the generated regions of coq/prog/ProgLibTG.v'
    return None


def coqc(qflags, f, lib=False):
    cmd = [COQC, *qflags, *WARN, *(LIBFLAGS if lib else []), os.path.relpath(f, HERE)]
    return subprocess.run(cmd, cwd=HERE, capture_output=True, text=True, encoding='utf-8', errors='replace')


def main():
    t0 = time.time()
    bad = [str(f.relative_to(HERE)) for f in (HERE / 'coq').rglob('*.v')
           if re.search(r'\b(Admitted|admit|Axiom|Axioms|Parameter|Parameters|Conjecture)\b',
                        strip_comments(f.read_text(encoding='utf-8')))]
    if bad:
        print('forbidden keyword in:', *bad, sep='\n  ')
        print('CHECK FAIL'); return 1
    err = check_table()
    if err:
        print(err); print('CHECK FAIL'); return 1
    print('m254tg_wade.tm: sha256 ok, 296 states + halt, 591 transitions; literal table = TableTG.v tg_table')
    err = check_generated()
    if err:
        print(err); print('CHECK FAIL'); return 1
    print('generated files reproduce: m254tg_wade.tm (TMBuilder, source_tg.py), DagTG.v, TableTG.v, NamesTG.v, '
          'ProgLibTG.v regions')
    qflags = [x for p, ds in ROOTS.items() for d in ds for x in ('-Q', os.path.relpath(d, HERE), p)]
    files = closure(ROOTS, TOP)
    print(f'{len(files)} files', flush=True)
    ok = True
    for f in files:
        t = time.time()
        r = coqc(qflags, f, UNDEC in f.parents)
        if r.returncode:
            print(f'FAILED {os.path.relpath(f, HERE)}\n{r.stdout}{r.stderr}')
            print('CHECK FAIL'); return 1
        if f == TOP:
            print(r.stdout)
            flat = ' '.join(r.stdout.split())
            src = ' '.join(strip_comments(TOP.read_text(encoding='utf-8')).split())
            for name, (full, printed) in STATEMENTS.items():
                if (f'Theorem {name} : halts tm c0 <-> @tprv sig0 zfp fon cls (fun phi => {full}) bot.' not in src
                        or f'{name} : halts tm c0 <-> tprv (fun phi : Core.form => {printed}) bot' not in flat):
                    print(f'unexpected statement of {name}'); ok = False
            k = r.stdout.count('Closed under the global context')
            print(f'E2E_TG: {k}/4 closed', flush=True)
            ok = ok and k == 4 and 'Axioms:' not in r.stdout
        else:
            print(f'{time.time() - t:7.1f}s  {os.path.relpath(f, HERE)}', flush=True)
    # the Coq machine tm (ZFTM.v) is the literal table tg_table (TableTG.v), checked against the file above
    probe = HERE / 'coq' / 'e2e' / 'Probe_tm_table.v'
    probe.write_text('From Coq Require Import Lists.List Strings.String.\nFrom BusyCoq Require Import TM.\n'
                     'From M254TGT Require Import RM DagTG TableTG ZFTM.\nImport ListNotations.\n'
                     'Open Scope string_scope.\nSet Printing Width 10000.\n'
                     'Check tm_table.\nPrint Assumptions tm_table.\n', encoding='utf-8')
    try:
        r = coqc(qflags, probe)
    finally:
        for p in [probe] + [probe.with_name(probe.stem + s) for s in ('.vo', '.vok', '.vos', '.glob')] \
                + [probe.with_name('.' + probe.stem + '.aux')]:
            p.unlink(missing_ok=True)
    flat = ' '.join((r.stdout + r.stderr).split())
    if r.returncode or TM_TABLE not in flat or flat.count('Closed under the global context') != 1:
        print('ZFTM.tm_table: unexpected statement or assumptions\n' + r.stdout + r.stderr); ok = False
    else:
        print(TM_TABLE)
        print('Print Assumptions tm_table: Closed under the global context')
    print(f'total {time.time() - t0:.0f}s')
    print('CHECK', 'PASS' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
