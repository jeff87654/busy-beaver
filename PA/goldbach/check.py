#!/usr/bin/env python3
"""Top-level check of PA/goldbach: the frozen 449-state machine machine/pa_wade.tm halts from the blank tape
iff PAeq ⊢TC GC_form (Goldbach's conjecture in the Coq Library of Undecidability Proofs' PA), in Coq,
with no axioms.  Portable (Linux / macOS / Windows).

    python3 check.py      # coqc / coqchk from $COQC / $COQCHK, default `coqc` / `coqchk` on PATH (Coq 8.20.x)

Steps:
  1. the frozen machine files have their recorded sha256 (the freeze set; README.md "The machine");
  Uses ../../ZF/generator (Wade's TMBuilder) and ../../ZF/stdzf_r3/vendor/busycoq (busycoq's TM.v).
  2. Wade's TMBuilder (../../ZF/generator, unmodified) compiles machine/source_pa.py to machine/pa_wade.tm
     (machine/build_tm.py; byte for byte up to line terminators);
  3. logic layer: coq/check.py (clean rebuild, statements, assumptions closed) -> CHECK PASS;
  4. TM layer: tm/check_tm.py (literal table = pa_wade.tm, generators reproduce, clean rebuild) -> CHECK PASS;
  5. program layer: prog/check.py (DagPA = machine, generated regions reproduce, clean rebuild) -> CHECK PASS;
  6. e2e: compile e2e/Headline.v (< 100 lines); its statements are the expected ones and both
     Print Assumptions report "Closed under the global context";
  7. coqchk (independent kernel re-check) of PAGBE.Headline and every library it loads.  coqchk lists the
     axioms present anywhere in that environment; the only ones allowed are the three that busycoq's TM.v
     brings in through its own imports (BusyCoq.LibTactics.inj_pair2, Coq.Logic.ProofIrrelevance.
     proof_irrelevance, Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq).  Step 6's Print Assumptions (dependency-
     precise) shows that the headline theorems use none of them.
Prints CHECK PASS / CHECK FAIL."""
import hashlib, os, re, shutil, subprocess, sys, tempfile, time
from pathlib import Path
try:
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
except Exception:
    pass
WIN = sys.platform == 'win32'
if WIN:                                               # run at Idle priority on Windows
    import ctypes
    ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x40)
else:
    try:
        os.nice(19)
    except Exception:
        pass
NOWIN = 0x08000000 | 0x40 if WIN else 0               # CREATE_NO_WINDOW | IDLE_PRIORITY_CLASS (Windows only)

M = Path(__file__).resolve().parent
COQC = os.environ.get('COQC') or shutil.which('coqc') or 'coqc'
COQCHK = os.environ.get('COQCHK') or shutil.which('coqchk') or 'coqchk'
BUSY = (M / '..' / '..' / 'ZF' / 'stdzf_r3' / 'vendor' / 'busycoq').resolve()   # shared with PA/m238, ZF/tg296
# The freeze set (the machine, its source, the spec and the spec's imports), exactly as frozen.
FROZEN = {
    'machine/pa_wade.tm': 'ed795af79b6752d72c037d7e32eca1d23efaa6a6c0f0d07fc7ba89869f2616a6',
    'machine/source_pa.py': '152d4a5f82be2f12c3823478a911c5f71fd21f78a21bca06f690030582b42587',
    'machine/spec_pa.py': '3cfdafbfe00828621ffdcddac7de09c57418a3b8eeadc08d2ee681ab9828dde4',
    'machine/design_choice_A.json': 'da10ced32774ea0ea3ea91f1d84d3fe15ef17324e760579165586b431fd7abf9',
    'machine/bignum.py': 'ec9338e9bf9385b42217a542412663b43f3a3ac165bf04541ed32e93b1a821c5',
    'machine/design.py': 'bc7b581091d321200dac2b7cd9ebeade6aae31ef0a50f9e18579ddf8e0d8bec4',
    'machine/ngw.py': 'a188af96792eece0b6bcd28602726144c8e8479a0a36b7ec1de5f077f2e3dea6',
    'machine/pagen.py': '9f4d232320de686008c5d2af1890e98936c258c18ad82c2789cc842e39064f19',
    'machine/pavars.py': '3b67eaed4c5afb934aaf6605f6080cf2a0a61f4afc97336b2f036f6bd93673a5',
    'machine/search_a.py': '7a3ae545b108e1c251b8749bcc7244c2258f9b6efc7e0e70844b52367dd27f57',
    'machine/search_nest.py': '777e361d21a22e5ded778bf8dd2dc7878a27419370a6e79edb1146636dabe64e',
    'machine/search_pa.py': '65c036f0cba6052201ec34336b1bbaf66de6fd6dc790e469ab3b7924465791dd',
    'machine/runs/GCw_coq_print.txt': '139d5a383dc12869d8cc611a7948062ad32d847d092bcc609af9af923fd2c568',
    'machine/runs/decode_final.txt': 'cb4f5f8554e16f7e9678118510c5a71651a33ce100fc46d389e05f3241d8476f',
    'machine/runs/push_order.txt': 'fedaffe5fe35fdc235078ddce2abe3c3d612de7df8531aa09f774f097aa3cc80',
}


def fail(msg):
    print('CHECK FAIL:', msg)
    sys.exit(1)


def run(args, cwd, tail=1500):
    print('>>', ' '.join(map(str, args)), flush=True)
    r = subprocess.run(args, cwd=cwd, capture_output=True, text=True, encoding='utf-8', errors='replace',
                       creationflags=NOWIN)
    out = r.stdout + r.stderr
    print(out[-tail:], flush=True)
    if r.returncode:
        fail(f'{args} exited with {r.returncode}')
    return out


t0 = time.time()
for f, h in FROZEN.items():
    if hashlib.sha256((M / f).read_bytes()).hexdigest() != h:
        fail(f'{f} does not have the frozen sha256')
print(f'frozen machine files: sha256 ok ({len(FROZEN)} files; pa_wade.tm {FROZEN["machine/pa_wade.tm"]})')

with tempfile.TemporaryDirectory() as tmp:
    out_tm = Path(tmp) / 'rebuilt.tm'
    run([sys.executable, '-I', str(M / 'machine' / 'build_tm.py'), str(out_tm)], M / 'machine', tail=300)
    lf = lambda b: b.replace(b'\r\n', b'\n')
    if lf(out_tm.read_bytes()) != (M / 'machine' / 'pa_wade.tm').read_bytes():
        fail('TMBuilder does not reproduce machine/pa_wade.tm from machine/source_pa.py')
print('TMBuilder (../../ZF/generator) reproduces machine/pa_wade.tm from machine/source_pa.py')

os.environ['COQC'] = COQC                             # the layer scripts use the same coqc
for args, cwd in [([sys.executable, '-I', str(M / 'coq' / 'check.py')], M / 'coq'),
                  ([sys.executable, '-I', str(M / 'tm' / 'check_tm.py')], M / 'tm'),
                  ([sys.executable, '-I', str(M / 'prog' / 'check.py')], M / 'prog')]:
    if 'CHECK PASS' not in run(args, cwd):
        fail(f'{args[-1]} did not print CHECK PASS')
    print(f'[{time.time() - t0:.0f}s]', flush=True)

E2E = M / 'e2e'
for f in E2E.glob('Headline.*'):
    if f.suffix in ('.vo', '.vok', '.vos', '.glob'):
        f.unlink()
out = run([sys.executable, '-I', str(E2E / 'build.py')], E2E)
head = (E2E / 'Headline.v').read_text(encoding='utf-8')
if len(head.splitlines()) >= 100:
    fail('Headline.v has 100 lines or more')
for stmt in ['Theorem pagb_halts_iff_PA_GC :\n  PAGBT.ZFTM.ZFTM.halts PAGBT.ZFTM.tm PAGBT.ZFTM.ZFTM.c0 <-> @tprv _ _ falsity_on class PAeq GC_form.',
             'Theorem GC_adequate rho : sat interp_nat rho GC_form <-> Goldbach_nat.',
             'Definition GC_form : form :=\n  ∀ ((even $0 ∧ leq (num 4) $0) → ∃ ∃ ((Pr $1 ∧ Pr $0) ∧ ($1 ⊕ $0 == $2))).']:
    if stmt not in head:
        fail('unexpected statement in Headline.v: ' + stmt)
if out.count('Closed under the global context') != 2 or 'Axioms:' in out:
    fail('Headline assumptions are not closed')

flags = ['-Q', str(M / 'vendor' / 'undecidability' / 'theories'), 'Undecidability',
         '-Q', str(BUSY), 'BusyCoq',
         '-Q', str(M / 'coq'), 'PAGB', '-Q', str(M / 'tm' / 'coq'), 'PAGBT',
         '-Q', str(M / 'prog' / 'coq'), 'PAGBP', '-Q', str(E2E), 'PAGBE']
out = run([COQCHK, '-silent', '-o', *flags, 'PAGBE.Headline'], M, tail=800)
m = re.search(r'\* Axioms:(.*?)\n\s*\n\* Constants', out, re.S)
if not m:
    fail('coqchk summary not found')
env_axioms = set(m.group(1).split()) - {'<none>'}
ALLOWED = {'BusyCoq.LibTactics.inj_pair2', 'Coq.Logic.ProofIrrelevance.proof_irrelevance',
           'Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq'}
if not env_axioms <= ALLOWED:
    fail(f'coqchk: unexpected axioms in the environment: {sorted(env_axioms - ALLOWED)}')
for k in ['type-in-type', 'unsafe (co)fixpoints', 'positivity is assumed']:
    if not re.search(re.escape(k) + r'[^\n]*:\s*<none>', out):
        fail(f'coqchk: {k} not <none>')
print('coqchk: kernel re-check ok; environment axioms', sorted(env_axioms),
      '(loaded by busycoq TM.v imports; Print Assumptions shows the headline theorems use none)')
print(f'total {time.time() - t0:.0f}s')
print('CHECK PASS: pa_wade.tm halts iff PAeq ⊢TC GC_form (Goldbach); Print Assumptions closed for both headline theorems')
