"""Build the PA/goldbach program-layer proofs (prog/coq, logical root PAGBP) with coqc 8.20 at low
priority, one coqc at a time.  Usage: python build.py [File.v ...]   (default: every *.v here)
coqc: $COQC, else `coqc` on PATH.

Other roots (read only, compiled by their owners' build scripts):
  Undecidability = ../../vendor/undecidability/theories   (built by ../../coq/build.py)
  PAGB           = ../../coq      (the logic layer: codes, the abstract enumerator)
  PAGBT          = ../../tm/coq   (RM.v, DagPA.v, RMEquiv.v: the TM layer's frozen dagpa)"""
import os, re, shutil, subprocess, sys, time
from pathlib import Path
try:
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
except Exception:
    pass
WIN = sys.platform == 'win32'
if WIN:
    import ctypes
    ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x40)  # IDLE
else:
    try:
        os.nice(19)
    except Exception:
        pass
NOWIN = 0x08000000 | 0x40 if WIN else 0  # CREATE_NO_WINDOW | IDLE_PRIORITY_CLASS (Windows only)

HERE = Path(__file__).resolve().parent
LOGIC = (HERE / '..' / '..' / 'coq').resolve()
VEN = (HERE / '..' / '..' / 'vendor' / 'undecidability' / 'theories').resolve()
TM = (HERE / '..' / '..' / 'tm' / 'coq').resolve()
COQC = os.environ.get('COQC') or shutil.which('coqc') or 'coqc'
ROOTS = {'PAGBP': HERE, 'PAGB': LOGIC, 'PAGBT': TM}
FLAGS = ['-Q', str(VEN), 'Undecidability', '-Q', str(LOGIC), 'PAGB', '-Q', str(TM), 'PAGBT', '-Q', str(HERE), 'PAGBP', '-w', '-notation-overridden,-stdlib-vector,-notation-incompatible-prefix,-postfix-notation-not-level-1,-closed-notation-not-level-0,-deprecated']
REQ = re.compile(r'From\s+(PAGBP|PAGB|PAGBT)\s+Require\s+(?:Import\s+|Export\s+)?([\w\s.]+?)\.(?:\s|$)')


def deps(v):
    text = re.sub(r'\(\*.*?\*\)', '', v.read_text(encoding='utf-8'), flags=re.S)
    return [ROOTS[r] / f'{n}.v' for r, names in REQ.findall(text) for n in names.split()
            if (ROOTS[r] / f'{n}.v').exists()]


def build(v, done, stack=()):
    if v in done:
        return done[v]
    assert v not in stack, f'dependency cycle at {v}'
    newest = v.stat().st_mtime
    for d in deps(v):
        newest = max(newest, build(d, done, stack + (v,)))
    vo = v.with_suffix('.vo')
    if v.parent != HERE:            # foreign root: must already be compiled by its owner
        if not vo.exists() or vo.stat().st_mtime < newest:
            raise SystemExit(f'{vo} missing or stale: build it with its own build.py')
        done[v] = vo.stat().st_mtime
        return done[v]
    if not vo.exists() or vo.stat().st_mtime < newest:
        t = time.time()
        r = subprocess.run([COQC, *FLAGS, str(v)], cwd=v.parent, capture_output=True, text=True,
                           encoding='utf-8', errors='replace', creationflags=NOWIN)
        if r.returncode:
            sys.stderr.write(f'FAILED {v.name}\n{r.stdout}{r.stderr}\n')
            raise SystemExit(1)
        print(f'compiled {v.name} in {time.time() - t:.1f}s', flush=True)
        if r.stdout.strip():
            print(r.stdout, flush=True)
    done[v] = vo.stat().st_mtime
    return done[v]


if __name__ == '__main__':
    targets = [HERE / a for a in sys.argv[1:]] or sorted(HERE.glob('*.v'))
    done = {}
    for t in targets:
        build(t.resolve(), done)
