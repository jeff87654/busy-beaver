"""Build the PA/goldbach TM-layer proofs (low priority) with coqc, no make.
Usage: python build.py [File.v ...]  (default: all *.v here).  coqc: $COQC, else `coqc` on PATH."""
import os, re, shutil, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
BUSY = (HERE / '..' / '..' / '..' / '..' / 'ZF' / 'stdzf_r3' / 'vendor' / 'busycoq').resolve()
COQC = os.environ.get('COQC') or shutil.which('coqc') or 'coqc'
WIN = sys.platform == 'win32'
if WIN:
    import ctypes
    ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x40)  # IDLE
else:
    try:
        os.nice(19)
    except Exception:
        pass
ROOTS = {'BusyCoq': BUSY, 'PAGBT': HERE}
FLAGS = ['-Q', str(BUSY), 'BusyCoq', '-Q', str(HERE), 'PAGBT']
REQ = re.compile(r'From\s+(BusyCoq|PAGBT)\s+Require\s+(?:Import\s+|Export\s+)?([\w\s.]+?)\.(?:\s|$)')


def deps(v):
    text = re.sub(r'\(\*.*?\*\)', '', v.read_text(encoding='utf-8'), flags=re.S)
    out = []
    for r, names in REQ.findall(text):
        for n in names.split():
            f = ROOTS[r] / f'{n}.v'
            if f.exists():
                out.append(f)
    return out


def build(v, done, stack=()):
    if v in done:
        return done[v]
    assert v not in stack, f'dependency cycle at {v}'
    newest = v.stat().st_mtime
    for d in deps(v):
        newest = max(newest, build(d, done, stack + (v,)))
    vo = v.with_suffix('.vo')
    if not vo.exists() or vo.stat().st_mtime < newest:
        t = time.time()
        r = subprocess.run([COQC, *FLAGS, str(v)], cwd=v.parent, capture_output=True, text=True, encoding='utf-8',
                           errors='replace', creationflags=(0x08000000 | 0x40) if WIN else 0)  # CREATE_NO_WINDOW | IDLE
        if r.returncode:
            sys.stderr.write(f'FAILED {v.name}\n{r.stdout}{r.stderr}\n')
            raise SystemExit(1)
        print(f"compiled {v.name} in {time.time() - t:.1f}s", flush=True)
        if r.stdout.strip(): print(r.stdout, flush=True)
    done[v] = vo.stat().st_mtime
    return done[v]


if __name__ == '__main__':
    targets = [HERE / a for a in sys.argv[1:]] or sorted(HERE.glob('*.v'))
    done = {}
    for t in targets:
        build(t.resolve(), done)
