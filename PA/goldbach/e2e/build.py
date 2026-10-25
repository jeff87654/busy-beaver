"""Compile PA/goldbach/e2e/Headline.v (low priority).  The layers must already be built by their own scripts
(coq/build.py, tm/coq/build.py, prog/coq/build.py).  coqc: $COQC, else `coqc` on PATH.
Roots: PAGBE = . (this file: PAGBE.Headline), Undecidability = ../vendor/undecidability/theories,
BusyCoq = ../../../ZF/stdzf_r3/vendor/busycoq, PAGB = ../coq, PAGBT = ../tm/coq, PAGBP = ../prog/coq."""
import os, shutil, subprocess, sys
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
M = HERE.parent
COQC = os.environ.get('COQC') or shutil.which('coqc') or 'coqc'
FLAGS = ['-Q', str(M / 'vendor' / 'undecidability' / 'theories'), 'Undecidability',
         '-Q', str((M / '..' / '..' / 'ZF' / 'stdzf_r3' / 'vendor' / 'busycoq').resolve()), 'BusyCoq',
         '-Q', str(M / 'coq'), 'PAGB',
         '-Q', str(M / 'tm' / 'coq'), 'PAGBT',
         '-Q', str(M / 'prog' / 'coq'), 'PAGBP',
         '-Q', str(HERE), 'PAGBE',
         '-w', '-notation-overridden,-stdlib-vector,-notation-incompatible-prefix,-postfix-notation-not-level-1,-closed-notation-not-level-0,-deprecated']
f = sys.argv[1] if len(sys.argv) > 1 else 'Headline.v'
r = subprocess.run([COQC, *FLAGS, f], cwd=HERE, capture_output=True, text=True, encoding='utf-8', errors='replace',
                   creationflags=NOWIN)
print(r.stdout); print(r.stderr); sys.exit(r.returncode)
