"""Compile source_pa.py with Andrew Wade's TMBuilder (../../../ZF/generator, unmodified) and write the table.

    python3 build_tm.py [OUT.tm]        (default: pa_rebuilt.tm next to this file)

tm.py writes in text mode, so the output equals pa_wade.tm (LF) byte for byte on Linux / macOS, and
up to line terminators on Windows. check.py compares the two after normalizing line terminators."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', '..', 'ZF', 'generator'))
sys.path.insert(0, HERE)
import source_pa

out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'pa_rebuilt.tm')
z = source_pa.ZF2()
z.debug = False
z.build_machine()
z.tm.save(out)
print(out, len(set(s[0] for s in z.tm.states)), 'states')
