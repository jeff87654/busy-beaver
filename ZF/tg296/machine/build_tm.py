"""Compile source_tg.py with Andrew Wade's TMBuilder (../../generator, unmodified) and write the table.

    python3 build_tm.py [OUT.tm]        (default: m254tg_rebuilt.tm next to this file)

tm.py writes in text mode, so the output equals m254tg_wade.tm (LF) byte for byte on Linux / macOS, and
up to line terminators on Windows. check.py compares the two after normalizing line terminators."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'generator'))
sys.path.insert(0, HERE)
import source_tg

out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'm254tg_rebuilt.tm')
z = source_tg.ZF2()
z.debug = False
z.build_machine()
z.tm.save(out)
print(out, len(set(s[0] for s in z.tm.states)), 'states')
