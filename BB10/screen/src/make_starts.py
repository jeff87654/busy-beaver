"""Write renum start configurations: the base machine of an mf35g family at its first E0 read (where the base machine
halts) after the exhaustion K(0^35; 0; b), one line "n35b<b> TAPE HEAD STATE" per b (mf35g.xstart).
  python make_starts.py FAMILY B1 B2 ... > starts.txt        e.g.  python make_starts.py GH 0 1 2 3 4 5 6 14"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import mf35g

fam = sys.argv[1]
for b in map(int, sys.argv[2:]):
    word, head, state = mf35g.xstart(fam, b)
    print(f'n35b{b} {word} {head} {state}')
