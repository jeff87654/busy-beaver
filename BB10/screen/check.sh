#!/bin/sh
# Smoke test of the package (about a minute): build, the zeros filter on the GH screen, the mini-follower on n1
# against the logged histories, a short renum run, and one symbolic follow2 stage.
#   ./check.sh            (PYTHON=... to choose the interpreter; CXX=... for the compiler)
set -e
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
command -v "$PY" >/dev/null 2>&1 || PY=python
EXE=
case "$(uname -s)" in MINGW*|MSYS*|CYGWIN*) EXE=.exe ;; esac
N1=1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_---0LC
GHBASE=1RB0RA_1LC1LF_1RD0LB_1RA1LE_---0LC_0RG1LD_1RH1LG_1LC0RG
T=.check_tmp
rm -rf "$T"; mkdir "$T"
trap 'rm -rf "$T"' EXIT
fail() { echo "FAIL: $*"; exit 1; }

echo "== (a) build"
./build.sh

echo "== (b) zeros filter on data/mf_GH.tsv.gz (n1 must be selected; the k-based measure must not flag it)"
"$PY" src/zeros_filter.py data/mf_GH.tsv.gz --compare-k --show "$N1" | tr -d '\r' > "$T/zf.txt"
cat "$T/zf.txt"
grep -q "^# show $N1: .*selected=yes, rank [12]," "$T/zf.txt" || fail "n1 not among the top two zeros-filter groups"
grep -q "k growth/jump 0.2," "$T/zf.txt" || fail "n1's k growth per jump changed"

echo "== (c) mini-follower (mf35g, family GH, run A) on n1 vs the logged histories"
"$PY" src/mf35g.py GH "$N1" --stages 12 --maxs 3000000 | tr -d '\r' > "$T/mf12.txt"
"$PY" src/mf35g.py GH "$N1" --stages 80 --maxs 3000000 | tr -d '\r' > "$T/mf80.txt"
"$PY" - "$N1" "$T/mf12.txt" data/mf_GH.tsv.gz "$T/mf80.txt" data/mg80_GH.tsv.gz <<'PYEOF'
import gzip, re, sys
n1 = sys.argv[1]
for out, ref in ((sys.argv[2], sys.argv[3]), (sys.argv[4], sys.argv[5])):
    got = open(out).read().strip().split(' ', 3)          # RESULT kind nrec history
    row = next(l.rstrip('\n').split('\t') for l in gzip.open(ref, 'rt') if l.startswith(n1 + '\t'))
    zs = [int(z) for z in re.findall(r'zeros=(\d+)', got[3])]
    print(f'{ref}: {got[1]}, {got[2]} records, zeros= {" ".join(map(str, zs))}')
    if [got[1], got[2], got[3]] != [row[1], row[2], row[4]]:
        sys.exit(f'FAIL: history differs from {ref}')
print('both histories identical to the logged rows')
PYEOF

echo "== (d) renum: documented starts and a short run (b = 0 start, 20000 steps)"
"$PY" src/make_starts.py GH 0 1 2 3 4 5 6 14 | tr -d '\r' > "$T/starts.txt"
cmp "$T/starts.txt" data/starts_GH.txt || fail "make_starts.py output differs from data/starts_GH.txt"
head -1 data/starts_GH.txt > "$T/st0.txt"
"src/renum$EXE" "$GHBASE" 10 "$T/st0.txt" 20000 | tr -d '\r' > "$T/renum.txt"
tail -1 "$T/renum.txt"
grep -q '^#summary nodes=17117 printed=11853 quiet=5264$' "$T/renum.txt" || fail "renum summary changed"
grep -q "^$N1	T:20000$" "$T/renum.txt" || fail "n1 is not a renum leaf"
echo "n1 is a leaf of the tree"

echo "== (e) follow2 (symbolic in b, literal stages by hyb10): first stage of n1"
"$PY" src/follow2.py "$N1" --n 35 --template R,G,P=1,u=01,s=1,d=3d+1,b=3b+1,S=1010 --stages 1 | tr -d '\r' > "$T/f2.txt"
cat "$T/f2.txt" | cut -c1-160
grep -q 'event config: D(2) D(5) D(1)^{12\*b+7} D(0)^{3} D(3) D(1)^{32} D(1) D(R1) (10)^4' "$T/f2.txt" || fail "follow2 stage 0 changed"

echo "ALL CHECKS PASSED"
