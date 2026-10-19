#!/usr/bin/bash
# Compile the M8 layer on top of the compiled C04 tree (../../BB9/verify_c04, built with its compile_clean.sh) and the
# compiled BB8 entry (../verify, built with its compile_clean.sh), then run probe.v.
#   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
#   BUSYCOQ=... ./compile_clean.sh deps     first build ../../BB9/verify_c04 and ../verify from scratch (their own
#                                           compile_clean.sh), then this directory
# C04 and BB8V may point to other compiled copies of those two trees.  COQC may be set to a specific coqc.
# Core files, in order: BB82 Individual82 Defs Tm8 Sim Transfer Headline8 Bridge.  Logical paths: the C04 tree's own (lib = BB8, dev = Dev,
# k31 = K31, score = Score, fgh = Fgh) plus this directory = M8; nothing from ../verify.  Then Beats8 (the comparison
# with the previous BB8 entry; it adds ../verify, also as BB8: its file names do not overlap the C04 tree's lib/),
# Statement (the theorems to read, with Defs.v), then probe.v (about 10 min, nearly all of it Print Assumptions).
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
cd "$(dirname "$0")" || exit 2
C04=${C04:-../../BB9/verify_c04}
BB8V=${BB8V:-../verify}
if [ "$1" = deps ]; then
  (cd "$C04" && bash ./compile_clean.sh) || { echo "building $C04 FAILED"; exit 1; }
  (cd "$BB8V" && bash ./compile_clean.sh) || { echo "building $BB8V FAILED"; exit 1; }
fi
for f in "$C04/fgh/Headline.vo" "$C04/dev/ScoreEnd.vo" "$BB8V/BB8_champ35_exact.vo"; do
  [ -f "$f" ] || { echo "$f is missing: build $C04 and $BB8V first (or run ./compile_clean.sh deps)" >&2; exit 2; }
done
FLAGS=(-Q "$BUSYCOQ" BusyCoq -Q "$C04/lib" BB8 -Q "$C04/dev" Dev -Q "$C04/k31" K31 -Q "$C04/score" Score
       -Q "$C04/fgh" Fgh -Q . M8)
run() {
  local f=$1; shift
  local start=$(date +%s)
  echo "== $f.v =="
  "$COQC" "$@" "$f.v" > "$f.log" 2>&1 || { cat "$f.log"; echo "$f.v FAILED"; exit 1; }
  echo "   ok, $(( $(date +%s) - start )) s"
}
for f in BB82 Individual82 Defs Tm8 Sim Transfer Headline8 Bridge; do run "$f" "${FLAGS[@]}"; done
for f in Beats8 Statement probe; do run "$f" "${FLAGS[@]}" -Q "$BB8V" BB8; done
closed=$(grep -c 'Closed under the global context' probe.log)
echo "probe: $closed of 20 Print Assumptions closed under the global context"
if grep -q 'Axioms:' probe.log || [ "$closed" -ne 20 ]; then exit 1; fi
exit 0
