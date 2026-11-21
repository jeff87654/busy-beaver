#!/bin/bash
# Clean compile of the BB(6,4) machine
#   1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ
# proofs against a busycoq checkout, in dependency order, then the probe.
#
#   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
#
# COQC may be set to a specific coqc executable.  The logical path of this
# directory is TM64; the bundled FGH library (../fgh/) is BB8.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
COQARGS=(-Q "$BUSYCOQ" BusyCoq -Q . TM64 -Q ../fgh BB8)

# 0. bundled fast-growing-hierarchy library (only Coq.Arith / Lia)
for f in Ord KnuthFGH; do
  echo "== fgh/$f.v =="
  start=$(date +%s)
  "$COQC" -Q ../fgh BB8 "../fgh/$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done

# 1. machine instantiation, macro rules, trajectory, score, lower bound
for f in BB64 Individual64 BB64_rules BB64_run BB64_score BB64_bound; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" "${COQARGS[@]}" "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done

# 2. bridge to the actual fast-growing hierarchy f_(omega+1)
echo "== FGH_BB64.v =="
start=$(date +%s)
"$COQC" "${COQARGS[@]}" FGH_BB64.v
echo "   ok, $(( $(date +%s) - start )) s"

echo "COMPILE DONE"
echo "== probe =="
"$COQC" "${COQARGS[@]}" probe.v > probe.log 2>&1
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 8 theorems closed under the global context"
grep -E 'Closed under the global context|Axioms' probe.log | tail -30
