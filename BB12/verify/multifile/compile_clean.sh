#!/usr/bin/bash
# Clean compile of the BB12 (T12a) proofs against a busycoq checkout (commit bd2e36f), in dependency order,
# then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path BB8 for this directory is historical.
# The first ten files are the BB(10) n1 development (identical to ../../../BB10/verify/multifile/): T12a's round 1
# is n1's run, and the score comparison uses n1's Coq-proved exact score.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
for f in BB102 Individual102 BB10_n1 BB10_lead_1RB0RA BB10_lead_bound BB10_champion_1RB1RA BB10_champion_bound \
         BB10_lead_vs_champion BB10_n1_bound BB10_n1_exact BB10_n1_fgh BB122 Individual122 BB12_T12a BB12_T12a_bound \
         BB12_T12a_fgh; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 5 theorems closed under the global context"
