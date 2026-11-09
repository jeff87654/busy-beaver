#!/usr/bin/bash
# Clean compile of the W2PR (25 states, built on B21) proof against a busycoq checkout (commit bd2e36f), in dependency order,
# then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path BB8 for this directory is historical.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
if [ -d ../../../BB21/verify/multifile ]; then bash ./share_check.sh; fi
"$COQC" --version | head -1
for f in BB252 Individual252 BB21_B21_absdef BB21_B21_grow BB21_B21_steps BB21_B21_inv BB21_B21_proc BB21_B21_phase BB21_B21_run BB25_W2PR_tm BB25_W2PR_sim BB25_W2PR_run BB25_W2PR_score BB25_W2PR; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 3 theorems closed under the global context"
