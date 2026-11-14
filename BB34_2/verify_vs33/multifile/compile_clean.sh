#!/usr/bin/bash
# Clean compile of the comparison hydra34 vs hydra33 (an upper bound for hydra33's score, and hydra34's lower bound
# above it) against a busycoq checkout (commit bd2e36f), then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# The machine files are byte-identical copies of the published ones (share_check.sh).  Logical path BB8 as there.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
bash ./share_check.sh
for f in BB332 Individual332 BB342 Individual342 BB33_tm BB33_rules BB34_tm BB34_rules Ord Hardy HydraOrd BB33_scan BB33_round BB33_game BB33_halt BB34_scan BB34_round BB34_game BB34_halt BB34_bound HydraUpper BB33_upper BB34_vs_BB33; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 6 theorems closed under the global context"
