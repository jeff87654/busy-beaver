#!/usr/bin/bash
# Clean compile of the comparison hydra32 vs hydra31 (an upper bound for hydra31's score, and hydra32's lower bound
# above it) against a busycoq checkout (commit bd2e36f), then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# The machine files are byte-identical copies of the published ones (share_check.sh).  Logical path BB8 as there.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
bash ./share_check.sh
for f in BB312 Individual312 BB322 Individual322 BB31_tm BB31_rules BB32_tm BB32_rules Ord Hardy HydraOrd BB31_scan BB31_round BB31_game BB31_halt BB32_scan BB32_round BB32_game BB32_halt BB32_bound HydraUpper BB31_upper BB32_vs_BB31; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 6 theorems closed under the global context"
