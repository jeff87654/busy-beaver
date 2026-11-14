#!/usr/bin/bash
# Clean compile of the comparison hydra30 vs hydra29 (hydra29's exact score bounded above, and hydra30's lower bound
# above it) against a busycoq checkout (commit bd2e36f), then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# The machine files are byte-identical copies of the published ones (share_check.sh).  Logical path BB8 as there.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
bash ./share_check.sh
for f in BB292 Individual292 BB29_tm BB29_rules BB29_scan BB29_round BB29_hydra BB29_halt Ord Ufun BB29_bound BB302 Individual302 BB30_tm BB30_rules Hardy HydraOrd BB30_scan BB30_round BB30_game BB30_halt BB30_bound BB29_upper BB30_vs_BB29; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 5 theorems closed under the global context"
