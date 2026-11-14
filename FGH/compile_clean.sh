#!/usr/bin/bash
# Clean compile of the FGH statements of the multi-symbol entries against a busycoq checkout (commit bd2e36f),
# then the probes.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# Builds the entry directories it loads (BB34/verify, BB43/verify, BB44/verify_44b, BB54/verify_54l) if their .vo files
# are missing.  Logical root BB8 here (Ord.v is a copy of BB31/verify/multifile/Ord.v).
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
bash ./share_check.sh
run() { echo "== $1 =="; start=$(date +%s); shift; "$COQC" -Q "$BUSYCOQ" BusyCoq "$@"; echo "   ok, $(( $(date +%s) - start )) s"; }
run Ord.v -Q . BB8 Ord.v
run KnuthFGH.v -Q . BB8 KnuthFGH.v
if [ ! -f ../BB34/verify/BB34_score.vo ]; then (cd ../BB34/verify && bash ./compile_clean.sh); fi
run FGH_BB34.v -Q . BB8 -Q ../BB34/verify TM34 FGH_BB34.v
if [ ! -f ../BB43/verify/BB43_score.vo ]; then (cd ../BB43/verify && bash ./compile_clean.sh); fi
run FGH_BB43.v -Q . BB8 -Q ../BB43/verify TM43 FGH_BB43.v
if [ ! -f ../BB44/verify_44b/BB44B_cmp.vo ]; then (cd ../BB44/verify_44b && bash ./compile_clean.sh); fi
run FGH_BB44.v -Q . BB8 -Q ../BB44/verify_44b Local FGH_BB44.v
if [ ! -f ../BB54/verify_54l/BB54_bound.vo ]; then (cd ../BB54/verify_54l && bash ./compile_clean.sh); fi
run FGH_BB54.v -Q . BB8 -Q ../BB54/verify_54l Local FGH_BB54.v
echo "COMPILE DONE"
: > probe.log
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 -Q ../BB34/verify TM34 probe34.v >> probe.log
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 -Q ../BB43/verify TM43 probe43.v >> probe.log
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 -Q ../BB44/verify_44b Local probe44.v >> probe.log
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 -Q ../BB54/verify_54l Local probe54.v >> probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 12 theorems closed under the global context"
