#!/usr/bin/bash
# Clean compile of the B21 omega^2 bound (Racheline's BB(21) champion) proof against a busycoq checkout (commit bd2e36f), in dependency order,
# then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path BB8 for this directory is historical.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
if [ -d ../../verify/multifile ] && [ -d ../../../BB20/verify/multifile ]; then bash ./share_check.sh; fi
"$COQC" --version | head -1
for f in BB202 Individual202 BB20_JZ20 BB182 Individual182 BB18_R18a BB212 Individual212 BB21_B21_absdef BB21_B21_tm BB21_B21_sim BB21_B21_grow BB21_B21_steps BB21_B21_inv BB21_B21_proc BB21_B21_phase BB21_B21_run BB21_B21_score BB_FGH_wa BB_FGH_wa2 BB21_B21_qnt BB21_B21_qnt2 BB21_B21_qnt3 BB21_B21_qnt4 BB21_B21_bound BB21_B21_w2 BB20_J20_w2_cube JZ_UB B21_vs_J20cube; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 7 theorems closed under the global context"
