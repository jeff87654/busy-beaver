#!/bin/bash
# Clean compile of the 44-C (BB(4,4)) proofs against a busycoq checkout (commit bd2e36f), in dependency order,
# then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path of this directory is Local (Argon's files).
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
for f in BB44 Individual44 BB44_rules BB44_run BB44_bound; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . Local "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "== BB44_sigma_cfg.v =="
start=$(date +%s)
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . Local BB44_sigma_cfg.v
echo "   ok, $(( $(date +%s) - start )) s"
# the comparison with the previous entry (loader3229's machine) needs ../verify compiled (logical path TM44)
if [ ! -f ../verify/BB44_score.vo ]; then (cd ../verify && bash ./compile_clean.sh); fi
echo "== BB44C_vs_loader3229.v =="
start=$(date +%s)
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q ../verify TM44 -Q . Local BB44C_vs_loader3229.v
echo "   ok, $(( $(date +%s) - start )) s"
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q ../verify TM44 -Q . Local probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 15 theorems closed under the global context"
