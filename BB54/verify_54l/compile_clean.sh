#!/bin/bash
# Clean compile of the 54-L (BB(5,4)) proofs against a busycoq checkout (commit bd2e36f), in dependency order,
# then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path of this directory is Local (Argon's files).
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
for f in BB54 Individual54 BB54_rules BB54_run BB54_bound; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . Local "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
# the comparison with the previous entry (Jacobzheng's machine) needs ../verify compiled (logical path TM54)
if [ ! -f ../verify/BB54_bound.vo ]; then (cd ../verify && bash ./compile_clean.sh); fi
echo "== BB54_J_upper.v =="
start=$(date +%s)
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q ../verify TM54 -Q . Local BB54_J_upper.v
echo "   ok, $(( $(date +%s) - start )) s"
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q ../verify TM54 -Q . Local probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 11 theorems closed under the global context"
