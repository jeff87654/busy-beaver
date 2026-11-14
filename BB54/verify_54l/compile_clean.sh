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
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . Local probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 8 theorems closed under the global context"
