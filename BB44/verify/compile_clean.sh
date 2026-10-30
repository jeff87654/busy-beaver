#!/bin/bash
# Clean compile of the BB(4,4) proofs against a busycoq checkout (commit bd2e36f), in dependency order,
# then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path of this directory is TM44.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
for f in BB44 Individual44 BB44_rules BB44_start BB44_run BB44_score; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . TM44 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . TM44 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 32 theorems closed under the global context"
