#!/bin/bash
# Clean compile of the BB73 proofs against a busycoq checkout, in dependency order,
# then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path of this directory is TM73.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
for f in BB73 Individual73 BB73_rules BB73_start BB73_run BB73_score; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . TM73 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . TM73 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) theorems closed under the global context"
grep -c 'Axioms' probe.log && echo "PROBLEM: axioms present" || echo "no axioms"
