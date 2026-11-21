#!/bin/bash
# Clean compile of the BB83 proofs against a busycoq checkout, in dependency order,
# then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path of this directory is TM83.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
for f in BB83 Individual83 BB83_rules BB83_start BB83_run BB83_score; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . TM83 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . TM83 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) theorems closed under the global context"
grep -c 'Axioms' probe.log && echo "PROBLEM: axioms present" || echo "no axioms"
