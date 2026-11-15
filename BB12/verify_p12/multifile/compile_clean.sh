#!/usr/bin/bash
# Clean compile of the P12 (12 states) proof against a busycoq checkout (commit bd2e36f), in dependency order,
# then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path BB8 for this directory is historical.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
if [ -d ../../verify_m12/multifile ] && [ -d ../../../BB11/verify_c4/multifile ]; then bash ./share_check.sh; fi
"$COQC" --version | head -1
for f in BB122 Individual122 BB12_P12 BB12_P12_bound BB112 Individual112 BB11_C4 BB12_P12_cmp; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 5 theorems closed under the global context"
