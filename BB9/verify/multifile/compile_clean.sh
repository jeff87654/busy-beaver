#!/usr/bin/bash
# Clean compile of the BB9 multi-file proofs against a busycoq checkout (commit bd2e36f), in dependency order.
#   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path BB8 for this directory is historical.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
for f in BB92 Individual92 BB9_record_1RB0RA BB9_record_bound BB9_champion_1RB1RA BB9_champion_bound \
         BB9_record_vs_champion BB9_record_twin_1RB0RA; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
