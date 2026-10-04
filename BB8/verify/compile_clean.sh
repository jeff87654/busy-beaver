#!/usr/bin/bash
# Clean compile of the BB8 proofs against a busycoq checkout (commit bd2e36f), in dependency order,
# followed by probe.v, which re-checks the statements and prints the assumptions.
#   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
for f in BB82 Individual82 BB8_champ35_1RB0RA BB8_champ35_bound BB8_champ35_exact probe; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
