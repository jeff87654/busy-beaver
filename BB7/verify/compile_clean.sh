#!/usr/bin/bash
# Clean compile of the champ_231 / champ_232 proofs (BB(7)) against a busycoq checkout (commit bd2e36f), in
# dependency order, then the two probes.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path of this directory is BB7.
# Nearly all of the time is in C231_init.v and C232_init.v (the 3715 / 3775 start-up steps, a few minutes each).
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
cd "$(dirname "$0")" || exit 2
set -e
for f in BB72 Individual72 Defs Uniq Clr Bound Bound3 \
         C231_rules1 C231_rules2 C231_rules3 C231_init C231_clear C231_run C231_main \
         C232_rules1 C232_rules2 C232_rules3 C232_init C232_clear C232_run C232_main Statement; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB7 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
for p in probe231 probe232; do
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB7 $p.v > $p.log
  echo "$p: $(grep -c 'Closed under the global context' $p.log) of 6 theorems closed under the global context"
done
