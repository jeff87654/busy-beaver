#!/usr/bin/bash
# Clean compile of the 44-B and 44-A proofs against a busycoq checkout (commit bd2e36f), in dependency order, then the
# probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# The first five files are byte-identical copies of ../verify_44c (share_check.sh).  Logical path Local, as there.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
bash ./share_check.sh
for f in BB44 Individual44 BB44_rules BB44_run BB44_bound BB44A_rules BB44A_run BB44A_cmp BB44B_rules BB44B_run BB44B_cmp; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . Local "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . Local probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 18 theorems closed under the global context"
