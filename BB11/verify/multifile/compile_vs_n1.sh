#!/usr/bin/bash
# Compile the comparison with n1 (run compile_clean.sh first).  The BB10_* files and BB102.v / Individual102.v are
# byte-identical to ../../../BB10/verify/multifile/; BB10_n1.v takes most of the time (about 6 minutes in all).
#   BUSYCOQ=/path/to/busycoq/verify ./compile_vs_n1.sh
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
for f in BB102 Individual102 BB10_n1 BB10_lead_1RB0RA BB10_lead_bound BB10_champion_1RB1RA BB10_champion_bound          BB10_lead_vs_champion BB10_n1_bound BB10_n1_exact BB10_n1_fgh BB11_M11b_vs_n1; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 probe_vs_n1.v > probe_vs_n1.log
echo "probe: $(grep -c 'Closed under the global context' probe_vs_n1.log) of 1 theorem closed under the global context"
