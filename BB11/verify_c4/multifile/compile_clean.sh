#!/usr/bin/bash
# Clean compile of the C4 (11 states) proof against a busycoq checkout (commit bd2e36f), in dependency order,
# then the probe.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
# COQC may be set to a specific coqc executable.  The logical path BB8 for this directory is historical.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
if [ -d ../../verify/multifile ] && [ -d ../../../BB12/verify_m12/multifile ]; then bash ./share_check.sh; fi
"$COQC" --version | head -1
for f in BB112 Individual112 BB11_M11b BB11_M11b_fgh BB11_M11b_upper BB11_C4 BB11_C4_bound BB11_C4_cmp BB122 Individual122 BB12_M12 BB12_M12_bound BB11_C4_vs_M12; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 9 theorems closed under the global context"
