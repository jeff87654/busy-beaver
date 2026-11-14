#!/usr/bin/bash
# Clean compile of 53-Main's comparisons: with the BB(4,3) entry (BB53_vs_BB43.v, loads ../../BB43/verify, logical
# root TM43) and with the standard fast-growing hierarchy (BB53_fgh.v, loads Ord.v, a byte-identical copy of
# BB31/verify/multifile/Ord.v, logical root BB8 here).  Both load ../verify (logical root Local).  Builds those two
# directories first if their .vo files are missing.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
bash ./share_check.sh
if [ ! -f ../verify/BB53_bound.vo ]; then (cd ../verify && bash ./compile_clean.sh); fi
if [ ! -f ../../BB43/verify/BB43_score.vo ]; then (cd ../../BB43/verify && bash ./compile_clean.sh); fi
Q="-Q $BUSYCOQ BusyCoq -Q ../verify Local -Q ../../BB43/verify TM43 -Q . BB8"
for f in Ord BB53_vs_BB43 BB53_fgh; do
  echo "== $f.v =="
  start=$(date +%s)
  "$COQC" $Q "$f.v"
  echo "   ok, $(( $(date +%s) - start )) s"
done
echo "COMPILE DONE"
"$COQC" $Q probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 5 theorems closed under the global context"
