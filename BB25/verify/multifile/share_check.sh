#!/usr/bin/bash
# The seven B21 layers in this directory are byte-identical copies of ../../../BB21/verify/multifile's files
# (the abstract block machine, growth and residues, the dominance invariant, frontier processing, phases, and
# B21's run file, which W2PR's run reuses).  This script checks that.   ./share_check.sh   (B21=... to override)
cd "$(dirname "$0")" || exit 2
B21=${B21:-../../../BB21/verify/multifile}
fail=0; n=0
for f in BB21_B21_absdef BB21_B21_grow BB21_B21_steps BB21_B21_inv BB21_B21_proc BB21_B21_phase BB21_B21_run; do
  if cmp -s "$f.v" "$B21/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $B21/$f.v"; fail=1; fi
done
echo "$n of 7 B21 layers byte-identical to $B21's"
exit $fail
