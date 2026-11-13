#!/usr/bin/bash
# BB132.v, Individual132.v, BB13_M13b.v, BB13_M13b_bound.v in this directory are byte-identical copies of ../../verify_m13b/multifile's
# (busycoq instantiated for 13 states, and the M13b proof that the comparison loads).  This script checks that.   ./share_check.sh   (OTHER=... to override)
cd "$(dirname "$0")" || exit 2
OTHER=${OTHER:-../../verify_m13b/multifile}
fail=0; n=0
for f in BB132 Individual132 BB13_M13b BB13_M13b_bound; do
  if cmp -s "$f.v" "$OTHER/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $OTHER/$f.v"; fail=1; fi
done
echo "$n of 4 shared files byte-identical to $OTHER's"
exit $fail
