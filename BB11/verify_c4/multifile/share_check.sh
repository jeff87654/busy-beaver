#!/usr/bin/bash
# BB112.v, Individual112.v, BB11_M11b.v, BB11_M11b_fgh.v, BB11_M11b_upper.v in this directory are byte-identical copies of ../../verify/multifile's
# (busycoq instantiated for 11 states, and the M11b proof that the comparison loads).  This script checks that.   ./share_check.sh   (OTHER=... to override)
cd "$(dirname "$0")" || exit 2
OTHER=${OTHER:-../../verify/multifile}
fail=0; n=0
for f in BB112 Individual112 BB11_M11b BB11_M11b_fgh BB11_M11b_upper; do
  if cmp -s "$f.v" "$OTHER/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $OTHER/$f.v"; fail=1; fi
done
echo "$n of 5 shared files byte-identical to $OTHER's"
exit $fail
