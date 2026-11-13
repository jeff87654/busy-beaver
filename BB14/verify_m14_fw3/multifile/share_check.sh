#!/usr/bin/bash
# BB142.v, Individual142.v, BB14_M14_31.v in this directory are byte-identical copies of ../../verify_m14_31/multifile's
# (busycoq instantiated for 14 states, and the M14_31 proof that the comparison loads).  This script checks that.   ./share_check.sh   (OTHER=... to override)
cd "$(dirname "$0")" || exit 2
OTHER=${OTHER:-../../verify_m14_31/multifile}
fail=0; n=0
for f in BB142 Individual142 BB14_M14_31; do
  if cmp -s "$f.v" "$OTHER/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $OTHER/$f.v"; fail=1; fi
done
echo "$n of 3 shared files byte-identical to $OTHER's"
exit $fail
