#!/usr/bin/bash
# BB112.v, Individual112.v, BB11_M11b.v, BB11_M11b_fgh.v, BB11_M11b_upper.v in this directory are byte-identical copies
# of ../../verify/multifile's (busycoq instantiated for 11 states, and the M11b proof that BB11_C4_cmp.v loads), and
# BB122.v, Individual122.v, BB12_M12.v, BB12_M12_bound.v of ../../../BB12/verify_m12/multifile's (busycoq for 12 states
# and the M12 proof that BB11_C4_vs_M12.v loads).  This script checks that.   ./share_check.sh
# (OTHER=... and OTHER12=... to override)
cd "$(dirname "$0")" || exit 2
OTHER=${OTHER:-../../verify/multifile}
OTHER12=${OTHER12:-../../../BB12/verify_m12/multifile}
fail=0; n=0
for f in BB112 Individual112 BB11_M11b BB11_M11b_fgh BB11_M11b_upper; do
  if cmp -s "$f.v" "$OTHER/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $OTHER/$f.v"; fail=1; fi
done
for f in BB122 Individual122 BB12_M12 BB12_M12_bound; do
  if cmp -s "$f.v" "$OTHER12/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $OTHER12/$f.v"; fail=1; fi
done
echo "$n of 9 shared files byte-identical to $OTHER's and $OTHER12's"
exit $fail
