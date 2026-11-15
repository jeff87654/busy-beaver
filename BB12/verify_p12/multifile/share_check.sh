#!/usr/bin/bash
# BB122.v and Individual122.v in this directory are byte-identical copies of ../../verify_m12/multifile's (busycoq
# instantiated for 12 states), and BB112.v, Individual112.v, BB11_C4.v of ../../../BB11/verify_c4/multifile's (busycoq
# for 11 states and the C4 proof that BB12_P12_cmp.v loads).  This script checks that.   ./share_check.sh
# (OTHER12=... and OTHER11=... to override)
cd "$(dirname "$0")" || exit 2
OTHER12=${OTHER12:-../../verify_m12/multifile}
OTHER11=${OTHER11:-../../../BB11/verify_c4/multifile}
fail=0; n=0
for f in BB122 Individual122; do
  if cmp -s "$f.v" "$OTHER12/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $OTHER12/$f.v"; fail=1; fi
done
for f in BB112 Individual112 BB11_C4; do
  if cmp -s "$f.v" "$OTHER11/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $OTHER11/$f.v"; fail=1; fi
done
echo "$n of 5 shared files byte-identical to $OTHER12's and $OTHER11's"
exit $fail
