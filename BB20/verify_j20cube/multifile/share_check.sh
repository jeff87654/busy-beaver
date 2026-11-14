#!/usr/bin/bash
# BB202.v, Individual202.v in this directory are byte-identical copies of ../../verify/multifile's
# (busycoq instantiated for 20 states).  This script checks that.   ./share_check.sh   (OTHER=... to override)
cd "$(dirname "$0")" || exit 2
OTHER=${OTHER:-../../verify/multifile}
fail=0; n=0
for f in BB202 Individual202; do
  if cmp -s "$f.v" "$OTHER/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $OTHER/$f.v"; fail=1; fi
done
echo "$n of 2 shared files byte-identical to $OTHER's"
exit $fail
