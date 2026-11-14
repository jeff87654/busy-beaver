#!/usr/bin/bash
# BB192.v, Individual192.v in this directory are byte-identical copies of ../../verify_jz19/multifile's
# (busycoq instantiated for 19 states).  This script checks that.   ./share_check.sh   (OTHER=... to override)
cd "$(dirname "$0")" || exit 2
OTHER=${OTHER:-../../verify_jz19/multifile}
fail=0; n=0
for f in BB192 Individual192; do
  if cmp -s "$f.v" "$OTHER/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $OTHER/$f.v"; fail=1; fi
done
echo "$n of 2 shared files byte-identical to $OTHER's"
exit $fail
