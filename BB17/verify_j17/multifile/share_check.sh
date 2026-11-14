#!/usr/bin/bash
# The files listed below are byte-identical copies of the other entries' files (busycoq instantiated for
# each number of states, the proofs that the comparison file loads, and the generic upper bounds JZ_UB.v,
# whose home is BB18/verify_r18c/multifile).  This script checks that.   ./share_check.sh
cd "$(dirname "$0")" || exit 2
fail=0; n=0
chk() { if cmp -s "$1.v" "$2/$1.v"; then n=$((n + 1)); else echo "$1.v differs from $2/$1.v"; fail=1; fi; }
chk BB172 ../../../BB17/verify/multifile
chk Individual172 ../../../BB17/verify/multifile
chk BB162 ../../../BB16/verify_j16/multifile
chk Individual162 ../../../BB16/verify_j16/multifile
chk BB16_J16_w2 ../../../BB16/verify_j16/multifile
chk JZ_UB ../../../BB18/verify_r18c/multifile
echo "$n of 6 shared files byte-identical to their originals"
exit $fail
