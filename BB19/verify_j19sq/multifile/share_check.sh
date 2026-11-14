#!/usr/bin/bash
# The files listed below are byte-identical copies of the other entries' files (busycoq instantiated for
# each number of states, the proofs that the comparison file loads, and the generic upper bounds JZ_UB.v,
# whose home is BB18/verify_r18c/multifile).  This script checks that.   ./share_check.sh
cd "$(dirname "$0")" || exit 2
fail=0; n=0
chk() { if cmp -s "$1.v" "$2/$1.v"; then n=$((n + 1)); else echo "$1.v differs from $2/$1.v"; fail=1; fi; }
chk BB192 ../../../BB19/verify_jz19/multifile
chk Individual192 ../../../BB19/verify_jz19/multifile
chk BB182 ../../../BB18/verify_r18c/multifile
chk Individual182 ../../../BB18/verify_r18c/multifile
chk BB18_R18c ../../../BB18/verify_r18c/multifile
chk BB202 ../../../BB20/verify/multifile
chk Individual202 ../../../BB20/verify/multifile
chk BB20_JZ20 ../../../BB20/verify/multifile
chk JZ_UB ../../../BB18/verify_r18c/multifile
echo "$n of 9 shared files byte-identical to their originals"
exit $fail
