#!/usr/bin/bash
# The files listed below are byte-identical copies of the other entries' files (busycoq instantiated for
# each number of states, the proofs that the comparison file loads, and the generic upper bounds JZ_UB.v,
# whose home is BB18/verify_r18c/multifile).  This script checks that.   ./share_check.sh
cd "$(dirname "$0")" || exit 2
fail=0; n=0
chk() { if cmp -s "$1.v" "$2/$1.v"; then n=$((n + 1)); else echo "$1.v differs from $2/$1.v"; fail=1; fi; }
chk BB182 ../../../BB18/verify_r18a/multifile
chk Individual182 ../../../BB18/verify_r18a/multifile
chk BB18_J18_w2_C_tnf ../../../BB18/verify_j18c/multifile
chk BB172 ../../../BB17/verify_j17/multifile
chk Individual172 ../../../BB17/verify_j17/multifile
chk BB17_J17_w2_champ ../../../BB17/verify_j17/multifile
echo "$n of 6 shared files byte-identical to their originals"
exit $fail
