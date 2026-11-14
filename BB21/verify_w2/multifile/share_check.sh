#!/usr/bin/bash
# 20 files here are byte-identical copies of published files: B21's whole halting proof (../../verify/multifile,
# all but its headline BB21_B21.v), and J20's and R18a's proofs (../../../BB20/verify/multifile,
# ../../../BB18/verify_r18a/multifile), which BB_FGH_wa.v loads to compare its hierarchy with theirs, and J20_cube's
# proof with its upper-bound library (../../../BB20/verify_j20cube/multifile), which B21_vs_J20cube.v loads.
# This script checks that.   ./share_check.sh
cd "$(dirname "$0")" || exit 2
fail=0; n=0
chk() { if cmp -s "$1.v" "$2/$1.v"; then n=$((n + 1)); else echo "$1.v differs from $2/$1.v"; fail=1; fi; }
for f in BB212 Individual212 BB21_B21_absdef BB21_B21_tm BB21_B21_sim BB21_B21_grow BB21_B21_steps BB21_B21_inv \
         BB21_B21_proc BB21_B21_phase BB21_B21_run BB21_B21_score; do chk "$f" ../../verify/multifile; done
for f in BB202 Individual202 BB20_JZ20; do chk "$f" ../../../BB20/verify/multifile; done
for f in BB182 Individual182 BB18_R18a; do chk "$f" ../../../BB18/verify_r18a/multifile; done
for f in BB20_J20_w2_cube JZ_UB; do chk "$f" ../../../BB20/verify_j20cube/multifile; done
echo "$n of 20 shared files byte-identical to the published copies"
exit $fail
