#!/usr/bin/bash
# 30 files here are byte-identical copies of published files: B21's halting proof and its omega^2 layer, J20's and
# R18a's proofs (all as in ../../../BB21/verify_w2/multifile), and W2PR's halting proof (../../verify/multifile).
# Only BB25_W2PR_bound.v and BB25_W2PR_w2.v are new.  This script checks that.   ./share_check.sh
cd "$(dirname "$0")" || exit 2
W2=../../../BB21/verify_w2/multifile; V=../../verify/multifile
fail=0; n=0
for f in *.v; do
  case "$f" in BB25_W2PR_bound.v|BB25_W2PR_w2.v|probe.v) continue ;; esac
  if [ -f "$V/$f" ]; then src=$V; else src=$W2; fi
  if cmp -s "$f" "$src/$f"; then n=$((n + 1)); else echo "$f differs from $src/$f"; fail=1; fi
done
echo "$n of 30 shared files byte-identical to the published copies"
exit $fail
