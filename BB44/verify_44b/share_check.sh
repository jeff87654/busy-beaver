#!/usr/bin/bash
# The shared files here must be byte-identical to BB44/verify_44c (44-C, Argon's files).
cd "$(dirname "$0")"
ok=0; bad=0
if cmp -s BB44.v ../verify_44c/BB44.v; then ok=$((ok+1)); else echo "DIFFERS: BB44.v"; bad=$((bad+1)); fi
if cmp -s Individual44.v ../verify_44c/Individual44.v; then ok=$((ok+1)); else echo "DIFFERS: Individual44.v"; bad=$((bad+1)); fi
if cmp -s BB44_rules.v ../verify_44c/BB44_rules.v; then ok=$((ok+1)); else echo "DIFFERS: BB44_rules.v"; bad=$((bad+1)); fi
if cmp -s BB44_run.v ../verify_44c/BB44_run.v; then ok=$((ok+1)); else echo "DIFFERS: BB44_run.v"; bad=$((bad+1)); fi
if cmp -s BB44_bound.v ../verify_44c/BB44_bound.v; then ok=$((ok+1)); else echo "DIFFERS: BB44_bound.v"; bad=$((bad+1)); fi
echo "share_check: $ok identical, $bad different"
[ "$bad" -eq 0 ]
