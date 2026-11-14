#!/usr/bin/bash
# The shared files here must be byte-identical to the published ones they copy.
cd "$(dirname "$0")"
ok=0; bad=0
if cmp -s Ord.v ../../BB31/verify/multifile/Ord.v; then ok=$((ok+1)); else echo "DIFFERS: Ord.v vs BB31/verify/multifile/Ord.v"; bad=$((bad+1)); fi
echo "share_check: $ok identical, $bad different"
[ "$bad" -eq 0 ]
