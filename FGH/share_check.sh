#!/usr/bin/bash
# FGH/Ord.v must be byte-identical to the published BB31/verify/multifile/Ord.v.
cd "$(dirname "$0")"
if cmp -s Ord.v ../BB31/verify/multifile/Ord.v; then echo "share_check: 1 identical, 0 different"; else echo "DIFFERS: Ord.v"; exit 1; fi
