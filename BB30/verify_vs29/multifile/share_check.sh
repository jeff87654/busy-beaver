#!/usr/bin/bash
# The shared files here must be byte-identical to the published ones they copy.
cd "$(dirname "$0")"
ok=0; bad=0
if cmp -s BB292.v ../../../BB29/verify/multifile/BB292.v; then ok=$((ok+1)); else echo "DIFFERS: BB292.v vs BB29/verify/multifile/BB292.v"; bad=$((bad+1)); fi
if cmp -s Individual292.v ../../../BB29/verify/multifile/Individual292.v; then ok=$((ok+1)); else echo "DIFFERS: Individual292.v vs BB29/verify/multifile/Individual292.v"; bad=$((bad+1)); fi
if cmp -s BB29_tm.v ../../../BB29/verify/multifile/BB29_tm.v; then ok=$((ok+1)); else echo "DIFFERS: BB29_tm.v vs BB29/verify/multifile/BB29_tm.v"; bad=$((bad+1)); fi
if cmp -s BB29_rules.v ../../../BB29/verify/multifile/BB29_rules.v; then ok=$((ok+1)); else echo "DIFFERS: BB29_rules.v vs BB29/verify/multifile/BB29_rules.v"; bad=$((bad+1)); fi
if cmp -s BB29_scan.v ../../../BB29/verify/multifile/BB29_scan.v; then ok=$((ok+1)); else echo "DIFFERS: BB29_scan.v vs BB29/verify/multifile/BB29_scan.v"; bad=$((bad+1)); fi
if cmp -s BB29_round.v ../../../BB29/verify/multifile/BB29_round.v; then ok=$((ok+1)); else echo "DIFFERS: BB29_round.v vs BB29/verify/multifile/BB29_round.v"; bad=$((bad+1)); fi
if cmp -s BB29_hydra.v ../../../BB29/verify/multifile/BB29_hydra.v; then ok=$((ok+1)); else echo "DIFFERS: BB29_hydra.v vs BB29/verify/multifile/BB29_hydra.v"; bad=$((bad+1)); fi
if cmp -s BB29_halt.v ../../../BB29/verify/multifile/BB29_halt.v; then ok=$((ok+1)); else echo "DIFFERS: BB29_halt.v vs BB29/verify/multifile/BB29_halt.v"; bad=$((bad+1)); fi
if cmp -s Ord.v ../../../BB29/verify/multifile/Ord.v; then ok=$((ok+1)); else echo "DIFFERS: Ord.v vs BB29/verify/multifile/Ord.v"; bad=$((bad+1)); fi
if cmp -s Ufun.v ../../../BB29/verify/multifile/Ufun.v; then ok=$((ok+1)); else echo "DIFFERS: Ufun.v vs BB29/verify/multifile/Ufun.v"; bad=$((bad+1)); fi
if cmp -s BB29_bound.v ../../../BB29/verify/multifile/BB29_bound.v; then ok=$((ok+1)); else echo "DIFFERS: BB29_bound.v vs BB29/verify/multifile/BB29_bound.v"; bad=$((bad+1)); fi
if cmp -s BB302.v ../../../BB30/verify/multifile/BB302.v; then ok=$((ok+1)); else echo "DIFFERS: BB302.v vs BB30/verify/multifile/BB302.v"; bad=$((bad+1)); fi
if cmp -s Individual302.v ../../../BB30/verify/multifile/Individual302.v; then ok=$((ok+1)); else echo "DIFFERS: Individual302.v vs BB30/verify/multifile/Individual302.v"; bad=$((bad+1)); fi
if cmp -s BB30_tm.v ../../../BB30/verify/multifile/BB30_tm.v; then ok=$((ok+1)); else echo "DIFFERS: BB30_tm.v vs BB30/verify/multifile/BB30_tm.v"; bad=$((bad+1)); fi
if cmp -s BB30_rules.v ../../../BB30/verify/multifile/BB30_rules.v; then ok=$((ok+1)); else echo "DIFFERS: BB30_rules.v vs BB30/verify/multifile/BB30_rules.v"; bad=$((bad+1)); fi
if cmp -s Hardy.v ../../../BB30/verify/multifile/Hardy.v; then ok=$((ok+1)); else echo "DIFFERS: Hardy.v vs BB30/verify/multifile/Hardy.v"; bad=$((bad+1)); fi
if cmp -s HydraOrd.v ../../../BB30/verify/multifile/HydraOrd.v; then ok=$((ok+1)); else echo "DIFFERS: HydraOrd.v vs BB30/verify/multifile/HydraOrd.v"; bad=$((bad+1)); fi
if cmp -s BB30_scan.v ../../../BB30/verify/multifile/BB30_scan.v; then ok=$((ok+1)); else echo "DIFFERS: BB30_scan.v vs BB30/verify/multifile/BB30_scan.v"; bad=$((bad+1)); fi
if cmp -s BB30_round.v ../../../BB30/verify/multifile/BB30_round.v; then ok=$((ok+1)); else echo "DIFFERS: BB30_round.v vs BB30/verify/multifile/BB30_round.v"; bad=$((bad+1)); fi
if cmp -s BB30_game.v ../../../BB30/verify/multifile/BB30_game.v; then ok=$((ok+1)); else echo "DIFFERS: BB30_game.v vs BB30/verify/multifile/BB30_game.v"; bad=$((bad+1)); fi
if cmp -s BB30_halt.v ../../../BB30/verify/multifile/BB30_halt.v; then ok=$((ok+1)); else echo "DIFFERS: BB30_halt.v vs BB30/verify/multifile/BB30_halt.v"; bad=$((bad+1)); fi
if cmp -s BB30_bound.v ../../../BB30/verify/multifile/BB30_bound.v; then ok=$((ok+1)); else echo "DIFFERS: BB30_bound.v vs BB30/verify/multifile/BB30_bound.v"; bad=$((bad+1)); fi
echo "share_check: $ok identical, $bad different"
[ "$bad" -eq 0 ]
