#!/usr/bin/bash
# The shared files here must be byte-identical to the published ones they copy.
cd "$(dirname "$0")"
ok=0; bad=0
if cmp -s Ord.v ../../../BB33/verify/multifile/Ord.v; then ok=$((ok+1)); else echo "DIFFERS: Ord.v vs BB33/verify/multifile/Ord.v"; bad=$((bad+1)); fi
if cmp -s Hardy.v ../../../BB33/verify/multifile/Hardy.v; then ok=$((ok+1)); else echo "DIFFERS: Hardy.v vs BB33/verify/multifile/Hardy.v"; bad=$((bad+1)); fi
if cmp -s HydraOrd.v ../../../BB33/verify/multifile/HydraOrd.v; then ok=$((ok+1)); else echo "DIFFERS: HydraOrd.v vs BB33/verify/multifile/HydraOrd.v"; bad=$((bad+1)); fi
if cmp -s BB332.v ../../../BB33/verify/multifile/BB332.v; then ok=$((ok+1)); else echo "DIFFERS: BB332.v vs BB33/verify/multifile/BB332.v"; bad=$((bad+1)); fi
if cmp -s Individual332.v ../../../BB33/verify/multifile/Individual332.v; then ok=$((ok+1)); else echo "DIFFERS: Individual332.v vs BB33/verify/multifile/Individual332.v"; bad=$((bad+1)); fi
if cmp -s BB33_tm.v ../../../BB33/verify/multifile/BB33_tm.v; then ok=$((ok+1)); else echo "DIFFERS: BB33_tm.v vs BB33/verify/multifile/BB33_tm.v"; bad=$((bad+1)); fi
if cmp -s BB33_rules.v ../../../BB33/verify/multifile/BB33_rules.v; then ok=$((ok+1)); else echo "DIFFERS: BB33_rules.v vs BB33/verify/multifile/BB33_rules.v"; bad=$((bad+1)); fi
if cmp -s BB33_scan.v ../../../BB33/verify/multifile/BB33_scan.v; then ok=$((ok+1)); else echo "DIFFERS: BB33_scan.v vs BB33/verify/multifile/BB33_scan.v"; bad=$((bad+1)); fi
if cmp -s BB33_round.v ../../../BB33/verify/multifile/BB33_round.v; then ok=$((ok+1)); else echo "DIFFERS: BB33_round.v vs BB33/verify/multifile/BB33_round.v"; bad=$((bad+1)); fi
if cmp -s BB33_game.v ../../../BB33/verify/multifile/BB33_game.v; then ok=$((ok+1)); else echo "DIFFERS: BB33_game.v vs BB33/verify/multifile/BB33_game.v"; bad=$((bad+1)); fi
if cmp -s BB33_halt.v ../../../BB33/verify/multifile/BB33_halt.v; then ok=$((ok+1)); else echo "DIFFERS: BB33_halt.v vs BB33/verify/multifile/BB33_halt.v"; bad=$((bad+1)); fi
if cmp -s BB342.v ../../../BB34_2/verify/multifile/BB342.v; then ok=$((ok+1)); else echo "DIFFERS: BB342.v vs BB34_2/verify/multifile/BB342.v"; bad=$((bad+1)); fi
if cmp -s Individual342.v ../../../BB34_2/verify/multifile/Individual342.v; then ok=$((ok+1)); else echo "DIFFERS: Individual342.v vs BB34_2/verify/multifile/Individual342.v"; bad=$((bad+1)); fi
if cmp -s BB34_tm.v ../../../BB34_2/verify/multifile/BB34_tm.v; then ok=$((ok+1)); else echo "DIFFERS: BB34_tm.v vs BB34_2/verify/multifile/BB34_tm.v"; bad=$((bad+1)); fi
if cmp -s BB34_rules.v ../../../BB34_2/verify/multifile/BB34_rules.v; then ok=$((ok+1)); else echo "DIFFERS: BB34_rules.v vs BB34_2/verify/multifile/BB34_rules.v"; bad=$((bad+1)); fi
if cmp -s BB34_scan.v ../../../BB34_2/verify/multifile/BB34_scan.v; then ok=$((ok+1)); else echo "DIFFERS: BB34_scan.v vs BB34_2/verify/multifile/BB34_scan.v"; bad=$((bad+1)); fi
if cmp -s BB34_round.v ../../../BB34_2/verify/multifile/BB34_round.v; then ok=$((ok+1)); else echo "DIFFERS: BB34_round.v vs BB34_2/verify/multifile/BB34_round.v"; bad=$((bad+1)); fi
if cmp -s BB34_game.v ../../../BB34_2/verify/multifile/BB34_game.v; then ok=$((ok+1)); else echo "DIFFERS: BB34_game.v vs BB34_2/verify/multifile/BB34_game.v"; bad=$((bad+1)); fi
if cmp -s BB34_halt.v ../../../BB34_2/verify/multifile/BB34_halt.v; then ok=$((ok+1)); else echo "DIFFERS: BB34_halt.v vs BB34_2/verify/multifile/BB34_halt.v"; bad=$((bad+1)); fi
if cmp -s BB34_bound.v ../../../BB34_2/verify/multifile/BB34_bound.v; then ok=$((ok+1)); else echo "DIFFERS: BB34_bound.v vs BB34_2/verify/multifile/BB34_bound.v"; bad=$((bad+1)); fi
echo "share_check: $ok identical, $bad different"
[ "$bad" -eq 0 ]
