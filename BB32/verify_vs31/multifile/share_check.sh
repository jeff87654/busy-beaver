#!/usr/bin/bash
# The shared files here must be byte-identical to the published ones they copy.
cd "$(dirname "$0")"
ok=0; bad=0
if cmp -s Ord.v ../../../BB31/verify/multifile/Ord.v; then ok=$((ok+1)); else echo "DIFFERS: Ord.v vs BB31/verify/multifile/Ord.v"; bad=$((bad+1)); fi
if cmp -s Hardy.v ../../../BB31/verify/multifile/Hardy.v; then ok=$((ok+1)); else echo "DIFFERS: Hardy.v vs BB31/verify/multifile/Hardy.v"; bad=$((bad+1)); fi
if cmp -s HydraOrd.v ../../../BB31/verify/multifile/HydraOrd.v; then ok=$((ok+1)); else echo "DIFFERS: HydraOrd.v vs BB31/verify/multifile/HydraOrd.v"; bad=$((bad+1)); fi
if cmp -s BB312.v ../../../BB31/verify/multifile/BB312.v; then ok=$((ok+1)); else echo "DIFFERS: BB312.v vs BB31/verify/multifile/BB312.v"; bad=$((bad+1)); fi
if cmp -s Individual312.v ../../../BB31/verify/multifile/Individual312.v; then ok=$((ok+1)); else echo "DIFFERS: Individual312.v vs BB31/verify/multifile/Individual312.v"; bad=$((bad+1)); fi
if cmp -s BB31_tm.v ../../../BB31/verify/multifile/BB31_tm.v; then ok=$((ok+1)); else echo "DIFFERS: BB31_tm.v vs BB31/verify/multifile/BB31_tm.v"; bad=$((bad+1)); fi
if cmp -s BB31_rules.v ../../../BB31/verify/multifile/BB31_rules.v; then ok=$((ok+1)); else echo "DIFFERS: BB31_rules.v vs BB31/verify/multifile/BB31_rules.v"; bad=$((bad+1)); fi
if cmp -s BB31_scan.v ../../../BB31/verify/multifile/BB31_scan.v; then ok=$((ok+1)); else echo "DIFFERS: BB31_scan.v vs BB31/verify/multifile/BB31_scan.v"; bad=$((bad+1)); fi
if cmp -s BB31_round.v ../../../BB31/verify/multifile/BB31_round.v; then ok=$((ok+1)); else echo "DIFFERS: BB31_round.v vs BB31/verify/multifile/BB31_round.v"; bad=$((bad+1)); fi
if cmp -s BB31_game.v ../../../BB31/verify/multifile/BB31_game.v; then ok=$((ok+1)); else echo "DIFFERS: BB31_game.v vs BB31/verify/multifile/BB31_game.v"; bad=$((bad+1)); fi
if cmp -s BB31_halt.v ../../../BB31/verify/multifile/BB31_halt.v; then ok=$((ok+1)); else echo "DIFFERS: BB31_halt.v vs BB31/verify/multifile/BB31_halt.v"; bad=$((bad+1)); fi
if cmp -s BB322.v ../../../BB32/verify/multifile/BB322.v; then ok=$((ok+1)); else echo "DIFFERS: BB322.v vs BB32/verify/multifile/BB322.v"; bad=$((bad+1)); fi
if cmp -s Individual322.v ../../../BB32/verify/multifile/Individual322.v; then ok=$((ok+1)); else echo "DIFFERS: Individual322.v vs BB32/verify/multifile/Individual322.v"; bad=$((bad+1)); fi
if cmp -s BB32_tm.v ../../../BB32/verify/multifile/BB32_tm.v; then ok=$((ok+1)); else echo "DIFFERS: BB32_tm.v vs BB32/verify/multifile/BB32_tm.v"; bad=$((bad+1)); fi
if cmp -s BB32_rules.v ../../../BB32/verify/multifile/BB32_rules.v; then ok=$((ok+1)); else echo "DIFFERS: BB32_rules.v vs BB32/verify/multifile/BB32_rules.v"; bad=$((bad+1)); fi
if cmp -s BB32_scan.v ../../../BB32/verify/multifile/BB32_scan.v; then ok=$((ok+1)); else echo "DIFFERS: BB32_scan.v vs BB32/verify/multifile/BB32_scan.v"; bad=$((bad+1)); fi
if cmp -s BB32_round.v ../../../BB32/verify/multifile/BB32_round.v; then ok=$((ok+1)); else echo "DIFFERS: BB32_round.v vs BB32/verify/multifile/BB32_round.v"; bad=$((bad+1)); fi
if cmp -s BB32_game.v ../../../BB32/verify/multifile/BB32_game.v; then ok=$((ok+1)); else echo "DIFFERS: BB32_game.v vs BB32/verify/multifile/BB32_game.v"; bad=$((bad+1)); fi
if cmp -s BB32_halt.v ../../../BB32/verify/multifile/BB32_halt.v; then ok=$((ok+1)); else echo "DIFFERS: BB32_halt.v vs BB32/verify/multifile/BB32_halt.v"; bad=$((bad+1)); fi
if cmp -s BB32_bound.v ../../../BB32/verify/multifile/BB32_bound.v; then ok=$((ok+1)); else echo "DIFFERS: BB32_bound.v vs BB32/verify/multifile/BB32_bound.v"; bad=$((bad+1)); fi
echo "share_check: $ok identical, $bad different"
[ "$bad" -eq 0 ]
