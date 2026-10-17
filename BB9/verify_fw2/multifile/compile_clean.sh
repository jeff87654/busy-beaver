#!/usr/bin/bash
# Clean compile of the BB(9) fw2 proofs against a busycoq checkout (commit bd2e36f), in dependency order, then the
# probes.   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh [core]
# Stage 1 (always): the halting proof and the score bounds (4 files), then probe.v.
# Stage 2 (unless "core" is given): the comparison file BB9_fw2_vs_records.v and the 15 files it depends on (the
# earlier BB(9) machines and the BB(9)/BB(10) champions), then probe_vs.v.  Three of those files are large halting
# proofs that do not depend on each other; with PAR=1 they are compiled in parallel.
# COQC may be set to a specific coqc executable.  The logical path BB8 for this directory is historical.
COQC=${COQC:-coqc}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
set -e
compile() {
  for f in "$@"; do
    echo "== $f.v =="
    start=$(date +%s)
    "$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 "$f.v"
    echo "   ok, $(( $(date +%s) - start )) s"
  done
}
compile BB92 Individual92 BB9_fw2_1RB0RD BB9_fw2_bound
echo "STAGE 1 COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 probe.v > probe.log
echo "probe: $(grep -c 'Closed under the global context' probe.log) of 4 theorems closed under the global context"
[ "$1" = core ] && exit 0

big="BB9_record_1RB0RA BB9_redir_0LA BB9_redir_0LA_fh"
if [ "$PAR" = 1 ]; then
  tmp=$(mktemp -d)
  pids=""
  for f in $big; do compile $f > "$tmp/$f.log" 2>&1 & pids="$pids $!"; done
  fail=0
  for p in $pids; do wait $p || fail=1; done
  for f in $big; do cat "$tmp/$f.log"; done
  rm -rf "$tmp"
  [ $fail = 0 ]
else
  compile $big
fi
compile BB9_record_bound BB9_champion_1RB1RA BB9_champion_bound BB9_record_vs_champion \
        BB9_redir_0LA_bound BB9_redir_0LA_fh_bound \
        BB102 Individual102 BB10_champion_1RB1RA BB10_champion_bound BB10_champion_upper \
        BB9_fw2_vs_records
echo "STAGE 2 COMPILE DONE"
"$COQC" -Q "$BUSYCOQ" BusyCoq -Q . BB8 probe_vs.v > probe_vs.log
echo "probe_vs: $(grep -c 'Closed under the global context' probe_vs.log) of 5 theorems closed under the global context"
