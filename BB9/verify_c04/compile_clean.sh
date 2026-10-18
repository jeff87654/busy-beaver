#!/usr/bin/bash
# Clean compile of the C04 proof against a busycoq checkout (commit bd2e36f), in dependency order, then the probe.
#   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh            everything (49 files), then probe.v
#   BUSYCOQ=... ./compile_clean.sh only dev/G_sub2 k31/K_e1 ...   only these files (whatever they need must already be
#                                                                 compiled; the CI splits the build this way)
#   BUSYCOQ=... ./compile_clean.sh probe                          probe.v only
# J (default 4) is the number of coqc run at once: a file starts as soon as the files it needs are compiled, the
# longest files first.  The whole build is about 9 CPU-hours, most of it in files that only need dev/Base.v (the
# longest, k31/K_e1.v, takes about 2.5 h on its own), so with J=4 it takes about 3 h.
# Per-file coqc output goes to $LOGDIR (default _logs/).  COQC may be set to a specific coqc executable.
# Logical paths: lib/ = BB8 (historical; the same name the fw2 files use), dev/ = Dev, k31/ = K31, score/ = Score.
COQC=${COQC:-coqc}
J=${J:-4}
LOGDIR=${LOGDIR:-_logs}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
cd "$(dirname "$0")" || exit 2
FLAGS=(-Q "$BUSYCOQ" BusyCoq -Q lib BB8 -Q dev Dev -Q k31 K31 -Q score Score)

# file  files it needs (from its Require lines), longest-running first within what can run in parallel
declare -A DEPS STATE PIDFILE
ORDER=()
while read -r f d; do ORDER+=("$f"); DEPS[$f]="$d"; done <<'EOF'
lib/BB92
lib/Individual92 lib/BB92
dev/Base lib/Individual92
dev/Orbit
k31/K_e1 lib/Individual92 dev/Base
dev/G_rules lib/Individual92 dev/Base
k31/K_e2 lib/Individual92 dev/Base
dev/G_sub2 lib/Individual92 dev/Base
dev/G_sub4 lib/Individual92 dev/Base
dev/G_entry lib/Individual92 dev/Base
dev/G_sub3 lib/Individual92 dev/Base
dev/G_sub5 lib/Individual92 dev/Base
dev/G_p20_5 lib/Individual92 dev/Base
dev/G_p20_4 lib/Individual92 dev/Base
dev/G_p20_3 lib/Individual92 dev/Base
dev/G_p20_2 lib/Individual92 dev/Base
dev/G_p20_1 lib/Individual92 dev/Base
dev/G_p20_0 lib/Individual92 dev/Base
dev/G_reb1 lib/Individual92 dev/Base
dev/G_stop lib/Individual92 dev/Base
dev/G_p14_5 lib/Individual92 dev/Base
dev/G_p14_4 lib/Individual92 dev/Base
dev/G_p14_3 lib/Individual92 dev/Base
dev/G_p14_2 lib/Individual92 dev/Base
dev/G_p14_1 lib/Individual92 dev/Base
dev/G_p14_0 lib/Individual92 dev/Base
dev/G_top lib/Individual92 dev/Base
k31/K_x lib/Individual92 dev/Base
k31/K_rf lib/Individual92 dev/Base
dev/G_end lib/Individual92 dev/Base
lib/BB9_fw2_1RB0RD lib/Individual92
lib/BB9_fw2_bound lib/Individual92 lib/BB9_fw2_1RB0RD
dev/Abs lib/Individual92 dev/Base dev/G_rules
dev/Lift lib/Individual92 dev/Base dev/G_rules dev/Abs
dev/Chain lib/Individual92 dev/Base dev/G_rules dev/G_reb1 dev/Abs
dev/Cascade dev/Orbit
dev/Step lib/Individual92 dev/Base dev/G_rules dev/G_sub2 dev/G_sub3 dev/G_sub4 dev/G_sub5 dev/G_stop dev/G_entry dev/G_top dev/Abs dev/Lift dev/Orbit dev/Chain
k31/K31_Abs lib/Individual92 dev/Base dev/G_rules dev/Abs dev/Lift dev/Step k31/K_rf
k31/K31_Mach lib/Individual92 dev/Base dev/G_rules dev/Abs dev/Lift dev/Step k31/K_e1 k31/K_e2 k31/K_x
k31/K31_End lib/Individual92 dev/Base dev/G_rules dev/Abs dev/Lift dev/Step k31/K31_Abs k31/K31_Mach
dev/CBtail lib/Individual92 dev/Base dev/G_rules dev/G_end dev/Abs dev/Lift dev/Orbit dev/Step
dev/Endgame lib/Individual92 dev/Base dev/G_rules dev/G_sub2 dev/G_sub3 dev/G_sub4 dev/G_sub5 dev/G_stop dev/G_entry dev/G_top dev/G_end dev/Abs dev/Lift dev/Orbit dev/Chain dev/Cascade dev/Step dev/CBtail dev/G_p14_0 dev/G_p14_1 dev/G_p14_2 dev/G_p14_3 dev/G_p14_4 dev/G_p14_5 dev/G_p20_0 dev/G_p20_1 dev/G_p20_2 dev/G_p20_3 dev/G_p20_4 dev/G_p20_5
dev/Fin lib/Individual92 dev/Base dev/G_rules dev/G_sub2 dev/G_sub3 dev/G_sub4 dev/G_sub5 dev/G_stop dev/G_entry dev/G_top dev/Abs dev/Lift dev/Orbit dev/Chain dev/Step
score/Score lib/Individual92 dev/Abs dev/Chain
score/Fw2Link lib/Individual92 lib/BB9_fw2_bound score/Score dev/Abs dev/Chain
score/Fw2Upper lib/Individual92 lib/BB9_fw2_1RB0RD lib/BB9_fw2_bound dev/Abs dev/Chain score/Score
score/ScoreK lib/Individual92 lib/BB9_fw2_1RB0RD lib/BB9_fw2_bound dev/Abs dev/Chain dev/Step score/Score score/Fw2Link score/Fw2Upper
dev/Final lib/Individual92 dev/Base dev/Lift dev/Endgame k31/K31_End
dev/ScoreEnd lib/Individual92 lib/BB9_fw2_1RB0RD lib/BB9_fw2_bound dev/Base dev/G_rules dev/G_sub2 dev/G_sub3 dev/G_sub4 dev/G_sub5 dev/G_stop dev/G_entry dev/G_top dev/G_end dev/Abs dev/Lift dev/Orbit dev/Chain dev/Cascade dev/Step dev/CBtail dev/G_p14_0 dev/G_p14_1 dev/G_p14_2 dev/G_p14_3 dev/G_p14_4 dev/G_p14_5 dev/G_p20_0 dev/G_p20_1 dev/G_p20_2 dev/G_p20_3 dev/G_p20_4 dev/G_p20_5 dev/Endgame dev/Fin k31/K31_Abs k31/K31_Mach k31/K31_End score/Score score/ScoreK
EOF

probe() {
  echo "== probe.v =="
  start=$(date +%s)
  "$COQC" "${FLAGS[@]}" probe.v > probe.log || { cat probe.log; echo "probe.v FAILED"; exit 1; }
  closed=$(grep -c 'Closed under the global context' probe.log)
  echo "   ok, $(( $(date +%s) - start )) s"
  echo "probe: $closed of 3 theorems closed under the global context"
  if grep -q 'Axioms:' probe.log || [ "$closed" -ne 3 ]; then exit 1; fi
}
[ "$1" = probe ] && { probe; exit 0; }
case "$1" in ''|only) ;; *) echo "usage: compile_clean.sh [only FILE... | probe]" >&2; exit 2 ;; esac

if [ "$1" = only ]; then
  shift
  for f in "${ORDER[@]}"; do STATE[$f]=done; done     # files not listed are taken as already compiled
  for f in "$@"; do
    [ -n "${DEPS[$f]+x}" ] || { echo "unknown file $f" >&2; exit 2; }
    STATE[$f]=
  done
  for f in "$@"; do
    for d in ${DEPS[$f]}; do
      [ "${STATE[$d]}" = done ] && [ ! -f "$d.vo" ] && { echo "$f needs $d.vo, which is missing" >&2; exit 2; }
    done
  done
fi

mkdir -p "$LOGDIR"
compile_one() {
  local f=$1 start=$(date +%s) log="$LOGDIR/${1//\//_}.log"
  echo "== $f.v started"
  if "$COQC" "${FLAGS[@]}" "$f.v" > "$log" 2>&1; then
    echo "   $f.v ok, $(( $(date +%s) - start )) s"
  else
    echo "   $f.v FAILED after $(( $(date +%s) - start )) s:"; tail -40 "$log"; return 1
  fi
}

t0=$(date +%s)
running=0; fail=0
declare -A JOB
while :; do
  if [ $fail = 0 ]; then
    for f in "${ORDER[@]}"; do
      [ $running -ge "$J" ] && break
      [ -z "${STATE[$f]}" ] || continue
      ready=1
      for d in ${DEPS[$f]}; do [ "${STATE[$d]}" = done ] || { ready=0; break; }; done
      [ $ready = 1 ] || continue
      STATE[$f]=running
      compile_one "$f" &
      JOB[$!]=$f; running=$((running + 1))
    done
  fi
  [ $running = 0 ] && break
  wait -n -p pid; rc=$?
  f=${JOB[$pid]}; unset "JOB[$pid]"; running=$((running - 1))
  if [ $rc = 0 ]; then STATE[$f]=done; else STATE[$f]=failed; fail=1; fi
done
for f in "${ORDER[@]}"; do
  [ "${STATE[$f]}" = done ] || { echo "NOT COMPILED: $f (${STATE[$f]:-blocked})"; fail=1; }
done
[ $fail = 0 ] || exit 1
echo "COMPILE DONE, $(( $(date +%s) - t0 )) s"
[ $# -eq 0 ] && probe
exit 0
