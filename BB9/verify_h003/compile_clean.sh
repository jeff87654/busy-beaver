#!/usr/bin/bash
# Clean compile of the h003 proof (the auxiliary machine X3, then the h003 layer) against a busycoq checkout (commit
# bd2e36f), in dependency order, then the probe.
#   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh            everything (66 files), then probe.v
#   BUSYCOQ=... ./compile_clean.sh only dev/HTop dev/HFinal ...   only these files (whatever they need must already be
#                                                                 compiled)
#   BUSYCOQ=... ./compile_clean.sh probe                          probe.v only
# J (default 4) is the number of coqc run at once: a file starts as soon as the files it needs are compiled, the
# longest files first.  Nearly all of the time is in the generated machine files that need only dev/Base.v
# (k31/K_e1.v and dev/G_sub2.v are the longest by far).
# Per-file coqc output goes to $LOGDIR (default _logs/).  COQC may be set to a specific coqc executable.
# Logical paths: lib/ = XL (busycoq for 11 states), lib9/ = BB8 (busycoq for 9 states: BB92.v and Individual92.v,
# byte-identical to ../verify_c04/lib/, which uses the same name), dev/ = XDev, k31/ = XK31, score/ = XScore,
# h003/ = H3.
COQC=${COQC:-coqc}
J=${J:-4}
LOGDIR=${LOGDIR:-_logs}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
cd "$(dirname "$0")" || exit 2
FLAGS=(-Q "$BUSYCOQ" BusyCoq -Q lib XL -Q lib9 BB8 -Q dev XDev -Q k31 XK31 -Q score XScore -Q h003 H3)

# file  files it needs (from its Require lines), longest-running first within what can run in parallel
declare -A DEPS STATE
ORDER=()
while read -r f d; do ORDER+=("$f"); DEPS[$f]="$d"; done <<'DEPLIST'
dev/Orbit 
lib/BB112 
lib9/BB92 
dev/Cascade dev/Orbit
lib/Individual112 lib/BB112
lib9/Individual92 lib9/BB92
dev/Ones lib/Individual112
h003/Defs lib9/Individual92
dev/Base lib/Individual112
k31/K_e1 lib/Individual112 dev/Base
dev/G_sub2 lib/Individual112 dev/Base
k31/K_e2 lib/Individual112 dev/Base
dev/G_entry lib/Individual112 dev/Base
dev/G_sub4 lib/Individual112 dev/Base
dev/G_sub5 lib/Individual112 dev/Base
dev/G_sub3 lib/Individual112 dev/Base
dev/G_stop lib/Individual112 dev/Base
dev/G_p20_5 lib/Individual112 dev/Base
dev/G_p20_4 lib/Individual112 dev/Base
dev/G_tops_P4 lib/Individual112 dev/Base
dev/G_p20_3 lib/Individual112 dev/Base
dev/G_p20_2 lib/Individual112 dev/Base
dev/G_tops_P3 lib/Individual112 dev/Base
dev/G_p20_1 lib/Individual112 dev/Base
dev/G_p20_0 lib/Individual112 dev/Base
dev/G_p14_5 lib/Individual112 dev/Base
dev/G_p14_4 lib/Individual112 dev/Base
dev/G_p14_3 lib/Individual112 dev/Base
dev/G_tops_TXa lib/Individual112 dev/Base
dev/G_p14_2 lib/Individual112 dev/Base
dev/G_p14_1 lib/Individual112 dev/Base
dev/G_p14_0 lib/Individual112 dev/Base
dev/G_pbab lib/Individual112 dev/Base
dev/G_t1_T1a1 lib/Individual112 dev/Base
dev/G_pbc lib/Individual112 dev/Base
dev/G_xt1 lib/Individual112 dev/Base
k31/K_x lib/Individual112 dev/Base
dev/G_rules lib/Individual112 dev/Base
dev/G_t1_T1a2a lib/Individual112 dev/Base
dev/G_tops_P4b lib/Individual112 dev/Base
dev/G_t1_T1b lib/Individual112 dev/Base
dev/G_end lib/Individual112 dev/Base
dev/G_t1_YE lib/Individual112 dev/Base
k31/K_rf lib/Individual112 dev/Base
h003/Sim lib9/Individual92 lib/Individual112 dev/Base dev/Ones h003/Defs
dev/G_t1_YR lib/Individual112 dev/Base
dev/Abs lib/Individual112 dev/Base dev/G_rules
dev/Res lib/Individual112 dev/Base dev/G_rules dev/Abs
score/Score lib/Individual112 dev/Abs
dev/Lift lib/Individual112 dev/Base dev/G_rules dev/Abs
dev/KStep lib/Individual112 dev/Base dev/G_rules dev/Abs
dev/HArith lib/Individual112 dev/Base dev/G_rules dev/Abs dev/Res
dev/HPhB lib/Individual112 dev/Base dev/G_rules dev/Abs dev/KStep dev/G_pbab dev/G_pbc
dev/Step lib/Individual112 dev/Base dev/G_rules dev/G_sub2 dev/G_sub3 dev/G_sub4 dev/G_sub5 dev/G_stop dev/G_entry dev/Abs dev/Lift dev/Orbit
k31/K31_Mach lib/Individual112 dev/Base dev/G_rules dev/Abs dev/Lift dev/Step k31/K_e1 k31/K_e2 k31/K_x
dev/CBtail lib/Individual112 dev/Base dev/G_rules dev/G_end dev/Abs dev/Lift dev/Orbit dev/Step
dev/HTop lib/Individual112 dev/Base dev/G_rules dev/Abs dev/KStep dev/Lift dev/HPhB dev/Res dev/HArith dev/G_t1_T1a1 dev/G_t1_T1a2a dev/G_t1_YR dev/G_t1_YE dev/G_t1_T1b dev/G_tops_P3 dev/G_tops_P4 dev/G_tops_P4b dev/G_tops_TXa dev/G_xt1
dev/Fin lib/Individual112 dev/Base dev/G_rules dev/G_sub2 dev/G_sub3 dev/G_sub4 dev/G_sub5 dev/G_stop dev/G_entry dev/Abs dev/Lift dev/Orbit dev/Step
k31/K31_Abs lib/Individual112 dev/Base dev/G_rules dev/Abs dev/Lift dev/Step k31/K_rf
k31/K31_End lib/Individual112 dev/Base dev/G_rules dev/Abs dev/Lift dev/Step k31/K31_Abs k31/K31_Mach
dev/Endgame lib/Individual112 dev/Base dev/G_rules dev/G_sub2 dev/G_sub3 dev/G_sub4 dev/G_sub5 dev/G_stop dev/G_entry dev/G_end dev/Abs dev/Lift dev/Orbit dev/Cascade dev/Step dev/CBtail dev/G_p14_0 dev/G_p14_1 dev/G_p14_2 dev/G_p14_3 dev/G_p14_4 dev/G_p14_5 dev/G_p20_0 dev/G_p20_1 dev/G_p20_2 dev/G_p20_3 dev/G_p20_4 dev/G_p20_5
dev/HFinal lib/Individual112 dev/Base dev/Abs dev/Lift dev/Step dev/Fin dev/Endgame dev/HTop k31/K31_End
dev/HScore lib/Individual112 dev/Base dev/G_rules dev/G_sub2 dev/G_sub3 dev/G_sub4 dev/G_sub5 dev/G_stop dev/G_entry dev/G_end dev/Abs dev/Lift dev/Orbit dev/Cascade dev/Step dev/CBtail dev/G_p14_0 dev/G_p14_1 dev/G_p14_2 dev/G_p14_3 dev/G_p14_4 dev/G_p14_5 dev/G_p20_0 dev/G_p20_1 dev/G_p20_2 dev/G_p20_3 dev/G_p20_4 dev/G_p20_5 dev/Endgame dev/Fin dev/HFinal dev/HTop k31/K31_Abs k31/K31_Mach k31/K31_End score/Score
dev/HGoal lib/Individual112 score/Score dev/Base dev/Abs dev/HTop dev/HScore dev/Ones k31/K31_Abs
h003/Final lib9/Individual92 lib/Individual112 dev/Abs dev/Ones dev/HFinal dev/HGoal score/Score h003/Defs h003/Sim
h003/Statement lib9/Individual92 h003/Defs h003/Final
DEPLIST

probe() {
  echo "== probe.v =="
  start=$(date +%s)
  "$COQC" "${FLAGS[@]}" probe.v > probe.log || { cat probe.log; echo "probe.v FAILED"; exit 1; }
  closed=$(grep -c 'Closed under the global context' probe.log)
  echo "   ok, $(( $(date +%s) - start )) s"
  echo "probe: $closed of 6 results closed under the global context"
  if grep -q 'Axioms:' probe.log || [ "$closed" -ne 6 ]; then exit 1; fi
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

echo "start $(date '+%F %T')"
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
