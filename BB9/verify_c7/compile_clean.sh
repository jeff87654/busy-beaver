#!/usr/bin/bash
# Clean compile of the C7 proof (the auxiliary machine X', then the C7 layer) against a busycoq checkout (commit
# bd2e36f), in dependency order, then the probe.
#   BUSYCOQ=/path/to/busycoq/verify ./compile_clean.sh            everything (46 files), then probe.v
#   BUSYCOQ=... ./compile_clean.sh only dev/G_ent dev/C7Top ...   only these files (whatever they need must already be
#                                                                 compiled)
#   BUSYCOQ=... ./compile_clean.sh probe                          probe.v only
# J (default 4) is the number of coqc run at once: a file starts as soon as the files it needs are compiled, the
# longest files first.  Nearly all of the time is in the 18 generated machine files that need only dev/Base.v
# (dev/G_ent.v alone is the longest by far).
# Per-file coqc output goes to $LOGDIR (default _logs/).  COQC may be set to a specific coqc executable.
# Logical paths: lib/ = XL (busycoq for 11 states), lib9/ = BB8 (busycoq for 9 states: BB92.v and Individual92.v,
# byte-identical to ../verify_c04/lib/, which uses the same name), dev/ = XDev, score/ = XScore, c7/ = C7.
COQC=${COQC:-coqc}
J=${J:-4}
LOGDIR=${LOGDIR:-_logs}
if [ -z "$BUSYCOQ" ]; then
  echo "set BUSYCOQ to the verify/ directory of a busycoq checkout" >&2
  exit 2
fi
cd "$(dirname "$0")" || exit 2
FLAGS=(-Q "$BUSYCOQ" BusyCoq -Q lib XL -Q lib9 BB8 -Q dev XDev -Q score XScore -Q c7 C7)

# file  files it needs (from its Require lines), longest-running first within what can run in parallel
declare -A DEPS STATE
ORDER=()
while read -r f d; do ORDER+=("$f"); DEPS[$f]="$d"; done <<'DEPLIST'
lib/BB112 
lib/Individual112 lib/BB112
dev/Base lib/Individual112
dev/G_ent lib/Individual112 dev/Base
dev/G_pa2 lib/Individual112 dev/Base
dev/G_pd lib/Individual112 dev/Base
dev/G_sub4 lib/Individual112 dev/Base
dev/G_sub3 lib/Individual112 dev/Base
dev/G_sub0 lib/Individual112 dev/Base
dev/G_pbab lib/Individual112 dev/Base
dev/G_pa1 lib/Individual112 dev/Base
dev/G_pbc lib/Individual112 dev/Base
dev/G_e2 lib/Individual112 dev/Base
dev/G_r30 lib/Individual112 dev/Base
dev/G_e3 lib/Individual112 dev/Base
dev/G_rules lib/Individual112 dev/Base
dev/G_r2pre lib/Individual112 dev/Base
dev/G_r2round lib/Individual112 dev/Base
dev/G_r2vhq lib/Individual112 dev/Base
dev/G_r2a1 lib/Individual112 dev/Base
dev/G_r2vh2b lib/Individual112 dev/Base
dev/Abs lib/Individual112 dev/Base dev/G_rules
dev/Res lib/Individual112 dev/Base dev/G_rules dev/Abs
dev/C7Arith lib/Individual112 dev/Base dev/G_rules dev/Abs dev/Res
dev/KStep lib/Individual112 dev/Base dev/G_rules dev/Abs
dev/Lift lib/Individual112 dev/Base dev/G_rules dev/Abs
score/Score lib/Individual112 dev/Abs
dev/Ones lib/Individual112
lib9/BB92 
lib9/Individual92 lib9/BB92
c7/Defs lib9/Individual92
c7/Sim lib9/Individual92 lib/Individual112 dev/Base dev/Ones c7/Defs
dev/C7Phases lib/Individual112 dev/Base dev/G_rules dev/Abs dev/KStep dev/G_pa1 dev/G_pa2 dev/G_pd dev/G_r30 dev/G_e2 dev/G_e3
dev/C7PhB lib/Individual112 dev/Base dev/G_rules dev/Abs dev/KStep dev/C7Phases dev/G_pbab dev/G_pbc
dev/C7Count lib/Individual112 dev/Base dev/G_rules dev/Abs dev/KStep dev/C7Phases
dev/C7Casc lib/Individual112 dev/Base dev/G_rules dev/Abs dev/Lift dev/KStep dev/G_sub3 dev/G_sub0 dev/G_sub4
dev/C7Entry lib/Individual112 dev/Base dev/G_rules dev/Abs dev/Lift dev/KStep dev/G_ent
dev/C7Top lib/Individual112 dev/Base dev/G_rules dev/Abs dev/Lift dev/KStep dev/Res dev/C7Arith dev/C7Phases dev/C7PhB dev/C7Count dev/C7Casc dev/C7Entry
dev/C7Halt lib/Individual112 dev/Base dev/G_rules dev/Abs dev/Lift dev/KStep dev/G_r2a1 dev/G_r2pre dev/G_r2round dev/G_r2vhq dev/G_r2vh2b dev/Ones
dev/C7Score lib/Individual112 score/Score dev/Base dev/G_rules dev/Abs dev/KStep dev/C7Count dev/C7Top
dev/C7Final lib/Individual112 score/Score dev/Base dev/G_rules dev/Abs dev/Lift dev/KStep dev/Res dev/C7Arith dev/C7Count dev/C7Top dev/C7Halt dev/C7Score dev/Ones
c7/Final7 lib9/Individual92 lib/Individual112 dev/Abs dev/Ones dev/C7Final score/Score c7/Defs c7/Sim
c7/Statement lib9/Individual92 c7/Defs c7/Final7
dev/C7Score5 lib/Individual112 score/Score dev/Base dev/G_rules dev/Abs dev/KStep dev/C7Count dev/C7Top dev/C7Score
dev/C7Final5 lib/Individual112 score/Score dev/Base dev/G_rules dev/Abs dev/Lift dev/KStep dev/Res dev/C7Arith dev/C7Count dev/C7Top dev/C7Halt dev/C7Score dev/C7Score5 dev/Ones
c7/Lower5 lib9/Individual92 lib/Individual112 dev/Abs dev/Ones dev/C7Final5 score/Score c7/Defs c7/Sim c7/Final7
DEPLIST

probe() {
  echo "== probe.v =="
  start=$(date +%s)
  "$COQC" "${FLAGS[@]}" probe.v > probe.log || { cat probe.log; echo "probe.v FAILED"; exit 1; }
  closed=$(grep -c 'Closed under the global context' probe.log)
  echo "   ok, $(( $(date +%s) - start )) s"
  echo "probe: $closed of 8 results closed under the global context"
  if grep -q 'Axioms:' probe.log || [ "$closed" -ne 8 ]; then exit 1; fi
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
