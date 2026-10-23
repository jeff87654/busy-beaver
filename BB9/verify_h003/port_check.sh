#!/usr/bin/bash
# Check which files of this tree are reused from the neighbouring BB(9) proofs, and how:
#  - 33 files are byte-identical to ../verify_f3's (C04's tree as ported there to the 11-state instance: the champion
#    rules, the cascade and its endgame, the key-31 machine files; also lib/ and score/Score.v);
#  - 5 files are ../verify_f3's with only X3's halting tape changed: X' and X halt after E0 = 1LJ, X3 after E0 = 0LJ,
#    so the first cell right of the halting head is 0 instead of 1 (and K31_End's ones bound drops by 1);
#  - dev/G_pbab, dev/G_pbc, dev/KStep, dev/Ones, dev/Res are byte-identical to ../verify_c7's;
#  - lib9/ is byte-identical to ../verify_c04/lib/;
#  - dev/Base.v is ../verify_c7/dev/Base.v with the rows of E0 and K changed and [step] = one raw step
#    (X3 replays C04's scripts with raw steps, see the header of dev/Base.v);
#  - h003/Defs.v is ../verify_c7/c7/Defs.v from "(** Counting ones. *)" on (only the machine differs).
cd "$(dirname "$0")" || exit 2
C04=${C04:-../verify_c04}
F3=${F3:-../verify_f3}
C7=${C7:-../verify_c7}
fail=0; n=0
SAME_F3="dev/Abs dev/Cascade dev/Endgame dev/Fin dev/G_entry dev/G_p14_0 dev/G_p14_1 dev/G_p14_2 dev/G_p14_3 dev/G_p14_4
dev/G_p14_5 dev/G_p20_0 dev/G_p20_1 dev/G_p20_2 dev/G_p20_3 dev/G_p20_4 dev/G_p20_5 dev/G_rules dev/G_stop dev/G_sub2
dev/G_sub3 dev/G_sub4 dev/G_sub5 dev/Lift dev/Orbit dev/Step k31/K_e1 k31/K_e2 k31/K_rf k31/K31_Abs lib/BB112
lib/Individual112 score/Score"
for f in $SAME_F3; do
  if cmp -s "$f.v" "$F3/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $F3/$f.v"; fail=1; fi
done
echo "$n files byte-identical to $F3's"

# X3's halting tape: <{{J}} (0 >> 1 >> 1 >> 1 >> 0 >> ...  where X (../verify_f3) has <{{J}} (1 >> 1 >> 1 >> 1 >> 0 >> ...
halt_port() {
  case "$1" in
    dev/G_end|k31/K_x) sed -e 's/<{{J}} (1 >> 1 >> 1 >> 1 >> 0 >> /<{{J}} (0 >> 1 >> 1 >> 1 >> 0 >> /g' ;;
    dev/CBtail) sed -e 's/^   (1 >> 1 >> 1 >> 1 >> 0 >> \[1;0;1;0\]^^r /   (0 >> 1 >> 1 >> 1 >> 0 >> [1;0;1;0]^^r /' ;;
    k31/K31_Mach) sed -e 's/^  1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> /  0 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> /' ;;
    k31/K31_End) sed -e 's/6 \* R + d + 12 <= N\./6 * R + d + 11 <= N./' \
                     -e 's/set (Rw := \[1;1;1;1;0;1;0;1;0\]/set (Rw := [0;1;1;1;0;1;0;1;0]/' ;;
  esac
}
n=0
for f in dev/G_end k31/K_x dev/CBtail k31/K31_Mach k31/K31_End; do
  if halt_port "$f" < "$F3/$f.v" | cmp -s - "$f.v"; then
    n=$((n + 1)); echo "$f.v = $F3/$f.v with X3's halting tape ($(diff "$F3/$f.v" "$f.v" | grep -c '^>') lines)"
  else
    echo "$f.v is not $F3/$f.v with X3's halting tape"; fail=1
  fi
done

n=0
for f in dev/G_pbab dev/G_pbc dev/KStep dev/Ones dev/Res; do
  if cmp -s "$f.v" "$C7/$f.v"; then n=$((n + 1)); else echo "$f.v differs from $C7/$f.v"; fail=1; fi
done
echo "$n files byte-identical to $C7's"

for f in BB92 Individual92; do cmp "lib9/$f.v" "$C04/lib/$f.v" || fail=1; done

body() { sed -n '/^From /,$p' "$1"; }
if body "$C7/dev/Base.v" | sed -e "s/^(\* machine X': .*/(* machine X3: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_0RG1LD_0LH1LH_1RI---_0RI0RF_0LK---_1RK1RC *)/" \
     -e 's/| E, 0 => Some (1, L, J)/| E, 0 => Some (0, L, J)/' \
     -e 's/| K, 0 => Some (1, L, C)  | K, 1 => Some (0, R, A)/| K, 0 => Some (1, R, K)  | K, 1 => Some (1, R, C)/' \
     -e 's/^(\*\* \*\* One C04 step \*)$/(** ** One raw step *)/' |
   sed -z 's/Ltac cur_cfg.*  | _ => step1\n  end\.\n/Ltac step := step1.\n/' | cmp -s - <(body dev/Base.v); then
  echo "dev/Base.v = $C7/dev/Base.v up to the header comment, the rows of E0 and K, and [step] = one raw step:"
  grep -e '^  | E, 0 => ' -e '^  | K, 0 => ' -e '^Ltac step :=' dev/Base.v
else
  echo "dev/Base.v differs from $C7/dev/Base.v beyond the header, the rows of E0 and K, and [step]"; fail=1
fi

tailc() { sed -n '/^(\*\* Counting ones\. \*)/,$p' "$1"; }
if cmp -s <(tailc h003/Defs.v) <(tailc "$C7/c7/Defs.v") && [ -n "$(tailc h003/Defs.v)" ]; then
  echo "h003/Defs.v = $C7/c7/Defs.v from (** Counting ones. *) on"
else
  echo "h003/Defs.v differs from $C7/c7/Defs.v after (** Counting ones. *)"; fail=1
fi
[ $fail = 0 ] && echo "lib9/ identical to $C04/lib/; port check passed"
exit $fail
