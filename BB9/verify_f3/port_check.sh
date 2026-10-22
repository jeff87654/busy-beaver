#!/usr/bin/bash
# Check that the machine files and abstract files listed below are exactly ../verify_c04's, up to the mechanical port
# to the auxiliary machine X: the busycoq instance (Individual92 -> Individual112, logical path XL), the state in which
# the halting configuration is reached after E0 (C04's H -> X's J, in the notation <{{H}} -> <{{J}}), and the logical
# paths Dev/K31/Score/Fgh -> XDev/XK31/XScore/XFgh.  Also that lib9/ is byte-identical to ../verify_c04/lib/.
cd "$(dirname "$0")" || exit 2
C04=${C04:-../verify_c04}
PORTED="dev/Abs dev/Cascade dev/CBtail dev/G_end dev/G_entry dev/G_p14_0 dev/G_p14_1 dev/G_p14_2 dev/G_p14_3 dev/G_p14_4
dev/G_p14_5 dev/G_p20_0 dev/G_p20_1 dev/G_p20_2 dev/G_p20_3 dev/G_p20_4 dev/G_p20_5 dev/G_rules dev/G_stop dev/G_sub2
dev/G_sub3 dev/G_sub4 dev/G_sub5 dev/Lift dev/Orbit k31/K31_Abs k31/K31_Mach k31/K_e1 k31/K_e2 k31/K_rf k31/K_x"
fail=0; n=0
for f in $PORTED; do
  if sed -e 's/From BB8 Require Import Individual92\./From XL Require Import Individual112./' -e 's/<{{H}}/<{{J}}/g' \
         -e 's/From \(Dev\|K31\|Score\|Fgh\) Require/From X\1 Require/g' "$C04/$f.v" | cmp -s - "$f.v"; then
    n=$((n + 1))
  else
    echo "$f.v is not the port of $C04/$f.v"; fail=1
  fi
done
echo "$n files are the mechanical port of $C04's"
for f in BB92 Individual92; do cmp "lib9/$f.v" "$C04/lib/$f.v" || fail=1; done
[ $fail = 0 ] && echo "lib9/BB92.v, lib9/Individual92.v identical to $C04/lib/"
exit $fail
