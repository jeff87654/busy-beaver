#!/usr/bin/bash
# Check which files of this tree are reused unchanged from the neighbouring BB(9) proofs:
#  - dev/Abs, dev/G_rules, dev/Lift are ../verify_c04's, up to the mechanical port to the 11-state instance
#    (Individual92 -> Individual112, logical paths Dev -> XDev) -- the same renames as ../verify_f3/port_check.sh;
#  - lib9/ is byte-identical to ../verify_c04/lib/; lib/ and score/Score.v are byte-identical to ../verify_f3's;
#  - dev/Base.v is ../verify_f3/dev/Base.v with only the comments and the table row of state K changed
#    (f3's X has K = 0RC/1RH, X' has K = 1LC/0RA: C7's state I).
cd "$(dirname "$0")" || exit 2
C04=${C04:-../verify_c04}
F3=${F3:-../verify_f3}
fail=0; n=0
for f in dev/Abs dev/G_rules dev/Lift; do
  if sed -e 's/From BB8 Require Import Individual92\./From XL Require Import Individual112./' -e 's/<{{H}}/<{{J}}/g' \
         -e 's/From \(Dev\|K31\|Score\|Fgh\) Require/From X\1 Require/g' "$C04/$f.v" | cmp -s - "$f.v"; then
    n=$((n + 1))
  else
    echo "$f.v is not the port of $C04/$f.v"; fail=1
  fi
done
echo "$n files are the mechanical port of $C04's"
for f in BB92 Individual92; do cmp "lib9/$f.v" "$C04/lib/$f.v" || fail=1; done
for f in lib/BB112 lib/Individual112 score/Score; do cmp "$f.v" "$F3/$f.v" || fail=1; done
body() { sed -n '/^From /,$p' "$1" | grep -v -e '^  | K, 0 => ' -e '^(\* machine X'; }
if body dev/Base.v | cmp -s - <(body "$F3/dev/Base.v"); then
  echo "dev/Base.v = $F3/dev/Base.v up to the header comment and the row of K:"
  grep '^  | K, 0 => ' dev/Base.v "$F3/dev/Base.v"
else
  echo "dev/Base.v differs from $F3/dev/Base.v beyond the header and the row of K"; fail=1
fi
[ $fail = 0 ] && echo "lib9/ identical to $C04/lib/; lib/, score/Score.v identical to $F3's"
exit $fail
