(** Abstract D0 moment [D0f] (canonical, flat runs) and the lifting of the generic residue sub-step lemmas to one
    orbit step.  D0f t L P s y l = 1001 (11111100)^t 11 1^L (001)^P 110 (01)^y 101 (01)^s 1 l  (head in B, blank right).
    Each generated SUBc_E has this shape after splitting the flat runs 1^L, (001)^P into the generator's block encodings. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs.

Definition D0f (t L P s y : nat) (l : side) : Q * tape :=
  (1 >> 0 >> 0 >> 1 >> [0;0;1;1;1;1;1;1]^^t *> 1 >> 1 >> [1]^^L *> [0;0;1]^^P *>
   1 >> 1 >> 0 >> [0;1]^^y *> 1 >> 0 >> 1 >> [0;1]^^s *> 1 >> l) {{B}}> const 0.

(** The generator's LHS for residue 4, class E=0: 1^L with L = 5J+24, parked (001)^P with P = 6p+12.
    Check that D0f with those flat counts is convertible to SUB4_0's LHS (pow splits only). *)
Lemma D0f_sub4_0_lhs : forall J p s t y l,
  D0f t (5 * J + 24) (6 * p + 12) s y l =
  (1 >> 0 >> 0 >> 1 >> [0;0;1;1;1;1;1;1]^^t *> 1 >> 1 >> [1;1;1;1;1]^^J *> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;0;1;0;0;1;0;0;1;0;0;1;0;0;1;0;0;1]^^p *> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> 1 >> 1 >> 0 >> [0;1]^^y *> 1 >> 0 >> 1 >> [0;1]^^s *> 1 >> l) {{B}}> (const 0).
Proof.
  intros. unfold D0f.
  rewrite (pow_add [1] (5 * J) 24), (pow_mul [1] 5 J).
  replace (6 * p + 12) with (6 + (6 * p + 6)) by lia.
  rewrite (pow_add [0;0;1] 6 (6 * p + 6)), (pow_add [0;0;1] (6 * p) 6), (pow_mul [0;0;1] 6 p).
  cbn [lpow Str_app]. reflexivity.
Qed.
