(** * C7Casc.v : C7's cascade sub-steps on the D0 moment D0f (Lift.v), restated from the generated lemmas
    (generated lemmas; the formulas were fitted on literal runs).  r = L mod 5; t -> t+2 always.
      r = 3: L = 5J+63 -> 3J+35, P -> P-4, s' = 2, y' = J+13, l' = (01)^y 1 (01)^s 1 l
      r = 0: L = 5J+60 -> 3J+32, P -> P-6, s' = 4, y' = J+14, same l'
      r = 4: L = 5J+64 -> 3J+32, P -> P-6, s' = 6, y' = J+14, same l'. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs Lift KStep.
From XDev Require G_sub3 G_sub0 G_sub4.
Opaque U arrow.
Local Open Scope nat_scope.

Definition lnext (s y : nat) (l : side) : side := [S0;S1]^^y *> S1 >> [S0;S1]^^s *> S1 >> l.


Lemma sub3 : forall J P s t y l, 4 <= P ->
  D0f t (5 * J + 63) P s y l -->+ D0f (2 + t) (3 * J + 35) (P - 4) 2 (J + 13) (lnext s y l).
Proof.
  intros J P s t y l HP. refine (prog_eq _ _ _ _ _ _ (G_sub3.SUB3 J (P - 4) s t y l)).
  - unfold D0f. rewrite (pow_add [S1] (5 * J) 63), (pow_mul [S1] 5 J).
    replace P with (4 + (P - 4)) at 1 by lia. rewrite (pow_add [S0;S0;S1] 4 (P - 4)). reflexivity.
  - unfold D0f, lnext. rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 2 t), (pow_add [S1] (3 * J) 35), (pow_mul [S1] 3 J),
      (pow_add [S0;S1] J 13). reflexivity.
Qed.

Lemma sub0 : forall J P s t y l, 6 <= P ->
  D0f t (5 * J + 60) P s y l -->+ D0f (2 + t) (3 * J + 32) (P - 6) 4 (J + 14) (lnext s y l).
Proof.
  intros J P s t y l HP. refine (prog_eq _ _ _ _ _ _ (G_sub0.SUB0 J (P - 6) s t y l)).
  - unfold D0f. rewrite (pow_add [S1] (5 * J) 60), (pow_mul [S1] 5 J).
    replace P with (6 + (P - 6)) at 1 by lia. rewrite (pow_add [S0;S0;S1] 6 (P - 6)). reflexivity.
  - unfold D0f, lnext. rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 2 t), (pow_add [S1] (3 * J) 32), (pow_mul [S1] 3 J),
      (pow_add [S0;S1] J 14). reflexivity.
Qed.

Lemma sub4 : forall J P s t y l, 6 <= P ->
  D0f t (5 * J + 64) P s y l -->+ D0f (2 + t) (3 * J + 32) (P - 6) 6 (J + 14) (lnext s y l).
Proof.
  intros J P s t y l HP. refine (prog_eq _ _ _ _ _ _ (G_sub4.SUB4 J (P - 6) s t y l)).
  - unfold D0f. rewrite (pow_add [S1] (5 * J) 64), (pow_mul [S1] 5 J).
    replace P with (6 + (P - 6)) at 1 by lia. rewrite (pow_add [S0;S0;S1] 6 (P - 6)). reflexivity.
  - unfold D0f, lnext. rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 2 t), (pow_add [S1] (3 * J) 32), (pow_mul [S1] 3 J),
      (pow_add [S0;S1] J 14). reflexivity.
Qed.
