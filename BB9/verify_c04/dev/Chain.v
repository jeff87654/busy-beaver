(** The concrete top of the run: c0 -->* exhaustion-#2 start.
    Composes Abs.run_to_exhaustion (R0) + REBUILD1 (R1, bridged to Kg) + CDP (clearing the D7 + zero list to R2). *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From Dev Require Import Base G_rules G_reb1 Abs.

Lemma lft_rep : forall n, lft (repeat 1%nat n) = [1;0;1]^^n *> lft [].
Proof. intro n. rewrite <- (app_nil_r (repeat 1%nat n)) at 1. apply lft_ones. Qed.

(** REBUILD1 as a Kg-level rule (bridge the raw REBUILD1 to the token family).  A = 3B+2, a = 3B-3. *)
Lemma KRebuild : forall B, 6 <= B ->
  Kg (repeat O 11) [] O B 0 -->+ Kg (repeat O (12 * B + 24) ++ [2]) [] O O 3.
Proof.
  intros B HB. unfold Kg.
  rewrite (map_rep (12 * B + 24) [2]), map_single, map_rep0, app_nil_r. change (tokd 2) with 7%nat.
  change (3 * O + 1) with 1%nat. change (3 * O + 2) with 2%nat.
  replace (3 * B + 2) with (5 + (3 * B - 3)) by lia.
  replace (12 * B + 24) with (36 + 4 * (3 * B - 3)) by lia.
  unfold Kt. rewrite !app_nil_r.
  rewrite lft_rep, (lft_ones (36 + 4 * (3 * B - 3)) [7]).
  rewrite (pow_add [0;1] 5 (3 * B - 3)).
  rewrite (pow_add [1;0;1] 36 (4 * (3 * B - 3))), (pow_mul [1;0;1] 4 (3 * B - 3)).
  exact (REBUILD1 (3 * B - 3)).
Qed.

(** Clear the D7 (= digit 2) and the zero list to the exhaustion-#2 accumulator R2 (reuse CDP).
    After the rebuild: Kg(repeat O (12B+24) ++ [2]) [] O O 3 ->* Kg(repeat O (12B+25)) [] O R2 3. *)
Definition R2 (B : nat) : nat := iter 2 (U (12 * B + 24)) O.

Lemma clear_to_R2 : forall B,
  Kg (repeat O (12 * B + 24) ++ [2]) [] O O 3 -->* Kg (repeat O (S (12 * B + 24))) [] O (R2 B) 3.
Proof.
  intro B. unfold R2. rewrite <- (app_nil_r (repeat O (S (12 * B + 24)))) at 1. exact (CDP (12 * B + 24) 2 [] [] O 3).
Qed.

(** The concrete top of the run: c0 ->* exhaustion-#2 start Kg(repeat O (12 Bx + 25)) [] O R2 3. *)
Theorem reach_exh2 : c0 -->* Kg (repeat O (S (12 * Bx + 24))) [] O (R2 Bx) 3.
Proof.
  eapply evstep_trans; [apply run_to_exhaustion |].
  eapply evstep_trans; [apply progress_evstep, (KRebuild Bx Bx_ge6) |].
  apply clear_to_R2.
Qed.
