(** * The sharper bound W j 5 >= 3 ^j 3 + j (arrows) for j >= 2, hence N = 2 W 20 5 + 7 > 3 ^20 3 *)
From BB7 Require Import Defs Clr Bound.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".

Lemma iterU0 : forall n, 2 * 3 ^ (S (S n)) <= iter (S n) (U 0) 3.
Proof.
  induction n.
  - simpl iter. rewrite U_0. simpl. lia.
  - change (iter (S (S n)) (U 0) 3) with (U 0 (iter (S n) (U 0) 3)). rewrite U_0.
    rewrite (Nat.pow_succ_r' 3 (S (S n))). lia.
Qed.

Lemma arrow_233 : arrow 2 3 3 = 3 ^ 27.
Proof.
  rewrite (arrow_SS 1 3 2), (arrow_SS 1 3 1), (arrow_one 2 3).
  rewrite (arrow_1_pow 3 3), (arrow_1_pow 3 (3 ^ 3)). change (3 ^ 3) with 27. reflexivity.
Qed.

Lemma W25 : W 2 5 = iter 26 (U 0) 3.
Proof. rewrite (W_S 1 5), (W_S 0 5), (W_0 5), (U_0 5), (U_S 0 (3 * 5 + 9)), (W_0 3). reflexivity. Qed.

Lemma pow3_ge : forall n, 3 <= 3 ^ (S n).
Proof. induction n; [simpl; lia |]. rewrite Nat.pow_succ_r'. lia. Qed.

Lemma ar_base : forall A P I, A = P -> 3 <= P -> 2 * P <= I -> A + 2 <= I.
Proof. intros. lia. Qed.

Lemma W_step : forall k, arrow k 3 3 + k <= W k 5 -> arrow (S k) 3 3 + S k <= W (S k) 5.
Proof.
  intros k IH. rewrite W_S, arrow_S3.
  pose proof (arrow_33 k). pose proof (U_lower k (W k 5)).
  pose proof (arrow_mono 3 k (arrow k 3 3 + 3) (W k 5 + 3 - k) ltac:(lia) ltac:(lia)).
  pose proof (arrow_step k (arrow k 3 3) ltac:(lia)). lia.
Qed.

Lemma W_arrow3 : forall j, arrow (S (S j)) 3 3 + S (S j) <= W (S (S j)) 5.
Proof.
  induction j as [| j IH].
  - rewrite W25. exact (ar_base _ _ _ arrow_233 (pow3_ge 26) (iterU0 25)).
  - apply W_step. exact IH.
Qed.

Lemma ar3 : forall N w A, N = 2 * w + 7 -> A + 20 <= w -> A < N.
Proof. intros. lia. Qed.

Theorem N_lower3 : forall N, N = 2 * W 20 5 + 7 -> arrow 20 3 3 < N.
Proof. intros N HN. exact (ar3 _ _ _ HN (W_arrow3 18)). Qed.
