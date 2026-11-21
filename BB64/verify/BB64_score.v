(** * The score of the BB(6,4) machine: exact nonzero-cell count at halt.

    The halting configuration [c_final] has tape

        0^inf  3^(2 m4 + 1)  2^k4  1  1  F>  3  1  0^inf ,

    so the nonzero cells are: (2 m4 + 1) threes, k4 twos, two ones on the
    left of the head, and the "3 1" on the right.  Hence

        sigma = 2 * m4 + k4 + 5 . *)

From TM64 Require Import Individual64 BB64_rules BB64_run.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Definition sigma : nat := 2 * m4 + k4 + 5.

Definition final_cells : list sym :=
  [S3]^^(2 * m4 + 1) ++ [S2]^^k4 ++ [S1; S1; S3; S1].

Lemma lpow_length : forall j (ys : list sym), length (ys ^^ j) = j * length ys.
Proof.
  induction j as [|j IH]; intros ys.
  - reflexivity.
  - simpl. rewrite length_app, IH. lia.
Qed.

Lemma in_lpow : forall j (ys : list sym) x, In x (ys ^^ j) -> In x ys.
Proof.
  induction j as [|j IH]; intros ys x H.
  - destruct H.
  - simpl in H. apply in_app_or in H as [H | H].
    + exact H.
    + exact (IH ys x H).
Qed.

Lemma cells_count_gen : forall M K : nat,
  length ([S3]^^(2 * M + 1) ++ [S2]^^K ++ [S1; S1; S3; S1]) = 2 * M + K + 5.
Proof.
  intros M K.
  rewrite !length_app, (lpow_length (2 * M + 1) [S3]), (lpow_length K [S2]).
  simpl. lia.
Qed.

Lemma final_cells_count : length final_cells = sigma.
Proof. unfold final_cells, sigma. apply cells_count_gen. Qed.

Lemma cells_nonblank_gen : forall (M K : nat) (y : sym),
  In y ([S3]^^(2 * M + 1) ++ [S2]^^K ++ [S1; S1; S3; S1]) -> y <> S0.
Proof.
  intros M K y H.
  apply in_app_or in H as [H | H].
  - apply in_lpow in H. simpl in H. intuition congruence.
  - apply in_app_or in H as [H | H].
    + apply in_lpow in H. simpl in H. intuition congruence.
    + simpl in H. intuition congruence.
Qed.

Lemma final_cells_all_nonblank : forall y, In y final_cells -> y <> S0.
Proof. intros y H. unfold final_cells in H. exact (cells_nonblank_gen m4 k4 y H). Qed.

Theorem bb64_score_main :
  halts tm c0 /\ length final_cells = sigma.
Proof. split; [apply bb64_halts | apply final_cells_count]. Qed.
