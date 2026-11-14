(** * Halting trajectory and exact final tape of the new BB(4,4) TNF champion:
      1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD *)

From Local Require Import Individual44 BB44_rules.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Sealed intermediate and final tower constants *)

Lemma g30_spec : {x : nat | x = Nat.iter 1 (g 3) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition g30 : nat := proj1_sig g30_spec.
Lemma g30_eq : g30 = Nat.iter 1 (g 3) 0%nat.
Proof. exact (proj2_sig g30_spec). Qed.

Lemma M44_final_spec : {x : nat | x = Nat.iter 4 (g (2 * g30)) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M44_final : nat := proj1_sig M44_final_spec.
Lemma M44_final_eq : M44_final = Nat.iter 4 (g (2 * g30)) 0%nat.
Proof. exact (proj2_sig M44_final_spec). Qed.

Theorem B_rule_gen : forall k n m r (x : nat),
  x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.
Proof. intros k n m r x Hx. subst x. apply B_rule. Qed.

Definition c_final : Q * tape :=
  Bcfg (S (2 * g30)) 0 M44_final (2 >> (1 >> const 0)).

Theorem reaches_final : c0 -->* c_final.
Proof.
  eapply evstep_trans; [apply start44_to_B4 |].
  eapply evstep_trans; [apply (B_rule_gen 3 1 0 (const 0) g30 g30_eq) |].
  eapply evstep_trans; [apply (C_lift g30) |].
  apply (B_rule_gen (2 * g30) 4 0 (2 >> (1 >> const 0)) M44_final M44_final_eq).
Qed.

Theorem final_halted : halted tm c_final.
Proof. reflexivity. Qed.

Theorem bb44_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_final | apply final_halted]. Qed.

(** ** Exact nonzero cell count [sigma] after the halting transition [A2 = 1RZ] *)

Definition sigma : nat := 2 * M44_final + 2 * g30 + 4.

Definition final_cells : list sym :=
  [3]^^(2 * M44_final + 1) ++ [2]^^(S (2 * g30)) ++ [S1; S1].

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

Lemma cells_count_gen : forall M G : nat,
  length ([3]^^(2 * M + 1) ++ [2]^^(S (2 * G)) ++ [S1; S1]) = 2 * M + 2 * G + 4.
Proof.
  intros M G.
  rewrite !length_app, (lpow_length (2 * M + 1) [3]), (lpow_length (S (2 * G)) [2]).
  simpl. lia.
Qed.

Theorem final_cells_count : length final_cells = sigma.
Proof. unfold final_cells, sigma. apply cells_count_gen. Qed.

Lemma cells_nonblank_gen : forall (M G : nat) (y : sym),
  In y ([3]^^(2 * M + 1) ++ [2]^^(S (2 * G)) ++ [S1; S1]) -> y <> S0.
Proof.
  intros M G y H.
  apply in_app_or in H as [H | H].
  - apply in_lpow in H. simpl in H. intuition congruence.
  - apply in_app_or in H as [H | H].
    + apply in_lpow in H. simpl in H. intuition congruence.
    + simpl in H. intuition congruence.
Qed.

Theorem final_cells_all_nonblank : forall y, In y final_cells -> y <> S0.
Proof.
  intros y H. unfold final_cells in H.
  exact (cells_nonblank_gen M44_final g30 y H).
Qed.
