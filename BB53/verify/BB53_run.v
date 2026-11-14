(** * Halting trajectory and exact final tape of the new BB(5,3) TNF champion:
      1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB *)

From Local Require Import Individual53 BB53_rules.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Sealed intermediate and final tower constants *)

Lemma M2_0_spec : {x : nat | x = g 8 (Nat.iter 5 (g 7) 0%nat)}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M2_0 : nat := proj1_sig M2_0_spec.
Lemma M2_0_eq : M2_0 = g 8 (Nat.iter 5 (g 7) 0%nat).
Proof. exact (proj2_sig M2_0_spec). Qed.

Lemma M2_1_spec : {x : nat | x = Nat.iter (2 * M2_0 + 4) (g 6) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M2_1 : nat := proj1_sig M2_1_spec.
Lemma M2_1_eq : M2_1 = Nat.iter (2 * M2_0 + 4) (g 6) 0%nat.
Proof. exact (proj2_sig M2_1_spec). Qed.

Lemma M2_2_spec : {x : nat | x = Nat.iter (2 * M2_1 + 4) (g 4) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M2_2 : nat := proj1_sig M2_2_spec.
Lemma M2_2_eq : M2_2 = Nat.iter (2 * M2_1 + 4) (g 4) 0%nat.
Proof. exact (proj2_sig M2_2_spec). Qed.

Lemma M2_3_spec : {x : nat | x = Nat.iter (2 * M2_2 + 4) (g 2) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M2_3 : nat := proj1_sig M2_3_spec.
Lemma M2_3_eq : M2_3 = Nat.iter (2 * M2_2 + 4) (g 2) 0%nat.
Proof. exact (proj2_sig M2_3_spec). Qed.

Lemma M2_4_spec : {x : nat | x = Nat.iter (2 * M2_3 + 4) (g 0) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M2_4 : nat := proj1_sig M2_4_spec.
Lemma M2_4_eq : M2_4 = Nat.iter (2 * M2_3 + 4) (g 0) 0%nat.
Proof. exact (proj2_sig M2_4_spec). Qed.

Lemma M3_0_spec : {x : nat | x = g (S (2 * M2_4)) (Nat.iter 5 (g (2 * M2_4)) 0%nat)}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M3_0 : nat := proj1_sig M3_0_spec.
Lemma M3_0_eq : M3_0 = g (S (2 * M2_4)) (Nat.iter 5 (g (2 * M2_4)) 0%nat).
Proof. exact (proj2_sig M3_0_spec). Qed.

Lemma M53_final_spec : {x : nat | x = drain_even M2_4 M3_0}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M53_final : nat := proj1_sig M53_final_spec.
Lemma M53_final_eq : M53_final = drain_even M2_4 M3_0.
Proof. exact (proj2_sig M53_final_spec). Qed.

(** ** Parameterized wrapper lemmas so Coq never unfolds sealed constants *)

Lemma even_round_gen : forall j (x : nat),
  x = g (S j) (Nat.iter 5 (g j) 0%nat) ->
  ([1]^^(S (S j)) *> [2]^^4 *> const 0) {{B}}> ([1]^^2 *> const 0) -->*
  Bcfg (S (S j)) 0 x (const 0).
Proof. intros j x Hx. subst x. apply even_round. Qed.

Lemma K_drain_step_gen : forall k m (x : nat),
  x = Nat.iter (2 * m + 4) (g k) 0%nat ->
  Bcfg (S (S (S k))) 0 m (const 0) -->* Bcfg (S k) 0 x (const 0).
Proof. intros k m x Hx. subst x. apply K_drain_step. Qed.

Lemma K_drain_even_gen : forall q m (x : nat),
  x = drain_even q m ->
  Bcfg (2 * q + 2) 0 m (const 0) -->* Bcfg 2 0 x (const 0).
Proof. intros q m x Hx. subst x. apply K_drain_even. Qed.

Definition c_final : Q * tape :=
  ([2]^^(2 * M53_final + 5) *> const 0) {{E}}> (const 0).

Theorem reaches_final : c0 -->* c_final.
Proof.
  eapply evstep_trans; [apply start53_to_round2 |].
  eapply evstep_trans; [apply (even_round_gen 7 M2_0 M2_0_eq) |].
  eapply evstep_trans; [apply (K_drain_step_gen 6 M2_0 M2_1 M2_1_eq) |].
  eapply evstep_trans; [apply (K_drain_step_gen 4 M2_1 M2_2 M2_2_eq) |].
  eapply evstep_trans; [apply (K_drain_step_gen 2 M2_2 M2_3 M2_3_eq) |].
  eapply evstep_trans; [apply (K_drain_step_gen 0 M2_3 M2_4 M2_4_eq) |].
  unfold Bcfg at 1. simpl ([1]^^0 *> const 0).
  eapply evstep_trans; [apply (lift_from_1 (2 * M2_4 + 1)) |].
  assert (EL : S (2 * M2_4 + 1) = S (S (2 * M2_4))) by lia.
  rewrite EL.
  eapply evstep_trans; [apply (even_round_gen (2 * M2_4) M3_0 M3_0_eq) |].
  assert (ED : S (S (2 * M2_4)) = 2 * M2_4 + 2) by lia.
  rewrite ED.
  eapply evstep_trans; [apply (K_drain_even_gen M2_4 M3_0 M53_final M53_final_eq) |].
  apply (halt_from_2 M53_final).
Qed.

Theorem final_halted : halted tm c_final.
Proof. reflexivity. Qed.

Theorem bb53_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_final | apply final_halted]. Qed.

(** ** Exact nonzero cell count [sigma] after the halting transition [E0 = 1RZ] *)

Definition sigma : nat := 2 * M53_final + 6.

Definition final_cells : list sym :=
  [2]^^(2 * M53_final + 5) ++ [S1].

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

Lemma cells_count_gen : forall M : nat,
  length ([2]^^(2 * M + 5) ++ [S1]) = 2 * M + 6.
Proof.
  intros M.
  rewrite length_app, (lpow_length (2 * M + 5) [2]).
  simpl. lia.
Qed.

Theorem final_cells_count : length final_cells = sigma.
Proof. unfold final_cells, sigma. apply cells_count_gen. Qed.

Lemma cells_nonblank_gen : forall (M : nat) (y : sym),
  In y ([2]^^(2 * M + 5) ++ [S1]) -> y <> S0.
Proof.
  intros M y H.
  apply in_app_or in H as [H | H].
  - apply in_lpow in H. simpl in H. intuition congruence.
  - simpl in H. intuition congruence.
Qed.

Theorem final_cells_all_nonblank : forall y, In y final_cells -> y <> S0.
Proof.
  intros y H. unfold final_cells in H.
  exact (cells_nonblank_gen M53_final y H).
Qed.
