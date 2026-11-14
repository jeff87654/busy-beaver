(** * Complete halting trajectory and exact final tape of the new BB(5,4) champion:
      1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE *)

From Local Require Import Individual54 BB54_rules.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Sealed tower constants (never unfolded during reductions or [lia]) *)

Lemma M1_spec : {x : nat | x = Nat.iter 1 (g 4) 0%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition M1 : nat := proj1_sig M1_spec.
Lemma M1_eq : M1 = Nat.iter 1 (g 4) 0%nat.
Proof. exact (proj2_sig M1_spec). Qed.

Lemma KM_final_spec : {p : nat * nat | p = Nat.iter (2 * M1 + 5) step_pair (0%nat, 1%nat)}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition K_final : nat := fst (proj1_sig KM_final_spec).
Definition M_final : nat := snd (proj1_sig KM_final_spec).
Lemma KM_final_eq : (K_final, M_final) = Nat.iter (2 * M1 + 5) step_pair (0%nat, 1%nat).
Proof.
  unfold K_final, M_final.
  rewrite <- surjective_pairing.
  exact (proj2_sig KM_final_spec).
Qed.

(** ** Abstracted wrappers so sealed constants never trigger reduction *)

Theorem B_rule_gen : forall k n m r (x : nat),
  x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.
Proof. intros k n m r x Hx. subst x. apply B_rule. Qed.

Theorem D_chain_gen : forall c k m r K M,
  (K, M) = Nat.iter c step_pair (k, m) ->
  Bcfg (S k) 0 m ([2]^^c *> r) -->* Bcfg (S K) 0 M r.
Proof.
  intros c k m r K M H.
  assert (HK : K = fst (Nat.iter c step_pair (k, m))) by (rewrite <- H; reflexivity).
  assert (HM : M = snd (Nat.iter c step_pair (k, m))) by (rewrite <- H; reflexivity).
  subst K M. apply D_chain.
Qed.

(** ** Full trajectory from blank tape [c0] to [c_final] *)

Definition c_final : Q * tape :=
  (1 >> ([2]^^(S K_final) *> ([3]^^(2 * M_final + 1) *> const 0))) {{B}}> (1 >> (1 >> const 0)).

Lemma halt_enter : forall K M,
  Bcfg (S K) 0 M (0 >> (1 >> (1 >> const 0))) -->*
  (1 >> ([2]^^(S K) *> ([3]^^(2 * M + 1) *> const 0))) {{B}}> (1 >> (1 >> const 0)).
Proof.
  intros K M. unfold Bcfg; simpl. st_step. finish.
Qed.

Theorem reaches_final : c0 -->* c_final.
Proof.
  eapply evstep_trans; [apply start_to_B5 |].
  eapply evstep_trans; [apply (B_rule_gen 4 1 0 (const 0) M1 M1_eq) |].
  eapply evstep_trans; [apply (B_sweep M1) |].
  eapply evstep_trans;
    [apply (D_chain_gen (2 * M1 + 5) 0%nat 1%nat (0 >> (1 >> (1 >> const 0))) K_final M_final KM_final_eq) |].
  apply (halt_enter K_final M_final).
Qed.

Theorem final_halted : halted tm c_final.
Proof. reflexivity. Qed.

Theorem bb54_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_final | apply final_halted]. Qed.

(** ** Exact nonzero cell count [sigma] after the halting transition [B1 = 1RZ] *)

Definition sigma : nat := 2 * M_final + K_final + 5.

Definition final_cells : list sym :=
  [3]^^(2 * M_final + 1) ++ [2]^^(S K_final) ++ [S1; S1; S1].

Lemma lpow_length : forall j (ys : list sym), length (ys ^^ j) = j * length ys.
Proof.
  induction j as [|j IH]; intros ys.
  - reflexivity.
  - simpl. rewrite app_length, IH. lia.
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
  length ([3]^^(2 * M + 1) ++ [2]^^(S K) ++ [S1; S1; S1]) = 2 * M + K + 5.
Proof.
  intros M K.
  rewrite !app_length, (lpow_length (2 * M + 1) [3]), (lpow_length (S K) [2]).
  simpl. lia.
Qed.

Theorem final_cells_count : length final_cells = sigma.
Proof. unfold final_cells, sigma. apply cells_count_gen. Qed.

Lemma cells_nonblank_gen : forall (M K : nat) (y : sym),
  In y ([3]^^(2 * M + 1) ++ [2]^^(S K) ++ [S1; S1; S1]) -> y <> S0.
Proof.
  intros M K y H.
  apply in_app_or in H as [H | H].
  - apply in_lpow in H. simpl in H. intuition congruence.
  - apply in_app_or in H as [H | H].
    + apply in_lpow in H. simpl in H. intuition congruence.
    + simpl in H. intuition congruence.
Qed.

Theorem final_cells_all_nonblank : forall y, In y final_cells -> y <> S0.
Proof.
  intros y H. unfold final_cells in H.
  exact (cells_nonblank_gen M_final K_final y H).
Qed.
