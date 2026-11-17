(** * The run of 2RD1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LG1LD_1RC2LE1LG_1RG0LA1RZ_1LD2RA2LG, its halting configuration, and the score *)

(** Configurations (the same Ligocki family as BB34):
      B(k, n, m) R = 0^inf 1^(2m+1) 2^k B> 1^n R = [Bcfg k n m r].
    The 255-step start ends at
      B(1, 1, 0) 0 1^12 2 0^inf.
    The main rule consumes the 12 ones; each one is turned into a fresh
    Ackermann-level descent by rule 3, and the last symbol 2 sends B to the
    halting configuration F>2.  The parameter [mfin] is sealed behind a [sig]
    exactly like [g15] in BB34_run.v, so that no tactic ever evaluates it. *)

From TM73 Require Import Individual73 BB73_rules BB73_start.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** The start: blank tape to [B(1,1,0) 0 1^12 2 0^inf] in 255 steps. *)

Lemma start_B : c0 -->* Bcfg 1 1 0 (0 >> ([1]^^12 *> (2 >> const 0))).
Proof.
  assert (Heq : Bcfg 1 1 0 (0 >> ([1]^^12 *> (2 >> const 0))) =
    Bcfg 1 1 0 (0 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 2 >> const 0)).
  { unfold Bcfg. simpl. reflexivity. }
  rewrite Heq.
  rewrite <- cfg_255_is_B.
  apply start_raw.
Qed.

(** ** [B_rule] with its result abstracted, as in BB34. *)

Theorem B_rule_gen : forall k n m r (x : nat),
  x = Nat.iter n (g k) m -> Bcfg (S k) n m r -->* Bcfg (S k) 0 x r.
Proof. intros k n m r x Hx. subst x. apply B_rule. Qed.

(** One step at level 1: [B(1,n+1,m) -> B(1,n,m+1)] specialises to n=0. *)
Lemma B1_one : forall m r,
  Bcfg 1 1 m r -->* Bcfg 1 0 (m + 1) r.
Proof.
  intros m r.
  follow (B_rule 0 1 m r).
  rewrite iter_g0.
  apply evstep_refl'. reflexivity.
Qed.

(** ** The descent after rule 2.

    [desc n m] is the value of the "m" parameter after [n] applications of
    rule 2, each followed by the main rule.  It is the same recursion as in
    BB35: [desc (S n) m = desc n (g (S n) m)]. *)

Fixpoint desc (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => desc n' (g (S n') m)
  end.

Lemma rule2_step : forall j m r,
  Bcfg (S (S j)) 0 m (0 >> r) -->*
  Bcfg (S j) 0 (g (S j) m) (0 >> r).
Proof.
  intros j m r.
  follow (rule2 j m r).
  assert (HE : S (S (2 * m)) = 2 * m + 2) by lia.
  rewrite HE.
  apply (B_rule_gen j (2 * m + 2) 0%nat (0 >> r) (g (S j) m)).
  reflexivity.
Qed.

Lemma rule2_phase : forall n m r,
  Bcfg (S (S n)) 0 m (0 >> r) -->*
  Bcfg 1 0 (desc (S n) m) (0 >> r).
Proof.
  intros n. revert n.
  fix IH 1. intros n m r.
  destruct n as [|n].
  - follow (rule2_step 0 m r).
    replace (desc (S 0) m) with (g (S 0) m) by reflexivity.
    finish_cfg.
  - follow (rule2_step (S n) m r).
    follow (IH n (g (S (S n)) m) r).
    replace (desc (S (S n)) m) with (desc (S n) (g (S (S n)) m)) by reflexivity.
    finish_cfg.
Qed.

(** ** One round of the tail automaton.

    In state [B(1,0,m)] with tail [0 1 r], rule 3 creates [B(2m+3,1,0)].
    The single 1 is consumed by [g_(2m+2)], and the [2m+2] applications of
    rule 2 descend through [g_(2m+2)], [g_(2m+1)], ..., [g_1].  Thus the new
    parameter is [round m = desc (2m+2) (g (2m+2) 0)]. *)

Definition round (m : nat) : nat := desc (2 * m + 2) (g (2 * m + 2) 0).

Lemma round_step : forall x y r,
  y = round x ->
  Bcfg (2 * x + 3) 1 0 (0 >> r) -->* Bcfg 1 0 y (0 >> r).
Proof.
  intros x y r Hy.
  replace (2 * x + 3) with (S (2 * x + 2)) by lia.
  eapply evstep_trans;
    [apply (B_rule_gen (2 * x + 2) 1 0%nat (0 >> r) (g (2 * x + 2) 0));
     reflexivity |].
  replace (S (2 * x + 2)) with (S (S (2 * x + 1))) by lia.
  follow (rule2_phase (2 * x + 1) (g (2 * x + 2) 0) r).
  replace (S (2 * x + 1)) with (2 * x + 2) by lia.
  replace (desc (2 * x + 2) (g (2 * x + 2) 0)) with (round x) by reflexivity.
  rewrite Hy. finish.
Qed.

(** ** All twelve rounds. *)

Lemma rounds : forall n m r,
  Bcfg 1 0 m (0 >> ([1]^^n *> r)) -->*
  Bcfg 1 0 (Nat.iter n round m) (0 >> r).
Proof.
  intros n. induction n as [|n IH]; intros m r.
  - replace ([1]^^0 *> r) with r by reflexivity.
    replace (Nat.iter 0 round m) with m by reflexivity.
    finish.
  - replace ([1]^^(S n) *> r) with (1 >> ([1]^^n *> r)) by reflexivity.
    follow (rule3 m ([1]^^n *> r)).
    follow (round_step m (round m) ([1]^^n *> r) eq_refl).
    rewrite iter_succ_r.
    apply IH.
Qed.

(** ** The sealed final parameter. *)

Lemma mfin_spec : {x : nat | x = Nat.iter 12 round 1%nat}.
Proof. exact (exist _ _ eq_refl). Qed.
Definition mfin : nat := proj1_sig mfin_spec.
Lemma mfin_eq : mfin = Nat.iter 12 round 1%nat.
Proof. exact (proj2_sig mfin_spec). Qed.
Opaque mfin.

Lemma reaches_before_halt : c0 -->* Bcfg 1 0 mfin (0 >> 2 >> const 0).
Proof.
  eapply evstep_trans; [apply start_B |].
  eapply evstep_trans; [apply (B1_one 0 (0 >> ([1]^^12 *> (2 >> const 0)))) |].
  eapply evstep_trans; [apply (rounds 12 1 (2 >> const 0)) |].
  rewrite mfin_eq.
  finish.
Qed.

(** ** The halting configuration. *)

Definition c_final : Q * tape :=
  (1 >> ([1]^^(S (S (S (2 * mfin)))) *> const 0)) {{F}}> (2 >> const 0).

Lemma reaches_final : c0 -->* c_final.
Proof.
  eapply evstep_trans; [apply reaches_before_halt |].
  unfold c_final.
  apply (halt_from_B mfin (const 0)).
Qed.

Theorem final_halted : halted tm c_final.
Proof. reflexivity. Qed.

Theorem bb73_halts : halts tm c0.
Proof. eapply halted_evstep_halts; [apply reaches_final | apply final_halted]. Qed.

(** ** Sigma: the number of nonzero cells after the halting write.

    The configuration before the halting write has [2mfin+4] ones to the left
    of the head and a 2 under the head.  The halting transition F2 writes a 1,
    giving [2mfin+5] nonzero cells. *)

Definition sigma : nat := 2 * mfin + 5.
Definition final_cells : list sym := [S1]^^(2 * mfin + 4) ++ [S1].

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

Lemma cells_count : forall x : nat,
  length ([S1]^^(2 * x + 4) ++ [S1]) = 2 * x + 5.
Proof.
  intros x.
  rewrite !length_app, (lpow_length (2 * x + 4) [S1]).
  simpl. lia.
Qed.

Lemma final_cells_count : length final_cells = sigma.
Proof. unfold final_cells, sigma. apply cells_count. Qed.

Lemma cells_nonblank : forall (x : nat) (y : sym),
  In y ([S1]^^(2 * x + 4) ++ [S1]) -> y <> S0.
Proof.
  intros x y H.
  apply in_app_or in H as [H | H].
  - apply in_lpow in H. simpl in H. intuition congruence.
  - simpl in H. intuition congruence.
Qed.

Lemma final_cells_all_nonblank : forall y, In y final_cells -> y <> S0.
Proof. intros y H. unfold final_cells in H. exact (cells_nonblank mfin y H). Qed.
