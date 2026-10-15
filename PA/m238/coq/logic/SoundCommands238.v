(** Original soundness invariant for the concrete PA238 command semantics.

    A numeric stack is safe when every finite sequence of pops exposes a
    derivable code. This includes the infinite zero tail of the source's
    numeric stacks, using the calculus's explicit truth axiom. A command
    halts only when its cache is the derivable code 1.

    This is soundness of [Compiler238.command_step] and [execute]. It does
    not identify their executions with the source, candidate decoder,
    abstract enumerator, literal TM, or ordinary PAeq. Those bridges remain
    separate obligations. No finiteness or classical choice is assumed. *)
From Coq Require Import Arith Lia Bool List.
From P238.logic Require Import Codes238 Compiler238.
Import ListNotations.

Fixpoint stack_entry (n w : nat) : nat :=
  match n with
  | 0 => fst (unP w)
  | S n => stack_entry n (snd (unP w))
  end.
Definition safe_stack w := forall n, derivable (stack_entry n w).

Lemma stack_entry_zero n : stack_entry n 0 = 0.
Proof. induction n; cbn [stack_entry unP next_pair]; auto. Qed.
Lemma safe_stack_zero : safe_stack 0.
Proof. intro n; rewrite stack_entry_zero; apply derives_truth. Qed.

Local Opaque P unP wim wel wal weq wn wa wex bundle.

Lemma safe_stack_push a w : derivable a -> safe_stack w -> safe_stack (P a w).
Proof.
  intros Ha Hw [|n]; cbn [stack_entry]; rewrite unP_P; cbn [fst snd].
  - exact Ha.
  - exact (Hw n).
Qed.
Lemma safe_stack_pop w : safe_stack w ->
  derivable (fst (unP w)) /\ safe_stack (snd (unP w)).
Proof.
  intro Hw; split.
  - exact (Hw 0).
  - intro n; exact (Hw (S n)).
Qed.
Lemma safe_stack_pack xs w : Forall derivable xs -> safe_stack w ->
  safe_stack (fold_right P w xs).
Proof.
  intros H; induction H; intro Hw; cbn [fold_right]; auto.
  apply safe_stack_push; auto.
Qed.

Lemma derivable_rows a h b c u : derivable h ->
  Forall derivable (ax_rows a h b c u).
Proof.
  intro Hh; unfold ax_rows.
  constructor; [apply derives_r1|].
  constructor; [apply derives_r2|].
  constructor; [apply derives_r3|].
  constructor; [apply derives_r4|].
  constructor; [apply derives_r5|].
  constructor; [apply derives_r6|].
  constructor; [apply derives_r7|].
  constructor; [apply derives_r8|].
  constructor; [apply derives_all; exact Hh|constructor].
Qed.
Lemma safe_ax_stack a h b c u t w :
  derivable h -> derivable t -> safe_stack w ->
  safe_stack (ax_stack a h b c u t w).
Proof.
  intros Hh Ht Hw; unfold ax_stack; apply safe_stack_pack; [|exact Hw].
  apply Forall_app; split.
  - apply derivable_rows; exact Hh.
  - constructor; [exact Ht|constructor].
Qed.
Lemma derivable_gate a b c : derivable (gate a b c).
Proof.
  unfold gate.
  destruct (Nat.eqb c a) eqn:Ha;
  destruct (Nat.eqb c b) eqn:Hb; cbn; try apply derives_truth.
  apply derives_bundle; apply Nat.eqb_neq; assumption.
Qed.

Definition retained (q : registers) : Prop :=
  let '(t, w, d, h) := q in derivable t /\ derivable h /\ safe_stack w.

Lemma retained_zero d : retained (0, 0, d, 0).
Proof.
  split; [apply derives_truth|].
  split; [apply derives_truth|apply safe_stack_zero].
Qed.

Theorem command_sound k q : retained q ->
  match command_step k q with
  | None => derivable 1
  | Some q' => retained q'
  end.
Proof.
  destruct q as [[[t w] d] h]; cbn [retained].
  intros [Ht [Hh Hw]]; destruct k as [x| | |c x y u]; cbn [command_step].
  - destruct (Nat.eqb (wim t (d + x)) h) eqn:E; cbn [retained].
    + apply Nat.eqb_eq in E; rewrite <- E in Hh.
      split; [exact (derives_mp t (d + x) Ht Hh)|].
      split; [apply derives_truth|].
      apply safe_stack_push; [apply derives_truth|exact Hw].
    + split; [apply derives_truth|].
      split; [apply derives_truth|exact Hw].
  - cbn [retained]; split; [exact Hh|].
    split; [exact Hh|apply safe_stack_push; assumption].
  - destruct (Nat.eqb h 1) eqn:E; cbn [retained].
    + apply Nat.eqb_eq in E; rewrite E in Hh; exact Hh.
    + destruct (safe_stack_pop w Hw) as [Hhead Htail].
      split; [exact Ht|]; split; assumption.
  - cbn [retained]; split; [apply derivable_gate|].
    split; [apply derives_truth|].
    apply safe_ax_stack; assumption.
Qed.

Theorem execute_sound ks : forall q, retained q ->
  match execute ks q with
  | None => derivable 1
  | Some q' => retained q'
  end.
Proof.
  induction ks as [|k ks IH]; intros q Hq; cbn [execute]; [exact Hq|].
  pose proof (command_sound k q Hq) as Hk.
  destruct (command_step k q) as [q'|]; [apply IH; exact Hk|exact Hk].
Qed.

Corollary sound_program_halt ks q : retained q -> execute ks q = None -> derivable 1.
Proof.
  intros Hq Hrun; pose proof (execute_sound ks q Hq) as H.
  rewrite Hrun in H; exact H.
Qed.
Corollary sound_blank_program_halt ks : execute ks (0, 0, 0, 0) = None -> derivable 1.
Proof.
  intro Hrun; eapply sound_program_halt; [apply retained_zero|exact Hrun].
Qed.
