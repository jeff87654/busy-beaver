(** Original adapter from the finite numeric replay to the actual PA238
    machine in the MIT-licensed BusyCoq semantics. Compilation and independent
    review remain required; this source carries no assumed bootstrap premise. *)

From Coq Require Import Arith.PeanoNat Lia.
From BusyCoq Require Import TM.
From P238.tm Require Import Table238 Table238Facts TM238 Finite238 Bootstrap238.
Local Unset Implicit Arguments.

Definition bounded_configuration (c : literal_configuration) :=
  let '(q, tape) := c in (state238_of_nat q, tape).

Lemma numeric_transition_machine q b w direction q' :
  tmn238 q b = Some (w, direction, q') ->
  machine238 (state238_of_nat q, b) = Some (w, direction, state238_of_nat q').
Proof.
  intros E.
  assert (Hq : q < 238).
  { destruct (Nat.lt_ge_cases q 238) as [Hq|Hq]; [exact Hq|].
    pose proof (proj2 (tmn238_none_iff q b) Hq) as N.
    rewrite E in N. discriminate. }
  unfold machine238. rewrite state238_of_nat_exact by lia.
  rewrite E. reflexivity.
Qed.

Lemma literal_step_machine c d : literal_step c d ->
  Semantics238.step machine238 (bounded_configuration c) (bounded_configuration d).
Proof.
  intros H. destruct H; unfold bounded_configuration; cbn.
  - apply Semantics238.step_left. apply numeric_transition_machine. assumption.
  - apply Semantics238.step_right. apply numeric_transition_machine. assumption.
Qed.

Theorem exact_steps_machine n c d : exact_steps n c d ->
  Semantics238.multistep machine238 n (bounded_configuration c) (bounded_configuration d).
Proof.
  intros H. induction H.
  - apply Semantics238.multistep_0.
  - eapply Semantics238.multistep_S.
    + apply literal_step_machine. eassumption.
    + exact IHexact_steps.
Qed.

Theorem blank_machine_reaches_checkpoint238 :
  Semantics238.multistep machine238 799504 Semantics238.c0
    (bounded_configuration (denote checkpoint238)).
Proof.
  change (Semantics238.multistep machine238 799504
    (bounded_configuration (denote blank238))
    (bounded_configuration (denote checkpoint238))).
  apply exact_steps_machine. exact blank_reaches_checkpoint238.
Qed.

(** A proved finite bootstrap transports the actual machine's halting question
    in both directions. The forward direction uses determinism of BusyCoq's
    small-step semantics through [preceeds_halt']; no checkpoint oracle is
    introduced. *)
Theorem blank_halts_iff_checkpoint238 :
  blank_halts238 <->
  Semantics238.halts machine238 (bounded_configuration (denote checkpoint238)).
Proof.
  unfold blank_halts238. split.
  - intros [n Hhalt]. exists (n - 799504).
    eapply Semantics238.preceeds_halt'.
    + exact Hhalt.
    + exact blank_machine_reaches_checkpoint238.
  - intros Hhalt. eapply Semantics238.halts_multistep.
    + exact Hhalt.
    + exact blank_machine_reaches_checkpoint238.
Qed.

Lemma checkpoint238_not_halted :
  ~ Semantics238.halted machine238 (bounded_configuration (denote checkpoint238)).
Proof.
  change (~ (machine238 (state238_of_nat 25, false) = None)).
  rewrite machine238_terminal_iff.
  change (25 <> 238). discriminate.
Qed.

(** The adapter also reflects real machine runs back to literal numeric
    derivations. Bounds are required only when starting from arbitrary numeric
    state labels, since [state238_of_nat] clamps labels above the terminal. *)
Definition numeric_configuration (c : state238 * centered_tape) : literal_configuration :=
  let '(q, tape) := c in (state238_number q, tape).

Definition literal_bounded (c : literal_configuration) : Prop :=
  let '(q, _) := c in q <= 238.

Lemma bounded_numeric_configuration c :
  bounded_configuration (numeric_configuration c) = c.
Proof.
  destruct c as [q tape].
  change ((state238_of_nat (state238_number q), tape) = (q, tape)).
  rewrite state238_of_number. reflexivity.
Qed.

Lemma numeric_bounded_configuration c : literal_bounded c ->
  numeric_configuration (bounded_configuration c) = c.
Proof.
  destruct c as [q tape]. intros Hq. change (q <= 238) in Hq.
  change ((state238_number (state238_of_nat q), tape) = (q, tape)).
  rewrite state238_of_nat_exact by exact Hq. reflexivity.
Qed.

Lemma machine_step_literal c d :
  Semantics238.step machine238 c d ->
  literal_step (numeric_configuration c) (numeric_configuration d).
Proof.
  intros H. destruct H as [q q' b w l r E | q q' b w l r E];
    unfold numeric_configuration; cbn.
  - apply literal_left.
    apply (proj1 (machine238_transition_iff q b w L q')). exact E.
  - apply literal_right.
    apply (proj1 (machine238_transition_iff q b w R q')). exact E.
Qed.

Theorem machine_steps_literal n c d :
  Semantics238.multistep machine238 n c d ->
  exact_steps n (numeric_configuration c) (numeric_configuration d).
Proof.
  intros H. induction H as [c | n c d e Hstep Hsteps IH].
  - apply exact_zero.
  - eapply exact_next.
    + apply machine_step_literal. exact Hstep.
    + exact IH.
Qed.

Theorem exact_steps_machine_iff n c d :
  literal_bounded c -> literal_bounded d ->
  (exact_steps n c d <->
   Semantics238.multistep machine238 n (bounded_configuration c) (bounded_configuration d)).
Proof.
  intros Hc Hd. split.
  - apply exact_steps_machine.
  - intros Hrun. pose proof (machine_steps_literal _ _ _ Hrun) as Hliteral.
    rewrite (numeric_bounded_configuration c Hc),
            (numeric_bounded_configuration d Hd) in Hliteral.
    exact Hliteral.
Qed.
