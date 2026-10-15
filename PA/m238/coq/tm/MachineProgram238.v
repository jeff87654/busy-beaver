(** * The actual bounded BusyCoq machine and the fixed PA238 program.

    Both execution directions pass through actual literal step derivations.
    The starting bound excludes the numeric adapter's out-of-table clamp. *)

From Coq Require Import Arith.Arith Lia.
From P238.tm Require Import Table238 Table238Facts TM238 Finite238 Bootstrap238
  BootstrapMachine238 LiteralHalting238 RM238 Prog238 Reflection238.
Local Unset Implicit Arguments.

Lemma literal_halted_machine238 c : literal_halted238 c ->
  Semantics238.halted machine238 (bounded_configuration c).
Proof.
  destruct c as [q [[l b] r]]. cbn [literal_halted238 bounded_configuration].
  intro H. apply tmn238_none_iff in H.
  change (machine238 (state238_of_nat q,b) = None).
  apply machine238_terminal_iff. unfold state238_number, state238_of_nat; cbn.
  apply Nat.min_r. exact H.
Qed.

Lemma machine_halted_literal238 c : Semantics238.halted machine238 c ->
  literal_halted238 (numeric_configuration c).
Proof.
  destruct c as [q [[l b] r]].
  change (machine238 (q,b) = None -> tmn238 (state238_number q) b = None).
  apply (proj1 (machine238_none_numeric_iff q b)).
Qed.

Theorem literal_machine_halts238 c : literal_bounded c ->
  (literal_halts238 c <-> Semantics238.halts machine238 (bounded_configuration c)).
Proof.
  intro Bound. split.
  - intros [n [terminal [R H]]]. exists n, (bounded_configuration terminal).
    split; [apply exact_steps_machine; exact R|apply literal_halted_machine238; exact H].
  - intros [n [terminal [R H]]]. exists n, (numeric_configuration terminal).
    split.
    + pose proof (machine_steps_literal n (bounded_configuration c) terminal R) as S.
      rewrite (numeric_bounded_configuration c Bound) in S. exact S.
    + apply machine_halted_literal238. exact H.
Qed.

Theorem actual_pa238_machine_program :
  blank_halts238 <-> rm_halts p238 (nil, R_boot238).
Proof.
  rewrite blank_halts_iff_checkpoint238.
  rewrite <- (literal_machine_halts238 (denote checkpoint238) ltac:(change (25 <= 238); lia)).
  apply checkpoint238_literal_iff_program.
Qed.
