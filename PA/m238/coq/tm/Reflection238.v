(** * Finite halt reflection for the actual PA238 dispatcher.

    Every nonhalting register instruction has a strictly positive literal
    segment. Determinism therefore consumes part of any actual finite halt
    derivation. A finite literal halt cannot remain forever between restored
    dispatcher configurations or stop at an unintended site. *)

From Coq Require Import Lists.List Arith.Arith Lia.
From P238.tm Require Import RM238 Prog238 Finite238 Bootstrap238
  LiteralHalting238 Simulation238.
Local Unset Implicit Arguments.
Import ListNotations.

Lemma exact_steps_halt_suffix238 n c d m terminal :
  exact_steps n c d -> exact_steps m c terminal -> literal_halted238 terminal ->
  exists remaining, m = n + remaining /\ exact_steps remaining d terminal.
Proof.
  intro R. revert m terminal.
  induction R as [c|n c mid d A R IH]; intros m terminal H Halt.
  - exists m. split; [lia|exact H].
  - inversion H as [c0|m0 c0 mid' terminal0 B Tail]; subst.
    + exfalso. eapply literal_halted_no_step238; eassumption.
    + assert (E : mid' = mid) by (eapply literal_step_deterministic238; eassumption).
      subst mid'. destruct (IH m0 terminal Tail Halt) as [remaining [L S]].
      exists remaining. split; [lia|exact S].
Qed.

Theorem inv238_reflects_halt N T : Inv238 N T -> literal_halts238 T ->
  rm_halts p238 ([], R_boot238).
Proof.
  intros Inv [count [terminal [Run Halt]]].
  revert N T Inv Run. induction count as [count IH] using lt_wf_ind;
    intros N T Inv Run.
  destruct (inv238_next N T Inv) as [[c [R H]]|[c' R]].
  - exists N, c. split; assumption.
  - destruct (inv238_step N T c' Inv R) as [T' [steps [Inv' Segment]]].
    destruct (exact_steps_halt_suffix238 (S steps) T T' count terminal Segment Run Halt)
      as [remaining [L Suffix]].
    apply (IH remaining ltac:(lia) (S N) T' Inv' Suffix).
Qed.

Theorem checkpoint238_literal_iff_program :
  literal_halts238 (denote checkpoint238) <-> rm_halts p238 ([], R_boot238).
Proof.
  split.
  - apply (inv238_reflects_halt 0 (denote checkpoint238) inv238_boot).
  - apply rm238_literal_halts.
Qed.
