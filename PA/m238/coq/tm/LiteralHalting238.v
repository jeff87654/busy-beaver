(** * Original PA238 literal halting transport.

    These constructions concern the literal table and centered stream tape
    used by Finite238 and Symbolic238. A proved macro preserves its halting
    question in both directions. The bounded BusyCoq adapter can compose
    these proofs with the actual machine; this module makes no PA claim. *)

From Coq Require Import Lists.Streams Arith.Arith Lia.
From P238.tm Require Import Table238 Finite238 Symbolic238.
Local Unset Implicit Arguments.

Definition literal_halted238 (c : literal_configuration) : Prop :=
  let '(q, (_, b, _)) := c in tmn238 q b = None.

Definition literal_halts238 (c : literal_configuration) : Prop :=
  exists n d, exact_steps n c d /\ literal_halted238 d.

Lemma literal_step_deterministic238 c d e :
  literal_step c d -> literal_step c e -> d = e.
Proof.
  intros A B. destruct A; inversion B; subst;
    match goal with
    | H : tmn238 _ _ = Some _, H' : tmn238 _ _ = Some _ |- _ =>
        rewrite H in H'; inversion H'; subst; reflexivity
    end.
Qed.

Lemma literal_halted_no_step238 c d :
  literal_halted238 c -> literal_step c d -> False.
Proof.
  intros H A. destruct A; cbn [literal_halted238] in H;
    match goal with
    | T : tmn238 _ _ = Some _ |- _ => rewrite T in H; discriminate
    end.
Qed.

Lemma literal_step_halts_forward238 c d :
  literal_step c d -> literal_halts238 c -> literal_halts238 d.
Proof.
  intros A [n [e [R H]]].
  inversion R as [c0|n0 c0 mid e0 B R']; subst.
  - exfalso. eapply literal_halted_no_step238; eassumption.
  - assert (E : mid = d) by (eapply literal_step_deterministic238; eassumption).
    subst mid. exists n0. eexists. split; eassumption.
Qed.

Theorem exact_steps_halts_iff238 n c d :
  exact_steps n c d -> (literal_halts238 c <-> literal_halts238 d).
Proof.
  intro R. split.
  - induction R; intro Halt.
    + exact Halt.
    + apply IHR. eapply literal_step_halts_forward238; eassumption.
  - intros [m [e [R' H]]]. exists (n + m), e. split.
    + eapply exact_append; eassumption.
    + exact H.
Qed.

Theorem symbolic_execute_halts_iff238 fuel target s s' k gap :
  symbolic_execute fuel target s = Some (s', k) ->
  (literal_halts238 (symbolic_denote gap s) <->
   literal_halts238 (symbolic_denote gap s')).
Proof.
  intro E. destruct (symbolic_execute_literal fuel target s s' k gap E) as [_ R].
  apply (exact_steps_halts_iff238 (count_at gap k)). exact R.
Qed.

Theorem symbolic_execute_progress238 fuel target s s' k gap :
  symbolic_execute fuel target s = Some (s', k) ->
  0 < snd k ->
  exists n, exact_steps (S n) (symbolic_denote gap s) (symbolic_denote gap s').
Proof.
  intros E K. destruct (symbolic_execute_literal fuel target s s' k gap E) as [_ R].
  assert (P : 0 < count_at gap k) by (unfold count_at; lia).
  destruct (count_at gap k) as [|n] eqn:N; [lia|]. exists n. exact R.
Qed.
