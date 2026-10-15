(** * Finite structural facts about the original PA238 table.

    These original PA238 proofs concern the literal finite transition table.
    They do not establish the bootstrap checkpoint or the PA correspondence.
    The computational certificates use kernel reduction when this file is
    compiled. The Python generator reproduces the source, not an axiom. *)

From Coq Require Import Lists.List Bool.Bool Arith.PeanoNat Lia.
From BusyCoq Require Import TM.
From P238.tm Require Import Table238.
Local Unset Implicit Arguments.

Lemma table238_length : length table238 = 238.
Proof. reflexivity. Qed.

Lemma table238_row_defined : forall q,
  nth_error table238 q <> None <-> q < 238.
Proof.
  intro q. rewrite nth_error_Some, table238_length. reflexivity.
Qed.

Lemma table238_no_row_iff : forall q,
  nth_error table238 q = None <-> 238 <= q.
Proof.
  intro q. rewrite nth_error_None, table238_length. reflexivity.
Qed.

Lemma table238_terminal_no_row : nth_error table238 terminal238 = None.
Proof. reflexivity. Qed.

Lemma table238_row_total : forall q, q < 238 ->
  exists row, nth_error table238 q = Some row.
Proof.
  intros q Hq. destruct (nth_error table238 q) as [row|] eqn:Hrow.
  - exists row. reflexivity.
  - apply table238_no_row_iff in Hrow. lia.
Qed.

(** The two destinations of every row stay inside 0..238. The final value
    includes the terminal state; it does not assert that every step continues. *)
Definition row238_bounded (row : bool * dir * nat * bool * dir * nat) : bool :=
  match row with (_, _, n0, _, _, n1) =>
    andb (Nat.leb n0 238) (Nat.leb n1 238)
  end.

Lemma table238_bounds_certificate : forallb row238_bounded table238 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma table238_row_bounds : forall q w0 d0 n0 w1 d1 n1,
  nth_error table238 q = Some (w0, d0, n0, w1, d1, n1) ->
  n0 <= 238 /\ n1 <= 238.
Proof.
  intros q w0 d0 n0 w1 d1 n1 Hrow.
  assert (Hin : In (w0, d0, n0, w1, d1, n1) table238).
  { eapply nth_error_In. exact Hrow. }
  pose proof table238_bounds_certificate as Hbounds.
  rewrite forallb_forall in Hbounds.
  specialize (Hbounds _ Hin).
  change (andb (Nat.leb n0 238) (Nat.leb n1 238) = true) in Hbounds.
  apply andb_true_iff in Hbounds as [H0 H1].
  split; apply Nat.leb_le; assumption.
Qed.

Lemma tmn238_total : forall q symbol, q < 238 ->
  exists written direction destination,
    tmn238 q symbol = Some (written, direction, destination).
Proof.
  intros q symbol Hq.
  destruct (table238_row_total q Hq) as [row Hrow].
  destruct row as [[[[[w0 d0] n0] w1] d1] n1].
  unfold tmn238. rewrite Hrow. destruct symbol.
  - exists w1, d1, n1. reflexivity.
  - exists w0, d0, n0. reflexivity.
Qed.

Lemma tmn238_destination_bound : forall q symbol written direction destination,
  tmn238 q symbol = Some (written, direction, destination) ->
  destination <= 238.
Proof.
  intros q symbol written direction destination Htransition.
  unfold tmn238 in Htransition.
  destruct (nth_error table238 q) as [row|] eqn:Hrow; [| discriminate].
  destruct row as [[[[[w0 d0] n0] w1] d1] n1].
  destruct (table238_row_bounds q w0 d0 n0 w1 d1 n1 Hrow) as [H0 H1].
  destruct symbol; inversion Htransition; subst; assumption.
Qed.

Lemma tmn238_terminal : forall symbol, tmn238 terminal238 symbol = None.
Proof.
  intro symbol. unfold tmn238. rewrite table238_terminal_no_row. reflexivity.
Qed.

Lemma tmn238_none_iff : forall q symbol, tmn238 q symbol = None <-> 238 <= q.
Proof.
  intros q symbol. unfold tmn238.
  destruct (nth_error table238 q) as [row|] eqn:Hrow.
  - destruct row as [[[[[w0 d0] n0] w1] d1] n1].
    assert (Hq : q < 238).
    { apply table238_row_defined. rewrite Hrow. discriminate. }
    destruct symbol; split; intro H; [discriminate | lia | discriminate | lia].
  - split.
    + intro H. apply table238_no_row_iff. exact Hrow.
    + intro H. reflexivity.
Qed.

(** State 131 on read 1 writes 1, moves right, and enters the terminal state.
    This fact does not assert that state 131 is reachable from blank tape. *)
Example table238_terminal_entry : tmn238 131 true = Some (true, R, 238).
Proof. reflexivity. Qed.
