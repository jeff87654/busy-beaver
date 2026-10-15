(** * The original PA238 table in BusyCoq's finite-machine semantics.

    Original PA238 implementation. The semantics and its finite-context
    signature are imported from MIT-licensed BusyCoq. The numeric transition
    function remains [tmn238]; the lemmas below show exact agreement with the
    bounded machine, including the terminal state. No bootstrap or arithmetic
    correctness assertion is made here. *)

From Coq Require Import Lists.List Bool.Bool Arith.PeanoNat Logic.Eqdep_dec Lia.
From BusyCoq Require Import TM.
From P238.tm Require Import Table238 Table238Facts.
Import ListNotations.
Local Unset Implicit Arguments.

(** The Boolean proof field permits equality without an assumption of general
    proof irrelevance. [UIP_dec] applies only to decidable Boolean equality. *)
Definition state238 : Type := { q : nat | Nat.leb q 238 = true }.

Definition state238_number (q : state238) : nat := proj1_sig q.

Lemma state238_number_bound : forall q, state238_number q <= 238.
Proof.
  intros [number valid]. unfold state238_number. simpl.
  apply Nat.leb_le. exact valid.
Qed.

Lemma state238_ext : forall q q',
  state238_number q = state238_number q' -> q = q'.
Proof.
  intros [number valid] [number' valid'] Hnumber.
  unfold state238_number in Hnumber. simpl in Hnumber. subst number'.
  assert (Hvalid : valid = valid').
  { apply UIP_dec. exact bool_dec. }
  subst valid'. reflexivity.
Qed.

(** Numeric names are packed by their minimum with 238. The exact-transition
    theorem uses the table bound to show that no destination is changed. *)
Definition state238_of_nat (number : nat) : state238 :=
  exist _ (Nat.min number 238)
    (proj2 (Nat.leb_le (Nat.min number 238) 238) (Nat.le_min_r number 238)).

Lemma state238_of_nat_exact : forall number, number <= 238 ->
  state238_number (state238_of_nat number) = number.
Proof.
  intros number Hnumber. unfold state238_number, state238_of_nat. simpl.
  apply Nat.min_l. exact Hnumber.
Qed.

Lemma state238_of_number : forall q, state238_of_nat (state238_number q) = q.
Proof.
  intro q. apply state238_ext. apply state238_of_nat_exact.
  apply state238_number_bound.
Qed.

Definition state238_eq_dec (q q' : state238) : {q = q'} + {q <> q'}.
Proof.
  destruct (Nat.eq_dec (state238_number q) (state238_number q')) as [Heq|Hneq].
  - left. apply state238_ext. exact Heq.
  - right. intro Heq. apply Hneq. rewrite Heq. reflexivity.
Defined.

Definition states238 : list state238 := map state238_of_nat (seq 0 239).

Lemma states238_length : length states238 = 239.
Proof. reflexivity. Qed.

Lemma states238_complete : forall q, In q states238.
Proof.
  intro q. unfold states238. rewrite <- (state238_of_number q).
  apply in_map. apply in_seq.
  pose proof (state238_number_bound q). lia.
Qed.

Module Context238 <: Ctx.
  Definition Q := state238.
  Definition Sym := bool.
  Definition q0 : Q := state238_of_nat 0.
  Definition s0 : Sym := false.
  Definition q1 : Q := state238_of_nat 1.
  Lemma q0_neq_q1 : q0 <> q1.
  Proof.
    intro Heq. pose proof (f_equal state238_number Heq) as Hnumber.
    change (0 = 1) in Hnumber. discriminate.
  Qed.
  Definition s1 : Sym := true.
  Lemma s0_neq_s1 : s0 <> s1.
  Proof. discriminate. Qed.
  Definition eqb_q := state238_eq_dec.
  Definition eqb_sym := bool_dec.
  Definition all_qs := states238.
  Definition all_qs_spec := states238_complete.
  Definition all_syms : list Sym := [false; true].
  Lemma all_syms_spec : forall symbol, In symbol all_syms.
  Proof. intros []; simpl; auto. Qed.
End Context238.

Module Semantics238 := TM.TM Context238.

Definition machine238 : Semantics238.TM :=
  fun '(q, symbol) =>
    match tmn238 (state238_number q) symbol with
    | Some (written, direction, destination) =>
        Some (written, direction, state238_of_nat destination)
    | None => None
    end.

Definition haltstate238 : state238 := state238_of_nat terminal238.

Lemma haltstate238_number : state238_number haltstate238 = 238.
Proof. reflexivity. Qed.

Lemma machine238_projects : forall q symbol,
  (match machine238 (q, symbol) with
   | Some (written, direction, destination) =>
       Some (written, direction, state238_number destination)
   | None => None
   end) = tmn238 (state238_number q) symbol.
Proof.
  intros q symbol. unfold machine238.
  destruct (tmn238 (state238_number q) symbol) as [[[written direction] destination]|]
    eqn:Htransition.
  - change (Some (written, direction, state238_number (state238_of_nat destination)) =
      Some (written, direction, destination)).
    rewrite state238_of_nat_exact.
    + reflexivity.
    + eapply tmn238_destination_bound. exact Htransition.
  - reflexivity.
Qed.

Lemma machine238_transition_iff : forall q symbol written direction destination,
  machine238 (q, symbol) = Some (written, direction, destination) <->
  tmn238 (state238_number q) symbol =
    Some (written, direction, state238_number destination).
Proof.
  intros q symbol written direction destination. split.
  - intro Htransition. rewrite <- machine238_projects.
    rewrite Htransition. reflexivity.
  - intro Htransition. unfold machine238. rewrite Htransition.
    rewrite state238_of_number. reflexivity.
Qed.

Lemma machine238_none_numeric_iff : forall q symbol,
  machine238 (q, symbol) = None <-> tmn238 (state238_number q) symbol = None.
Proof.
  intros q symbol. unfold machine238.
  destruct (tmn238 (state238_number q) symbol) as [[[written direction] destination]|];
    split; intro H; [discriminate | discriminate | reflexivity | reflexivity].
Qed.

Lemma machine238_terminal_iff : forall q symbol,
  machine238 (q, symbol) = None <-> state238_number q = 238.
Proof.
  intros q symbol. rewrite machine238_none_numeric_iff, tmn238_none_iff.
  pose proof (state238_number_bound q) as Hbound. split; intro H; lia.
Qed.

Lemma machine238_terminal : forall symbol, machine238 (haltstate238, symbol) = None.
Proof.
  intro symbol. apply machine238_terminal_iff. exact haltstate238_number.
Qed.

Lemma machine238_active_total : forall q symbol, state238_number q < 238 ->
  exists written direction destination,
    machine238 (q, symbol) = Some (written, direction, destination).
Proof.
  intros q symbol Hactive.
  destruct (tmn238_total (state238_number q) symbol Hactive)
    as [written [direction [destination Htransition]]].
  exists written, direction, (state238_of_nat destination).
  unfold machine238. rewrite Htransition. reflexivity.
Qed.

Lemma machine238_halted_iff : forall q left symbol right,
  Semantics238.halted machine238 (q, (left, symbol, right)) <->
  state238_number q = 238.
Proof.
  intros q left symbol right.
  change (machine238 (q, symbol) = None <-> state238_number q = 238).
  apply machine238_terminal_iff.
Qed.

(** The external PA238 objective will eventually concern this actual blank
    configuration and [Semantics238.halts], rather than a numeric surrogate. *)
Definition blank_halts238 : Prop := Semantics238.halts machine238 Semantics238.c0.
