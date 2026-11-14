(** * Instantiating busycoq to machines with 31 states and 2 symbols (the BB29 / BB31 / BB33 hydra machines).
    States are q-prefixed: qA..qZ, then qAA.. for the
    characters [ \ ] ^ _ ` a of the machine string, so there are no clashes with the
    directions L/R, Nat.S, Nat.O, True's I, the type Q or ZArith's Z. *)

From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Inductive state :=
  qA | qB | qC | qD | qE | qF | qG | qH | qI | qJ | qK | qL | qM | qN | qO | qP | qQ | qR | qS | qT | qU | qV | qW | qX | qY | qZ | qAA | qAB | qAC | qAD | qAE.
Inductive sym := S0 | S1.

Module BB312 <: Ctx.
  Definition Q := state.
  Definition Sym := sym.
  Definition q0 := qA.
  Definition q1 := qB.
  Definition s0 := S0.
  Definition s1 := S1.

  Lemma q0_neq_q1 : q0 <> q1.
  Proof. discriminate. Qed.

  Lemma s0_neq_s1 : s0 <> s1.
  Proof. discriminate. Qed.

  Definition eqb_q (a b : Q): {a = b} + {a <> b}.
    decide equality.
  Defined.

  Definition eqb_sym (a b : Sym): {a = b} + {a <> b}.
    decide equality.
  Defined.

  Definition all_qs := [qA; qB; qC; qD; qE; qF; qG; qH; qI; qJ; qK; qL; qM; qN; qO; qP; qQ; qR; qS; qT; qU; qV; qW; qX; qY; qZ; qAA; qAB; qAC; qAD; qAE].

  Lemma all_qs_spec : forall a, In a all_qs.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.

  Definition all_syms := [S0; S1].

  Lemma all_syms_spec : forall a, In a all_syms.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.
End BB312.
