(** * Instantiating busycoq to machines with 19 states and 2 symbols (bb8 project).
    The 17th, 18th, and 19th states are named QQ, RR, SS (the letters Q, R, S of the machine string)
    because Q is the Ctx state type, R is the direction, and S is Datatypes.S.
    The state L shadows busycoq's direction constructor L (use TM.L), and O shadows Datatypes.O (use 0 or Datatypes.O). *)

From Coq Require Import Lists.List. Import ListNotations.
From BusyCoq Require Export Flip.
Set Default Goal Selector "!".

Inductive state := A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | QQ | RR | SS.
Inductive sym := S0 | S1.

Module BB192 <: Ctx.
  Definition Q := state.
  Definition Sym := sym.
  Definition q0 := A.
  Definition q1 := B.
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

  Definition all_qs := [A; B; C; D; E; F; G; H; I; J; K; L; M; N; O; P; QQ; RR; SS].

  Lemma all_qs_spec : forall a, In a all_qs.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.

  Definition all_syms := [S0; S1].

  Lemma all_syms_spec : forall a, In a all_syms.
  Proof.
    destruct a; repeat ((left; reflexivity) || right).
  Qed.
End BB192.
