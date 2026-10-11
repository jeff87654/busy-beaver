(** * Std_brpow: the library's closed ZF axioms prove the de Bruijn closure of O'Rear's power set
    axiom ([bridge_POW], Std_iface2.v).  The proof is the one written by a Haiku 5.5 subagent in the
    experiment file Haiku_pow.v, moved here unchanged (names renamed) and reviewed. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic Std_dB Std_tr Std_gen Std_iface Std_iface2 Std_setnd Std_setbase.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(* Explicit form of the library closure of POW: forall v3 v2 v1 v0, with POW's body
   not v1 (not v2 ((forall v3 (v3 in v2 -> v3 in v0)) -> v2 in v1)), v0 = $0 at the innermost level. *)
Lemma Lib4_POW_eq' : Lib 4 POW =
  (∀ (∀ (∀ (∀ (¬ (∀ (¬ (∀ ((∀ (($0 ∈' $1) → ($0 ∈' $3))) → ($0 ∈' $1)))))))))).
Proof. reflexivity. Qed.

Lemma ff4' (A : list form) (phi : form) :
  (forall psi, In psi A -> closedf psi) -> A ⊢C phi -> A ⊢C (∀ (∀ (∀ (∀ phi)))).
Proof.
  intros HA H.
  exact (AllI_closed _ _ HA (AllI_closed _ _ HA (AllI_closed _ _ HA (AllI_closed _ _ HA H)))).
Qed.

Lemma pow_nd (G : list form) : In ax_power' G ->
  G ⊢C (¬ (∀ (¬ (∀ ((∀ (($0 ∈' $1) → ($0 ∈' $3))) → ($0 ∈' $1)))))).
Proof.
  intro HP.
  fintro H.
  fassert Hax : ax_power'.
  { apply Ctx. exact HP. }
  unfold ax_power' in Hax. simp_in Hax.
  finst Hax ($0).
  fex Hax t Ht.
  unfold is_power in Ht. simp_in Ht.
  finst H t.
  fapply H.
  fall z.
  fintro Hs.
  finst Ht z.
  exact (iff_r _ _ _ Ht Hs).
Qed.

Theorem bridge_POW_proof : bridge_POW.
Proof.
  unfold bridge_POW, thm.
  exists [ax_power'].
  split.
  - intros psi [<-|[]]. unfold ZFc. left. constructor 1. unfold ZF0base. cbn. tauto.
  - rewrite Lib4_POW_eq'. apply ff4'.
    + intros psi [<-|[]]. apply ZF0base_closed. unfold ZF0base. cbn. tauto.
    + apply pow_nd. now left.
Qed.

Print Assumptions bridge_POW_proof.
