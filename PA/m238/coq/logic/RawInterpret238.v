(** Original finite ordinary-ND readback of the raw PA238 logical
    connectives. These proofs expose the classical conjunction,
    disjunction and existential encoded by negation and implication.
    They have no model or IR premise. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module RawInterpret238.
Module C := Compact238.Compact238.
Notation "G ⊢RI phi" :=
  (@prv sig_empty ZF_pred_sig falsity_on class G phi) (at level 61).

Lemma dual_conjunction_intro G (phi psi : C.set_form) :
  G ⊢RI phi -> G ⊢RI psi -> G ⊢RI ¬ (phi → ¬ psi).
Proof.
  intros Hphi Hpsi; apply II; eapply IE.
  - eapply IE; [apply Ctx; now left|].
    eapply Weak; [exact Hphi|]; intros chi Hchi; now right.
  - eapply Weak; [exact Hpsi|]; intros chi Hchi; now right.
Qed.

Lemma dual_conjunction_left G (phi psi : C.set_form) :
  G ⊢RI ¬ (phi → ¬ psi) -> G ⊢RI phi.
Proof.
  intro H; apply DN, II; eapply IE.
  - eapply Weak; [exact H|]; intros chi Hchi; now right.
  - apply II, II; eapply IE.
    + apply Ctx; right; right; now left.
    + apply Ctx; right; now left.
Qed.

Lemma dual_conjunction_right G (phi psi : C.set_form) :
  G ⊢RI ¬ (phi → ¬ psi) -> G ⊢RI psi.
Proof.
  intro H; apply DN, II; eapply IE.
  - eapply Weak; [exact H|]; intros chi Hchi; now right.
  - apply II, Ctx; right; now left.
Qed.

Lemma dual_disjunction_left G (phi psi : C.set_form) :
  G ⊢RI phi -> G ⊢RI (¬ phi → psi).
Proof.
  intro H; apply II, Exp; eapply IE; [apply Ctx; now left|].
  eapply Weak; [exact H|]; intros chi Hchi; now right.
Qed.

Lemma dual_disjunction_right G (phi psi : C.set_form) :
  G ⊢RI psi -> G ⊢RI (¬ phi → psi).
Proof. intro H; apply II; eapply Weak; [exact H|]; intros chi Hchi; now right. Qed.

Lemma dual_disjunction_native G (phi psi : C.set_form) :
  G ⊢RI (¬ phi → psi) -> G ⊢RI (phi ∨ psi).
Proof.
  intro H; apply DN, II.
  assert (Hnot : (¬ (phi ∨ psi)) :: G ⊢RI ¬ phi).
  { apply II; eapply IE; [apply Ctx; right; now left|apply DI1, Ctx; now left]. }
  eapply IE; [apply Ctx; now left|apply DI2].
  eapply IE; [|exact Hnot].
  eapply Weak; [exact H|]; intros chi Hchi; now right.
Qed.

Lemma native_disjunction_dual G (phi psi : C.set_form) :
  G ⊢RI (phi ∨ psi) -> G ⊢RI (¬ phi → psi).
Proof.
  intro H; apply II.
  assert (Hsum : (¬ phi) :: G ⊢RI phi ∨ psi).
  { eapply Weak; [exact H|]; intros chi Hchi; now right. }
  eapply DE; [exact Hsum| |].
  - apply Exp; eapply IE; [apply Ctx; right; now left|apply Ctx; now left].
  - apply Ctx; now left.
Qed.

Lemma dual_existential_native G (phi : C.set_form) :
  G ⊢RI ¬ (∀ ¬ phi) -> G ⊢RI ∃ phi.
Proof.
  intro H; apply DN, II; eapply IE.
  - eapply Weak; [exact H|]; intros chi Hchi; now right.
  - apply AllI_named; intro t; apply II.
    eapply IE; [apply Ctx; right; now left|].
    apply (ExI t), Ctx; now left.
Qed.

Lemma native_existential_dual G (phi : C.set_form) :
  G ⊢RI ∃ phi -> G ⊢RI ¬ (∀ ¬ phi).
Proof.
  intro H; apply II.
  assert (Hex : (∀ ¬ phi) :: G ⊢RI ∃ phi).
  { eapply Weak; [exact H|]; intros chi Hchi; now right. }
  eapply ExE_named; [exact Hex|]; intro t.
  assert (Hall : phi[t..] :: (∀ ¬ phi) :: G ⊢RI ∀ ¬ phi).
  { apply Ctx; right; now left. }
  eapply IE; [exact (AllE t Hall)|apply Ctx; now left].
Qed.

(** The forward schema transport obtains this IR proof from the
    actual derived numeric supplier; it is not an axiom of its S0 producer. *)
Lemma native_falsity_alias G t : G ⊢RI C.ir ->
  G ⊢RI (C.R t t → ⊥) /\ G ⊢RI (⊥ → C.R t t).
Proof.
  intro HIR; split; [apply C.ir_guard; exact HIR|].
  apply II, Exp, Ctx; now left.
Qed.

Print Assumptions dual_conjunction_left.
Print Assumptions dual_disjunction_native.
Print Assumptions dual_existential_native.
Print Assumptions native_existential_dual.
Print Assumptions native_falsity_alias.
End RawInterpret238.
