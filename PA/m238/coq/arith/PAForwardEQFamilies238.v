(** Concrete finite proof families for every equality and successor axiom
    of the pinned ordinary PAeq theory. Each family is chosen before any
    parameter or eigenvariable is introduced by a caller. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 IsoPALaws238
  PAForwardTerms238 PAForwardFormula238 PAForwardEqualityLaws238 PAForwardDeterminacy238
  PAForwardFormulaBasis238 PAForwardQuantifier238 PAForwardCongruence238
  PAForwardBinaryCongruence238 PAForwardSuccessorLaws238 PAForwardInduction238 PAForwardFinite238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 IsoPALaws238.IsoPALaws238
  PAForwardTerms238.PAForwardTerms238 PAForwardFormula238.PAForwardFormula238
  PAForwardEqualityLaws238.PAForwardEqualityLaws238 PAForwardDeterminacy238.PAForwardDeterminacy238
  PAForwardFormulaBasis238.PAForwardFormulaBasis238 PAForwardQuantifier238.PAForwardQuantifier238
  PAForwardCongruence238.PAForwardCongruence238 PAForwardBinaryCongruence238.PAForwardBinaryCongruence238
  PAForwardSuccessorLaws238.PAForwardSuccessorLaws238 PAForwardInduction238.PAForwardInduction238
  PAForwardFinite238.PAForwardFinite238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardEQFamilies238.

Lemma pa_family_from_formula_basis (phi : PA238.pa_form) :
  (forall G rho, G ⊢238 formula_transport_basis -> G ⊢238 pa_formula_value phi rho) ->
  pa_axiom_proof_family phi.
Proof.
  intro HP. destruct S0_formula_transport_basis as [G [HG HB]].
  exists G. split; [exact HG|]. intros D rho Hinc HD. apply HP.
  eapply Weak; [exact HB|exact Hinc].
Qed.

Lemma pa_family_from_formula_basis_and_law (phi : PA238.pa_form) (law : set_form) :
  derivable finite_set_S0 law ->
  (forall G rho, G ⊢238 formula_transport_basis -> G ⊢238 law -> G ⊢238 pa_formula_value phi rho) ->
  pa_axiom_proof_family phi.
Proof.
  intros [Gl [HGl HL]] HP.
  destruct S0_formula_transport_basis as [Gb [HGb HB]]. set (G := Gb ++ Gl).
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGb|now apply HGl].
  - intros D rho Hinc HD. apply HP.
    + eapply Weak; [exact HB|]. intros psi Hpsi. apply Hinc. unfold G. apply in_or_app. now left.
    + eapply Weak; [exact HL|]. intros psi Hpsi. apply Hinc. unfold G. apply in_or_app. now right.
Qed.

Lemma interpreted_pa_reflexivity_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 pa_formula_value ax_refl rho.
Proof.
  intro HB. change (G ⊢238 pa_formula_value
    (∀ pa_equality_formula (pa_variable 0) (pa_variable 0)) rho).
  apply interpreted_all_introduce. intro x.
  apply (interpreted_variable_equality_intro _ (x .: rho) 0 0).
  - apply weaken_one. exact HB.
  - apply Ctx. now left.
  - apply Ctx. now left.
  - apply (iso_reflexivity_instance _ x).
    + apply weaken_one. exact (CE1 (CE2 (CE2 HB))).
    + apply Ctx. now left.
Qed.

Theorem pa_EQ_proof_family (phi : PA238.pa_form) :
  List.In phi EQ -> pa_axiom_proof_family phi.
Proof.
  unfold EQ. intros [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  - apply pa_family_from_formula_basis. exact interpreted_pa_reflexivity_axiom.
  - apply pa_family_from_formula_basis. exact interpreted_pa_symmetry_axiom.
  - apply pa_family_from_formula_basis. exact interpreted_pa_transitivity_axiom.
  - apply pa_family_from_formula_basis. exact interpreted_pa_successor_congruence_axiom.
  - apply pa_family_from_formula_basis. exact interpreted_pa_addition_congruence_axiom.
  - apply pa_family_from_formula_basis. exact interpreted_pa_multiplication_congruence_axiom.
Qed.

Theorem pa_successor_injectivity_proof_family : pa_axiom_proof_family ax_succ_inj.
Proof.
  apply (pa_family_from_formula_basis_and_law ax_succ_inj iso_successor_injectivity_ax
    S0_order_iso_successor_injective_closed). exact interpreted_pa_successor_injectivity_axiom.
Qed.

Theorem pa_zero_discrimination_proof_family : pa_axiom_proof_family ax_zero_succ.
Proof.
  apply pa_family_from_formula_basis. exact interpreted_pa_zero_discrimination_axiom.
Qed.

Theorem pa_induction_proof_family (phi : PA238.pa_form) :
  pa_axiom_proof_family (ax_induction phi).
Proof. exact (S0_pa_induction_proof_family phi). Qed.

Print Assumptions pa_family_from_formula_basis.
Print Assumptions pa_family_from_formula_basis_and_law.
Print Assumptions interpreted_pa_reflexivity_axiom.
Print Assumptions pa_EQ_proof_family.
Print Assumptions pa_successor_injectivity_proof_family.
Print Assumptions pa_zero_discrimination_proof_family.
Print Assumptions pa_induction_proof_family.
End PAForwardEQFamilies238.
