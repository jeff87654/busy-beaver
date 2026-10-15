(** Ordinary fully universally closed PAeq refutation to compact set
    theory, by actual finite classical natural-deduction transport.
    Arithmetic functions are realized by retained finite graphs; the
    induction family is the derived S0 minimum-counterexample proof. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 S0InCompact238
  AddPALaws238 MulPALaws238 PAForwardFormula238 PAForwardFinite238 PAForwardEQFamilies238
  PAForwardAdditionAxioms238 PAForwardMultiplicationAxioms238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 S0InCompact238.S0InCompact238
  AddPALaws238.AddPALaws238 MulPALaws238.MulPALaws238
  PAForwardFormula238.PAForwardFormula238 PAForwardFinite238.PAForwardFinite238
  PAForwardEQFamilies238.PAForwardEQFamilies238
  PAForwardAdditionAxioms238.PAForwardAdditionAxioms238
  PAForwardMultiplicationAxioms238.PAForwardMultiplicationAxioms238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForward238.

Theorem pa_FA_proof_family (phi : PA238.pa_form) :
  List.In phi FA -> pa_axiom_proof_family phi.
Proof.
  unfold FA. intros [<-|[<-|[<-|[<-|[]]]]].
  - apply (pa_family_from_formula_basis_and_law ax_add_zero add_left_zero_ax S0_add_left_zero_closed).
    exact interpreted_pa_addition_zero_axiom.
  - apply (pa_family_from_formula_basis_and_law ax_add_rec add_left_successor_ax S0_add_left_successor_closed).
    exact interpreted_pa_addition_recursion_axiom.
  - apply (pa_family_from_formula_basis_and_law ax_mult_zero mul_left_zero_ax S0_mul_left_zero_closed).
    exact interpreted_pa_multiplication_zero_axiom.
  - apply (pa_family_from_formula_basis_and_law ax_mult_rec mul_left_successor_ax S0_mul_left_successor_closed).
    exact interpreted_pa_multiplication_recursion_axiom.
Qed.

Theorem pa_PAeq_proof_family (phi : PA238.pa_form) :
  PAeq phi -> pa_axiom_proof_family phi.
Proof.
  intro Hphi. destruct Hphi as [phi Hphi| | |phi].
  - unfold FAeq in Hphi. apply in_app_or in Hphi as [Hphi|Hphi].
    + exact (pa_EQ_proof_family phi Hphi).
    + exact (pa_FA_proof_family phi Hphi).
  - exact pa_zero_discrimination_proof_family.
  - exact pa_successor_injectivity_proof_family.
  - exact (pa_induction_proof_family phi).
Qed.

Theorem ordinary_PAeq_proof_family (phi : PA238.pa_form) :
  PA238.ordinary_PAeq phi -> pa_axiom_proof_family phi.
Proof.
  intros [psi [Hpsi <-]]. apply pa_axiom_proof_family_close.
  exact (pa_PAeq_proof_family psi Hpsi).
Qed.

Theorem ordinary_PAeq_refutation_to_S0 :
  PA238.PAeq_inconsistent -> derivable finite_set_S0 falsity.
Proof.
  intros [A [HA HP]]. apply (finite_pa_refutation_from_proof_families A).
  - intros phi Hphi. exact (ordinary_PAeq_proof_family phi (HA phi Hphi)).
  - exact HP.
Qed.

Theorem ordinary_PAeq_refutation_to_compact :
  PA238.PAeq_inconsistent -> derivable compact_theory falsity.
Proof. intro H. apply S0_to_compact, ordinary_PAeq_refutation_to_S0, H. Qed.

Print Assumptions pa_FA_proof_family.
Print Assumptions pa_PAeq_proof_family.
Print Assumptions ordinary_PAeq_proof_family.
Print Assumptions ordinary_PAeq_refutation_to_S0.
Print Assumptions ordinary_PAeq_refutation_to_compact.
End PAForward238.
