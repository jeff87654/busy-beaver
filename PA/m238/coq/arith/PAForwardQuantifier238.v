(** Concrete quantifier rules for the finite PA natural-deduction compiler.
    Term instantiation first obtains an actual represented ordinal value. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238
  PAForwardTerms238 PAForwardFormula238 PAForwardTotal238 PAForwardSubstitutionGuard238
  PAForwardFormulaBasis238 PAForwardFormulaSubstitution238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  PAForwardTerms238.PAForwardTerms238 PAForwardFormula238.PAForwardFormula238
  PAForwardTotal238.PAForwardTotal238 PAForwardSubstitutionGuard238.PAForwardSubstitutionGuard238
  PAForwardFormulaBasis238.PAForwardFormulaBasis238
  PAForwardFormulaSubstitution238.PAForwardFormulaSubstitution238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardQuantifier238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma pa_term_domains_from_environment G t rho :
  G ⊢238 (∀ E $0 $0) -> (forall n, G ⊢238 ordinal_representative (rho n)) ->
  G ⊢238 pa_term_domains t rho.
Proof.
  intros HE HD.
  apply (pa_substitution_values_domains t G (@var PA_funcs_signature) rho rho).
  apply pa_substitution_values_from_environment. intro n.
  apply variable_value_intro; [exact HE|exact (HD n)].
Qed.

Lemma interpreted_all_introduce G (phi : PA238.pa_form) rho :
  (forall x, (ordinal_representative x :: G) ⊢238 pa_formula_value phi (x .: rho)) ->
  G ⊢238 pa_formula_value (∀ phi) rho.
Proof.
  intro HI. change (G ⊢238 ∀ (ordinal_representative $0 →
    pa_formula_value phi (source_binder_environment rho))).
  apply AllI_named. intro x.
  change (G ⊢238 (ordinal_representative x →
    (pa_formula_value phi (source_binder_environment rho))[x..])).
  rewrite pa_formula_value_binder_witness. apply II. exact (HI x).
Qed.

Lemma interpreted_all_eliminate G (phi : PA238.pa_form) u rho :
  G ⊢238 formula_transport_basis -> (forall n, G ⊢238 ordinal_representative (rho n)) ->
  G ⊢238 pa_formula_value (∀ phi) rho -> G ⊢238 pa_formula_value (phi[u..]) rho.
Proof.
  intros HB HD HA. eapply ExE_named.
  - apply (pa_term_value_total G u rho); [exact (CE1 HB)|].
    apply pa_term_domains_from_environment; [exact (CE1 (CE1 (CE2 HB)))|exact HD].
  - intro x. rewrite pa_term_value_witness_specialize.
    assert (HV : (pa_term_value u rho x :: G) ⊢238 pa_term_value u rho x).
    { apply Ctx. now left. }
    eapply IE; [eapply CE2|].
    + apply (pa_formula_value_single_substitution _ phi u rho x).
      * inherit HB.
      * exact HV.
      * intro n. inherit (HD n).
    + change (G ⊢238 ∀ (ordinal_representative $0 →
        pa_formula_value phi (source_binder_environment rho))) in HA.
      pose proof (AllE x HA) as Hx.
      change (G ⊢238 (ordinal_representative x →
        (pa_formula_value phi (source_binder_environment rho))[x..])) in Hx.
      rewrite pa_formula_value_binder_witness in Hx.
      eapply IE; [inherit Hx|]. apply (pa_term_value_ordinal _ u rho x). exact HV.
Qed.

Lemma interpreted_exists_introduce G (phi : PA238.pa_form) u rho :
  G ⊢238 formula_transport_basis -> (forall n, G ⊢238 ordinal_representative (rho n)) ->
  G ⊢238 pa_formula_value (phi[u..]) rho -> G ⊢238 pa_formula_value (∃ phi) rho.
Proof.
  intros HB HD HP. eapply ExE_named.
  - apply (pa_term_value_total G u rho); [exact (CE1 HB)|].
    apply pa_term_domains_from_environment; [exact (CE1 (CE1 (CE2 HB)))|exact HD].
  - intro x. rewrite pa_term_value_witness_specialize.
    assert (HV : (pa_term_value u rho x :: G) ⊢238 pa_term_value u rho x).
    { apply Ctx. now left. }
    change ((pa_term_value u rho x :: G) ⊢238 ∃ (ordinal_representative $0 ∧
      pa_formula_value phi (source_binder_environment rho))).
    apply (ExI x).
    change ((pa_term_value u rho x :: G) ⊢238 (ordinal_representative x ∧
      (pa_formula_value phi (source_binder_environment rho))[x..])).
    rewrite pa_formula_value_binder_witness. apply CI.
    + apply (pa_term_value_ordinal _ u rho x). exact HV.
    + eapply IE; [eapply CE1|inherit HP].
      apply (pa_formula_value_single_substitution _ phi u rho x).
      * inherit HB.
      * exact HV.
      * intro n. inherit (HD n).
Qed.

Lemma interpreted_exists_eliminate G (phi : PA238.pa_form) rho (chi : set_form) :
  G ⊢238 pa_formula_value (∃ phi) rho ->
  (forall x, (ordinal_representative x ∧ pa_formula_value phi (x .: rho) :: G) ⊢238 chi) ->
  G ⊢238 chi.
Proof.
  intros HE HC. change (G ⊢238 ∃ (ordinal_representative $0 ∧
    pa_formula_value phi (source_binder_environment rho))) in HE.
  eapply ExE_named; [exact HE|]. intro x.
  change ((ordinal_representative x ∧
    (pa_formula_value phi (source_binder_environment rho))[x..] :: G) ⊢238 chi).
  rewrite pa_formula_value_binder_witness. exact (HC x).
Qed.

Print Assumptions pa_term_domains_from_environment.
Print Assumptions interpreted_all_introduce.
Print Assumptions interpreted_all_eliminate.
Print Assumptions interpreted_exists_introduce.
Print Assumptions interpreted_exists_eliminate.
End PAForwardQuantifier238.
