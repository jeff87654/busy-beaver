(** Actual finite equality transport through ordinary PA substitution.
    Both directions select source term values by the derived totality
    theorem and combine the actual Iso graphs by inverse and composition. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 IsoGraph238
  PAForwardTerms238 PAForwardFormula238 PAForwardEquality238 PAForwardTotal238
  PAForwardCoherenceBasis238 PAForwardDeterminacy238 PAForwardSubstitution238
  PAForwardSubstitutionGuard238 PAForwardFormulaBasis238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 IsoGraph238.IsoGraph238
  PAForwardTerms238.PAForwardTerms238 PAForwardFormula238.PAForwardFormula238
  PAForwardEquality238.PAForwardEquality238 PAForwardTotal238.PAForwardTotal238
  PAForwardCoherenceBasis238.PAForwardCoherenceBasis238 PAForwardDeterminacy238.PAForwardDeterminacy238
  PAForwardSubstitution238.PAForwardSubstitution238
  PAForwardSubstitutionGuard238.PAForwardSubstitutionGuard238
  PAForwardFormulaBasis238.PAForwardFormulaBasis238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardAtomicSubstitution238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma interpreted_equality_substitution_forward G t u sigma rho tau :
  G ⊢238 formula_transport_basis ->
  G ⊢238 pa_substitution_values t sigma rho tau ->
  G ⊢238 pa_substitution_values u sigma rho tau ->
  G ⊢238 interpreted_equality (t`[sigma]) (u`[sigma]) rho ->
  G ⊢238 interpreted_equality t u tau.
Proof.
  intros HB HT HU HE. apply (interpreted_equality_elim G (t`[sigma]) (u`[sigma]) rho _ HE).
  intros z w.
  assert (HJ : (pa_term_value (t`[sigma]) rho z ∧
    (pa_term_value (u`[sigma]) rho w ∧ order_iso z w) :: G)
      ⊢238 (pa_term_value (t`[sigma]) rho z ∧
        (pa_term_value (u`[sigma]) rho w ∧ order_iso z w))).
  { apply Ctx. now left. }
  eapply ExE_named.
  - apply (pa_term_value_total _ t tau).
    + inherit (CE1 HB).
    + apply (pa_substitution_values_domains t _ sigma rho tau). inherit HT.
  - intro x. rewrite pa_term_value_witness_specialize.
    assert (HX : (pa_term_value t tau x :: pa_term_value (t`[sigma]) rho z ∧
      (pa_term_value (u`[sigma]) rho w ∧ order_iso z w) :: G) ⊢238 pa_term_value t tau x).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (pa_term_value_total _ u tau).
      * inherit (CE1 HB).
      * apply (pa_substitution_values_domains u _ sigma rho tau). inherit HU.
    + intro y. rewrite pa_term_value_witness_specialize.
      assert (HY : (pa_term_value u tau y :: pa_term_value t tau x ::
        pa_term_value (t`[sigma]) rho z ∧
          (pa_term_value (u`[sigma]) rho w ∧ order_iso z w) :: G)
            ⊢238 pa_term_value u tau y).
      { apply Ctx. now left. }
      apply (interpreted_equality_intro _ t u tau x y); [inherit HX|exact HY|].
      apply (formula_basis_iso_transitive _ x w y).
      * inherit HB.
      * apply (pa_term_value_ordinal _ t tau x). inherit HX.
      * apply (formula_basis_iso_transitive _ x z w).
        -- inherit HB.
        -- apply (pa_term_value_ordinal _ t tau x). inherit HX.
        -- apply (formula_basis_iso_symmetric _ z x).
           ++ inherit HB.
           ++ apply (pa_term_value_ordinal _ (t`[sigma]) rho z). inherit (CE1 HJ).
           ++ apply (pa_term_value_pa_substitution t _ sigma rho tau z x).
              ** inherit (CE1 (CE2 HB)).
              ** inherit (CE1 (CE2 (CE2 HB))).
              ** inherit HT.
              ** inherit (CE1 HJ).
              ** inherit HX.
        -- inherit (CE2 (CE2 HJ)).
      * apply (pa_term_value_pa_substitution u _ sigma rho tau w y).
        -- inherit (CE1 (CE2 HB)).
        -- inherit (CE1 (CE2 (CE2 HB))).
        -- inherit HU.
        -- inherit (CE1 (CE2 HJ)).
        -- exact HY.
Qed.

Lemma interpreted_equality_substitution_backward G t u sigma rho tau :
  G ⊢238 formula_transport_basis ->
  G ⊢238 pa_substitution_values t sigma rho tau ->
  G ⊢238 pa_substitution_values u sigma rho tau ->
  G ⊢238 interpreted_equality t u tau ->
  G ⊢238 interpreted_equality (t`[sigma]) (u`[sigma]) rho.
Proof.
  intros HB HT HU HE. apply (interpreted_equality_elim G t u tau _ HE).
  intros x y.
  assert (HJ : (pa_term_value t tau x ∧ (pa_term_value u tau y ∧ order_iso x y) :: G)
    ⊢238 (pa_term_value t tau x ∧ (pa_term_value u tau y ∧ order_iso x y))).
  { apply Ctx. now left. }
  eapply ExE_named.
  - apply (pa_term_value_total _ (t`[sigma]) rho).
    + inherit (CE1 HB).
    + apply (pa_substitution_values_input_domains t _ sigma rho tau).
      * inherit (CE1 (CE1 (CE2 HB))).
      * inherit (CE1 (CE2 (CE1 (CE2 HB)))).
      * inherit (CE1 (CE2 (CE2 (CE1 (CE2 HB))))).
      * inherit HT.
  - intro z. rewrite pa_term_value_witness_specialize.
    assert (HZ : (pa_term_value (t`[sigma]) rho z ::
      pa_term_value t tau x ∧ (pa_term_value u tau y ∧ order_iso x y) :: G)
        ⊢238 pa_term_value (t`[sigma]) rho z).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (pa_term_value_total _ (u`[sigma]) rho).
      * inherit (CE1 HB).
      * apply (pa_substitution_values_input_domains u _ sigma rho tau).
        -- inherit (CE1 (CE1 (CE2 HB))).
        -- inherit (CE1 (CE2 (CE1 (CE2 HB)))).
        -- inherit (CE1 (CE2 (CE2 (CE1 (CE2 HB))))).
        -- inherit HU.
    + intro w. rewrite pa_term_value_witness_specialize.
      assert (HW : (pa_term_value (u`[sigma]) rho w :: pa_term_value (t`[sigma]) rho z ::
        pa_term_value t tau x ∧ (pa_term_value u tau y ∧ order_iso x y) :: G)
          ⊢238 pa_term_value (u`[sigma]) rho w).
      { apply Ctx. now left. }
      apply (interpreted_equality_intro _ (t`[sigma]) (u`[sigma]) rho z w); [inherit HZ|exact HW|].
      apply (formula_basis_iso_transitive _ z y w).
      * inherit HB.
      * apply (pa_term_value_ordinal _ (t`[sigma]) rho z). inherit HZ.
      * apply (formula_basis_iso_transitive _ z x y).
        -- inherit HB.
        -- apply (pa_term_value_ordinal _ (t`[sigma]) rho z). inherit HZ.
        -- apply (pa_term_value_pa_substitution t _ sigma rho tau z x).
           ++ inherit (CE1 (CE2 HB)).
           ++ inherit (CE1 (CE2 (CE2 HB))).
           ++ inherit HT.
           ++ inherit HZ.
           ++ inherit (CE1 HJ).
        -- inherit (CE2 (CE2 HJ)).
      * apply (formula_basis_iso_symmetric _ w y).
        -- inherit HB.
        -- apply (pa_term_value_ordinal _ (u`[sigma]) rho w). exact HW.
        -- apply (pa_term_value_pa_substitution u _ sigma rho tau w y).
           ++ inherit (CE1 (CE2 HB)).
           ++ inherit (CE1 (CE2 (CE2 HB))).
           ++ inherit HU.
           ++ exact HW.
           ++ inherit (CE1 (CE2 HJ)).
Qed.

Theorem S0_interpreted_equality_substitution t u sigma rho tau :
  derivable finite_set_S0
    (pa_substitution_values t sigma rho tau →
      (pa_substitution_values u sigma rho tau →
        (interpreted_equality (t`[sigma]) (u`[sigma]) rho ↔ interpreted_equality t u tau))).
Proof.
  destruct S0_formula_transport_basis as [G [HG HB]]. exists G. split; [exact HG|].
  apply II, II, CI.
  - apply II, (interpreted_equality_substitution_forward _ t u sigma rho tau).
    + inherit HB.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
  - apply II, (interpreted_equality_substitution_backward _ t u sigma rho tau).
    + inherit HB.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Print Assumptions interpreted_equality_substitution_forward.
Print Assumptions interpreted_equality_substitution_backward.
Print Assumptions S0_interpreted_equality_substitution.
End PAForwardAtomicSubstitution238.
