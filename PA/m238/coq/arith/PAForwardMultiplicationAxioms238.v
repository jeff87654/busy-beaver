(** Exact pinned FA multiplication axioms. The successor right-hand side
    uses fixed operand plus old product, as in the upstream PA signature;
    the uniformly derived graph law supplies this orientation. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 IsoGraph238
  AddGraph238 MulGraph238 MulPALaws238 PAForwardTerms238 PAForwardFormula238
  PAForwardEquality238 PAForwardEqualityLaws238 PAForwardBasis238 PAForwardTotal238
  PAForwardFormulaBasis238 PAForwardQuantifier238 PAForwardCongruence238 PAForwardBinaryCongruence238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 IsoGraph238.IsoGraph238
  AddGraph238.AddGraph238 MulGraph238.MulGraph238 MulPALaws238.MulPALaws238
  PAForwardTerms238.PAForwardTerms238 PAForwardFormula238.PAForwardFormula238
  PAForwardEquality238.PAForwardEquality238 PAForwardEqualityLaws238.PAForwardEqualityLaws238
  PAForwardBasis238.PAForwardBasis238 PAForwardTotal238.PAForwardTotal238
  PAForwardFormulaBasis238.PAForwardFormulaBasis238 PAForwardQuantifier238.PAForwardQuantifier238
  PAForwardCongruence238.PAForwardCongruence238 PAForwardBinaryCongruence238.PAForwardBinaryCongruence238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardMultiplicationAxioms238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma interpreted_multiplication_zero G u rho y :
  G ⊢238 formula_transport_basis -> G ⊢238 mul_left_zero_ax ->
  G ⊢238 pa_term_value u rho y -> G ⊢238 interpreted_equality (pa_multiplication pa_zero u) pa_zero rho.
Proof.
  intros HB HM HU. eapply ExE_named.
  - apply (pa_term_value_total G pa_zero rho); [exact (CE1 HB)|apply II, Ctx; now left].
  - intro e. rewrite pa_term_value_witness_specialize.
    assert (HE : (pa_term_value pa_zero rho e :: G) ⊢238 pa_term_value pa_zero rho e).
    { apply Ctx. now left. }
    eapply (binary_result_elim _ mul_result e y).
    + exact source_mul_result_subst.
    + apply term_basis_multiplication; [inherit (CE1 HB)|exact (CE1 HE)|].
      apply (pa_term_value_ordinal _ u rho y). inherit HU.
    + intro z.
      assert (HP : (mul_result e y z :: pa_term_value pa_zero rho e :: G) ⊢238 mul_result e y z).
      { apply Ctx. now left. }
      apply (interpreted_equality_intro _ (pa_multiplication pa_zero u) pa_zero rho z e).
      * apply (multiplication_value_intro _ pa_zero u rho e y z); [inherit HE|inherit HU|exact HP].
      * inherit HE.
      * apply (mul_left_zero_instance _ e y z e).
        -- inherit HM.
        -- inherit (CE1 HE).
        -- inherit (CE2 HE).
        -- apply (pa_term_value_ordinal _ u rho y). inherit HU.
        -- inherit (CE2 HE).
        -- exact HP.
Qed.

Lemma interpreted_multiplication_recursion G t u rho x y :
  G ⊢238 formula_transport_basis -> G ⊢238 mul_left_successor_ax ->
  G ⊢238 pa_term_value t rho x -> G ⊢238 pa_term_value u rho y ->
  G ⊢238 interpreted_equality (pa_multiplication (pa_successor t) u)
    (pa_addition u (pa_multiplication t u)) rho.
Proof.
  intros HB HM HT HU. eapply (represented_successor_elim G x).
  - apply term_basis_successor; [exact (CE1 HB)|exact (pa_term_value_ordinal G t rho x HT)].
  - intro sx.
    assert (HSX : (ordinal_representative sx ∧ raw_successor x sx :: G)
      ⊢238 (ordinal_representative sx ∧ raw_successor x sx)).
    { apply Ctx. now left. }
    eapply (binary_result_elim _ mul_result x y).
    + exact source_mul_result_subst.
    + apply term_basis_multiplication; [inherit (CE1 HB)| |].
      * apply (pa_term_value_ordinal _ t rho x). inherit HT.
      * apply (pa_term_value_ordinal _ u rho y). inherit HU.
    + intro p.
      assert (HP : (mul_result x y p :: ordinal_representative sx ∧ raw_successor x sx :: G)
        ⊢238 mul_result x y p).
      { apply Ctx. now left. }
      eapply (binary_result_elim _ mul_result sx y).
      * exact source_mul_result_subst.
      * apply term_basis_multiplication; [inherit (CE1 HB)|inherit (CE1 HSX)|].
        apply (pa_term_value_ordinal _ u rho y). inherit HU.
      * intro z.
        assert (HZ : (mul_result sx y z :: mul_result x y p ::
          ordinal_representative sx ∧ raw_successor x sx :: G) ⊢238 mul_result sx y z).
        { apply Ctx. now left. }
        eapply (binary_result_elim _ add_result y p).
        -- exact source_add_result_subst.
        -- apply term_basis_addition; [inherit (CE1 HB)| |].
           ++ apply (pa_term_value_ordinal _ u rho y). inherit HU.
           ++ apply (mul_result_ordinal _ x y p). inherit HP.
        -- intro w.
           assert (HW : (add_result y p w :: mul_result sx y z :: mul_result x y p ::
             ordinal_representative sx ∧ raw_successor x sx :: G) ⊢238 add_result y p w).
           { apply Ctx. now left. }
           apply (interpreted_equality_intro _ (pa_multiplication (pa_successor t) u)
             (pa_addition u (pa_multiplication t u)) rho z w).
           ++ apply (multiplication_value_intro _ (pa_successor t) u rho sx y z).
              ** apply (successor_value_intro _ t rho x sx);
                   [inherit (CE1 HSX)|inherit HT|inherit (CE2 HSX)].
              ** inherit HU.
              ** inherit HZ.
           ++ apply (addition_value_intro _ u (pa_multiplication t u) rho y p w).
              ** inherit HU.
              ** apply (multiplication_value_intro _ t u rho x y p); [inherit HT|inherit HU|inherit HP].
              ** exact HW.
           ++ apply (mul_left_successor_instance _ x sx y p z w).
              ** inherit HM.
              ** apply (pa_term_value_ordinal _ t rho x). inherit HT.
              ** inherit (CE1 HSX).
              ** apply (pa_term_value_ordinal _ u rho y). inherit HU.
              ** inherit (CE2 HSX).
              ** inherit HP.
              ** inherit HZ.
              ** exact HW.
Qed.

Lemma interpreted_pa_multiplication_zero_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 mul_left_zero_ax ->
  G ⊢238 pa_formula_value ax_mult_zero rho.
Proof.
  intros HB HM. change (G ⊢238 pa_formula_value
    (∀ pa_equality_formula (pa_multiplication pa_zero (pa_variable 0)) pa_zero) rho).
  apply interpreted_all_introduce. intro y.
  apply (interpreted_multiplication_zero _ (pa_variable 0) (y .: rho) y).
  - inherit HB.
  - inherit HM.
  - apply (variable_value_intro _ (y .: rho) 0); [inherit (CE1 (CE1 (CE2 HB)))|apply Ctx; now left].
Qed.

Lemma interpreted_pa_multiplication_recursion_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 mul_left_successor_ax ->
  G ⊢238 pa_formula_value ax_mult_rec rho.
Proof.
  intros HB HM. change (G ⊢238 pa_formula_value
    (∀ ∀ pa_equality_formula (pa_multiplication (pa_successor (pa_variable 1)) (pa_variable 0))
      (pa_addition (pa_variable 0) (pa_multiplication (pa_variable 1) (pa_variable 0)))) rho).
  apply interpreted_all_introduce. intro x.
  assert (HX : (ordinal_representative x :: G) ⊢238 ordinal_representative x).
  { apply Ctx. now left. }
  apply interpreted_all_introduce. intro y.
  apply (interpreted_multiplication_recursion _ (pa_variable 1) (pa_variable 0) (y .: x .: rho) x y).
  - inherit HB.
  - inherit HM.
  - apply (variable_value_intro _ (y .: x .: rho) 1); [inherit (CE1 (CE1 (CE2 HB)))|inherit HX].
  - apply (variable_value_intro _ (y .: x .: rho) 0);
      [inherit (CE1 (CE1 (CE2 HB)))|apply Ctx; now left].
Qed.

Theorem S0_pa_multiplication_zero_axiom rho : derivable finite_set_S0 (pa_formula_value ax_mult_zero rho).
Proof.
  destruct S0_formula_transport_basis as [Gb [HGb HB]].
  destruct S0_mul_left_zero_closed as [Gz [HGz HM]]. set (G := Gb ++ Gz).
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGb|now apply HGz].
  - apply interpreted_pa_multiplication_zero_axiom.
    + eapply Weak; [exact HB|]. intros psi Hpsi. unfold G. apply in_or_app. now left.
    + eapply Weak; [exact HM|]. intros psi Hpsi. unfold G. apply in_or_app. now right.
Qed.

Theorem S0_pa_multiplication_recursion_axiom rho : derivable finite_set_S0 (pa_formula_value ax_mult_rec rho).
Proof.
  destruct S0_formula_transport_basis as [Gb [HGb HB]].
  destruct S0_mul_left_successor_closed as [Gs [HGs HM]]. set (G := Gb ++ Gs).
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGb|now apply HGs].
  - apply interpreted_pa_multiplication_recursion_axiom.
    + eapply Weak; [exact HB|]. intros psi Hpsi. unfold G. apply in_or_app. now left.
    + eapply Weak; [exact HM|]. intros psi Hpsi. unfold G. apply in_or_app. now right.
Qed.

Print Assumptions interpreted_multiplication_zero.
Print Assumptions interpreted_multiplication_recursion.
Print Assumptions interpreted_pa_multiplication_zero_axiom.
Print Assumptions interpreted_pa_multiplication_recursion_axiom.
Print Assumptions S0_pa_multiplication_zero_axiom.
Print Assumptions S0_pa_multiplication_recursion_axiom.
End PAForwardMultiplicationAxioms238.
