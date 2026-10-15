(** Exact pinned FA addition axioms are derived from actual term values
    and the uniformly derived zero and successor trace laws. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 IsoGraph238 AddGraph238 AddPALaws238
  PAForwardTerms238 PAForwardFormula238 PAForwardEquality238 PAForwardEqualityLaws238
  PAForwardBasis238 PAForwardTotal238 PAForwardFormulaBasis238 PAForwardQuantifier238
  PAForwardCongruence238 PAForwardBinaryCongruence238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 IsoGraph238.IsoGraph238
  AddGraph238.AddGraph238 AddPALaws238.AddPALaws238 PAForwardTerms238.PAForwardTerms238
  PAForwardFormula238.PAForwardFormula238 PAForwardEquality238.PAForwardEquality238
  PAForwardEqualityLaws238.PAForwardEqualityLaws238 PAForwardBasis238.PAForwardBasis238
  PAForwardTotal238.PAForwardTotal238 PAForwardFormulaBasis238.PAForwardFormulaBasis238
  PAForwardQuantifier238.PAForwardQuantifier238 PAForwardCongruence238.PAForwardCongruence238
  PAForwardBinaryCongruence238.PAForwardBinaryCongruence238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardAdditionAxioms238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma interpreted_addition_zero G u rho y :
  G ⊢238 formula_transport_basis -> G ⊢238 add_left_zero_ax ->
  G ⊢238 pa_term_value u rho y -> G ⊢238 interpreted_equality (pa_addition pa_zero u) u rho.
Proof.
  intros HB HZ HU. eapply ExE_named.
  - apply (pa_term_value_total G pa_zero rho); [exact (CE1 HB)|apply II, Ctx; now left].
  - intro e. rewrite pa_term_value_witness_specialize.
    assert (HE : (pa_term_value pa_zero rho e :: G) ⊢238 pa_term_value pa_zero rho e).
    { apply Ctx. now left. }
    eapply (binary_result_elim _ add_result e y).
    + exact source_add_result_subst.
    + apply term_basis_addition; [inherit (CE1 HB)|exact (CE1 HE)|].
      apply (pa_term_value_ordinal _ u rho y). inherit HU.
    + intro z.
      assert (HA : (add_result e y z :: pa_term_value pa_zero rho e :: G) ⊢238 add_result e y z).
      { apply Ctx. now left. }
      apply (interpreted_equality_intro _ (pa_addition pa_zero u) u rho z y).
      * apply (addition_value_intro _ pa_zero u rho e y z); [inherit HE|inherit HU|exact HA].
      * inherit HU.
      * apply (add_left_zero_instance _ e y z).
        -- inherit HZ.
        -- inherit (CE1 HE).
        -- inherit (CE2 HE).
        -- apply (pa_term_value_ordinal _ u rho y). inherit HU.
        -- exact HA.
Qed.

Lemma interpreted_addition_recursion G t u rho x y :
  G ⊢238 formula_transport_basis -> G ⊢238 add_left_successor_ax ->
  G ⊢238 pa_term_value t rho x -> G ⊢238 pa_term_value u rho y ->
  G ⊢238 interpreted_equality (pa_addition (pa_successor t) u) (pa_successor (pa_addition t u)) rho.
Proof.
  intros HB HS HT HU. eapply (represented_successor_elim G x).
  - apply term_basis_successor; [exact (CE1 HB)|exact (pa_term_value_ordinal G t rho x HT)].
  - intro sx.
    assert (HSX : (ordinal_representative sx ∧ raw_successor x sx :: G)
      ⊢238 (ordinal_representative sx ∧ raw_successor x sx)).
    { apply Ctx. now left. }
    eapply (binary_result_elim _ add_result x y).
    + exact source_add_result_subst.
    + apply term_basis_addition; [inherit (CE1 HB)| |].
      * apply (pa_term_value_ordinal _ t rho x). inherit HT.
      * apply (pa_term_value_ordinal _ u rho y). inherit HU.
    + intro z.
      assert (HZ : (add_result x y z :: ordinal_representative sx ∧ raw_successor x sx :: G)
        ⊢238 add_result x y z).
      { apply Ctx. now left. }
      eapply (represented_successor_elim _ z).
      * apply term_basis_successor; [inherit (CE1 HB)|exact (add_result_ordinal _ x y z HZ)].
      * intro sz.
        assert (HSZ : (ordinal_representative sz ∧ raw_successor z sz :: add_result x y z ::
          ordinal_representative sx ∧ raw_successor x sx :: G)
            ⊢238 (ordinal_representative sz ∧ raw_successor z sz)).
        { apply Ctx. now left. }
        eapply (binary_result_elim _ add_result sx y).
        -- exact source_add_result_subst.
        -- apply term_basis_addition; [inherit (CE1 HB)|inherit (CE1 HSX)|].
           apply (pa_term_value_ordinal _ u rho y). inherit HU.
        -- intro w.
           assert (HW : (add_result sx y w :: ordinal_representative sz ∧ raw_successor z sz ::
             add_result x y z :: ordinal_representative sx ∧ raw_successor x sx :: G)
               ⊢238 add_result sx y w).
           { apply Ctx. now left. }
           apply (interpreted_equality_intro _ (pa_addition (pa_successor t) u)
             (pa_successor (pa_addition t u)) rho w sz).
           ++ apply (addition_value_intro _ (pa_successor t) u rho sx y w).
              ** apply (successor_value_intro _ t rho x sx);
                   [inherit (CE1 HSX)|inherit HT|inherit (CE2 HSX)].
              ** inherit HU.
              ** exact HW.
           ++ apply (successor_value_intro _ (pa_addition t u) rho z sz).
              ** inherit (CE1 HSZ).
              ** apply (addition_value_intro _ t u rho x y z); [inherit HT|inherit HU|inherit HZ].
              ** inherit (CE2 HSZ).
           ++ apply (add_left_successor_instance _ x sx y z sz w).
              ** inherit HS.
              ** apply (pa_term_value_ordinal _ t rho x). inherit HT.
              ** apply (pa_term_value_ordinal _ u rho y). inherit HU.
              ** inherit (CE2 HSX).
              ** inherit HZ.
              ** inherit (CE2 HSZ).
              ** exact HW.
Qed.

Lemma interpreted_pa_addition_zero_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 add_left_zero_ax ->
  G ⊢238 pa_formula_value ax_add_zero rho.
Proof.
  intros HB HZ. change (G ⊢238 pa_formula_value
    (∀ pa_equality_formula (pa_addition pa_zero (pa_variable 0)) (pa_variable 0)) rho).
  apply interpreted_all_introduce. intro y.
  apply (interpreted_addition_zero _ (pa_variable 0) (y .: rho) y).
  - inherit HB.
  - inherit HZ.
  - apply (variable_value_intro _ (y .: rho) 0); [inherit (CE1 (CE1 (CE2 HB)))|apply Ctx; now left].
Qed.

Lemma interpreted_pa_addition_recursion_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 add_left_successor_ax ->
  G ⊢238 pa_formula_value ax_add_rec rho.
Proof.
  intros HB HS. change (G ⊢238 pa_formula_value
    (∀ ∀ pa_equality_formula (pa_addition (pa_successor (pa_variable 0)) (pa_variable 1))
      (pa_successor (pa_addition (pa_variable 0) (pa_variable 1)))) rho).
  apply interpreted_all_introduce. intro y.
  assert (HY : (ordinal_representative y :: G) ⊢238 ordinal_representative y).
  { apply Ctx. now left. }
  apply interpreted_all_introduce. intro x.
  apply (interpreted_addition_recursion _ (pa_variable 0) (pa_variable 1) (x .: y .: rho) x y).
  - inherit HB.
  - inherit HS.
  - apply (variable_value_intro _ (x .: y .: rho) 0);
      [inherit (CE1 (CE1 (CE2 HB)))|apply Ctx; now left].
  - apply (variable_value_intro _ (x .: y .: rho) 1); [inherit (CE1 (CE1 (CE2 HB)))|inherit HY].
Qed.

Theorem S0_pa_addition_zero_axiom rho : derivable finite_set_S0 (pa_formula_value ax_add_zero rho).
Proof.
  destruct S0_formula_transport_basis as [Gb [HGb HB]].
  destruct S0_add_left_zero_closed as [Gz [HGz HZ]]. set (G := Gb ++ Gz).
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGb|now apply HGz].
  - apply interpreted_pa_addition_zero_axiom.
    + eapply Weak; [exact HB|]. intros psi Hpsi. unfold G. apply in_or_app. now left.
    + eapply Weak; [exact HZ|]. intros psi Hpsi. unfold G. apply in_or_app. now right.
Qed.

Theorem S0_pa_addition_recursion_axiom rho : derivable finite_set_S0 (pa_formula_value ax_add_rec rho).
Proof.
  destruct S0_formula_transport_basis as [Gb [HGb HB]].
  destruct S0_add_left_successor_closed as [Gs [HGs HS]]. set (G := Gb ++ Gs).
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGb|now apply HGs].
  - apply interpreted_pa_addition_recursion_axiom.
    + eapply Weak; [exact HB|]. intros psi Hpsi. unfold G. apply in_or_app. now left.
    + eapply Weak; [exact HS|]. intros psi Hpsi. unfold G. apply in_or_app. now right.
Qed.

Print Assumptions interpreted_addition_zero.
Print Assumptions interpreted_addition_recursion.
Print Assumptions interpreted_pa_addition_zero_axiom.
Print Assumptions interpreted_pa_addition_recursion_axiom.
Print Assumptions S0_pa_addition_zero_axiom.
Print Assumptions S0_pa_addition_recursion_axiom.
End PAForwardAdditionAxioms238.
