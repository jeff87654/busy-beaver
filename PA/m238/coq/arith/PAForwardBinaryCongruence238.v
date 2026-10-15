(** Actual addition and multiplication congruence for interpreted PA
    equality. Every operand and result witness is retained in the finite
    derivation; joint comparison constructs the output Iso graph. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 IsoGraph238 AddGraph238 MulGraph238
  PAForwardTerms238 PAForwardFormula238 PAForwardEquality238 PAForwardEqualityLaws238
  PAForwardBasis238 PAForwardCoherenceBasis238 PAForwardFormulaBasis238 PAForwardQuantifier238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 IsoGraph238.IsoGraph238
  AddGraph238.AddGraph238 MulGraph238.MulGraph238 PAForwardTerms238.PAForwardTerms238
  PAForwardFormula238.PAForwardFormula238 PAForwardEquality238.PAForwardEquality238
  PAForwardEqualityLaws238.PAForwardEqualityLaws238 PAForwardBasis238.PAForwardBasis238
  PAForwardCoherenceBasis238.PAForwardCoherenceBasis238 PAForwardFormulaBasis238.PAForwardFormulaBasis238
  PAForwardQuantifier238.PAForwardQuantifier238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardBinaryCongruence238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma binary_result_body_specialize op x y z :
  (forall a b c sigma, (op a b c)[sigma] = op a`[sigma] b`[sigma] c`[sigma]) ->
  (op x`[↑] y`[↑] $0)[z..] = op x y z.
Proof.
  intro Hop. rewrite Hop.
  change (op x`[↑]`[z..] y`[↑]`[z..] z = op x y z).
  now rewrite !source_shift_witness_cancel.
Qed.

Lemma binary_result_elim G op x y (phi : set_form) :
  (forall a b c sigma, (op a b c)[sigma] = op a`[sigma] b`[sigma] c`[sigma]) ->
  G ⊢238 ∃ op x`[↑] y`[↑] $0 ->
  (forall z, (op x y z :: G) ⊢238 phi) -> G ⊢238 phi.
Proof.
  intros Hop HE HZ. eapply ExE_named; [exact HE|]. intro z.
  apply (derivation_head_replace G ((op x`[↑] y`[↑] $0)[z..]) (op x y z) phi).
  - exact (binary_result_body_specialize op x y z Hop).
  - exact (HZ z).
Qed.

Lemma interpreted_binary_congruence G op fop t t' u u' rho :
  (forall a b c sigma, (op a b c)[sigma] = op a`[sigma] b`[sigma] c`[sigma]) ->
  (forall D x y, D ⊢238 term_totality_basis ->
    D ⊢238 ordinal_representative x -> D ⊢238 ordinal_representative y ->
    D ⊢238 ∃ op x`[↑] y`[↑] $0) ->
  (forall D v w eta x y z, D ⊢238 pa_term_value v eta x ->
    D ⊢238 pa_term_value w eta y -> D ⊢238 op x y z ->
    D ⊢238 pa_term_value (fop v w) eta z) ->
  (forall D x x' y y' z z', D ⊢238 term_coherence_basis ->
    D ⊢238 ordinal_representative x -> D ⊢238 ordinal_representative x' ->
    D ⊢238 ordinal_representative y -> D ⊢238 ordinal_representative y' ->
    D ⊢238 order_iso x x' -> D ⊢238 order_iso y y' ->
    D ⊢238 op x y z -> D ⊢238 op x' y' z' -> D ⊢238 order_iso z z') ->
  G ⊢238 formula_transport_basis -> G ⊢238 interpreted_equality t t' rho ->
  G ⊢238 interpreted_equality u u' rho ->
  G ⊢238 interpreted_equality (fop t u) (fop t' u') rho.
Proof.
  intros Hop HT HV HC HB HE HF.
  apply (interpreted_equality_elim G t t' rho _ HE). intros x x'.
  assert (HX : (pa_term_value t rho x ∧ (pa_term_value t' rho x' ∧ order_iso x x') :: G)
    ⊢238 (pa_term_value t rho x ∧ (pa_term_value t' rho x' ∧ order_iso x x'))).
  { apply Ctx. now left. }
  eapply (interpreted_equality_elim _ u u' rho).
  - inherit HF.
  - intros y y'.
    assert (HY : (pa_term_value u rho y ∧ (pa_term_value u' rho y' ∧ order_iso y y') ::
      pa_term_value t rho x ∧ (pa_term_value t' rho x' ∧ order_iso x x') :: G)
        ⊢238 (pa_term_value u rho y ∧ (pa_term_value u' rho y' ∧ order_iso y y'))).
    { apply Ctx. now left. }
    eapply (binary_result_elim _ op x y).
    + exact Hop.
    + apply HT; [inherit (CE1 HB)| |].
      * apply (pa_term_value_ordinal _ t rho x). inherit (CE1 HX).
      * exact (pa_term_value_ordinal _ u rho y (CE1 HY)).
    + intro z.
      assert (HZ : (op x y z :: pa_term_value u rho y ∧
        (pa_term_value u' rho y' ∧ order_iso y y') ::
        pa_term_value t rho x ∧ (pa_term_value t' rho x' ∧ order_iso x x') :: G)
          ⊢238 op x y z).
      { apply Ctx. now left. }
      eapply (binary_result_elim _ op x' y').
      * exact Hop.
      * apply HT; [inherit (CE1 HB)| |].
        -- apply (pa_term_value_ordinal _ t' rho x'). inherit (CE1 (CE2 HX)).
        -- apply (pa_term_value_ordinal _ u' rho y'). inherit (CE1 (CE2 HY)).
      * intro z'.
        assert (HZ' : (op x' y' z' :: op x y z ::
          pa_term_value u rho y ∧ (pa_term_value u' rho y' ∧ order_iso y y') ::
          pa_term_value t rho x ∧ (pa_term_value t' rho x' ∧ order_iso x x') :: G)
            ⊢238 op x' y' z').
        { apply Ctx. now left. }
        apply (interpreted_equality_intro _ (fop t u) (fop t' u') rho z z').
        -- apply (HV _ t u rho x y z); [inherit (CE1 HX)|inherit (CE1 HY)|inherit HZ].
        -- apply (HV _ t' u' rho x' y' z');
             [inherit (CE1 (CE2 HX))|inherit (CE1 (CE2 HY))|exact HZ'].
        -- apply (HC _ x x' y y' z z').
           ++ inherit (CE1 (CE2 HB)).
           ++ apply (pa_term_value_ordinal _ t rho x). inherit (CE1 HX).
           ++ apply (pa_term_value_ordinal _ t' rho x'). inherit (CE1 (CE2 HX)).
           ++ apply (pa_term_value_ordinal _ u rho y). inherit (CE1 HY).
           ++ apply (pa_term_value_ordinal _ u' rho y'). inherit (CE1 (CE2 HY)).
           ++ inherit (CE2 (CE2 HX)).
           ++ inherit (CE2 (CE2 HY)).
           ++ inherit HZ.
           ++ exact HZ'.
Qed.

Lemma interpreted_addition_congruence G t t' u u' rho :
  G ⊢238 formula_transport_basis -> G ⊢238 interpreted_equality t t' rho ->
  G ⊢238 interpreted_equality u u' rho ->
  G ⊢238 interpreted_equality (pa_addition t u) (pa_addition t' u') rho.
Proof.
  apply (interpreted_binary_congruence G add_result pa_addition t t' u u' rho
    source_add_result_subst term_basis_addition addition_value_intro term_basis_addition_compare).
Qed.

Lemma interpreted_multiplication_congruence G t t' u u' rho :
  G ⊢238 formula_transport_basis -> G ⊢238 interpreted_equality t t' rho ->
  G ⊢238 interpreted_equality u u' rho ->
  G ⊢238 interpreted_equality (pa_multiplication t u) (pa_multiplication t' u') rho.
Proof.
  apply (interpreted_binary_congruence G mul_result pa_multiplication t t' u u' rho
    source_mul_result_subst term_basis_multiplication multiplication_value_intro term_basis_multiplication_compare).
Qed.

Lemma interpreted_pa_addition_congruence_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 pa_formula_value ax_add_congr rho.
Proof.
  intro HB. change (G ⊢238 pa_formula_value
    (∀ ∀ ∀ ∀ (pa_equality_formula (pa_variable 0) (pa_variable 1) →
      pa_equality_formula (pa_variable 2) (pa_variable 3) →
      pa_equality_formula (pa_addition (pa_variable 0) (pa_variable 2))
        (pa_addition (pa_variable 1) (pa_variable 3)))) rho).
  apply interpreted_all_introduce. intro a. apply interpreted_all_introduce. intro b.
  apply interpreted_all_introduce. intro c. apply interpreted_all_introduce. intro d.
  change ((ordinal_representative d :: ordinal_representative c :: ordinal_representative b ::
    ordinal_representative a :: G) ⊢238
      (interpreted_equality (pa_variable 0) (pa_variable 1) (d .: c .: b .: a .: rho) →
        interpreted_equality (pa_variable 2) (pa_variable 3) (d .: c .: b .: a .: rho) →
          interpreted_equality (pa_addition (pa_variable 0) (pa_variable 2))
            (pa_addition (pa_variable 1) (pa_variable 3)) (d .: c .: b .: a .: rho))).
  apply II, II, interpreted_addition_congruence.
  - inherit HB.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Lemma interpreted_pa_multiplication_congruence_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 pa_formula_value ax_mult_congr rho.
Proof.
  intro HB. change (G ⊢238 pa_formula_value
    (∀ ∀ ∀ ∀ (pa_equality_formula (pa_variable 0) (pa_variable 1) →
      pa_equality_formula (pa_variable 2) (pa_variable 3) →
      pa_equality_formula (pa_multiplication (pa_variable 0) (pa_variable 2))
        (pa_multiplication (pa_variable 1) (pa_variable 3)))) rho).
  apply interpreted_all_introduce. intro a. apply interpreted_all_introduce. intro b.
  apply interpreted_all_introduce. intro c. apply interpreted_all_introduce. intro d.
  change ((ordinal_representative d :: ordinal_representative c :: ordinal_representative b ::
    ordinal_representative a :: G) ⊢238
      (interpreted_equality (pa_variable 0) (pa_variable 1) (d .: c .: b .: a .: rho) →
        interpreted_equality (pa_variable 2) (pa_variable 3) (d .: c .: b .: a .: rho) →
          interpreted_equality (pa_multiplication (pa_variable 0) (pa_variable 2))
            (pa_multiplication (pa_variable 1) (pa_variable 3)) (d .: c .: b .: a .: rho))).
  apply II, II, interpreted_multiplication_congruence.
  - inherit HB.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Theorem S0_pa_addition_congruence_axiom rho :
  derivable finite_set_S0 (pa_formula_value ax_add_congr rho).
Proof.
  destruct S0_formula_transport_basis as [G [HG HB]]. exists G. split; [exact HG|].
  exact (interpreted_pa_addition_congruence_axiom G rho HB).
Qed.

Theorem S0_pa_multiplication_congruence_axiom rho :
  derivable finite_set_S0 (pa_formula_value ax_mult_congr rho).
Proof.
  destruct S0_formula_transport_basis as [G [HG HB]]. exists G. split; [exact HG|].
  exact (interpreted_pa_multiplication_congruence_axiom G rho HB).
Qed.

Print Assumptions binary_result_body_specialize.
Print Assumptions binary_result_elim.
Print Assumptions interpreted_binary_congruence.
Print Assumptions interpreted_addition_congruence.
Print Assumptions interpreted_multiplication_congruence.
Print Assumptions interpreted_pa_addition_congruence_axiom.
Print Assumptions interpreted_pa_multiplication_congruence_axiom.
Print Assumptions S0_pa_addition_congruence_axiom.
Print Assumptions S0_pa_multiplication_congruence_axiom.
End PAForwardBinaryCongruence238.
