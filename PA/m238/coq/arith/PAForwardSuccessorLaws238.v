(** Actual source derivations of the pinned PA successor injectivity and
    zero discrimination axioms. Their input atoms retain the real value
    witnesses and equality graphs needed by the predecessor laws. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 PairGraph238 IsoGraph238 IsoPALaws238
  PAForwardTerms238 PAForwardValueCases238 PAForwardFormula238 PAForwardEquality238
  PAForwardEqualityLaws238 PAForwardFormulaBasis238 PAForwardQuantifier238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 PairGraph238.PairGraph238
  IsoGraph238.IsoGraph238 IsoPALaws238.IsoPALaws238 PAForwardTerms238.PAForwardTerms238
  PAForwardValueCases238.PAForwardValueCases238 PAForwardFormula238.PAForwardFormula238
  PAForwardEquality238.PAForwardEquality238 PAForwardEqualityLaws238.PAForwardEqualityLaws238
  PAForwardFormulaBasis238.PAForwardFormulaBasis238 PAForwardQuantifier238.PAForwardQuantifier238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardSuccessorLaws238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma successor_injectivity_instance G a sa b sb :
  G ⊢238 iso_successor_injectivity_ax -> G ⊢238 ordinal_representative a ->
  G ⊢238 ordinal_representative sa -> G ⊢238 ordinal_representative b ->
  G ⊢238 ordinal_representative sb -> G ⊢238 raw_successor a sa ->
  G ⊢238 raw_successor b sb -> G ⊢238 order_iso sa sb -> G ⊢238 order_iso a b.
Proof.
  destruct a as [ia|[]], sa as [isa|[]], b as [ib|[]], sb as [isb|[]].
  intros HI HA HSA HB HSB HS HT HE. unfold iso_successor_injectivity_ax in HI.
  pose proof (AllE $isb (AllE $ib (AllE $isa (AllE $ia HI)))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HE]. eapply IE; [|exact HT]. eapply IE; [|exact HS].
  eapply IE; [|exact HSB]. eapply IE; [|exact HB]. eapply IE; [|exact HSA].
  eapply IE; [exact H|exact HA].
Qed.

Lemma interpreted_successor_injective G t u rho :
  G ⊢238 formula_transport_basis -> G ⊢238 iso_successor_injectivity_ax ->
  G ⊢238 interpreted_equality (pa_successor t) (pa_successor u) rho ->
  G ⊢238 interpreted_equality t u rho.
Proof.
  intros HB HI HE. apply (interpreted_equality_elim G (pa_successor t) (pa_successor u) rho _ HE).
  intros sa sb.
  assert (HJ : (pa_term_value (pa_successor t) rho sa ∧
    (pa_term_value (pa_successor u) rho sb ∧ order_iso sa sb) :: G)
      ⊢238 (pa_term_value (pa_successor t) rho sa ∧
        (pa_term_value (pa_successor u) rho sb ∧ order_iso sa sb))).
  { apply Ctx. now left. }
  eapply ExE_named.
  - apply (successor_value_inputs _ t rho sa). exact (CE1 HJ).
  - intro a. rewrite successor_value_body_specialize.
    assert (HA : (pa_term_value t rho a ∧ raw_successor a sa ::
      pa_term_value (pa_successor t) rho sa ∧
        (pa_term_value (pa_successor u) rho sb ∧ order_iso sa sb) :: G)
          ⊢238 (pa_term_value t rho a ∧ raw_successor a sa)).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (successor_value_inputs _ u rho sb). inherit (CE1 (CE2 HJ)).
    + intro b. rewrite successor_value_body_specialize.
      assert (HC : (pa_term_value u rho b ∧ raw_successor b sb ::
        pa_term_value t rho a ∧ raw_successor a sa ::
        pa_term_value (pa_successor t) rho sa ∧
          (pa_term_value (pa_successor u) rho sb ∧ order_iso sa sb) :: G)
            ⊢238 (pa_term_value u rho b ∧ raw_successor b sb)).
      { apply Ctx. now left. }
      apply (interpreted_equality_intro _ t u rho a b); [inherit (CE1 HA)|exact (CE1 HC)|].
      apply (successor_injectivity_instance _ a sa b sb).
      * inherit HI.
      * apply (pa_term_value_ordinal _ t rho a). inherit (CE1 HA).
      * apply (pa_term_value_ordinal _ (pa_successor t) rho sa). inherit (CE1 HJ).
      * exact (pa_term_value_ordinal _ u rho b (CE1 HC)).
      * apply (pa_term_value_ordinal _ (pa_successor u) rho sb). inherit (CE1 (CE2 HJ)).
      * inherit (CE2 HA).
      * exact (CE2 HC).
      * inherit (CE2 (CE2 HJ)).
Qed.

Lemma interpreted_zero_successor_false G u rho :
  G ⊢238 formula_transport_basis ->
  G ⊢238 interpreted_equality pa_zero (pa_successor u) rho -> G ⊢238 falsity.
Proof.
  intros HB HE. apply (interpreted_equality_elim G pa_zero (pa_successor u) rho _ HE).
  intros z s.
  assert (HJ : (pa_term_value pa_zero rho z ∧
    (pa_term_value (pa_successor u) rho s ∧ order_iso z s) :: G)
      ⊢238 (pa_term_value pa_zero rho z ∧
        (pa_term_value (pa_successor u) rho s ∧ order_iso z s))).
  { apply Ctx. now left. }
  eapply ExE_named.
  - apply (successor_value_inputs _ u rho s). exact (CE1 (CE2 HJ)).
  - intro a. rewrite successor_value_body_specialize.
    apply (order_iso_successor_zero_false _ a s z).
    + inherit (CE1 (CE1 (CE2 HB))).
    + eapply CE2, Ctx. now left.
    + inherit (CE2 (CE1 HJ)).
    + apply (formula_basis_iso_symmetric _ z s).
      * inherit HB.
      * inherit (CE1 (CE1 HJ)).
      * inherit (CE2 (CE2 HJ)).
Qed.

Lemma interpreted_pa_successor_injectivity_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 iso_successor_injectivity_ax ->
  G ⊢238 pa_formula_value ax_succ_inj rho.
Proof.
  intros HB HI. change (G ⊢238 pa_formula_value
    (∀ ∀ (pa_equality_formula (pa_successor (pa_variable 1)) (pa_successor (pa_variable 0)) →
      pa_equality_formula (pa_variable 1) (pa_variable 0))) rho).
  apply interpreted_all_introduce. intro x. apply interpreted_all_introduce. intro y.
  change ((ordinal_representative y :: ordinal_representative x :: G) ⊢238
    (interpreted_equality (pa_successor (pa_variable 1)) (pa_successor (pa_variable 0)) (y .: x .: rho) →
      interpreted_equality (pa_variable 1) (pa_variable 0) (y .: x .: rho))).
  apply II, interpreted_successor_injective; [inherit HB|inherit HI|apply Ctx; now left].
Qed.

Lemma interpreted_pa_zero_discrimination_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 pa_formula_value ax_zero_succ rho.
Proof.
  intro HB. change (G ⊢238 pa_formula_value
    (∀ (pa_equality_formula pa_zero (pa_successor (pa_variable 0)) → falsity)) rho).
  apply interpreted_all_introduce. intro x.
  change ((ordinal_representative x :: G) ⊢238
    (interpreted_equality pa_zero (pa_successor (pa_variable 0)) (x .: rho) → falsity)).
  apply II, (interpreted_zero_successor_false _ (pa_variable 0) (x .: rho));
    [inherit HB|apply Ctx; now left].
Qed.

Theorem S0_pa_successor_injectivity_axiom rho :
  derivable finite_set_S0 (pa_formula_value ax_succ_inj rho).
Proof.
  destruct S0_formula_transport_basis as [Gb [HGb HB]].
  destruct S0_order_iso_successor_injective_closed as [Gi [HGi HI]].
  set (G := Gb ++ Gi). exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGb|now apply HGi].
  - apply interpreted_pa_successor_injectivity_axiom.
    + eapply Weak; [exact HB|]. intros psi Hpsi. unfold G. apply in_or_app. now left.
    + eapply Weak; [exact HI|]. intros psi Hpsi. unfold G. apply in_or_app. now right.
Qed.

Theorem S0_pa_zero_discrimination_axiom rho :
  derivable finite_set_S0 (pa_formula_value ax_zero_succ rho).
Proof.
  destruct S0_formula_transport_basis as [G [HG HB]]. exists G. split; [exact HG|].
  exact (interpreted_pa_zero_discrimination_axiom G rho HB).
Qed.

Print Assumptions successor_injectivity_instance.
Print Assumptions interpreted_successor_injective.
Print Assumptions interpreted_zero_successor_false.
Print Assumptions interpreted_pa_successor_injectivity_axiom.
Print Assumptions interpreted_pa_zero_discrimination_axiom.
Print Assumptions S0_pa_successor_injectivity_axiom.
Print Assumptions S0_pa_zero_discrimination_axiom.
End PAForwardSuccessorLaws238.
