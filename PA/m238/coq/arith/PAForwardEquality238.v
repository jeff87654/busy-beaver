(** Original finite proof constructors for interpreted PA equality.
    Every atom keeps two actual term values and an actual Iso graph.
    The pinned ordinary PA reflexivity axiom is derived directly in S0. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 IsoGraph238
  PAForwardTerms238 PAForwardBasis238 PAForwardTotal238 PAForwardDeterminacy238
  PAForwardValueCases238 PAForwardFormula238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 IsoGraph238.IsoGraph238
  PAForwardTerms238.PAForwardTerms238 PAForwardBasis238.PAForwardBasis238
  PAForwardTotal238.PAForwardTotal238 PAForwardDeterminacy238.PAForwardDeterminacy238
  PAForwardValueCases238.PAForwardValueCases238 PAForwardFormula238.PAForwardFormula238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardEquality238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma derivation_formula_replace G (phi psi : set_form) :
  phi = psi -> G ⊢238 psi -> G ⊢238 phi.
Proof. intros <- H. exact H. Qed.

Lemma derivation_head_replace G (phi psi chi : set_form) :
  phi = psi -> (psi :: G) ⊢238 chi -> (phi :: G) ⊢238 chi.
Proof. intros <- H. exact H. Qed.

Lemma interpreted_equality_intro G t u rho x y :
  G ⊢238 pa_term_value t rho x -> G ⊢238 pa_term_value u rho y ->
  G ⊢238 order_iso x y -> G ⊢238 interpreted_equality t u rho.
Proof.
  intros HT HU HI. unfold interpreted_equality. apply (ExI x).
  change (G ⊢238 ∃ (binary_value_body
    (fun a b (_ : set_term) => order_iso a b) t u rho $0)[up (x..)]).
  apply (ExI y).
  change (G ⊢238 ((binary_value_body
    (fun a b (_ : set_term) => order_iso a b) t u rho $0)[up (x.. )])[y..]).
  apply (derivation_formula_replace G
    (((binary_value_body (fun a b (_ : set_term) => order_iso a b)
      t u rho $0)[up (x.. )])[y..])
    (pa_term_value t rho x ∧ (pa_term_value u rho y ∧ order_iso x y))).
  - exact (binary_value_body_specialize (fun a b (_ : set_term) => order_iso a b)
      t u rho $0 x y ltac:(intros a b c sigma; apply source_iso_subst)).
  - apply CI; [exact HT|]. apply CI; assumption.
Qed.

Lemma interpreted_equality_elim G t u rho (phi : set_form) :
  G ⊢238 interpreted_equality t u rho ->
  (forall x y, (pa_term_value t rho x ∧
    (pa_term_value u rho y ∧ order_iso x y) :: G) ⊢238 phi) -> G ⊢238 phi.
Proof.
  intros HE HC. unfold interpreted_equality in HE. eapply ExE_named; [exact HE|].
  intro x. change ((∃ (binary_value_body
    (fun a b (_ : set_term) => order_iso a b) t u rho $0)[up (x..)] :: G) ⊢238 phi).
  eapply ExE_named; [apply Ctx; now left|]. intro y.
  change ((((binary_value_body (fun a b (_ : set_term) => order_iso a b)
    t u rho $0)[up (x.. )])[y..] ::
      (∃ (binary_value_body (fun a b (_ : set_term) => order_iso a b)
        t u rho $0)[up (x..)]) :: G) ⊢238 phi).
  apply (derivation_head_replace
    ((∃ (binary_value_body (fun a b (_ : set_term) => order_iso a b)
      t u rho $0)[up (x..)]) :: G)
    (((binary_value_body (fun a b (_ : set_term) => order_iso a b)
      t u rho $0)[up (x.. )])[y..])
    (pa_term_value t rho x ∧ (pa_term_value u rho y ∧ order_iso x y)) phi).
  - exact (binary_value_body_specialize (fun a b (_ : set_term) => order_iso a b)
      t u rho $0 x y ltac:(intros a b c sigma; apply source_iso_subst)).
  - eapply Weak; [exact (HC x y)|]. intros chi Hchi. destruct Hchi as [<-|Hchi].
    + now left.
    + right. now right.
Qed.

Lemma interpreted_equality_reflexive G t rho :
  G ⊢238 term_totality_basis -> G ⊢238 iso_reflexivity_ax ->
  G ⊢238 pa_term_domains t rho -> G ⊢238 interpreted_equality t t rho.
Proof.
  intros HB HR HD. eapply ExE_named.
  - apply (pa_term_value_total G t rho); assumption.
  - intro x. rewrite pa_term_value_witness_specialize.
    assert (HX : (pa_term_value t rho x :: G) ⊢238 pa_term_value t rho x).
    { apply Ctx. now left. }
    apply (interpreted_equality_intro _ t t rho x x); [exact HX|exact HX|].
    apply (iso_reflexivity_instance _ x); [inherit HR|].
    apply (pa_term_value_ordinal _ t rho x). exact HX.
Qed.

Theorem S0_interpreted_equality_reflexive t rho :
  derivable finite_set_S0 (pa_term_domains t rho → interpreted_equality t t rho).
Proof.
  destruct S0_term_totality_basis as [Gt [HGt HT]].
  destruct S0_iso_reflexivity_ax as [Gr [HGr HR]]. set (G := Gt ++ Gr).
  assert (HT' : G ⊢238 term_totality_basis).
  { eapply Weak; [exact HT|]. intros psi Hpsi. unfold G. apply in_or_app. now left. }
  assert (HR' : G ⊢238 iso_reflexivity_ax).
  { eapply Weak; [exact HR|]. intros psi Hpsi. unfold G. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGt|now apply HGr].
  - apply II, (interpreted_equality_reflexive _ t rho);
      [inherit HT'|inherit HR'|apply Ctx; now left].
Qed.

Lemma source_binder_environment_witness rho x k :
  (source_binder_environment rho k)`[x..] = (x .: rho) k.
Proof.
  destruct k as [|k]; [reflexivity|].
  unfold source_binder_environment, scons, shifted_environment.
  apply source_shift_witness_cancel.
Qed.

(** This is the exact upstream FA.ax_refl, not an invented atomic schema.
    The source binders guard their actual ordinal witness. The totality
    and identity-graph contexts are selected before introducing it. *)
Theorem S0_pa_reflexivity_axiom rho :
  derivable finite_set_S0 (pa_formula_value ax_refl rho).
Proof.
  destruct S0_term_totality_basis as [Gt [HGt HT]].
  destruct S0_iso_reflexivity_ax as [Gr [HGr HR]]. set (G := Gt ++ Gr).
  assert (HT' : G ⊢238 term_totality_basis).
  { eapply Weak; [exact HT|]. intros psi Hpsi. unfold G. apply in_or_app. now left. }
  assert (HR' : G ⊢238 iso_reflexivity_ax).
  { eapply Weak; [exact HR|]. intros psi Hpsi. unfold G. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGt|now apply HGr].
  - change (G ⊢238 ∀ (ordinal_representative $0 →
      interpreted_equality (pa_variable 0) (pa_variable 0) (source_binder_environment rho))).
    apply AllI_named. intro x.
    change (G ⊢238 ((ordinal_representative $0)[x..] →
      (interpreted_equality (pa_variable 0) (pa_variable 0) (source_binder_environment rho))[x..])).
    rewrite ordinal_value_subst, interpreted_equality_source_subst.
    change (G ⊢238 (ordinal_representative x → interpreted_equality
      (pa_variable 0) (pa_variable 0) (fun k => (source_binder_environment rho k)`[x..]))).
    rewrite (interpreted_equality_environment_ext (pa_variable 0) (pa_variable 0) _
      (x .: rho) (source_binder_environment_witness rho x)).
    apply II, (interpreted_equality_reflexive _ (pa_variable 0) (x .: rho));
      [inherit HT'|inherit HR'|apply Ctx; now left].
Qed.

Print Assumptions interpreted_equality_intro.
Print Assumptions interpreted_equality_elim.
Print Assumptions interpreted_equality_reflexive.
Print Assumptions S0_interpreted_equality_reflexive.
Print Assumptions source_binder_environment_witness.
Print Assumptions S0_pa_reflexivity_axiom.
End PAForwardEquality238.
