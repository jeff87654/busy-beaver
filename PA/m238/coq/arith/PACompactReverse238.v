(** Original finite PA proof construction for the collided compact schema
    and compact-to-ordinary-PA transport. Every coding input below is an
    actual finite bounded-comprehension certificate. The singleton filter
    tests equality to the chosen point and evaluates the property there;
    equality substitutivity recovers the varying-member clause. *)
From Coq Require Import List.
From Undecidability.FOL.Sets Require Import Signatures.
From Undecidability.FOL.Syntax Require Import BinSig.
From P238.arith Require Import PAeq238 Compact238 CompactInPA238 PAEqCongruence238
  PAPowerTrace238 PABitPosition238 PAFiniteSupport238 PALiteralSupportBounds238
  PASeparationFromCode238 PAPointedFromCode238.
From P238.logic Require Import Compiler238 NumericBundle238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 CompactInPA238 PAEqCongruence238
  PAPowerTrace238 PABitPosition238 PAFiniteSupport238 PALiteralSupportBounds238
  PASeparationFromCode238 PAPointedFromCode238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PACompactReverse238.
Module C := Compact238.Compact238.
Module M := CompactInPA238.CompactInPA238.

(** Traverse the retained finite PA context. Each step cuts its head
    formula with that formula's concrete finite ordinary-PA derivation. *)
Lemma finite_ordinary_context_cut G psi : G ⊢C psi ->
  (forall phi, List.In phi G -> paeq_derivable phi) -> paeq_derivable psi.
Proof.
  revert psi; induction G as [|phi G IH]; intros psi HD HS.
  - exists []; split; [intros chi Hchi; inversion Hchi|exact HD].
  - eapply paeq_modus_ponens with (phi := phi).
    + apply IH; [apply II; exact HD|].
      intros chi Hchi; apply HS; now right.
    + apply HS; now left.
Qed.

Definition singleton_property (phi : pa_form) : pa_form := $0 == $1 ∧ phi[↑].
Definition singleton_point_slots : nat -> pa_term := $1 .: (fun k => $(2 + k)).
Definition singleton_axiom_body (phi : pa_form) : pa_form :=
  (∀ (coded_member $1 $0 → phi[bound_slots])) ∧
  (phi[singleton_point_slots] → coded_member $0 $1).
Definition singleton_code (phi : pa_form) : pa_form := ∃ singleton_axiom_body phi.
Definition singleton_result (phi : pa_form) (W : pa_term) : pa_form :=
  (∀ (coded_member W`[↑] $0 → phi[up ↑])) ∧ (phi → coded_member W $0).

Lemma singleton_property_at phi t :
  (singleton_property phi)[t..] = (t == $0 ∧ phi).
Proof.
  unfold singleton_property.
  change ((t == $0 ∧ phi[↑][t..]) = (t == $0 ∧ phi)).
  now rewrite subst_shift.
Qed.

Lemma singleton_member_subst (phi : pa_form) W :
  phi[bound_slots][up (W..)] = phi[up ↑].
Proof.
  rewrite subst_comp; apply subst_ext; intros [|k];
    cbn [bound_slots up scons funcomp subst_term]; reflexivity.
Qed.

Lemma singleton_point_subst (phi : pa_form) W :
  phi[singleton_point_slots][W..] = phi.
Proof.
  rewrite subst_comp; transitivity phi[var]; [|apply subst_var].
  apply subst_ext; intros [|k];
    cbn [singleton_point_slots scons funcomp subst_term]; reflexivity.
Qed.

Lemma singleton_member_at_point (phi : pa_form) : phi[up ↑][$0..] = phi.
Proof.
  rewrite subst_comp; transitivity phi[var]; [|apply subst_var].
  apply subst_ext; intros [|k]; cbn [up scons funcomp subst_term]; reflexivity.
Qed.

Lemma singleton_witness phi W :
  (singleton_axiom_body phi)[W..] = singleton_result phi W.
Proof.
  unfold singleton_axiom_body, singleton_result.
  change (((∀ ((coded_member $1 $0)[up (W..)] → phi[bound_slots][up (W..)])) ∧
    (phi[singleton_point_slots][W..] → (coded_member $0 $1)[W..])) =
    ((∀ (coded_member W`[↑] $0 → phi[up ↑])) ∧ (phi → coded_member W $0))).
  rewrite singleton_member_subst, singleton_point_subst, !coded_member_subst; reflexivity.
Qed.

(** The support is strictly below x+1. This is a finite PA arithmetic
    proof from the actual order and equality certificates in bit_context. *)
Theorem singleton_support phi :
  paeq_derivable (support_bound (singleton_property phi) (σ $0)).
Proof.
  unfold support_bound; apply bit_proof, AllI_named; intro t.
  change (bit_context ⊢C ((singleton_property phi)[t..] → (PAlt $0 (σ $1))[t..])).
  rewrite PAlt_subst, singleton_property_at.
  change (bit_context ⊢C ((t == $0 ∧ phi) → t ⧀ σ $0)); apply II.
  set (G := List.cons (t == $0 ∧ phi) bit_context).
  change (G ⊢C (t ⧀ σ $0)).
  assert (HG : has_bit_context G).
  { unfold G; apply has_bit_cons; exact bit_context_self. }
  assert (HEQ : G ⊢C (t == $0)).
  { eapply CE1; apply Ctx; unfold G; now left. }
  exact (strict_left_transport G t $0 (σ $0) HG
    (weak_successor_upper G $0 $0 HG (weak_self G $0 HG)) HEQ).
Qed.

Lemma singleton_filtered_at G phi W t :
  G ⊢C finite_support_body (singleton_property phi) W ->
  G ⊢C (coded_member W t ↔ (t == $0 ∧ phi)).
Proof.
  intro HC; pose proof (AllE t HC) as H.
  change (G ⊢C ((coded_member W`[↑] $0)[t..] ↔ (singleton_property phi)[t..])) in H.
  rewrite coded_member_subst, singleton_property_at in H.
  change (G ⊢C (coded_member W`[↑]`[t..] t ↔ (t == $0 ∧ phi))) in H.
  pose proof (f_equal (fun U : pa_term => coded_member U t ↔ (t == $0 ∧ phi))
    (@subst_term_shift PA_funcs_signature W t)) as HF.
  exact (eq_rect _ (fun psi : pa_form => G ⊢C psi) H _ HF).
Qed.

Lemma singleton_filtered_to_code G phi : has_bit_context G ->
  G ⊢C finite_support_code (singleton_property phi) -> G ⊢C singleton_code phi.
Proof.
  intros HG HC; unfold finite_support_code in HC.
  eapply ExE_named; [exact HC|]; intro W; rewrite finite_support_witness.
  set (E := List.cons (finite_support_body (singleton_property phi) W) G).
  change (E ⊢C singleton_code phi).
  assert (HE : has_bit_context E).
  { unfold E; apply has_bit_cons; exact HG. }
  assert (HT : E ⊢C finite_support_body (singleton_property phi) W).
  { apply Ctx; unfold E; now left. }
  unfold singleton_code; apply (ExI W); rewrite singleton_witness; unfold singleton_result; apply CI.
  - apply AllI_named; intro t.
    change (E ⊢C ((coded_member W`[↑] $0)[t..] → (phi[up ↑])[t..])).
    rewrite coded_member_subst.
    change (E ⊢C (coded_member W`[↑]`[t..] t → (phi[up ↑])[t..])).
    pose proof (f_equal (fun U : pa_term => coded_member U t → (phi[up ↑])[t..])
      (@subst_term_shift PA_funcs_signature W t)) as HF.
    refine (eq_rect _ (fun psi : pa_form => E ⊢C psi) _ _ (eq_sym HF)).
    apply II.
    set (D := List.cons (coded_member W t) E).
    change (D ⊢C (phi[up ↑])[t..]).
    assert (HD : has_bit_context D).
    { unfold D; apply has_bit_cons; exact HE. }
    pose proof (singleton_filtered_at D phi W t
      (weaken_head E _ (coded_member W t) HT)) as Hfilter.
    assert (HM : D ⊢C coded_member W t) by (apply Ctx; unfold D; now left).
    pose proof (IE (CE1 Hfilter) HM) as Hpair.
    pose proof (formula_substitutivity D (phi[up ↑]) t $0
      (trace_has_equality D (bit_has_trace D HD)) (CE1 Hpair)) as Hreplace.
    rewrite singleton_member_at_point in Hreplace.
    exact (IE (CE2 Hreplace) (CE2 Hpair)).
  - apply II; set (D := List.cons phi E).
    change (D ⊢C coded_member W $0).
    assert (HD : has_bit_context D).
    { unfold D; apply has_bit_cons; exact HE. }
    pose proof (singleton_filtered_at D phi W $0 (weaken_head E _ phi HT)) as Hfilter.
    eapply IE; [exact (CE2 Hfilter)|]; apply CI.
    + apply reflexivity_instance, trace_has_equality, bit_has_trace; exact HD.
    + apply Ctx; unfold D; now left.
Qed.

Theorem singleton_code_from_actual_certificate phi :
  paeq_derivable (universal_close (bounded_comprehension (singleton_property phi))) ->
  paeq_derivable (singleton_code phi).
Proof.
  intro HC; pose proof (finite_support_from_actual_bounded_certificate
    (singleton_property phi) (σ $0) HC (singleton_support phi)) as Hcode.
  eapply paeq_modus_ponens with (phi := finite_support_code (singleton_property phi)); [|exact Hcode].
  apply bit_proof, II.
  apply (singleton_filtered_to_code
    (List.cons (finite_support_code (singleton_property phi)) bit_context) phi).
  - apply has_bit_cons; exact bit_context_self.
  - apply Ctx; now left.
Qed.

Theorem singleton_from_actual_certificate phi :
  paeq_derivable (universal_close (bounded_comprehension (singleton_property phi))) ->
  paeq_derivable (∀ singleton_code phi).
Proof. intro HC; apply paeq_generalize, singleton_code_from_actual_certificate; exact HC. Qed.

Lemma translate_singleton_body phi :
  M.translate (C.singleton_filter_body phi) = singleton_axiom_body (M.translate phi).
Proof.
  unfold C.singleton_filter_body, singleton_axiom_body.
  change (((∀ (coded_member $1 $0 → M.translate (phi[C.collision_member_slots]))) ∧
    (M.translate (phi[C.collision_point_slots]) → coded_member $0 $1)) =
    ((∀ (coded_member $1 $0 → (M.translate phi)[bound_slots])) ∧
    ((M.translate phi)[singleton_point_slots] → coded_member $0 $1))).
  rewrite !M.translate_subst.
  assert (HM : (M.translate phi)[M.embed_substitution C.collision_member_slots] =
    (M.translate phi)[bound_slots]).
  { apply subst_ext; intros [|k]; reflexivity. }
  assert (HP : (M.translate phi)[M.embed_substitution C.collision_point_slots] =
    (M.translate phi)[singleton_point_slots]).
  { apply subst_ext; intros [|k]; reflexivity. }
  now rewrite HM, HP.
Qed.

(** This logical tail uses the actual compact IR derivation and its
    arithmetic producer. It introduces no additional PA axiom supplier. *)
Theorem translated_singleton_implies_collided phi :
  paeq_derivable (M.translate (C.singleton_filter_body phi) → M.translate (C.collided_body phi)).
Proof.
  assert (Hset : @prv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on class
    ([C.ir]) (C.singleton_filter_body phi → C.collided_body phi)).
  { apply II; apply C.singleton_to_collided.
    - apply Ctx; right; now left.
    - apply Ctx; now left. }
  pose proof (M.translate_prv class ([C.ir])
    (C.singleton_filter_body phi → C.collided_body phi) Hset) as HP.
  apply (finite_ordinary_context_cut
    (List.map M.translate ([C.ir]))
    (M.translate (C.singleton_filter_body phi) → M.translate (C.collided_body phi)) HP).
  intros psi Hpsi; cbn in Hpsi; destruct Hpsi as [<-|[]].
  exact actual_ir_producer.
Qed.

Lemma singleton_code_to_collided G phi :
  (forall W, G ⊢C ((singleton_axiom_body (M.translate phi))[W..] →
    (M.translate (C.collided_body phi))[W..])) ->
  G ⊢C singleton_code (M.translate phi) -> G ⊢C ∃ M.translate (C.collided_body phi).
Proof.
  intros Htail Hsingle; unfold singleton_code in Hsingle.
  eapply ExE_named; [exact Hsingle|]; intro W; apply (ExI W).
  eapply IE; [apply weaken_head; exact (Htail W)|apply Ctx; now left].
Qed.

Theorem collided_from_actual_certificate phi :
  paeq_derivable (universal_close
    (bounded_comprehension (singleton_property (M.translate phi)))) ->
  paeq_derivable (M.translate (C.collided_ax phi)).
Proof.
  intro HC.
  pose proof (singleton_code_from_actual_certificate (M.translate phi) HC) as Hsingle.
  assert (Htail : paeq_derivable
    (singleton_code (M.translate phi) → ∃ M.translate (C.collided_body phi))).
  { pose proof (translated_singleton_implies_collided phi) as Hlogical.
    destruct Hlogical as [A [HA HD]].
    exists A; split; [exact HA|].
    apply II; apply (singleton_code_to_collided
      (List.cons (singleton_code (M.translate phi)) A) phi).
    - intro W.
      pose proof (subst_Weak (W..) HD) as HI.
      change (List.map (subst_form (W..)) A ⊢C
        (M.translate (C.singleton_filter_body phi))[W..] →
        (M.translate (C.collided_body phi))[W..]) in HI.
      rewrite (paeq_context_subst A (W..) HA), translate_singleton_body in HI.
      apply weaken_head; exact HI.
    - apply Ctx; now left. }
  apply paeq_generalize.
  eapply paeq_modus_ponens; [exact Htail|exact Hsingle].
Qed.

Theorem collided_from_actual_bounded_comprehension :
  bounded_comprehension_goal -> collided_producer_goal.
Proof.
  intros HC phi n Hclosed; rewrite translate_forall_times; apply paeq_capture.
  apply collided_from_actual_certificate; apply HC.
Qed.

Theorem compact_axiom_reverse : bounded_comprehension_goal -> forall phi,
  C.compact_theory phi -> paeq_derivable (M.translate phi).
Proof.
  intros HC phi Hphi; destruct Hphi as [phi HEq| |phi n Hclosed|phi n Hclosed].
  - exact (M.equality_producer phi HEq).
  - exact actual_ir_producer.
  - exact (pointed_from_actual_bounded_comprehension HC phi n Hclosed).
  - exact (collided_from_actual_bounded_comprehension HC phi n Hclosed).
Qed.

Theorem compact_finite_proof_reverse : bounded_comprehension_goal -> forall phi,
  C.derivable C.compact_theory phi -> paeq_derivable (M.translate phi).
Proof.
  intros HC phi [A [HA HD]].
  apply (finite_ordinary_context_cut (List.map M.translate A) (M.translate phi)
    (M.translate_prv class A phi HD)).
  intros psi Hpsi; apply List.in_map_iff in Hpsi as [chi [<- Hchi]].
  apply compact_axiom_reverse; [exact HC|apply HA; exact Hchi].
Qed.

Theorem compact_refutation_to_ordinary_PA : bounded_comprehension_goal ->
  C.derivable C.compact_theory falsity -> PA238.PAeq_inconsistent.
Proof.
  intros HC Hfalse; exact (compact_finite_proof_reverse HC falsity Hfalse).
Qed.

Corollary numeric_refutation_to_ordinary_PA : bounded_comprehension_goal ->
  Compiler238.derivable 1 -> PA238.PAeq_inconsistent.
Proof.
  intros HC Hnumeric; apply (compact_refutation_to_ordinary_PA HC).
  exact (NumericBundle238.NumericBundle238.numeric_refutation_to_compact Hnumeric).
Qed.

Print Assumptions finite_ordinary_context_cut.
Print Assumptions translated_singleton_implies_collided.
Print Assumptions collided_from_actual_certificate.
Print Assumptions collided_from_actual_bounded_comprehension.
Print Assumptions compact_axiom_reverse.
Print Assumptions compact_finite_proof_reverse.
Print Assumptions compact_refutation_to_ordinary_PA.
Print Assumptions numeric_refutation_to_ordinary_PA.
Print Assumptions singleton_support.
Print Assumptions singleton_filtered_to_code.
Print Assumptions singleton_code_from_actual_certificate.
Print Assumptions singleton_from_actual_certificate.
End PACompactReverse238.
