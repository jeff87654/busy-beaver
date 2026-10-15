(* Original full-parameter PA induction on an actual decoded doubling trace.
   The theorem is conditional on pow2 n p; it requires no trace existence,
   beta totality, exponentiation symbol, or semantic arithmetic model. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAEqCongruence238 PAOrderBounds238
  PAQuotient238 PAOrderGrowth238 CompactInPA238 PAPowerTrace238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrderBounds238
  PAQuotient238 PAOrderGrowth238 CompactInPA238 PAPowerTrace238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAPowerBound238.

Lemma strict_upper_transport G x y z : has_trace_context G ->
  G ⊢C (x ⧀ y) -> G ⊢C (y == z) -> G ⊢C (x ⧀ z).
Proof.
  intros HG HL HEQ. unfold PAlt in HL.
  eapply ExE_named; [exact HL|]. intros d.
  change ((List.cons (y`[↑]`[d..] == σ x`[↑]`[d..] ⊕ d) G) ⊢C (x ⧀ z)).
  rewrite (@subst_term_shift PA_funcs_signature y d),
    (@subst_term_shift PA_funcs_signature x d).
  set (D := List.cons (y == σ x ⊕ d) G).
  change (D ⊢C (x ⧀ z)).
  assert (HD : has_trace_context D).
  { unfold D. apply has_trace_cons. exact HG. }
  pose proof (trace_has_equality D HD) as HE.
  pose proof (weaken_head G (y == z) (y == σ x ⊕ d) HEQ) as HYZ.
  pose proof (equality_symmetry D y z HE HYZ) as HZY.
  assert (HY : D ⊢C (y == σ x ⊕ d)).
  { apply Ctx. unfold D. now left. }
  apply (strict_order_witness D x z d).
  exact (equality_transitivity D z y (σ x ⊕ d) HE HZY HY).
Qed.

Definition index_property (n : pa_term) : pa_form :=
  ∀ (pow2 n`[↑] $0 → n`[↑] ⧀ $0).
Lemma index_property_subst n rho :
  (index_property n)[rho] = index_property n`[rho].
Proof.
  unfold index_property. cbn [subst_form]. rewrite pow2_subst, PAlt_subst.
  now rewrite !up_term.
Qed.
Lemma index_property_at G n p :
  G ⊢C index_property n -> G ⊢C (pow2 n p → n ⧀ p).
Proof.
  intros H. pose proof (AllE p H) as HK.
  change (G ⊢C (pow2 n`[↑] $0)[p..] → (PAlt n`[↑] $0)[p..]) in HK.
  assert (HN : n`[↑]`[p..] = n) by apply subst_term_shift.
  rewrite pow2_subst, PAlt_subst in HK.
  change (G ⊢C (pow2 n`[↑]`[p..] p → n`[↑]`[p..] ⧀ p)) in HK.
  rewrite HN in HK. exact HK.
Qed.
Lemma index_property_introduce G n :
  (forall p, G ⊢C (pow2 n p → n ⧀ p)) -> G ⊢C index_property n.
Proof.
  intros H. unfold index_property. apply AllI_named. intros p.
  change (G ⊢C (pow2 n`[↑] $0)[p..] → (PAlt n`[↑] $0)[p..]).
  assert (HN : n`[↑]`[p..] = n) by apply subst_term_shift.
  rewrite pow2_subst, PAlt_subst.
  change (G ⊢C (pow2 n`[↑]`[p..] p → n`[↑]`[p..] ⧀ p)).
  rewrite HN. exact (H p).
Qed.
Lemma predecessor_endpoint_eliminate G n p (psi : pa_form) :
  G ⊢C predecessor_endpoint n p ->
  (forall r, (List.cons (pow2 n r ∧ (p == r ⊕ r)) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. unfold predecessor_endpoint in HX.
  eapply ExE_named; [exact HX|]. intros r.
  change ((List.cons ((pow2 n`[↑] $0)[r..] ∧
    (p`[↑]`[r..] == r ⊕ r)) G) ⊢C psi).
  assert (HN : n`[↑]`[r..] = n) by apply subst_term_shift.
  assert (HP : p`[↑]`[r..] = p) by apply subst_term_shift.
  rewrite pow2_subst.
  change ((List.cons (pow2 n`[↑]`[r..] r ∧ (p`[↑]`[r..] == r ⊕ r)) G) ⊢C psi).
  rewrite HN, HP. exact (H r).
Qed.

Definition index_formula : pa_form := index_property $0.
Lemma index_base : paeq_derivable index_formula[zero..].
Proof.
  unfold index_formula. rewrite index_property_subst.
  change (paeq_derivable (index_property zero)).
  apply trace_proof, index_property_introduce. intros p. apply II.
  set (G := List.cons (pow2 zero p) trace_context).
  change (G ⊢C (zero ⧀ p)).
  assert (HG : has_trace_context G).
  { unfold G. apply has_trace_cons. exact trace_context_self. }
  assert (HP : G ⊢C pow2 zero p).
  { apply Ctx. unfold G. now left. }
  pose proof (zero_endpoint G p HG HP) as HEQ.
  pose proof (equality_symmetry G p (σ zero) (trace_has_equality G HG) HEQ) as Hback.
  pose proof (successor_self G zero (trace_has_quotient G HG)) as H01.
  exact (strict_upper_transport G zero (σ zero) p HG H01 Hback).
Qed.
Lemma index_step :
  paeq_derivable (∀ (index_formula → index_formula[σ $0 .: S >> var])).
Proof.
  unfold index_formula. rewrite index_property_subst.
  change (paeq_derivable (∀ (index_property $0 → index_property (σ $0)))).
  apply paeq_generalize, trace_proof, II, index_property_introduce.
  intros p. apply II.
  set (G := List.cons (pow2 (σ $0) p) (List.cons (index_property $0) trace_context)).
  change (G ⊢C (σ $0 ⧀ p)).
  assert (HG : has_trace_context G).
  { unfold G. apply has_trace_cons, has_trace_cons. exact trace_context_self. }
  assert (HP : G ⊢C pow2 (σ $0) p).
  { apply Ctx. unfold G. now left. }
  pose proof (successor_endpoint G $0 p HG HP) as HX.
  eapply predecessor_endpoint_eliminate; [exact HX|]. intros r.
  set (D := List.cons (pow2 $0 r ∧ (p == r ⊕ r)) G).
  change (D ⊢C (σ $0 ⧀ p)).
  assert (HD : has_trace_context D).
  { unfold D. apply has_trace_cons. exact HG. }
  assert (HC : D ⊢C (pow2 $0 r ∧ (p == r ⊕ r))).
  { apply Ctx. unfold D. now left. }
  assert (HI : D ⊢C index_property $0).
  { apply Ctx. unfold D, G. right. right. now left. }
  pose proof (IE (index_property_at D $0 r HI) (CE1 HC)) as Hlt.
  pose proof (successor_double_growth D $0 r (trace_has_quotient D HD) Hlt) as Hgrow.
  pose proof (equality_symmetry D p (r ⊕ r) (trace_has_equality D HD) (CE2 HC)) as Hback.
  exact (strict_upper_transport D (σ $0) (r ⊕ r) p HD Hgrow Hback).
Qed.

Theorem pow2_strict_bound :
  paeq_derivable (∀ ∀ (pow2 $1 $0 → $1 ⧀ $0)).
Proof.
  change (paeq_derivable (∀ index_formula)).
  apply (paeq_induction_rule index_formula).
  - exact index_base.
  - exact index_step.
Qed.

End PAPowerBound238.

Print Assumptions PAPowerBound238.index_base.
Print Assumptions PAPowerBound238.index_step.
Print Assumptions PAPowerBound238.pow2_strict_bound.
