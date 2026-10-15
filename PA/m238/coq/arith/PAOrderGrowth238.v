(* Original finite PA order certificates for the binary trace bound.
   The doubling witness below is constructed directly from the difference
   in k<v. It uses successor recursion and associativity, without any
   commutativity certificate or assumption about a power trace. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238
  PAOrderBounds238 PAQuotient238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAOrderBounds238 PAQuotient238 PAEqCongruence238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAOrderGrowth238.

Lemma quotient_right_zero : List.In right_zero_sentence quotient_context.
Proof. apply quotient_bounds. exact bounds_right_zero. Qed.
Lemma quotient_right_successor : List.In right_successor_sentence quotient_context.
Proof. apply quotient_bounds. exact bounds_right_successor. Qed.
Lemma quotient_add_rec : List.In ax_add_rec quotient_context.
Proof. apply quotient_bounds. exact bounds_add_rec. Qed.

Lemma right_zero_at G a : has_quotient_context G -> G ⊢C (a ⊕ zero == a).
Proof.
  intros HG. assert (HH : G ⊢C right_zero_sentence).
  { apply Ctx. exact (HG right_zero_sentence quotient_right_zero). }
  pose proof (AllE a HH) as HK.
  change (G ⊢C (a ⊕ zero == a)) in HK. exact HK.
Qed.
Lemma successor_self G n : has_quotient_context G -> G ⊢C (n ⧀ σ n).
Proof.
  intros HG. pose proof (quotient_has_equality G HG) as HE.
  pose proof (right_zero_at G (σ n) HG) as HZ.
  apply (strict_order_witness G n (σ n) zero).
  exact (equality_symmetry G (σ n ⊕ zero) (σ n) HE HZ).
Qed.

Lemma strict_upper_successor G i n : has_quotient_context G ->
  G ⊢C (i ⧀ n) -> G ⊢C (i ⧀ σ n).
Proof.
  intros HG HI. unfold PAlt in HI. eapply ExE_named; [exact HI|]. intros d.
  change ((List.cons (n`[↑]`[d..] == σ i`[↑]`[d..] ⊕ d) G) ⊢C (i ⧀ σ n)).
  rewrite (@subst_term_shift PA_funcs_signature n d),
    (@subst_term_shift PA_funcs_signature i d).
  set (D := List.cons (n == σ i ⊕ d) G).
  change (D ⊢C (i ⧀ σ n)).
  assert (HD : has_quotient_context D).
  { unfold D. apply has_quotient_cons. exact HG. }
  pose proof (quotient_has_equality D HD) as HE.
  assert (HN : D ⊢C (n == σ i ⊕ d)).
  { apply Ctx. unfold D. now left. }
  pose proof (IE (successor_instance D n (σ i ⊕ d) HE) HN) as HS.
  pose proof (right_successor_instance D (σ i) d
    (HD right_successor_sentence quotient_right_successor)) as HR.
  pose proof (equality_symmetry D (σ i ⊕ σ d) (σ (σ i ⊕ d)) HE HR) as HB.
  apply (strict_order_witness D i (σ n) (σ d)).
  exact (equality_transitivity D (σ n) (σ (σ i ⊕ d)) (σ i ⊕ σ d) HE HS HB).
Qed.

Lemma successor_double_growth G k v : has_quotient_context G ->
  G ⊢C (k ⧀ v) -> G ⊢C (σ k ⧀ (v ⊕ v)).
Proof.
  intros HG HI. unfold PAlt in HI. eapply ExE_named; [exact HI|]. intros d.
  change ((List.cons (v`[↑]`[d..] == σ k`[↑]`[d..] ⊕ d) G) ⊢C (σ k ⧀ (v ⊕ v))).
  rewrite (@subst_term_shift PA_funcs_signature v d),
    (@subst_term_shift PA_funcs_signature k d).
  set (D := List.cons (v == σ k ⊕ d) G).
  change (D ⊢C (σ k ⧀ (v ⊕ v))).
  assert (HD : has_quotient_context D).
  { unfold D. apply has_quotient_cons. exact HG. }
  pose proof (quotient_has_equality D HD) as HE.
  assert (HV : D ⊢C (v == σ k ⊕ d)).
  { apply Ctx. unfold D. now left. }
  pose proof (PAOrder238.add_rec_instance D k d
    (HD ax_add_rec quotient_add_rec)) as HR.
  pose proof (equality_transitivity D v (σ k ⊕ d) (σ (k ⊕ d)) HE HV HR) as HVS.
  pose proof (reflexivity_instance D v HE) as HRV.
  pose proof (IE (IE (addition_instance D v v v (σ (k ⊕ d)) HE) HRV) HVS) as H1.
  pose proof (right_successor_instance D v (k ⊕ d)
    (HD right_successor_sentence quotient_right_successor)) as H2.
  pose proof (equality_transitivity D (v ⊕ v) (v ⊕ σ (k ⊕ d))
    (σ (v ⊕ (k ⊕ d))) HE H1 H2) as Hfront.
  pose proof (reflexivity_instance D (k ⊕ d) HE) as HRK.
  pose proof (IE (IE (addition_instance D v (σ k ⊕ d) (k ⊕ d) (k ⊕ d) HE) HV) HRK) as H3.
  pose proof (associativity_instance D (σ k) d (k ⊕ d)
    (HD associativity_sentence quotient_associative)) as H4.
  pose proof (equality_symmetry D (σ k ⊕ (d ⊕ (k ⊕ d)))
    ((σ k ⊕ d) ⊕ (k ⊕ d)) HE H4) as H5.
  pose proof (equality_transitivity D (v ⊕ (k ⊕ d)) ((σ k ⊕ d) ⊕ (k ⊕ d))
    (σ k ⊕ (d ⊕ (k ⊕ d))) HE H3 H5) as Hmid.
  pose proof (IE (successor_instance D (v ⊕ (k ⊕ d))
    (σ k ⊕ (d ⊕ (k ⊕ d))) HE) Hmid) as H6.
  pose proof (PAOrder238.add_rec_instance D (σ k) (d ⊕ (k ⊕ d))
    (HD ax_add_rec quotient_add_rec)) as H7.
  pose proof (equality_symmetry D (σ (σ k) ⊕ (d ⊕ (k ⊕ d)))
    (σ (σ k ⊕ (d ⊕ (k ⊕ d)))) HE H7) as H8.
  pose proof (equality_transitivity D (v ⊕ v) (σ (v ⊕ (k ⊕ d)))
    (σ (σ k ⊕ (d ⊕ (k ⊕ d)))) HE Hfront H6) as Hall.
  apply (strict_order_witness D (σ k) (v ⊕ v) (d ⊕ (k ⊕ d))).
  exact (equality_transitivity D (v ⊕ v) (σ (σ k ⊕ (d ⊕ (k ⊕ d))))
    (σ (σ k) ⊕ (d ⊕ (k ⊕ d))) HE Hall H8).
Qed.

Theorem strict_successor_upper :
  paeq_derivable (∀ ∀ ($0 ⧀ $1 → $0 ⧀ σ $1)).
Proof.
  apply paeq_generalize, paeq_generalize, quotient_proof, II.
  set (G := List.cons ($0 ⧀ $1) quotient_context).
  apply (strict_upper_successor G $0 $1).
  - unfold G. apply has_quotient_cons. exact quotient_context_self.
  - apply Ctx. unfold G. now left.
Qed.
Theorem successor_double_bound :
  paeq_derivable (∀ ∀ ($0 ⧀ $1 → σ $0 ⧀ ($1 ⊕ $1))).
Proof.
  apply paeq_generalize, paeq_generalize, quotient_proof, II.
  set (G := List.cons ($0 ⧀ $1) quotient_context).
  apply (successor_double_growth G $0 $1).
  - unfold G. apply has_quotient_cons. exact quotient_context_self.
  - apply Ctx. unfold G. now left.
Qed.

End PAOrderGrowth238.

Print Assumptions PAOrderGrowth238.successor_self.
Print Assumptions PAOrderGrowth238.strict_successor_upper.
Print Assumptions PAOrderGrowth238.successor_double_bound.
