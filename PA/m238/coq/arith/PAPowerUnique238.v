(* Original finite PA uniqueness of an actual decoded binary-power trace.
   Induction compares two independently decoded traces through their actual
   predecessor endpoints. No shared sequence code or totality is assumed. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAEqCongruence238 CompactInPA238
  PAPowerTrace238 PAPowerBound238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 CompactInPA238
  PAPowerTrace238 PAPowerBound238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAPowerUnique238.

Definition uniqueness_matrix (n p q : pa_term) : pa_form :=
  pow2 n p → pow2 n q → p == q.
Definition uniqueness_property (n : pa_term) : pa_form :=
  ∀ ∀ uniqueness_matrix n`[↑]`[↑] $1 $0.
Lemma uniqueness_matrix_subst n p q rho :
  (uniqueness_matrix n p q)[rho] =
  uniqueness_matrix n`[rho] p`[rho] q`[rho].
Proof.
  unfold uniqueness_matrix. cbn [subst_form]. rewrite !pow2_subst. reflexivity.
Qed.
Lemma uniqueness_property_subst n rho :
  (uniqueness_property n)[rho] = uniqueness_property n`[rho].
Proof.
  unfold uniqueness_property. cbn [subst_form]. rewrite uniqueness_matrix_subst.
  now rewrite !up_term.
Qed.
Lemma uniqueness_first_instance n p :
  (∀ uniqueness_matrix n`[↑]`[↑] $1 $0)[p..] =
  ∀ uniqueness_matrix n`[↑] p`[↑] $0.
Proof.
  cbn [subst_form]. rewrite uniqueness_matrix_subst, !up_term, !subst_term_shift.
  reflexivity.
Qed.
Lemma uniqueness_at G n p q :
  G ⊢C uniqueness_property n -> G ⊢C uniqueness_matrix n p q.
Proof.
  intros H. pose proof (AllE p H) as H1.
  rewrite uniqueness_first_instance in H1.
  pose proof (AllE q H1) as H2.
  assert (HN : n`[↑]`[q..] = n) by apply subst_term_shift.
  assert (HP : p`[↑]`[q..] = p) by apply subst_term_shift.
  rewrite uniqueness_matrix_subst in H2.
  change (G ⊢C uniqueness_matrix n`[↑]`[q..] p`[↑]`[q..] q) in H2.
  rewrite HN, HP in H2. exact H2.
Qed.
Lemma uniqueness_introduce G n :
  (forall p q, G ⊢C uniqueness_matrix n p q) -> G ⊢C uniqueness_property n.
Proof.
  intros H. unfold uniqueness_property. apply AllI_named. intros p.
  rewrite uniqueness_first_instance. apply AllI_named. intros q.
  assert (HN : n`[↑]`[q..] = n) by apply subst_term_shift.
  assert (HP : p`[↑]`[q..] = p) by apply subst_term_shift.
  rewrite uniqueness_matrix_subst.
  change (G ⊢C uniqueness_matrix n`[↑]`[q..] p`[↑]`[q..] q).
  rewrite HN, HP. exact (H p q).
Qed.

Definition uniqueness_formula : pa_form := uniqueness_property $0.
Lemma uniqueness_base : paeq_derivable uniqueness_formula[zero..].
Proof.
  unfold uniqueness_formula. rewrite uniqueness_property_subst.
  change (paeq_derivable (uniqueness_property zero)).
  apply trace_proof, uniqueness_introduce. intros p q.
  unfold uniqueness_matrix. apply II, II.
  set (G := List.cons (pow2 zero q) (List.cons (pow2 zero p) trace_context)).
  change (G ⊢C (p == q)).
  assert (HG : has_trace_context G).
  { unfold G. apply has_trace_cons, has_trace_cons. exact trace_context_self. }
  assert (HP : G ⊢C pow2 zero p).
  { apply Ctx. unfold G. right. now left. }
  assert (HQ : G ⊢C pow2 zero q).
  { apply Ctx. unfold G. now left. }
  pose proof (zero_endpoint G p HG HP) as HL.
  pose proof (zero_endpoint G q HG HQ) as HR.
  pose proof (equality_symmetry G q (σ zero) (trace_has_equality G HG) HR) as HB.
  exact (equality_transitivity G p (σ zero) q (trace_has_equality G HG) HL HB).
Qed.
Lemma uniqueness_step :
  paeq_derivable (∀ (uniqueness_formula → uniqueness_formula[σ $0 .: S >> var])).
Proof.
  unfold uniqueness_formula. rewrite uniqueness_property_subst.
  change (paeq_derivable (∀ (uniqueness_property $0 → uniqueness_property (σ $0)))).
  apply paeq_generalize, trace_proof, II, uniqueness_introduce.
  intros p q. unfold uniqueness_matrix. apply II, II.
  set (G := List.cons (pow2 (σ $0) q) (List.cons (pow2 (σ $0) p)
    (List.cons (uniqueness_property $0) trace_context))).
  change (G ⊢C (p == q)).
  assert (HG : has_trace_context G).
  { unfold G. apply has_trace_cons, has_trace_cons, has_trace_cons.
    exact trace_context_self. }
  assert (HP : G ⊢C pow2 (σ $0) p).
  { apply Ctx. unfold G. right. now left. }
  pose proof (successor_endpoint G $0 p HG HP) as HX.
  eapply predecessor_endpoint_eliminate; [exact HX|]. intros r.
  set (D := List.cons (pow2 $0 r ∧ (p == r ⊕ r)) G).
  change (D ⊢C (p == q)).
  assert (HD : has_trace_context D).
  { unfold D. apply has_trace_cons. exact HG. }
  assert (HQ : D ⊢C pow2 (σ $0) q).
  { apply Ctx. unfold D, G. right. now left. }
  pose proof (successor_endpoint D $0 q HD HQ) as HY.
  eapply predecessor_endpoint_eliminate; [exact HY|]. intros s.
  set (E := List.cons (pow2 $0 s ∧ (q == s ⊕ s)) D).
  change (E ⊢C (p == q)).
  assert (HE : has_trace_context E).
  { unfold E. apply has_trace_cons. exact HD. }
  pose proof (trace_has_equality E HE) as HEq.
  assert (HI : E ⊢C uniqueness_property $0).
  { apply Ctx. unfold E, D, G. right. right. right. right. now left. }
  assert (HL : E ⊢C (pow2 $0 r ∧ (p == r ⊕ r))).
  { apply Ctx. unfold E, D. right. now left. }
  assert (HR : E ⊢C (pow2 $0 s ∧ (q == s ⊕ s))).
  { apply Ctx. unfold E. now left. }
  pose proof (IE (IE (uniqueness_at E $0 r s HI) (CE1 HL)) (CE1 HR)) as Hrs.
  pose proof (IE (IE (addition_instance E r s r s HEq) Hrs) Hrs) as Hdouble.
  pose proof (equality_transitivity E p (r ⊕ r) (s ⊕ s) HEq (CE2 HL) Hdouble) as Hfront.
  pose proof (equality_symmetry E q (s ⊕ s) HEq (CE2 HR)) as Hback.
  exact (equality_transitivity E p (s ⊕ s) q HEq Hfront Hback).
Qed.

Theorem actual_pow2_unique : pow2_unique_goal.
Proof.
  change (paeq_derivable (∀ uniqueness_formula)).
  apply (paeq_induction_rule uniqueness_formula).
  - exact uniqueness_base.
  - exact uniqueness_step.
Qed.

End PAPowerUnique238.

Print Assumptions PAPowerUnique238.uniqueness_base.
Print Assumptions PAPowerUnique238.uniqueness_step.
Print Assumptions PAPowerUnique238.actual_pow2_unique.
