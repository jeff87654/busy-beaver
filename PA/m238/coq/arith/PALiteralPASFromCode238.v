(* Original finite PA transport of the literal PAS logical tail.
   A concrete fixed-formula filtered code is turned into the two displayed
   source implications. All finite PA axioms and the actual code witness
   are retained. No filtered-code existence theorem is assumed as an axiom. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 CompactInPA238 PAFiniteSupport238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 CompactInPA238 PAFiniteSupport238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PALiteralPASFromCode238.

Definition literal_guard : pa_form := ¬ coded_member $1 $0 → $0 == $2.
Definition literal_pas_body (guard phi : pa_form) (C : pa_term) : pa_form :=
  ∀ ((guard → phi → coded_member C`[↑] $0) ∧ (coded_member C`[↑] $0 → phi)).
Definition literal_pas_code (guard phi : pa_form) : pa_form :=
  ∃ ∀ ((guard[up ↑] → phi[up ↑] → coded_member $1 $0) ∧
    (coded_member $1 $0 → phi[up ↑])).
Lemma literal_pas_witness guard phi C :
  (∀ ((guard[up ↑] → phi[up ↑] → coded_member $1 $0) ∧
    (coded_member $1 $0 → phi[up ↑])))[C..] = literal_pas_body guard phi C.
Proof.
  unfold literal_pas_body.
  change ((∀ ((guard[up ↑][up (C..)] → phi[up ↑][up (C..)] →
      (coded_member $1 $0)[up (C..)]) ∧
    ((coded_member $1 $0)[up (C..)] → phi[up ↑][up (C..)]))) =
    ∀ ((guard → phi → coded_member C`[↑] $0) ∧ (coded_member C`[↑] $0 → phi))).
  rewrite !member_shift_cancel, !coded_member_subst. reflexivity.
Qed.
Lemma literal_pas_introduce G guard phi C :
  G ⊢C literal_pas_body guard phi C -> G ⊢C literal_pas_code guard phi.
Proof.
  intros H. unfold literal_pas_code. apply (ExI C). rewrite literal_pas_witness. exact H.
Qed.
Lemma filtered_code_to_literal_pas G guard phi :
  G ⊢C finite_support_code (guard ∧ phi) -> G ⊢C literal_pas_code guard phi.
Proof.
  intros HC. unfold finite_support_code in HC.
  eapply ExE_named; [exact HC|]. intros C. rewrite finite_support_witness.
  set (D := List.cons (finite_support_body (guard ∧ phi) C) G).
  change (D ⊢C literal_pas_code guard phi).
  apply (literal_pas_introduce D guard phi C).
  assert (HX : D ⊢C finite_support_body (guard ∧ phi) C).
  { apply Ctx. unfold D. now left. }
  exact (forall_filter_to_literal_pas D guard phi (coded_member C`[↑] $0) HX).
Qed.
Theorem ordinary_filtered_code_to_literal_pas guard phi :
  paeq_derivable (finite_support_code (guard ∧ phi)) ->
  paeq_derivable (literal_pas_code guard phi).
Proof.
  intros (A & HA & HC). exists A. split; [exact HA|].
  exact (filtered_code_to_literal_pas A guard phi HC).
Qed.
Theorem literal_pas_from_actual_bounded_certificate guard phi B :
  paeq_derivable (universal_close (bounded_comprehension (guard ∧ phi))) ->
  paeq_derivable (support_bound (guard ∧ phi) B) ->
  paeq_derivable (literal_pas_code guard phi).
Proof.
  intros HC HS. apply ordinary_filtered_code_to_literal_pas.
  exact (finite_support_from_actual_bounded_certificate (guard ∧ phi) B HC HS).
Qed.
Corollary source_guard_pas_from_actual_bounded_certificate phi B :
  paeq_derivable (universal_close (bounded_comprehension (literal_guard ∧ phi))) ->
  paeq_derivable (support_bound (literal_guard ∧ phi) B) ->
  paeq_derivable (literal_pas_code literal_guard phi).
Proof. exact (literal_pas_from_actual_bounded_certificate literal_guard phi B). Qed.

End PALiteralPASFromCode238.

Print Assumptions PALiteralPASFromCode238.filtered_code_to_literal_pas.
Print Assumptions PALiteralPASFromCode238.ordinary_filtered_code_to_literal_pas.
Print Assumptions PALiteralPASFromCode238.source_guard_pas_from_actual_bounded_certificate.
