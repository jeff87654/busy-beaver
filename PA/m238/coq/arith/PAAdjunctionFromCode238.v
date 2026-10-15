(* Original finite PA Adjunction transport from one actual bounded-code
   certificate. The fixed guard uses the point/input order of the literal
   Compact schema, and its support bound is proved by direct PA arithmetic. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 Compact238 CompactInPA238 PAEqCongruence238
  PABitPosition238 PAFiniteSupport238 PALiteralSupportBounds238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 CompactInPA238 PAEqCongruence238
  PABitPosition238 PAFiniteSupport238 PALiteralSupportBounds238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAAdjunctionFromCode238.

Definition swapped_guard : pa_form := ¬ coded_member $2 $0 → $0 == $1.
Definition adjunction_code : pa_form :=
  ∃ ∀ (coded_member $1 $0 ↔ (coded_member $3 $0 ∨ $0 == $2)).
Definition adjunction_code_body (C : pa_term) : pa_form :=
  ∀ (coded_member C`[↑] $0 ↔ (coded_member $2 $0 ∨ $0 == $1)).

Lemma guard_equivalent G A D x :
  G ⊢C ((¬ coded_member A x → x == D) ↔ (coded_member A x ∨ x == D)).
Proof.
  apply CI.
  - apply II. eapply XMc with (phi := coded_member A x).
    + apply DI1, Ctx. now left.
    + apply DI2. eapply IE with (phi := ¬ coded_member A x).
      * apply Ctx. right. now left.
      * apply Ctx. now left.
  - apply II, II.
    set (E := List.cons (¬ coded_member A x)
      (List.cons (coded_member A x ∨ x == D) G)).
    change (E ⊢C (x == D)).
    assert (Hdisj : E ⊢C (coded_member A x ∨ x == D)).
    { apply Ctx. unfold E. right. now left. }
    eapply DE; [exact Hdisj| |].
    + apply Exp. eapply IE with (phi := coded_member A x).
      * apply Ctx. unfold E. right. now left.
      * apply Ctx. now left.
    + apply Ctx. now left.
Qed.
Lemma equivalence_join G (P Q R : pa_form) :
  G ⊢C (P ↔ Q) -> G ⊢C (Q ↔ R) -> G ⊢C (P ↔ R).
Proof.
  intros HP HQ. apply CI.
  - apply II.
    pose proof (weaken_head G (P ↔ Q) P HP) as H1.
    pose proof (weaken_head G (Q ↔ R) P HQ) as H2.
    eapply IE; [exact (CE1 H2)|]. eapply IE; [exact (CE1 H1)|].
    apply Ctx. now left.
  - apply II.
    pose proof (weaken_head G (P ↔ Q) R HP) as H1.
    pose proof (weaken_head G (Q ↔ R) R HQ) as H2.
    eapply IE; [exact (CE2 H1)|]. eapply IE; [exact (CE2 H2)|].
    apply Ctx. now left.
Qed.
Lemma swapped_guard_support :
  paeq_derivable (support_bound swapped_guard ($1 ⊕ σ $0)).
Proof.
  unfold support_bound. apply bit_proof, AllI_named. intros x.
  change (bit_context ⊢C (swapped_guard[x..] → (PAlt $0 ($2 ⊕ σ $1))[x..])).
  rewrite PAlt_subst.
  change (bit_context ⊢C (swapped_guard[x..] → x ⧀ ($1 ⊕ σ $0))). apply II.
  set (G := List.cons swapped_guard[x..] bit_context).
  change (G ⊢C (x ⧀ ($1 ⊕ σ $0))).
  assert (HG : has_bit_context G).
  { unfold G. apply has_bit_cons. exact bit_context_self. }
  assert (Hguard : G ⊢C swapped_guard[x..]).
  { apply Ctx. unfold G. now left. }
  change (G ⊢C (¬ ((coded_member $2 $0)[x..]) → x == $0)) in Hguard.
  rewrite coded_member_subst in Hguard.
  change (G ⊢C (¬ coded_member $1 x → x == $0)) in Hguard.
  exact (guard_cutoff G $1 $0 x HG Hguard).
Qed.
Lemma adjunction_witness C :
  (∀ (coded_member $1 $0 ↔ (coded_member $3 $0 ∨ $0 == $2)))[C..] =
  adjunction_code_body C.
Proof.
  unfold adjunction_code_body.
  change ((∀ ((coded_member $1 $0)[up (C..)] ↔
    ((coded_member $3 $0)[up (C..)] ∨ $0 == $1))) =
    ∀ (coded_member C`[↑] $0 ↔ (coded_member $2 $0 ∨ $0 == $1))).
  rewrite !coded_member_subst. reflexivity.
Qed.
Lemma guarded_code_to_adjunction G :
  G ⊢C finite_support_code swapped_guard -> G ⊢C adjunction_code.
Proof.
  intros HC. unfold finite_support_code in HC.
  eapply ExE_named; [exact HC|]. intros C. rewrite finite_support_witness.
  set (E := List.cons (finite_support_body swapped_guard C) G).
  change (E ⊢C adjunction_code).
  unfold adjunction_code. apply (ExI C). rewrite adjunction_witness.
  unfold adjunction_code_body. apply AllI_named. intros x.
  change (E ⊢C ((coded_member C`[↑] $0)[x..] ↔
    ((coded_member $2 $0)[x..] ∨ x == $0))).
  rewrite !coded_member_subst.
  assert (HCx : C`[↑]`[x..] = C) by apply subst_term_shift.
  change (E ⊢C (coded_member C`[↑]`[x..] x ↔ (coded_member $1 x ∨ x == $0))).
  rewrite HCx.
  assert (HT : E ⊢C finite_support_body swapped_guard C).
  { apply Ctx. unfold E. now left. }
  pose proof (AllE x HT) as HK.
  change (E ⊢C ((coded_member C`[↑] $0)[x..] ↔
    (¬ ((coded_member $2 $0)[x..]) → x == $0))) in HK.
  rewrite !coded_member_subst in HK.
  change (E ⊢C (coded_member C`[↑]`[x..] x ↔
    (¬ coded_member $1 x → x == $0))) in HK. rewrite HCx in HK.
  exact (equivalence_join E (coded_member C x) (¬ coded_member $1 x → x == $0)
    (coded_member $1 x ∨ x == $0) HK (guard_equivalent E $1 $0 x)).
Qed.
Theorem arithmetic_adjunction_from_actual_certificate :
  paeq_derivable (universal_close (bounded_comprehension swapped_guard)) ->
  paeq_derivable adjunction_code.
Proof.
  intros HC. destruct (finite_support_from_actual_bounded_certificate swapped_guard
    ($1 ⊕ σ $0) HC swapped_guard_support) as (A & HA & HD).
  exists A. split; [exact HA|]. exact (guarded_code_to_adjunction A HD).
Qed.
Theorem adjunction_from_actual_bounded_comprehension :
  bounded_comprehension_goal -> adjunction_producer_goal.
Proof.
  intros HC. change (paeq_derivable (∀ ∀ adjunction_code)).
  apply paeq_generalize, paeq_generalize, arithmetic_adjunction_from_actual_certificate.
  apply HC.
Qed.

End PAAdjunctionFromCode238.

Print Assumptions PAAdjunctionFromCode238.swapped_guard_support.
Print Assumptions PAAdjunctionFromCode238.arithmetic_adjunction_from_actual_certificate.
Print Assumptions PAAdjunctionFromCode238.adjunction_from_actual_bounded_comprehension.
