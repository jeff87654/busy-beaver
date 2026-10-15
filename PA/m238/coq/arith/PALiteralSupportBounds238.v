(* Original finite PA bound for the literal source PAS guard.
   Classical case analysis derives membership in A or equality to D from
   (not member(A,x) -> x=D). The actual bit-position and addition certificates
   then bound x below A+S D. The fixed formula may have arbitrary parameters. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238 PAOrderBounds238
  PAQuotient238 PARemainderUnique238 PAOrderGrowth238 PAPowerTrace238 PAPowerBound238
  CompactInPA238 PABitPosition238 PAFiniteSupport238 PALiteralPASFromCode238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrderBounds238 PAQuotient238
  PARemainderUnique238 PAOrderGrowth238 PAPowerTrace238 PAPowerBound238
  CompactInPA238 PABitPosition238 PAFiniteSupport238 PALiteralPASFromCode238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PALiteralSupportBounds238.

Lemma weak_self G a : has_bit_context G -> G ⊢C (a ⧀= a).
Proof.
  intros HG. pose proof (trace_has_quotient G (bit_has_trace G HG)) as HQ.
  pose proof (trace_has_equality G (bit_has_trace G HG)) as HE.
  pose proof (right_zero_at G a HQ) as HZ.
  apply (weak_order_witness G a a zero).
  exact (equality_symmetry G (a ⊕ zero) a HE HZ).
Qed.
Lemma weak_successor_upper G x y : has_bit_context G ->
  G ⊢C (x ⧀= y) -> G ⊢C (x ⧀ σ y).
Proof.
  intros HG HL. unfold PAle in HL. eapply ExE_named; [exact HL|]. intros d.
  change ((List.cons (y`[↑]`[d..] == x`[↑]`[d..] ⊕ d) G) ⊢C (x ⧀ σ y)).
  rewrite (@subst_term_shift PA_funcs_signature y d),
    (@subst_term_shift PA_funcs_signature x d).
  set (E := List.cons (y == x ⊕ d) G).
  change (E ⊢C (x ⧀ σ y)).
  assert (HEG : has_bit_context E).
  { unfold E. apply has_bit_cons. exact HG. }
  pose proof (trace_has_equality E (bit_has_trace E HEG)) as HE.
  pose proof (trace_has_quotient E (bit_has_trace E HEG)) as HQ.
  assert (HY : E ⊢C (y == x ⊕ d)).
  { apply Ctx. unfold E. now left. }
  pose proof (IE (successor_instance E y (x ⊕ d) HE) HY) as HS.
  pose proof (PAOrder238.add_rec_instance E x d (HQ ax_add_rec quotient_add_rec)) as HA.
  pose proof (equality_symmetry E (σ x ⊕ d) (σ (x ⊕ d)) HE HA) as HB.
  apply (strict_order_witness E x (σ y) d).
  exact (equality_transitivity E (σ y) (σ (x ⊕ d)) (σ x ⊕ d) HE HS HB).
Qed.
Lemma strict_left_transport G x y z : has_bit_context G ->
  G ⊢C (y ⧀ z) -> G ⊢C (x == y) -> G ⊢C (x ⧀ z).
Proof.
  intros HG HL HEQ. unfold PAlt in HL. eapply ExE_named; [exact HL|]. intros d.
  change ((List.cons (z`[↑]`[d..] == σ y`[↑]`[d..] ⊕ d) G) ⊢C (x ⧀ z)).
  rewrite (@subst_term_shift PA_funcs_signature z d),
    (@subst_term_shift PA_funcs_signature y d).
  set (E := List.cons (z == σ y ⊕ d) G).
  change (E ⊢C (x ⧀ z)).
  assert (HEG : has_bit_context E).
  { unfold E. apply has_bit_cons. exact HG. }
  pose proof (trace_has_equality E (bit_has_trace E HEG)) as HE.
  pose proof (weaken_head G (x == y) (z == σ y ⊕ d) HEQ) as Hxy.
  pose proof (IE (successor_instance E x y HE) Hxy) as Hs.
  pose proof (reflexivity_instance E d HE) as Hd.
  pose proof (IE (IE (addition_instance E (σ x) (σ y) d d HE) Hs) Hd) as Ha.
  pose proof (equality_symmetry E (σ x ⊕ d) (σ y ⊕ d) HE Ha) as Hb.
  assert (Hz : E ⊢C (z == σ y ⊕ d)).
  { apply Ctx. unfold E. now left. }
  apply (strict_order_witness E x z d).
  exact (equality_transitivity E z (σ y ⊕ d) (σ x ⊕ d) HE Hz Hb).
Qed.
Lemma point_cutoff G A D : has_bit_context G -> G ⊢C (D ⧀ (A ⊕ σ D)).
Proof.
  intros HG. pose proof (bit_has_trace G HG) as HT.
  pose proof (trace_has_quotient G HT) as HQ.
  pose proof (trace_has_equality G HT) as HE.
  pose proof (right_bound_at G A D HG) as Hweak.
  pose proof (weak_successor_upper G D (A ⊕ D) HG Hweak) as Hstrict.
  pose proof (right_successor_instance G A D
    (HQ right_successor_sentence quotient_right_successor)) as Hrs.
  pose proof (equality_symmetry G (A ⊕ σ D) (σ (A ⊕ D)) HE Hrs) as Hback.
  exact (strict_upper_transport G D (σ (A ⊕ D)) (A ⊕ σ D) HT Hstrict Hback).
Qed.
Lemma guard_cutoff G A D x : has_bit_context G ->
  G ⊢C (¬ coded_member A x → x == D) -> G ⊢C (x ⧀ (A ⊕ σ D)).
Proof.
  intros HG Hguard. eapply XMc with (phi := coded_member A x).
  - set (E := List.cons (coded_member A x) G).
    change (E ⊢C (x ⧀ (A ⊕ σ D))).
    assert (HEG : has_bit_context E).
    { unfold E. apply has_bit_cons. exact HG. }
    assert (HM : E ⊢C coded_member A x).
    { apply Ctx. unfold E. now left. }
    pose proof (bit_position E A x HEG HM) as HxA.
    pose proof (right_extension_at E A A (σ D) HEG (weak_self E A HEG)) as Hweak.
    exact (IE (IE (strict_weak_at E x A (A ⊕ σ D)
      (trace_has_quotient E (bit_has_trace E HEG))) HxA) Hweak).
  - set (E := List.cons (¬ coded_member A x) G).
    change (E ⊢C (x ⧀ (A ⊕ σ D))).
    assert (HEG : has_bit_context E).
    { unfold E. apply has_bit_cons. exact HG. }
    pose proof (weaken_head G (¬ coded_member A x → x == D) (¬ coded_member A x) Hguard) as Himp.
    assert (HN : E ⊢C ¬ coded_member A x).
    { apply Ctx. unfold E. now left. }
    pose proof (IE Himp HN) as HxD.
    exact (strict_left_transport E x D (A ⊕ σ D) HEG (point_cutoff E A D HEG) HxD).
Qed.

Theorem actual_literal_guard_support phi :
  paeq_derivable (support_bound (literal_guard ∧ phi) ($0 ⊕ σ $1)).
Proof.
  unfold support_bound. apply bit_proof, AllI_named. intros x.
  change (bit_context ⊢C ((literal_guard ∧ phi)[x..] →
    (PAlt $0 ($1 ⊕ σ $2))[x..])).
  rewrite PAlt_subst.
  change (bit_context ⊢C ((literal_guard ∧ phi)[x..] → x ⧀ ($0 ⊕ σ $1))). apply II.
  set (G := List.cons (literal_guard ∧ phi)[x..] bit_context).
  change (G ⊢C (x ⧀ ($0 ⊕ σ $1))).
  assert (HG : has_bit_context G).
  { unfold G. apply has_bit_cons. exact bit_context_self. }
  assert (HC : G ⊢C (literal_guard ∧ phi)[x..]).
  { apply Ctx. unfold G. now left. }
  pose proof (CE1 HC) as Hguard.
  change (G ⊢C (¬ ((coded_member $1 $0)[x..]) → x == $1)) in Hguard.
  rewrite coded_member_subst in Hguard.
  change (G ⊢C (¬ coded_member $0 x → x == $1)) in Hguard.
  exact (guard_cutoff G $0 $1 x HG Hguard).
Qed.
Theorem literal_pas_from_actual_comprehension phi :
  paeq_derivable (universal_close (bounded_comprehension (literal_guard ∧ phi))) ->
  paeq_derivable (literal_pas_code literal_guard phi).
Proof.
  intros HC. exact (source_guard_pas_from_actual_bounded_certificate phi ($0 ⊕ σ $1)
    HC (actual_literal_guard_support phi)).
Qed.

End PALiteralSupportBounds238.

Print Assumptions PALiteralSupportBounds238.point_cutoff.
Print Assumptions PALiteralSupportBounds238.actual_literal_guard_support.
Print Assumptions PALiteralSupportBounds238.literal_pas_from_actual_comprehension.
