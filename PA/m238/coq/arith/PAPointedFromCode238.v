(* Original finite PA transport of a fixed filtered code into the complete
   pointed schema, including the chosen-point clause. The only coding input
   is an actual bounded-comprehension certificate for that fixed formula. *)
From Coq Require Import List.
From Undecidability.FOL.Sets Require Import Signatures.
From Undecidability.FOL.Syntax Require Import BinSig.
From P238.arith Require Import PAeq238 Compact238 CompactInPA238 PAEqCongruence238
  PAPowerTrace238 PABitPosition238 PAFiniteSupport238 PALiteralSupportBounds238
  PAAdjunctionFromCode238 PASeparationFromCode238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 CompactInPA238 PAEqCongruence238 PAPowerTrace238
  PABitPosition238 PAFiniteSupport238 PALiteralSupportBounds238
  PAAdjunctionFromCode238 PASeparationFromCode238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAPointedFromCode238.

Definition swap_slots : nat -> pa_term := $0 .: $2 .: $1 .: (fun k => $(3 + k)).
Definition member_slots : nat -> pa_term := $0 .: $3 .: $2 .: (fun k => $(4 + k)).
Definition point_slots : nat -> pa_term := $1 .: $2 .: $1 .: (fun k => $(3 + k)).
Definition point_property (phi : pa_form) : pa_form := phi[swap_slots].
Definition pointed_axiom_body (phi : pa_form) : pa_form :=
  (∀ ((coded_member $3 $0 → phi[member_slots] → coded_member $1 $0) ∧
    (coded_member $1 $0 → phi[member_slots]))) ∧
  (phi[point_slots] → coded_member $0 $1).
Definition pointed_code (phi : pa_form) : pa_form := ∃ pointed_axiom_body phi.
Definition pointed_result (phi : pa_form) (C : pa_term) : pa_form :=
  (∀ ((coded_member $2 $0 → point_property phi → coded_member C`[↑] $0) ∧
    (coded_member C`[↑] $0 → point_property phi))) ∧
  ((point_property phi)[$0..] → coded_member C $0).

Lemma support_conjunction G B (guard phi : pa_form) :
  G ⊢C support_bound guard B -> G ⊢C support_bound (guard ∧ phi) B.
Proof.
  intros HS. unfold support_bound. apply AllI_named. intros x.
  change (G ⊢C ((guard[x..] ∧ phi[x..]) → (PAlt $0 B`[↑])[x..])). apply II.
  pose proof (weaken_head G (support_bound guard B) (guard[x..] ∧ phi[x..]) HS) as HE.
  pose proof (AllE x HE) as HX.
  change ((List.cons (guard[x..] ∧ phi[x..]) G) ⊢C
    (guard[x..] → (PAlt $0 B`[↑])[x..])) in HX.
  eapply IE; [exact HX|]. eapply CE1. apply Ctx. now left.
Qed.
Lemma ordinary_support_conjunction B guard phi :
  paeq_derivable (support_bound guard B) -> paeq_derivable (support_bound (guard ∧ phi) B).
Proof.
  intros (A & HA & HD). exists A. split; [exact HA|]. exact (support_conjunction A B guard phi HD).
Qed.
Lemma pointed_member_subst (phi : pa_form) (C : pa_term) :
  phi[member_slots][up (C..)] = point_property phi.
Proof.
  unfold point_property. rewrite subst_comp. apply subst_ext. intros [|[|[|k]]];
    cbn [member_slots swap_slots up scons funcomp subst_term]; reflexivity.
Qed.
Lemma pointed_point_subst (phi : pa_form) (C : pa_term) :
  phi[point_slots][C..] = (point_property phi)[$0..].
Proof.
  unfold point_property. rewrite !subst_comp. apply subst_ext. intros [|[|[|k]]];
    cbn [point_slots swap_slots up scons funcomp subst_term]; reflexivity.
Qed.
Lemma pointed_witness phi C : (pointed_axiom_body phi)[C..] = pointed_result phi C.
Proof.
  unfold pointed_axiom_body, pointed_result.
  change (((∀ (((coded_member $3 $0)[up (C..)] → phi[member_slots][up (C..)] →
      (coded_member $1 $0)[up (C..)]) ∧
    ((coded_member $1 $0)[up (C..)] → phi[member_slots][up (C..)]))) ∧
    (phi[point_slots][C..] → (coded_member $0 $1)[C..])) =
    ((∀ ((coded_member $2 $0 → point_property phi → coded_member C`[↑] $0) ∧
      (coded_member C`[↑] $0 → point_property phi))) ∧
      ((point_property phi)[$0..] → coded_member C $0))).
  rewrite !pointed_member_subst, pointed_point_subst, !coded_member_subst. reflexivity.
Qed.
Lemma member_implies_guard G A D x :
  G ⊢C (coded_member A x → (¬ coded_member A x → x == D)).
Proof.
  apply II, II, Exp. eapply IE with (phi := coded_member A x).
  - apply Ctx. now left.
  - apply Ctx. right. now left.
Qed.
Lemma pointed_member_tail G A D x (phi : pa_form) C :
  G ⊢C (coded_member C x ↔ ((¬ coded_member A x → x == D) ∧ phi)) ->
  G ⊢C ((coded_member A x → phi → coded_member C x) ∧ (coded_member C x → phi)).
Proof.
  intros HC. apply CI.
  - apply II, II.
    set (E := List.cons phi (List.cons (coded_member A x) G)).
    assert (HE : E ⊢C (coded_member C x ↔ ((¬ coded_member A x → x == D) ∧ phi))).
    { unfold E. apply weaken_head, weaken_head. exact HC. }
    eapply IE; [exact (CE2 HE)|]. apply CI.
    + eapply IE; [exact (member_implies_guard E A D x)|]. apply Ctx. unfold E. right. now left.
    + apply Ctx. unfold E. now left.
  - apply II.
    pose proof (weaken_head G (coded_member C x ↔ ((¬ coded_member A x → x == D) ∧ phi))
      (coded_member C x) HC) as HE.
    eapply CE2. eapply IE; [exact (CE1 HE)|]. apply Ctx. now left.
Qed.
Lemma filtered_code_at G phi C x :
  G ⊢C finite_support_body (swapped_guard ∧ point_property phi) C ->
  G ⊢C (coded_member C x ↔ ((¬ coded_member $1 x → x == $0) ∧ (point_property phi)[x..])).
Proof.
  intros HT. pose proof (AllE x HT) as HK.
  change (G ⊢C ((coded_member C`[↑] $0)[x..] ↔
    ((¬ ((coded_member $2 $0)[x..]) → x == $0) ∧ (point_property phi)[x..]))) in HK.
  rewrite !coded_member_subst in HK.
  assert (HC : C`[↑]`[x..] = C) by apply subst_term_shift.
  change (G ⊢C (coded_member C`[↑]`[x..] x ↔
    ((¬ coded_member $1 x → x == $0) ∧ (point_property phi)[x..]))) in HK.
  rewrite HC in HK. exact HK.
Qed.

Lemma filtered_code_to_pointed G phi : has_bit_context G ->
  G ⊢C finite_support_code (swapped_guard ∧ point_property phi) -> G ⊢C pointed_code phi.
Proof.
  intros HG HC. unfold finite_support_code in HC.
  eapply ExE_named; [exact HC|]. intros C. rewrite finite_support_witness.
  set (E := List.cons (finite_support_body (swapped_guard ∧ point_property phi) C) G).
  change (E ⊢C pointed_code phi).
  assert (HE : has_bit_context E).
  { unfold E. apply has_bit_cons. exact HG. }
  assert (HT : E ⊢C finite_support_body (swapped_guard ∧ point_property phi) C).
  { apply Ctx. unfold E. now left. }
  unfold pointed_code. apply (ExI C). rewrite pointed_witness. unfold pointed_result. apply CI.
  - apply AllI_named. intros x.
    change (E ⊢C (((coded_member $2 $0)[x..] → (point_property phi)[x..] →
      (coded_member C`[↑] $0)[x..]) ∧
      ((coded_member C`[↑] $0)[x..] → (point_property phi)[x..]))).
    rewrite !coded_member_subst.
    assert (HCx : C`[↑]`[x..] = C) by apply subst_term_shift.
    change (E ⊢C ((coded_member $1 x → (point_property phi)[x..] →
      coded_member C`[↑]`[x..] x) ∧
      (coded_member C`[↑]`[x..] x → (point_property phi)[x..]))).
    rewrite HCx.
    exact (pointed_member_tail E $1 $0 x (point_property phi)[x..] C
      (filtered_code_at E phi C x HT)).
  - apply II.
    set (D := List.cons (point_property phi)[$0..] E).
    change (D ⊢C coded_member C $0).
    assert (HD : has_bit_context D).
    { unfold D. apply has_bit_cons. exact HE. }
    pose proof (weaken_head E (finite_support_body (swapped_guard ∧ point_property phi) C)
      (point_property phi)[$0..] HT) as Hcode.
    pose proof (filtered_code_at D phi C $0 Hcode) as Hpoint.
    eapply IE; [exact (CE2 Hpoint)|]. apply CI.
    + apply II.
      set (F := List.cons (¬ coded_member $1 $0) D).
      apply (reflexivity_instance F $0).
      apply trace_has_equality, bit_has_trace. unfold F. apply has_bit_cons. exact HD.
    + apply Ctx. unfold D. now left.
Qed.
Theorem arithmetic_pointed_from_actual_certificate phi :
  paeq_derivable (universal_close
    (bounded_comprehension (swapped_guard ∧ point_property phi))) ->
  paeq_derivable (∀ ∀ pointed_code phi).
Proof.
  intros HC.
  pose proof (ordinary_support_conjunction ($1 ⊕ σ $0) swapped_guard (point_property phi)
    swapped_guard_support) as HS.
  pose proof (finite_support_from_actual_bounded_certificate
    (swapped_guard ∧ point_property phi) ($1 ⊕ σ $0) HC HS) as Hcode.
  apply paeq_generalize, paeq_generalize.
  eapply paeq_modus_ponens with (phi := finite_support_code (swapped_guard ∧ point_property phi));
    [|exact Hcode].
  apply bit_proof, II.
  set (G := List.cons (finite_support_code (swapped_guard ∧ point_property phi)) bit_context).
  apply (filtered_code_to_pointed G phi).
  - unfold G. apply has_bit_cons. exact bit_context_self.
  - apply Ctx. unfold G. now left.
Qed.
Lemma translate_pointed phi :
  translate (Compact238.pointed_ax phi) = ∀ ∀ pointed_code (translate phi).
Proof.
  unfold Compact238.pointed_ax, Compact238.pointed_body.
  change ((∀ ∀ ∃ ((∀ ((coded_member $3 $0 →
      translate (phi[Compact238.member_slots]) → coded_member $1 $0) ∧
    (coded_member $1 $0 → translate (phi[Compact238.member_slots])))) ∧
    (translate (phi[Compact238.point_slots]) → coded_member $0 $1))) =
    ∀ ∀ pointed_code (translate phi)).
  rewrite !translate_subst.
  assert (HM : (translate phi)[embed_substitution Compact238.member_slots] =
    (translate phi)[member_slots]).
  { apply subst_ext. intros [|[|[|k]]]; reflexivity. }
  assert (HP : (translate phi)[embed_substitution Compact238.point_slots] =
    (translate phi)[point_slots]).
  { apply subst_ext. intros [|[|[|k]]]; reflexivity. }
  rewrite HM, HP. reflexivity.
Qed.
Theorem pointed_from_actual_bounded_comprehension :
  bounded_comprehension_goal -> pointed_producer_goal.
Proof.
  intros HC phi n Hclosed. rewrite translate_forall_times. apply paeq_capture.
  rewrite translate_pointed. apply arithmetic_pointed_from_actual_certificate. apply HC.
Qed.

End PAPointedFromCode238.

Print Assumptions PAPointedFromCode238.filtered_code_to_pointed.
Print Assumptions PAPointedFromCode238.arithmetic_pointed_from_actual_certificate.
Print Assumptions PAPointedFromCode238.pointed_from_actual_bounded_comprehension.
