(* Original finite PA Separation transport for every fixed arithmetic formula.
   Its support bound is supplied by the actual Ackermann bit-position proof.
   The only coding input is the concrete bounded-comprehension certificate
   for that formula; this file does not assume a coding producer axiom. *)
From Coq Require Import List.
From Undecidability.FOL.Sets Require Import Signatures.
From Undecidability.FOL.Syntax Require Import BinSig.
From P238.arith Require Import PAeq238 Compact238 CompactInPA238 PABitPosition238
  PAFiniteSupport238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 CompactInPA238 PABitPosition238 PAFiniteSupport238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PASeparationFromCode238.

Definition separation_property (phi : pa_form) : pa_form :=
  coded_member $1 $0 ∧ phi[up ↑].
Definition separation_formula (phi : pa_form) : pa_form :=
  ∀ ∃ ∀ (coded_member $1 $0 ↔ (coded_member $2 $0 ∧ phi[bound_slots])).
Lemma member_shift_twice (phi : pa_form) : phi[up ↑][up ↑] = phi[bound_slots].
Proof.
  rewrite subst_comp. apply subst_ext. intros [|k];
    cbn [bound_slots up scons funcomp subst_term]; reflexivity.
Qed.
Lemma separation_code_equation phi :
  finite_support_code (separation_property phi) =
  ∃ ∀ (coded_member $1 $0 ↔ (coded_member $2 $0 ∧ phi[bound_slots])).
Proof.
  unfold finite_support_code, separation_property.
  change ((∃ ∀ (coded_member $1 $0 ↔
    ((coded_member $1 $0)[up ↑] ∧ phi[up ↑][up ↑]))) =
    ∃ ∀ (coded_member $1 $0 ↔ (coded_member $2 $0 ∧ phi[bound_slots]))).
  rewrite coded_member_subst, member_shift_twice. reflexivity.
Qed.

Lemma separation_support phi :
  paeq_derivable (support_bound (separation_property phi) $0).
Proof.
  unfold support_bound. apply bit_proof, AllI_named. intros x.
  change (bit_context ⊢C (separation_property phi)[x..] → (PAlt $0 $1)[x..]).
  rewrite PAlt_subst.
  change (bit_context ⊢C (separation_property phi)[x..] → x ⧀ $0). apply II.
  set (G := List.cons (separation_property phi)[x..] bit_context).
  change (G ⊢C (x ⧀ $0)).
  assert (HG : has_bit_context G).
  { unfold G. apply has_bit_cons. exact bit_context_self. }
  assert (HC : G ⊢C (separation_property phi)[x..]).
  { apply Ctx. unfold G. now left. }
  change (G ⊢C ((coded_member $1 $0)[x..] ∧ (phi[up ↑])[x..])) in HC.
  pose proof (CE1 HC) as HM. rewrite coded_member_subst in HM.
  change (G ⊢C coded_member $0 x) in HM.
  exact (bit_position G $0 x HG HM).
Qed.
Theorem arithmetic_separation_from_actual_certificate phi :
  paeq_derivable (universal_close (bounded_comprehension (separation_property phi))) ->
  paeq_derivable (separation_formula phi).
Proof.
  intros HC. pose proof (finite_support_from_actual_bounded_certificate
    (separation_property phi) $0 HC (separation_support phi)) as HS.
  unfold separation_formula. apply paeq_generalize.
  rewrite <- separation_code_equation. exact HS.
Qed.

Lemma translate_separation phi :
  translate (Compact238.separation_ax phi) = separation_formula (translate phi).
Proof.
  unfold Compact238.separation_ax, separation_formula.
  change ((∀ ∃ ∀ (coded_member $1 $0 ↔
    (coded_member $2 $0 ∧ translate (phi[Compact238.separation_slots])))) =
    ∀ ∃ ∀ (coded_member $1 $0 ↔
      (coded_member $2 $0 ∧ (translate phi)[bound_slots]))).
  rewrite translate_subst.
  assert (HS : (translate phi)[embed_substitution Compact238.separation_slots] =
    (translate phi)[bound_slots]).
  { apply subst_ext. intros [|k]; reflexivity. }
  rewrite HS. reflexivity.
Qed.
Lemma translate_forall_times n (phi : Compact238.set_form) :
  translate (@FullSyntax.forall_times BinSig.sig_empty ZFSignature.ZF_pred_sig
    falsity_on n phi) =
  @capture PA_funcs_signature PA_preds_signature full_operators falsity_on All n (translate phi).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - change ((∀ translate (@FullSyntax.forall_times BinSig.sig_empty ZFSignature.ZF_pred_sig
      falsity_on n phi)) =
      ∀ (@capture PA_funcs_signature PA_preds_signature full_operators falsity_on All n (translate phi))).
    now rewrite IH.
Qed.

Theorem separation_from_actual_bounded_comprehension :
  bounded_comprehension_goal -> separation_producer_goal.
Proof.
  intros HC phi n Hclosed. rewrite translate_forall_times. apply paeq_capture.
  rewrite translate_separation.
  apply arithmetic_separation_from_actual_certificate. apply HC.
Qed.

End PASeparationFromCode238.

Print Assumptions PASeparationFromCode238.separation_support.
Print Assumptions PASeparationFromCode238.arithmetic_separation_from_actual_certificate.
Print Assumptions PASeparationFromCode238.separation_from_actual_bounded_comprehension.
