(* Original finite PA proof transformations for fixed-formula comprehension.
   These consume concrete PA certificates and preserve their finite ordinary
   axiom lists. The arithmetic coding-existence certificate is an explicit
   input, not an additional axiom or a supplied adequacy assertion. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 CompactInPA238 PAEqCongruence238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 CompactInPA238 PAEqCongruence238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAFiniteSupport238.

Definition bound_slots : nat -> pa_term := $0 .: (fun k => $(3 + k)).
Definition bounded_axiom_body (phi : pa_form) : pa_form :=
  ∃ ∀ (coded_member $1 $0 ↔ (($0 ⧀ $2) ∧ phi[bound_slots])).
Definition bounded_code (phi : pa_form) (B : pa_term) : pa_form :=
  ∃ ∀ (coded_member $1 $0 ↔ (($0 ⧀ B`[↑]`[↑]) ∧ phi[up ↑])).
Definition support_bound (phi : pa_form) (B : pa_term) : pa_form :=
  ∀ (phi → $0 ⧀ B`[↑]).
Definition finite_support_code (phi : pa_form) : pa_form :=
  ∃ ∀ (coded_member $1 $0 ↔ phi[up ↑]).
Definition bounded_code_body (phi : pa_form) (B C : pa_term) : pa_form :=
  ∀ (coded_member C`[↑] $0 ↔ (($0 ⧀ B`[↑]) ∧ phi)).
Definition finite_support_body (phi : pa_form) (C : pa_term) : pa_form :=
  ∀ (coded_member C`[↑] $0 ↔ phi).

Lemma bounded_comprehension_body phi :
  bounded_comprehension phi = ∀ bounded_axiom_body phi.
Proof. reflexivity. Qed.
Lemma member_shift_cancel (phi : pa_form) (C : pa_term) :
  phi[up ↑][up (C..)] = phi.
Proof.
  rewrite subst_comp. transitivity phi[var].
  - apply subst_ext. intros [|k]; reflexivity.
  - apply subst_var.
Qed.
Lemma bounded_axiom_at phi B : (bounded_axiom_body phi)[B..] = bounded_code phi B.
Proof.
  unfold bounded_axiom_body, bounded_code.
  change ((∃ ∀ ((coded_member $1 $0)[up (up (B..))] ↔
    ((PAlt $0 $2)[up (up (B..))] ∧ phi[bound_slots][up (up (B..))]))) =
    ∃ ∀ (coded_member $1 $0 ↔ (($0 ⧀ B`[↑]`[↑]) ∧ phi[up ↑]))).
  assert (HS : phi[bound_slots][up (up (B..))] = phi[up ↑]).
  { rewrite subst_comp. apply subst_ext. intros [|k];
      cbn [bound_slots up scons funcomp subst_term]; reflexivity. }
  rewrite HS, coded_member_subst, PAlt_subst. reflexivity.
Qed.
Lemma bounded_code_witness phi B C :
  (∀ (coded_member $1 $0 ↔ (($0 ⧀ B`[↑]`[↑]) ∧ phi[up ↑])))[C..] =
  bounded_code_body phi B C.
Proof.
  unfold bounded_code_body.
  change ((∀ ((coded_member $1 $0)[up (C..)] ↔
    ((PAlt $0 B`[↑]`[↑])[up (C..)] ∧ phi[up ↑][up (C..)]))) =
    ∀ (coded_member C`[↑] $0 ↔ (($0 ⧀ B`[↑]) ∧ phi))).
  rewrite member_shift_cancel, coded_member_subst, PAlt_subst.
  assert (HB : B`[↑]`[↑]`[up (C..)] = B`[↑]).
  { rewrite up_term, subst_term_shift. reflexivity. }
  rewrite HB. reflexivity.
Qed.
Lemma finite_support_witness phi C :
  (∀ (coded_member $1 $0 ↔ phi[up ↑]))[C..] = finite_support_body phi C.
Proof.
  unfold finite_support_body.
  change ((∀ ((coded_member $1 $0)[up (C..)] ↔ phi[up ↑][up (C..)])) =
    ∀ (coded_member C`[↑] $0 ↔ phi)).
  rewrite member_shift_cancel, coded_member_subst. reflexivity.
Qed.

Lemma bounded_code_at G phi B :
  G ⊢C bounded_comprehension phi -> G ⊢C bounded_code phi B.
Proof.
  intros H. rewrite bounded_comprehension_body in H.
  pose proof (AllE B H) as HK. rewrite bounded_axiom_at in HK. exact HK.
Qed.
Lemma finite_support_introduce G phi C :
  G ⊢C finite_support_body phi C -> G ⊢C finite_support_code phi.
Proof.
  intros H. unfold finite_support_code. apply (ExI C).
  rewrite finite_support_witness. exact H.
Qed.
Lemma remove_finite_bound G phi B :
  G ⊢C bounded_code phi B -> G ⊢C support_bound phi B ->
  G ⊢C finite_support_code phi.
Proof.
  intros HC HS. unfold bounded_code in HC.
  eapply ExE_named; [exact HC|]. intros C. rewrite bounded_code_witness.
  set (D := List.cons (bounded_code_body phi B C) G).
  change (D ⊢C finite_support_code phi).
  apply (finite_support_introduce D phi C).
  assert (HC' : D ⊢C bounded_code_body phi B C).
  { apply Ctx. unfold D. now left. }
  pose proof (weaken_head G (support_bound phi B) (bounded_code_body phi B C) HS) as HS'.
  exact (forall_forget_finite_bound D ($0 ⧀ B`[↑]) phi
    (coded_member C`[↑] $0) HS' HC').
Qed.

Lemma ordinary_unclose phi :
  paeq_derivable (universal_close phi) -> paeq_derivable phi.
Proof.
  intros (A & HA & HD). exists A. split; [exact HA|].
  apply close_extract. exact HD.
Qed.
Lemma ordinary_bounded_code phi B :
  paeq_derivable (universal_close (bounded_comprehension phi)) ->
  paeq_derivable (bounded_code phi B).
Proof.
  intros H. destruct (ordinary_unclose (bounded_comprehension phi) H) as (A & HA & HD).
  exists A. split; [exact HA|]. exact (bounded_code_at A phi B HD).
Qed.
Lemma ordinary_remove_finite_bound phi B :
  paeq_derivable (bounded_code phi B) -> paeq_derivable (support_bound phi B) ->
  paeq_derivable (finite_support_code phi).
Proof.
  intros (A & HA & HC) (Bctx & HBctx & HS).
  exists (List.app A Bctx). split.
  - intros psi Hpsi. apply List.in_app_iff in Hpsi as [Hpsi|Hpsi];
      [exact (HA psi Hpsi)|exact (HBctx psi Hpsi)].
  - apply (remove_finite_bound (List.app A Bctx) phi B).
    + eapply Weak; [exact HC|]. intros psi Hpsi. apply List.in_app_iff. now left.
    + eapply Weak; [exact HS|]. intros psi Hpsi. apply List.in_app_iff. now right.
Qed.
Theorem finite_support_from_actual_bounded_certificate phi B :
  paeq_derivable (universal_close (bounded_comprehension phi)) ->
  paeq_derivable (support_bound phi B) -> paeq_derivable (finite_support_code phi).
Proof.
  intros HC HS. exact (ordinary_remove_finite_bound phi B (ordinary_bounded_code phi B HC) HS).
Qed.

End PAFiniteSupport238.

Print Assumptions PAFiniteSupport238.bounded_code_at.
Print Assumptions PAFiniteSupport238.remove_finite_bound.
Print Assumptions PAFiniteSupport238.finite_support_from_actual_bounded_certificate.
