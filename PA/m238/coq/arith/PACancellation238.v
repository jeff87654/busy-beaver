(* Original finite PA induction certificates used to peel quotient witnesses
   in beta remainder uniqueness. No arithmetic equality is supplied by a
   model or an adequacy hypothesis. Arbitrary parameters are universally
   closed through the ordinary PA238 induction interface. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238 PAAddition238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PACancellation238.

Definition cancellation_context : list pa_form := FAeq ++ [ax_succ_inj].

Lemma cancellation_proof phi : cancellation_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. apply paeq_from_upstream. exists cancellation_context. split.
  - intros psi Hpsi. unfold cancellation_context in Hpsi.
    apply List.in_app_iff in Hpsi as [Hpsi|Hpsi].
    + now apply PAeq_FA.
    + destruct Hpsi as [<-|[]]. apply PAeq_inj.
  - exact HD.
Qed.

Lemma cancellation_primitive phi :
  List.In phi FAeq -> List.In phi cancellation_context.
Proof. intros H. unfold cancellation_context. apply List.in_app_iff. now left. Qed.

Lemma cancellation_has_equality : PAEqCongruence238.has_equality cancellation_context.
Proof.
  intros phi Hphi. apply cancellation_primitive. unfold FAeq.
  apply List.in_app_iff. now left.
Qed.

Lemma cancellation_add_zero : List.In ax_add_zero cancellation_context.
Proof.
  apply cancellation_primitive. unfold FAeq. apply List.in_app_iff. right.
  unfold FA. now left.
Qed.
Lemma cancellation_add_rec : List.In ax_add_rec cancellation_context.
Proof.
  apply cancellation_primitive. unfold FAeq. apply List.in_app_iff. right.
  unfold FA. right. now left.
Qed.
Lemma cancellation_injective : List.In ax_succ_inj cancellation_context.
Proof. unfold cancellation_context. apply List.in_app_iff. right. now left. Qed.

Definition left_cancellation_formula : pa_form :=
  $0 ⊕ $1 == $0 ⊕ $2 → $1 == $2.

Lemma left_cancellation_base :
  paeq_derivable left_cancellation_formula[zero..].
Proof.
  change (paeq_derivable (zero ⊕ $0 == zero ⊕ $1 → $0 == $1)).
  apply cancellation_proof, II.
  set (G := List.cons (zero ⊕ $0 == zero ⊕ $1) cancellation_context).
  change (G ⊢C ($0 == $1)).
  assert (HE : PAEqCongruence238.has_equality G).
  { unfold G. apply PAEqCongruence238.has_equality_cons. exact cancellation_has_equality. }
  assert (H0 : List.In ax_add_zero G).
  { unfold G. right. exact cancellation_add_zero. }
  assert (HI : G ⊢C (zero ⊕ $0 == zero ⊕ $1)).
  { apply Ctx. unfold G. now left. }
  pose proof (PAAddition238.add_zero_instance G $0 H0) as HL.
  pose proof (PAAddition238.add_zero_instance G $1 H0) as HR.
  pose proof (PAEqCongruence238.equality_symmetry G (zero ⊕ $0) $0 HE HL) as HB.
  pose proof (PAEqCongruence238.equality_transitivity G
    $0 (zero ⊕ $0) (zero ⊕ $1) HE HB HI) as HF.
  exact (PAEqCongruence238.equality_transitivity G $0 (zero ⊕ $1) $1 HE HF HR).
Qed.

Lemma left_cancellation_step :
  paeq_derivable (∀ (left_cancellation_formula →
    left_cancellation_formula[σ $0 .: S >> var])).
Proof.
  change (paeq_derivable (∀
    (($0 ⊕ $1 == $0 ⊕ $2 → $1 == $2) → σ $0 ⊕ $1 == σ $0 ⊕ $2 → $1 == $2))).
  apply paeq_generalize, cancellation_proof, II, II.
  set (G := List.cons (σ $0 ⊕ $1 == σ $0 ⊕ $2)
    (List.cons ($0 ⊕ $1 == $0 ⊕ $2 → $1 == $2) cancellation_context)).
  change (G ⊢C ($1 == $2)).
  assert (HE : PAEqCongruence238.has_equality G).
  { unfold G. apply PAEqCongruence238.has_equality_cons,
      PAEqCongruence238.has_equality_cons. exact cancellation_has_equality. }
  assert (Hrec : List.In ax_add_rec G).
  { unfold G. right. right. exact cancellation_add_rec. }
  assert (Hinj : List.In ax_succ_inj G).
  { unfold G. right. right. exact cancellation_injective. }
  assert (HI : G ⊢C ($0 ⊕ $1 == $0 ⊕ $2 → $1 == $2)).
  { apply Ctx. unfold G. right. now left. }
  assert (HS : G ⊢C (σ $0 ⊕ $1 == σ $0 ⊕ $2)).
  { apply Ctx. unfold G. now left. }
  pose proof (PAOrder238.add_rec_instance G $0 $1 Hrec) as HL.
  pose proof (PAOrder238.add_rec_instance G $0 $2 Hrec) as HR.
  pose proof (PAEqCongruence238.equality_symmetry G
    (σ $0 ⊕ $1) (σ ($0 ⊕ $1)) HE HL) as HB.
  pose proof (PAEqCongruence238.equality_transitivity G
    (σ ($0 ⊕ $1)) (σ $0 ⊕ $1) (σ $0 ⊕ $2) HE HB HS) as HF.
  pose proof (PAEqCongruence238.equality_transitivity G
    (σ ($0 ⊕ $1)) (σ $0 ⊕ $2) (σ ($0 ⊕ $2)) HE HF HR) as HH.
  pose proof (IE (PAOrder238.succ_inj_instance G ($0 ⊕ $1) ($0 ⊕ $2) Hinj) HH) as HM.
  exact (IE HI HM).
Qed.

Theorem add_cancel_left :
  paeq_derivable (∀ ∀ ∀ ($0 ⊕ $1 == $0 ⊕ $2 → $1 == $2)).
Proof.
  apply paeq_generalize, paeq_generalize.
  apply (paeq_induction_rule left_cancellation_formula).
  - exact left_cancellation_base.
  - exact left_cancellation_step.
Qed.

Definition predecessor_formula : pa_form := $0 == zero ∨ ∃ ($1 == σ $0).

Lemma predecessor_base : paeq_derivable predecessor_formula[zero..].
Proof.
  apply cancellation_proof, DI1.
  exact (PAEqCongruence238.reflexivity_instance cancellation_context zero cancellation_has_equality).
Qed.

Lemma predecessor_step :
  paeq_derivable (∀ (predecessor_formula → predecessor_formula[σ $0 .: S >> var])).
Proof.
  apply paeq_generalize, cancellation_proof, II.
  set (G := List.cons predecessor_formula cancellation_context).
  change (G ⊢C ((σ $0 == zero) ∨ ∃ (σ $1 == σ $0))).
  apply DI2, (ExI $0). change (G ⊢C (σ $0 == σ $0)).
  assert (HE : PAEqCongruence238.has_equality G).
  { unfold G. apply PAEqCongruence238.has_equality_cons. exact cancellation_has_equality. }
  exact (PAEqCongruence238.reflexivity_instance G (σ $0) HE).
Qed.

Theorem zero_or_successor : paeq_derivable (∀ ($0 == zero ∨ ∃ ($1 == σ $0))).
Proof.
  apply (paeq_induction_rule predecessor_formula).
  - exact predecessor_base.
  - exact predecessor_step.
Qed.

End PACancellation238.

Print Assumptions PACancellation238.add_cancel_left.
Print Assumptions PACancellation238.zero_or_successor.
