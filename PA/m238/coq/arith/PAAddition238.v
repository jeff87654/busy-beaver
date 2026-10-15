(* Original syntactic arithmetic prerequisites for the reverse interpretation.
   Each equation is constructed in the finite upstream FAeq context. Full
   induction uses PA238's ordinary universally closed axiom interface, so
   every arbitrary parameter is retained and closed by that interface. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAAddition238.

Definition arithmetic_context : list pa_form := FAeq.

Lemma arithmetic_has_equality : PAEqCongruence238.has_equality arithmetic_context.
Proof.
  intros phi Hphi. unfold arithmetic_context, FAeq.
  apply List.in_app_iff. now left.
Qed.

Lemma arithmetic_add_zero : List.In ax_add_zero arithmetic_context.
Proof.
  unfold arithmetic_context, FAeq. apply List.in_app_iff. right.
  unfold FA. now left.
Qed.

Lemma arithmetic_add_rec : List.In ax_add_rec arithmetic_context.
Proof.
  unfold arithmetic_context, FAeq. apply List.in_app_iff. right.
  unfold FA. right. now left.
Qed.

Lemma arithmetic_proof phi : arithmetic_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros H. apply paeq_from_upstream. exists arithmetic_context. split.
  - intros psi Hpsi. apply PAeq_FA. exact Hpsi.
  - exact H.
Qed.

Lemma add_zero_instance G a :
  List.In ax_add_zero G -> G ⊢C (zero ⊕ a == a).
Proof.
  intros H. change (G ⊢C (zero ⊕ $0 == $0)[a..]).
  apply (subst_forall_prv (phi := zero ⊕ $0 == $0) (N := 1)).
  - change (G ⊢C ax_add_zero). now apply Ctx.
  - solve_bounds.
Qed.

Lemma right_zero_base : paeq_derivable (zero ⊕ zero == zero).
Proof. apply arithmetic_proof, add_zero_instance, arithmetic_add_zero. Qed.

Lemma right_zero_step :
  paeq_derivable (∀ ($0 ⊕ zero == $0 → σ $0 ⊕ zero == σ $0)).
Proof.
  apply paeq_generalize, arithmetic_proof, II.
  set (G := List.cons ($0 ⊕ zero == $0) arithmetic_context).
  change (G ⊢C (σ $0 ⊕ zero == σ $0)).
  assert (HE : PAEqCongruence238.has_equality G).
  { unfold G. apply PAEqCongruence238.has_equality_cons.
    exact arithmetic_has_equality. }
  assert (HR : G ⊢C (σ $0 ⊕ zero == σ ($0 ⊕ zero))).
  { apply PAOrder238.add_rec_instance. unfold G. right. exact arithmetic_add_rec. }
  assert (HI : G ⊢C ($0 ⊕ zero == $0)).
  { apply Ctx. unfold G. now left. }
  pose proof (IE (PAEqCongruence238.successor_instance G ($0 ⊕ zero) $0 HE) HI) as HS.
  exact (PAEqCongruence238.equality_transitivity G
    (σ $0 ⊕ zero) (σ ($0 ⊕ zero)) (σ $0) HE HR HS).
Qed.

Theorem add_right_zero : paeq_derivable (∀ ($0 ⊕ zero == $0)).
Proof.
  apply (paeq_induction_rule ($0 ⊕ zero == $0)).
  - exact right_zero_base.
  - exact right_zero_step.
Qed.

Definition right_successor_formula : pa_form :=
  $0 ⊕ σ $1 == σ ($0 ⊕ $1).

Lemma right_successor_base : paeq_derivable right_successor_formula[zero..].
Proof.
  change (paeq_derivable (zero ⊕ σ $0 == σ (zero ⊕ $0))).
  apply arithmetic_proof.
  pose proof (add_zero_instance arithmetic_context (σ $0) arithmetic_add_zero) as HZ.
  pose proof (add_zero_instance arithmetic_context $0 arithmetic_add_zero) as HB.
  pose proof (IE (PAEqCongruence238.successor_instance arithmetic_context
    (zero ⊕ $0) $0 arithmetic_has_equality) HB) as HS.
  pose proof (PAEqCongruence238.equality_symmetry arithmetic_context
    (σ (zero ⊕ $0)) (σ $0) arithmetic_has_equality HS) as HT.
  exact (PAEqCongruence238.equality_transitivity arithmetic_context
    (zero ⊕ σ $0) (σ $0) (σ (zero ⊕ $0)) arithmetic_has_equality HZ HT).
Qed.

Lemma right_successor_step :
  paeq_derivable (∀ (right_successor_formula →
    right_successor_formula[σ $0 .: S >> var])).
Proof.
  change (paeq_derivable (∀
    ($0 ⊕ σ $1 == σ ($0 ⊕ $1) → σ $0 ⊕ σ $1 == σ (σ $0 ⊕ $1)))).
  apply paeq_generalize, arithmetic_proof, II.
  set (G := List.cons ($0 ⊕ σ $1 == σ ($0 ⊕ $1)) arithmetic_context).
  change (G ⊢C (σ $0 ⊕ σ $1 == σ (σ $0 ⊕ $1))).
  assert (HE : PAEqCongruence238.has_equality G).
  { unfold G. apply PAEqCongruence238.has_equality_cons.
    exact arithmetic_has_equality. }
  assert (Hrec : List.In ax_add_rec G).
  { unfold G. right. exact arithmetic_add_rec. }
  assert (HI : G ⊢C ($0 ⊕ σ $1 == σ ($0 ⊕ $1))).
  { apply Ctx. unfold G. now left. }
  pose proof (PAOrder238.add_rec_instance G $0 (σ $1) Hrec) as Hleft.
  pose proof (IE (PAEqCongruence238.successor_instance G
    ($0 ⊕ σ $1) (σ ($0 ⊕ $1)) HE) HI) as Hmid.
  pose proof (PAOrder238.add_rec_instance G $0 $1 Hrec) as Hr.
  pose proof (IE (PAEqCongruence238.successor_instance G
    (σ $0 ⊕ $1) (σ ($0 ⊕ $1)) HE) Hr) as Hright.
  pose proof (PAEqCongruence238.equality_symmetry G
    (σ (σ $0 ⊕ $1)) (σ (σ ($0 ⊕ $1))) HE Hright) as Hback.
  pose proof (PAEqCongruence238.equality_transitivity G
    (σ $0 ⊕ σ $1) (σ ($0 ⊕ σ $1)) (σ (σ ($0 ⊕ $1))) HE Hleft Hmid) as Hfront.
  exact (PAEqCongruence238.equality_transitivity G
    (σ $0 ⊕ σ $1) (σ (σ ($0 ⊕ $1))) (σ (σ $0 ⊕ $1)) HE Hfront Hback).
Qed.

Theorem add_right_successor :
  paeq_derivable (∀ ∀ ($0 ⊕ σ $1 == σ ($0 ⊕ $1))).
Proof.
  apply paeq_generalize.
  apply (paeq_induction_rule right_successor_formula).
  - exact right_successor_base.
  - exact right_successor_step.
Qed.

Definition associativity_formula : pa_form :=
  $0 ⊕ ($1 ⊕ $2) == ($0 ⊕ $1) ⊕ $2.

Lemma associativity_base : paeq_derivable associativity_formula[zero..].
Proof.
  change (paeq_derivable (zero ⊕ ($0 ⊕ $1) == (zero ⊕ $0) ⊕ $1)).
  apply arithmetic_proof.
  pose proof (add_zero_instance arithmetic_context ($0 ⊕ $1) arithmetic_add_zero) as Hleft.
  pose proof (add_zero_instance arithmetic_context $0 arithmetic_add_zero) as Hzero.
  pose proof (PAEqCongruence238.reflexivity_instance arithmetic_context $1 arithmetic_has_equality) as Hrefl.
  pose proof (IE (IE (PAEqCongruence238.addition_instance arithmetic_context
    (zero ⊕ $0) $0 $1 $1 arithmetic_has_equality) Hzero) Hrefl) as Hright.
  pose proof (PAEqCongruence238.equality_symmetry arithmetic_context
    ((zero ⊕ $0) ⊕ $1) ($0 ⊕ $1) arithmetic_has_equality Hright) as Hback.
  exact (PAEqCongruence238.equality_transitivity arithmetic_context
    (zero ⊕ ($0 ⊕ $1)) ($0 ⊕ $1) ((zero ⊕ $0) ⊕ $1)
    arithmetic_has_equality Hleft Hback).
Qed.

Lemma associativity_step :
  paeq_derivable (∀ (associativity_formula →
    associativity_formula[σ $0 .: S >> var])).
Proof.
  change (paeq_derivable (∀
    ($0 ⊕ ($1 ⊕ $2) == ($0 ⊕ $1) ⊕ $2 →
      σ $0 ⊕ ($1 ⊕ $2) == (σ $0 ⊕ $1) ⊕ $2))).
  apply paeq_generalize, arithmetic_proof, II.
  set (G := List.cons ($0 ⊕ ($1 ⊕ $2) == ($0 ⊕ $1) ⊕ $2) arithmetic_context).
  change (G ⊢C (σ $0 ⊕ ($1 ⊕ $2) == (σ $0 ⊕ $1) ⊕ $2)).
  assert (HE : PAEqCongruence238.has_equality G).
  { unfold G. apply PAEqCongruence238.has_equality_cons.
    exact arithmetic_has_equality. }
  assert (Hrec : List.In ax_add_rec G).
  { unfold G. right. exact arithmetic_add_rec. }
  assert (HI : G ⊢C ($0 ⊕ ($1 ⊕ $2) == ($0 ⊕ $1) ⊕ $2)).
  { apply Ctx. unfold G. now left. }
  pose proof (PAOrder238.add_rec_instance G $0 ($1 ⊕ $2) Hrec) as Hleft.
  pose proof (IE (PAEqCongruence238.successor_instance G
    ($0 ⊕ ($1 ⊕ $2)) (($0 ⊕ $1) ⊕ $2) HE) HI) as Hmid.
  pose proof (PAEqCongruence238.equality_transitivity G
    (σ $0 ⊕ ($1 ⊕ $2)) (σ ($0 ⊕ ($1 ⊕ $2))) (σ (($0 ⊕ $1) ⊕ $2))
    HE Hleft Hmid) as Hfront.
  pose proof (PAOrder238.add_rec_instance G $0 $1 Hrec) as Hinner.
  pose proof (PAEqCongruence238.reflexivity_instance G $2 HE) as Hrefl.
  pose proof (IE (IE (PAEqCongruence238.addition_instance G
    (σ $0 ⊕ $1) (σ ($0 ⊕ $1)) $2 $2 HE) Hinner) Hrefl) as Houter.
  pose proof (PAOrder238.add_rec_instance G ($0 ⊕ $1) $2 Hrec) as Hlast.
  pose proof (PAEqCongruence238.equality_transitivity G
    ((σ $0 ⊕ $1) ⊕ $2) (σ ($0 ⊕ $1) ⊕ $2) (σ (($0 ⊕ $1) ⊕ $2))
    HE Houter Hlast) as Hright.
  pose proof (PAEqCongruence238.equality_symmetry G
    ((σ $0 ⊕ $1) ⊕ $2) (σ (($0 ⊕ $1) ⊕ $2)) HE Hright) as Hback.
  exact (PAEqCongruence238.equality_transitivity G
    (σ $0 ⊕ ($1 ⊕ $2)) (σ (($0 ⊕ $1) ⊕ $2)) ((σ $0 ⊕ $1) ⊕ $2)
    HE Hfront Hback).
Qed.

Theorem add_associative :
  paeq_derivable (∀ ∀ ∀ ($0 ⊕ ($1 ⊕ $2) == ($0 ⊕ $1) ⊕ $2)).
Proof.
  apply paeq_generalize, paeq_generalize.
  apply (paeq_induction_rule associativity_formula).
  - exact associativity_base.
  - exact associativity_step.
Qed.

End PAAddition238.

Print Assumptions PAAddition238.add_right_zero.
Print Assumptions PAAddition238.add_right_successor.
Print Assumptions PAAddition238.add_associative.
