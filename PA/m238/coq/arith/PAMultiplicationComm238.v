(* Original finite ordinary-PA commutativity certificates.  All induction
   parameters are closed by PA238's ordinary axiom interface.  Derived
   sentences enter each finite context only by cutting their certificates. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238
  PAAddition238 PAOrderBounds238 PAQuotient238 PASemiring238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrderBounds238
  PAQuotient238 PASemiring238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAMultiplicationComm238.

Definition add_commutativity_formula : pa_form := $0 ⊕ $1 == $1 ⊕ $0.

Lemma add_commutativity_base :
  paeq_derivable add_commutativity_formula[zero..].
Proof.
  change (paeq_derivable (zero ⊕ $0 == $0 ⊕ zero)).
  apply product_proof.
  pose proof (product_has_equality product_context product_context_self) as HE.
  pose proof (PAAddition238.add_zero_instance product_context $0 product_add_zero) as HL.
  assert (HZ : product_context ⊢C right_zero_sentence).
  { apply Ctx. exact bounds_right_zero. }
  pose proof (AllE $0 HZ) as HR.
  change (product_context ⊢C ($0 ⊕ zero == $0)) in HR.
  pose proof (equality_symmetry product_context ($0 ⊕ zero) $0 HE HR) as HB.
  exact (equality_transitivity product_context (zero ⊕ $0) $0
    ($0 ⊕ zero) HE HL HB).
Qed.

Lemma add_commutativity_step : paeq_derivable
  (∀ (add_commutativity_formula →
    add_commutativity_formula[σ $0 .: S >> var])).
Proof.
  change (paeq_derivable (∀
    ($0 ⊕ $1 == $1 ⊕ $0 → σ $0 ⊕ $1 == $1 ⊕ σ $0))).
  apply paeq_generalize, product_proof, II.
  set (G := List.cons ($0 ⊕ $1 == $1 ⊕ $0) product_context).
  assert (HG : has_product_context G).
  { unfold G. apply has_product_cons. exact product_context_self. }
  pose proof (product_has_equality G HG) as HE.
  assert (HI : G ⊢C ($0 ⊕ $1 == $1 ⊕ $0)).
  { apply Ctx. unfold G. now left. }
  pose proof (PAOrder238.add_rec_instance G $0 $1
    (HG ax_add_rec product_add_rec)) as HL.
  pose proof (IE (successor_instance G ($0 ⊕ $1) ($1 ⊕ $0) HE) HI) as HM.
  pose proof (right_successor_instance G $1 $0
    (HG right_successor_sentence bounds_right_successor)) as HR.
  pose proof (equality_symmetry G ($1 ⊕ σ $0) (σ ($1 ⊕ $0)) HE HR) as HB.
  pose proof (equality_transitivity G (σ $0 ⊕ $1) (σ ($0 ⊕ $1))
    (σ ($1 ⊕ $0)) HE HL HM) as HF.
  exact (equality_transitivity G (σ $0 ⊕ $1) (σ ($1 ⊕ $0))
    ($1 ⊕ σ $0) HE HF HB).
Qed.

Theorem add_commutative : paeq_derivable (∀ ∀ ($0 ⊕ $1 == $1 ⊕ $0)).
Proof.
  apply paeq_generalize.
  apply (paeq_induction_rule add_commutativity_formula).
  - exact add_commutativity_base.
  - exact add_commutativity_step.
Qed.

Definition add_commutativity_sentence : pa_form :=
  ∀ ∀ ($0 ⊕ $1 == $1 ⊕ $0).
Definition addition_context : list pa_form :=
  List.cons add_commutativity_sentence product_context.
Definition has_addition_context (G : list pa_form) : Prop :=
  forall phi, List.In phi addition_context -> List.In phi G.

Lemma addition_proof phi : addition_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := add_commutativity_sentence).
  - apply product_proof, II. exact HD.
  - exact add_commutative.
Qed.
Lemma addition_context_self : has_addition_context addition_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_addition_cons G phi : has_addition_context G ->
  has_addition_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma addition_has_product G : has_addition_context G -> has_product_context G.
Proof. intros HG phi Hphi. apply HG. unfold addition_context. now right. Qed.
Lemma addition_commutativity : List.In add_commutativity_sentence addition_context.
Proof. unfold addition_context. now left. Qed.

Lemma add_commutative_at G a b : List.In add_commutativity_sentence G ->
  G ⊢C (a ⊕ b == b ⊕ a).
Proof.
  intros H. change (G ⊢C ($0 ⊕ $1 == $1 ⊕ $0)[a .: b .: var]).
  apply (subst_forall_prv (phi := $0 ⊕ $1 == $1 ⊕ $0) (N := 2)).
  - change (G ⊢C add_commutativity_sentence). now apply Ctx.
  - solve_bounds.
Qed.

(* This explicit exchange is the only additive rearrangement in the right
   successor induction.  It is three equality cuts, with congruence under
   the final addition between the two associativity steps. *)
Lemma add_exchange G a b c : has_addition_context G ->
  G ⊢C (a ⊕ (b ⊕ c) == b ⊕ (a ⊕ c)).
Proof.
  intros HG.
  pose proof (addition_has_product G HG) as HP.
  pose proof (product_has_equality G HP) as HE.
  pose proof (associativity_instance G a b c
    (HP associativity_sentence product_associativity)) as Hfirst.
  pose proof (add_commutative_at G a b
    (HG add_commutativity_sentence addition_commutativity)) as HC.
  pose proof (reflexivity_instance G c HE) as HR.
  pose proof (IE (IE (addition_instance G (a ⊕ b) (b ⊕ a) c c HE) HC) HR) as Hsecond.
  pose proof (associativity_instance G b a c
    (HP associativity_sentence product_associativity)) as Hthird.
  pose proof (equality_symmetry G (b ⊕ (a ⊕ c)) ((b ⊕ a) ⊕ c) HE Hthird) as Hback.
  pose proof (equality_transitivity G (a ⊕ (b ⊕ c)) ((a ⊕ b) ⊕ c)
    ((b ⊕ a) ⊕ c) HE Hfirst Hsecond) as Hfront.
  exact (equality_transitivity G (a ⊕ (b ⊕ c)) ((b ⊕ a) ⊕ c)
    (b ⊕ (a ⊕ c)) HE Hfront Hback).
Qed.

Definition mult_right_successor_formula : pa_form :=
  $0 ⊗ σ $1 == $0 ⊕ ($0 ⊗ $1).

Lemma mult_right_successor_base :
  paeq_derivable mult_right_successor_formula[zero..].
Proof.
  change (paeq_derivable (zero ⊗ σ $0 == zero ⊕ (zero ⊗ $0))).
  apply product_proof.
  pose proof (product_has_equality product_context product_context_self) as HE.
  pose proof (mult_zero_instance product_context (σ $0) product_mult_zero) as HL.
  pose proof (PAAddition238.add_zero_instance product_context
    (zero ⊗ $0) product_add_zero) as HA.
  pose proof (mult_zero_instance product_context $0 product_mult_zero) as HM.
  pose proof (equality_transitivity product_context (zero ⊕ (zero ⊗ $0))
    (zero ⊗ $0) zero HE HA HM) as HR.
  pose proof (equality_symmetry product_context (zero ⊕ (zero ⊗ $0)) zero HE HR) as HB.
  exact (equality_transitivity product_context (zero ⊗ σ $0) zero
    (zero ⊕ (zero ⊗ $0)) HE HL HB).
Qed.

Lemma mult_right_successor_step : paeq_derivable
  (∀ (mult_right_successor_formula →
    mult_right_successor_formula[σ $0 .: S >> var])).
Proof.
  change (paeq_derivable (∀
    ($0 ⊗ σ $1 == $0 ⊕ ($0 ⊗ $1) →
      σ $0 ⊗ σ $1 == σ $0 ⊕ (σ $0 ⊗ $1)))).
  apply paeq_generalize, addition_proof, II.
  set (G := List.cons ($0 ⊗ σ $1 == $0 ⊕ ($0 ⊗ $1)) addition_context).
  assert (HG : has_addition_context G).
  { unfold G. apply has_addition_cons. exact addition_context_self. }
  pose proof (addition_has_product G HG) as HP.
  pose proof (product_has_equality G HP) as HE.
  assert (HI : G ⊢C ($0 ⊗ σ $1 == $0 ⊕ ($0 ⊗ $1))).
  { apply Ctx. unfold G. now left. }
  pose proof (mult_rec_instance G $0 (σ $1)
    (HP ax_mult_rec product_mult_rec)) as Hfirst.
  pose proof (reflexivity_instance G (σ $1) HE) as HS.
  pose proof (IE (IE (addition_instance G (σ $1) (σ $1) ($0 ⊗ σ $1)
    ($0 ⊕ ($0 ⊗ $1)) HE) HS) HI) as Hsecond.
  pose proof (PAOrder238.add_rec_instance G $1 ($0 ⊕ ($0 ⊗ $1))
    (HP ax_add_rec product_add_rec)) as Hthird.
  pose proof (add_exchange G $1 $0 ($0 ⊗ $1) HG) as HX.
  pose proof (IE (successor_instance G ($1 ⊕ ($0 ⊕ ($0 ⊗ $1)))
    ($0 ⊕ ($1 ⊕ ($0 ⊗ $1))) HE) HX) as Hfourth.
  pose proof (equality_transitivity G (σ $0 ⊗ σ $1)
    (σ $1 ⊕ ($0 ⊗ σ $1)) (σ $1 ⊕ ($0 ⊕ ($0 ⊗ $1)))
    HE Hfirst Hsecond) as H12.
  pose proof (equality_transitivity G (σ $0 ⊗ σ $1)
    (σ $1 ⊕ ($0 ⊕ ($0 ⊗ $1))) (σ ($1 ⊕ ($0 ⊕ ($0 ⊗ $1))))
    HE H12 Hthird) as H123.
  pose proof (equality_transitivity G (σ $0 ⊗ σ $1)
    (σ ($1 ⊕ ($0 ⊕ ($0 ⊗ $1)))) (σ ($0 ⊕ ($1 ⊕ ($0 ⊗ $1))))
    HE H123 Hfourth) as Hleft.
  pose proof (mult_rec_instance G $0 $1
    (HP ax_mult_rec product_mult_rec)) as HM.
  pose proof (reflexivity_instance G (σ $0) HE) as HR.
  pose proof (IE (IE (addition_instance G (σ $0) (σ $0) (σ $0 ⊗ $1)
    ($1 ⊕ ($0 ⊗ $1)) HE) HR) HM) as Hrightfirst.
  pose proof (PAOrder238.add_rec_instance G $0 ($1 ⊕ ($0 ⊗ $1))
    (HP ax_add_rec product_add_rec)) as Hrightsecond.
  pose proof (equality_transitivity G (σ $0 ⊕ (σ $0 ⊗ $1))
    (σ $0 ⊕ ($1 ⊕ ($0 ⊗ $1))) (σ ($0 ⊕ ($1 ⊕ ($0 ⊗ $1))))
    HE Hrightfirst Hrightsecond) as Hright.
  pose proof (equality_symmetry G (σ $0 ⊕ (σ $0 ⊗ $1))
    (σ ($0 ⊕ ($1 ⊕ ($0 ⊗ $1)))) HE Hright) as Hback.
  exact (equality_transitivity G (σ $0 ⊗ σ $1)
    (σ ($0 ⊕ ($1 ⊕ ($0 ⊗ $1)))) (σ $0 ⊕ (σ $0 ⊗ $1)) HE Hleft Hback).
Qed.

Theorem mult_right_successor : paeq_derivable
  (∀ ∀ ($0 ⊗ σ $1 == $0 ⊕ ($0 ⊗ $1))).
Proof.
  apply paeq_generalize.
  apply (paeq_induction_rule mult_right_successor_formula).
  - exact mult_right_successor_base.
  - exact mult_right_successor_step.
Qed.

Definition mult_right_zero_sentence : pa_form := ∀ ($0 ⊗ zero == zero).
Definition mult_right_successor_sentence : pa_form :=
  ∀ ∀ ($0 ⊗ σ $1 == $0 ⊕ ($0 ⊗ $1)).
Definition multiplication_context : list pa_form :=
  List.cons mult_right_successor_sentence
    (List.cons mult_right_zero_sentence addition_context).
Definition has_multiplication_context (G : list pa_form) : Prop :=
  forall phi, List.In phi multiplication_context -> List.In phi G.

Lemma multiplication_proof phi :
  multiplication_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := mult_right_successor_sentence).
  - eapply paeq_modus_ponens with (phi := mult_right_zero_sentence).
    + apply addition_proof, II, II. exact HD.
    + exact PASemiring238.mult_right_zero.
  - exact mult_right_successor.
Qed.
Lemma multiplication_context_self : has_multiplication_context multiplication_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_multiplication_cons G phi : has_multiplication_context G ->
  has_multiplication_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma multiplication_has_addition G : has_multiplication_context G ->
  has_addition_context G.
Proof. intros HG phi Hphi. apply HG. unfold multiplication_context. right. now right. Qed.
Lemma multiplication_right_zero :
  List.In mult_right_zero_sentence multiplication_context.
Proof. unfold multiplication_context. right. now left. Qed.
Lemma multiplication_right_successor :
  List.In mult_right_successor_sentence multiplication_context.
Proof. unfold multiplication_context. now left. Qed.

Lemma mult_right_zero_at G a : List.In mult_right_zero_sentence G ->
  G ⊢C (a ⊗ zero == zero).
Proof.
  intros H. change (G ⊢C ($0 ⊗ zero == zero)[a..]).
  apply (subst_forall_prv (phi := $0 ⊗ zero == zero) (N := 1)).
  - change (G ⊢C mult_right_zero_sentence). now apply Ctx.
  - solve_bounds.
Qed.
Lemma mult_right_successor_at G a b :
  List.In mult_right_successor_sentence G ->
  G ⊢C (a ⊗ σ b == a ⊕ (a ⊗ b)).
Proof.
  intros H. change (G ⊢C ($0 ⊗ σ $1 == $0 ⊕ ($0 ⊗ $1))[a .: b .: var]).
  apply (subst_forall_prv (phi := $0 ⊗ σ $1 == $0 ⊕ ($0 ⊗ $1)) (N := 2)).
  - change (G ⊢C mult_right_successor_sentence). now apply Ctx.
  - solve_bounds.
Qed.

Definition mult_commutativity_formula : pa_form := $0 ⊗ $1 == $1 ⊗ $0.

Lemma mult_commutativity_base :
  paeq_derivable mult_commutativity_formula[zero..].
Proof.
  change (paeq_derivable (zero ⊗ $0 == $0 ⊗ zero)).
  apply multiplication_proof.
  pose proof (multiplication_has_addition multiplication_context multiplication_context_self) as HA.
  pose proof (addition_has_product multiplication_context HA) as HP.
  pose proof (product_has_equality multiplication_context HP) as HE.
  pose proof (mult_zero_instance multiplication_context $0
    (HP ax_mult_zero product_mult_zero)) as HL.
  pose proof (mult_right_zero_at multiplication_context $0 multiplication_right_zero) as HR.
  pose proof (equality_symmetry multiplication_context ($0 ⊗ zero) zero HE HR) as HB.
  exact (equality_transitivity multiplication_context (zero ⊗ $0) zero
    ($0 ⊗ zero) HE HL HB).
Qed.

Lemma mult_commutativity_step : paeq_derivable
  (∀ (mult_commutativity_formula →
    mult_commutativity_formula[σ $0 .: S >> var])).
Proof.
  change (paeq_derivable (∀
    ($0 ⊗ $1 == $1 ⊗ $0 → σ $0 ⊗ $1 == $1 ⊗ σ $0))).
  apply paeq_generalize, multiplication_proof, II.
  set (G := List.cons ($0 ⊗ $1 == $1 ⊗ $0) multiplication_context).
  assert (HG : has_multiplication_context G).
  { unfold G. apply has_multiplication_cons. exact multiplication_context_self. }
  pose proof (multiplication_has_addition G HG) as HA.
  pose proof (addition_has_product G HA) as HP.
  pose proof (product_has_equality G HP) as HE.
  assert (HI : G ⊢C ($0 ⊗ $1 == $1 ⊗ $0)).
  { apply Ctx. unfold G. now left. }
  pose proof (mult_rec_instance G $0 $1
    (HP ax_mult_rec product_mult_rec)) as HL.
  pose proof (reflexivity_instance G $1 HE) as HR.
  pose proof (IE (IE (addition_instance G $1 $1 ($0 ⊗ $1) ($1 ⊗ $0) HE)
    HR) HI) as HM.
  pose proof (mult_right_successor_at G $1 $0
    (HG mult_right_successor_sentence multiplication_right_successor)) as HS.
  pose proof (equality_symmetry G ($1 ⊗ σ $0) ($1 ⊕ ($1 ⊗ $0)) HE HS) as HB.
  pose proof (equality_transitivity G (σ $0 ⊗ $1) ($1 ⊕ ($0 ⊗ $1))
    ($1 ⊕ ($1 ⊗ $0)) HE HL HM) as HF.
  exact (equality_transitivity G (σ $0 ⊗ $1) ($1 ⊕ ($1 ⊗ $0))
    ($1 ⊗ σ $0) HE HF HB).
Qed.

Theorem mult_commutative : paeq_derivable (∀ ∀ ($0 ⊗ $1 == $1 ⊗ $0)).
Proof.
  apply paeq_generalize.
  apply (paeq_induction_rule mult_commutativity_formula).
  - exact mult_commutativity_base.
  - exact mult_commutativity_step.
Qed.

Definition mult_commutativity_sentence : pa_form :=
  ∀ ∀ ($0 ⊗ $1 == $1 ⊗ $0).
Definition commutative_context : list pa_form :=
  List.cons mult_commutativity_sentence multiplication_context.
Definition has_commutative_context (G : list pa_form) : Prop :=
  forall phi, List.In phi commutative_context -> List.In phi G.

Lemma commutative_proof phi : commutative_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := mult_commutativity_sentence).
  - apply multiplication_proof, II. exact HD.
  - exact mult_commutative.
Qed.
Lemma commutative_context_self : has_commutative_context commutative_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_commutative_cons G phi : has_commutative_context G ->
  has_commutative_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma commutative_has_multiplication G : has_commutative_context G ->
  has_multiplication_context G.
Proof. intros HG phi Hphi. apply HG. unfold commutative_context. now right. Qed.
Lemma commutative_multiplication : List.In mult_commutativity_sentence commutative_context.
Proof. unfold commutative_context. now left. Qed.
Lemma mult_commutative_at G a b : List.In mult_commutativity_sentence G ->
  G ⊢C (a ⊗ b == b ⊗ a).
Proof.
  intros H. change (G ⊢C ($0 ⊗ $1 == $1 ⊗ $0)[a .: b .: var]).
  apply (subst_forall_prv (phi := $0 ⊗ $1 == $1 ⊗ $0) (N := 2)).
  - change (G ⊢C mult_commutativity_sentence). now apply Ctx.
  - solve_bounds.
Qed.
Lemma multiplication_commutative_at G a b : has_commutative_context G ->
  G ⊢C (a ⊗ b == b ⊗ a).
Proof.
  intros HG. apply mult_commutative_at.
  exact (HG mult_commutativity_sentence commutative_multiplication).
Qed.

End PAMultiplicationComm238.

Print Assumptions PAMultiplicationComm238.add_commutative.
Print Assumptions PAMultiplicationComm238.mult_right_successor.
Print Assumptions PAMultiplicationComm238.mult_commutative.
