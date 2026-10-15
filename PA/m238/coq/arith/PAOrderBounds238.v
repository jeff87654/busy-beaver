(* Original finite PA certificates for the conditional Ackermann-bit bound.
   The lower bound on u+p is proved directly by induction on u. The right
   extension uses associativity. Every derived arithmetic sentence below
   is cut in using its actual finite PA certificate. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238 PAAddition238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAOrderBounds238.

Definition right_zero_sentence : pa_form := ∀ ($0 ⊕ zero == $0).
Definition right_successor_sentence : pa_form := ∀ ∀ ($0 ⊕ σ $1 == σ ($0 ⊕ $1)).
Definition associativity_sentence : pa_form :=
  ∀ ∀ ∀ ($0 ⊕ ($1 ⊕ $2) == ($0 ⊕ $1) ⊕ $2).
Definition bounds_context : list pa_form :=
  FAeq ++ [right_zero_sentence; right_successor_sentence; associativity_sentence].

Lemma bounds_proof phi : bounds_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD.
  destruct PAAddition238.add_right_zero as (A & HA & Hzero).
  destruct PAAddition238.add_right_successor as (B & HB & Hsuccessor).
  destruct PAAddition238.add_associative as (C & HC & Hassoc).
  exists (List.map universal_close FAeq ++ A ++ B ++ C). split.
  - intros psi Hpsi. apply List.in_app_iff in Hpsi as [Hpsi|Hpsi].
    + apply List.in_map_iff in Hpsi as (chi & <- & Hchi).
      apply paeq_axiom_closed, PAeq_FA. exact Hchi.
    + apply List.in_app_iff in Hpsi as [Hpsi|Hpsi]; [now apply HA|].
      apply List.in_app_iff in Hpsi as [Hpsi|Hpsi]; [now apply HB|now apply HC].
  - eapply prv_cut; [exact HD|]. intros psi Hpsi.
    unfold bounds_context in Hpsi. apply List.in_app_iff in Hpsi as [Hpsi|Hpsi].
    + apply close_extract, Ctx. apply List.in_app_iff. left.
      now apply List.in_map.
    + destruct Hpsi as [<-|[<-|[<-|[]]]].
      * eapply Weak; [exact Hzero|]. intros chi Hchi.
        apply List.in_app_iff. right. apply List.in_app_iff. now left.
      * eapply Weak; [exact Hsuccessor|]. intros chi Hchi.
        apply List.in_app_iff. right. apply List.in_app_iff. right.
        apply List.in_app_iff. now left.
      * eapply Weak; [exact Hassoc|]. intros chi Hchi.
        apply List.in_app_iff. right. apply List.in_app_iff. right.
        apply List.in_app_iff. now right.
Qed.

Lemma bounds_has_equality : PAEqCongruence238.has_equality bounds_context.
Proof.
  intros phi Hphi. unfold bounds_context, FAeq. apply List.in_app_iff. left.
  apply List.in_app_iff. now left.
Qed.
Lemma bounds_add_zero : List.In ax_add_zero bounds_context.
Proof.
  unfold bounds_context, FAeq. apply List.in_app_iff. left.
  apply List.in_app_iff. right. unfold FA. now left.
Qed.
Lemma bounds_add_rec : List.In ax_add_rec bounds_context.
Proof.
  unfold bounds_context, FAeq. apply List.in_app_iff. left.
  apply List.in_app_iff. right. unfold FA. right. now left.
Qed.
Lemma bounds_right_zero : List.In right_zero_sentence bounds_context.
Proof. unfold bounds_context. apply List.in_app_iff. right. now left. Qed.
Lemma bounds_right_successor : List.In right_successor_sentence bounds_context.
Proof. unfold bounds_context. apply List.in_app_iff. right. right. now left. Qed.
Lemma bounds_associativity : List.In associativity_sentence bounds_context.
Proof. unfold bounds_context. apply List.in_app_iff. right. right. right. now left. Qed.

Lemma right_successor_instance G p k :
  List.In right_successor_sentence G -> G ⊢C (p ⊕ σ k == σ (p ⊕ k)).
Proof.
  intros H. change (G ⊢C ($0 ⊕ σ $1 == σ ($0 ⊕ $1))[p .: k .: var]).
  apply (subst_forall_prv (phi := $0 ⊕ σ $1 == σ ($0 ⊕ $1)) (N := 2)).
  - change (G ⊢C right_successor_sentence). now apply Ctx.
  - solve_bounds.
Qed.

Lemma associativity_instance G a b c :
  List.In associativity_sentence G -> G ⊢C (a ⊕ (b ⊕ c) == (a ⊕ b) ⊕ c).
Proof.
  intros H. change (G ⊢C ($0 ⊕ ($1 ⊕ $2) == ($0 ⊕ $1) ⊕ $2)
    [a .: b .: c .: var]).
  apply (subst_forall_prv
    (phi := $0 ⊕ ($1 ⊕ $2) == ($0 ⊕ $1) ⊕ $2) (N := 3)).
  - change (G ⊢C associativity_sentence). now apply Ctx.
  - solve_bounds.
Qed.

Lemma weak_order_witness G p v k :
  G ⊢C (v == p ⊕ k) -> G ⊢C (p ⧀= v).
Proof.
  intros H. unfold PAle. apply (ExI k).
  assert (HV : v`[↑]`[k..] = v) by apply subst_term_shift.
  assert (HP : p`[↑]`[k..] = p) by apply subst_term_shift.
  change (G ⊢C (v`[↑]`[k..] == p`[↑]`[k..] ⊕ k)).
  rewrite HV, HP. exact H.
Qed.

Definition right_bound_formula : pa_form := $1 ⧀= ($0 ⊕ $1).

Lemma right_bound_base : paeq_derivable right_bound_formula[zero..].
Proof.
  change (paeq_derivable ($0 ⧀= (zero ⊕ $0))). apply bounds_proof.
  assert (HZ : bounds_context ⊢C right_zero_sentence).
  { apply Ctx. exact bounds_right_zero. }
  pose proof (AllE $0 HZ) as HR.
  change (bounds_context ⊢C ($0 ⊕ zero == $0)) in HR.
  pose proof (PAAddition238.add_zero_instance bounds_context $0 bounds_add_zero) as HL.
  pose proof (PAEqCongruence238.equality_symmetry bounds_context
    ($0 ⊕ zero) $0 bounds_has_equality HR) as HB.
  apply (weak_order_witness bounds_context $0 (zero ⊕ $0) zero).
  exact (PAEqCongruence238.equality_transitivity bounds_context
    (zero ⊕ $0) $0 ($0 ⊕ zero) bounds_has_equality HL HB).
Qed.

Lemma right_bound_step :
  paeq_derivable (∀ (right_bound_formula → right_bound_formula[σ $0 .: S >> var])).
Proof.
  change (paeq_derivable (∀ ($1 ⧀= ($0 ⊕ $1) → $1 ⧀= (σ $0 ⊕ $1)))).
  apply paeq_generalize, bounds_proof, II.
  set (G := List.cons ($1 ⧀= ($0 ⊕ $1)) bounds_context).
  change (G ⊢C ($1 ⧀= (σ $0 ⊕ $1))).
  assert (HX : G ⊢C ∃ (($0 ⊕ $1)`[↑] == $1`[↑] ⊕ $0)).
  { change (G ⊢C ($1 ⧀= ($0 ⊕ $1))). apply Ctx. unfold G. now left. }
  eapply ExE_named; [exact HX|]. intros k. cbn.
  set (D := List.cons ($0 ⊕ $1 == $1 ⊕ k) G).
  change (D ⊢C ($1 ⧀= (σ $0 ⊕ $1))).
  assert (HE : PAEqCongruence238.has_equality D).
  { unfold D, G. apply PAEqCongruence238.has_equality_cons,
      PAEqCongruence238.has_equality_cons. exact bounds_has_equality. }
  assert (HI : D ⊢C ($0 ⊕ $1 == $1 ⊕ k)).
  { apply Ctx. unfold D. now left. }
  assert (Hrec : List.In ax_add_rec D).
  { unfold D, G. right. right. exact bounds_add_rec. }
  assert (Hsuc : List.In right_successor_sentence D).
  { unfold D, G. right. right. exact bounds_right_successor. }
  pose proof (PAOrder238.add_rec_instance D $0 $1 Hrec) as Hleft.
  pose proof (IE (PAEqCongruence238.successor_instance D
    ($0 ⊕ $1) ($1 ⊕ k) HE) HI) as Hmid.
  pose proof (right_successor_instance D $1 k Hsuc) as Hright.
  pose proof (PAEqCongruence238.equality_symmetry D
    ($1 ⊕ σ k) (σ ($1 ⊕ k)) HE Hright) as Hback.
  pose proof (PAEqCongruence238.equality_transitivity D
    (σ $0 ⊕ $1) (σ ($0 ⊕ $1)) (σ ($1 ⊕ k)) HE Hleft Hmid) as Hfront.
  apply (weak_order_witness D $1 (σ $0 ⊕ $1) (σ k)).
  exact (PAEqCongruence238.equality_transitivity D
    (σ $0 ⊕ $1) (σ ($1 ⊕ k)) ($1 ⊕ σ k) HE Hfront Hback).
Qed.

Theorem addition_right_bound : paeq_derivable (∀ ∀ ($1 ⧀= ($0 ⊕ $1))).
Proof.
  apply paeq_generalize. apply (paeq_induction_rule right_bound_formula).
  - exact right_bound_base.
  - exact right_bound_step.
Qed.

Theorem weak_order_right_extension :
  paeq_derivable (∀ ∀ ∀ ($0 ⧀= $1 → $0 ⧀= ($1 ⊕ $2))).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, bounds_proof, II.
  set (G := List.cons ($0 ⧀= $1) bounds_context).
  change (G ⊢C ($0 ⧀= ($1 ⊕ $2))).
  assert (HX : G ⊢C ∃ ($1`[↑] == $0`[↑] ⊕ $0)).
  { change (G ⊢C ($0 ⧀= $1)). apply Ctx. unfold G. now left. }
  eapply ExE_named; [exact HX|]. intros k. cbn.
  set (D := List.cons ($1 == $0 ⊕ k) G).
  change (D ⊢C ($0 ⧀= ($1 ⊕ $2))).
  assert (HE : PAEqCongruence238.has_equality D).
  { unfold D, G. apply PAEqCongruence238.has_equality_cons,
      PAEqCongruence238.has_equality_cons. exact bounds_has_equality. }
  assert (HI : D ⊢C ($1 == $0 ⊕ k)).
  { apply Ctx. unfold D. now left. }
  assert (Hassoc : List.In associativity_sentence D).
  { unfold D, G. right. right. exact bounds_associativity. }
  pose proof (PAEqCongruence238.reflexivity_instance D $2 HE) as HR.
  pose proof (IE (IE (PAEqCongruence238.addition_instance D
    $1 ($0 ⊕ k) $2 $2 HE) HI) HR) as Hleft.
  pose proof (associativity_instance D $0 k $2 Hassoc) as Hright.
  pose proof (PAEqCongruence238.equality_symmetry D
    ($0 ⊕ (k ⊕ $2)) (($0 ⊕ k) ⊕ $2) HE Hright) as Hback.
  apply (weak_order_witness D $0 ($1 ⊕ $2) (k ⊕ $2)).
  exact (PAEqCongruence238.equality_transitivity D
    ($1 ⊕ $2) (($0 ⊕ k) ⊕ $2) ($0 ⊕ (k ⊕ $2)) HE Hleft Hback).
Qed.

Lemma strict_order_witness G x z k :
  G ⊢C (z == σ x ⊕ k) -> G ⊢C (x ⧀ z).
Proof.
  intros H. unfold PAlt. apply (ExI k).
  assert (HZ : z`[↑]`[k..] = z) by apply subst_term_shift.
  assert (HX : x`[↑]`[k..] = x) by apply subst_term_shift.
  change (G ⊢C (z`[↑]`[k..] == σ (x`[↑]`[k..]) ⊕ k)).
  rewrite HZ, HX. exact H.
Qed.

(* Join the two actual difference witnesses. This supplies the arithmetic
   comparison needed by the bit-position and remainder-uniqueness leaves. *)
Theorem strict_weak_transitive :
  paeq_derivable (∀ ∀ ∀ ($0 ⧀ $1 → $1 ⧀= $2 → $0 ⧀ $2)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, bounds_proof, II, II.
  set (G := List.cons ($1 ⧀= $2) (List.cons ($0 ⧀ $1) bounds_context)).
  change (G ⊢C ($0 ⧀ $2)).
  assert (Hxy : G ⊢C ∃ ($1`[↑] == σ $0`[↑] ⊕ $0)).
  { change (G ⊢C ($0 ⧀ $1)). apply Ctx. unfold G. right. now left. }
  eapply ExE_named; [exact Hxy|]. intros k. cbn.
  set (D := List.cons ($1 == σ $0 ⊕ k) G).
  change (D ⊢C ($0 ⧀ $2)).
  assert (Hyz : D ⊢C ∃ ($2`[↑] == $1`[↑] ⊕ $0)).
  { change (D ⊢C ($1 ⧀= $2)). apply Ctx. unfold D, G. right. now left. }
  eapply ExE_named; [exact Hyz|]. intros l. cbn.
  set (E := List.cons ($2 == $1 ⊕ l) D).
  change (E ⊢C ($0 ⧀ $2)).
  assert (HE : PAEqCongruence238.has_equality E).
  { unfold E, D, G. apply PAEqCongruence238.has_equality_cons,
      PAEqCongruence238.has_equality_cons, PAEqCongruence238.has_equality_cons,
      PAEqCongruence238.has_equality_cons. exact bounds_has_equality. }
  assert (H1 : E ⊢C ($1 == σ $0 ⊕ k)).
  { apply Ctx. unfold E, D. right. now left. }
  assert (H2 : E ⊢C ($2 == $1 ⊕ l)).
  { apply Ctx. unfold E. now left. }
  assert (Hassoc : List.In associativity_sentence E).
  { unfold E, D, G. right. right. right. right. exact bounds_associativity. }
  pose proof (PAEqCongruence238.reflexivity_instance E l HE) as HR.
  pose proof (IE (IE (PAEqCongruence238.addition_instance E
    $1 (σ $0 ⊕ k) l l HE) H1) HR) as HA.
  pose proof (associativity_instance E (σ $0) k l Hassoc) as HB.
  pose proof (PAEqCongruence238.equality_symmetry E
    (σ $0 ⊕ (k ⊕ l)) ((σ $0 ⊕ k) ⊕ l) HE HB) as HC.
  pose proof (PAEqCongruence238.equality_transitivity E
    $2 ($1 ⊕ l) ((σ $0 ⊕ k) ⊕ l) HE H2 HA) as HF.
  apply (strict_order_witness E $0 $2 (k ⊕ l)).
  exact (PAEqCongruence238.equality_transitivity E
    $2 ((σ $0 ⊕ k) ⊕ l) (σ $0 ⊕ (k ⊕ l)) HE HF HC).
Qed.

End PAOrderBounds238.

Print Assumptions PAOrderBounds238.bounds_proof.
Print Assumptions PAOrderBounds238.weak_order_witness.
Print Assumptions PAOrderBounds238.addition_right_bound.
Print Assumptions PAOrderBounds238.weak_order_right_extension.

Print Assumptions PAOrderBounds238.strict_weak_transitive.
