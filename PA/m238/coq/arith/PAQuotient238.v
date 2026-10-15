(* Original finite PA quotient-row certificates for beta uniqueness.
   Successor quotients are compared by canceling a common modulus prefix.
   The finite derived context is discharged by the displayed actual PA
   proofs; its sentences are never added to ordinary PA as axioms. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238
  PAAddition238 PAOrderBounds238 PACancellation238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAQuotient238.

Definition quotient_row (q m r : pa_term) : pa_term := (q ⊗ m) ⊕ r.
Lemma quotient_row_subst q m r rho :
  (quotient_row q m r)`[rho] = quotient_row q`[rho] m`[rho] r`[rho].
Proof. reflexivity. Qed.

Definition order_ir_sentence : pa_form := ∀ ¬ ($0 ⧀ $0).
Definition strict_weak_sentence : pa_form := ∀ ∀ ∀ ($0 ⧀ $1 → $1 ⧀= $2 → $0 ⧀ $2).
Definition cancellation_sentence : pa_form := ∀ ∀ ∀ ($0 ⊕ $1 == $0 ⊕ $2 → $1 == $2).
Definition predecessor_sentence : pa_form := ∀ ($0 == zero ∨ ∃ ($1 == σ $0)).
Definition quotient_context : list pa_form :=
  [order_ir_sentence; strict_weak_sentence; cancellation_sentence; predecessor_sentence]
    ++ PAOrderBounds238.bounds_context.
Definition has_quotient_context (G : list pa_form) : Prop :=
  forall phi, List.In phi quotient_context -> List.In phi G.

Lemma quotient_proof phi : quotient_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD.
  eapply paeq_modus_ponens with (phi := order_ir_sentence);
    [|exact PAOrder238.order_irreflexive].
  eapply paeq_modus_ponens with (phi := strict_weak_sentence);
    [|exact PAOrderBounds238.strict_weak_transitive].
  eapply paeq_modus_ponens with (phi := cancellation_sentence);
    [|exact PACancellation238.add_cancel_left].
  eapply paeq_modus_ponens with (phi := predecessor_sentence);
    [|exact PACancellation238.zero_or_successor].
  apply PAOrderBounds238.bounds_proof. apply II, II, II, II. exact HD.
Qed.

Lemma quotient_bounds phi : List.In phi PAOrderBounds238.bounds_context ->
  List.In phi quotient_context.
Proof. intros H. unfold quotient_context. apply List.in_app_iff. now right. Qed.
Lemma quotient_has_equality G : has_quotient_context G -> PAEqCongruence238.has_equality G.
Proof.
  intros HG phi Hphi. apply HG, quotient_bounds.
  exact (PAOrderBounds238.bounds_has_equality phi Hphi).
Qed.
Lemma has_quotient_cons G phi : has_quotient_context G -> has_quotient_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma quotient_context_self : has_quotient_context quotient_context.
Proof. intros phi Hphi. exact Hphi. Qed.

Lemma quotient_mult_zero : List.In ax_mult_zero quotient_context.
Proof.
  apply quotient_bounds. unfold PAOrderBounds238.bounds_context.
  apply List.in_app_iff. left. unfold FAeq. apply List.in_app_iff. right.
  unfold FA. right. right. now left.
Qed.
Lemma quotient_mult_rec : List.In ax_mult_rec quotient_context.
Proof.
  apply quotient_bounds. unfold PAOrderBounds238.bounds_context.
  apply List.in_app_iff. left. unfold FAeq. apply List.in_app_iff. right.
  unfold FA. right. right. right. now left.
Qed.
Lemma quotient_add_zero : List.In ax_add_zero quotient_context.
Proof. apply quotient_bounds. exact PAOrderBounds238.bounds_add_zero. Qed.
Lemma quotient_associative : List.In PAOrderBounds238.associativity_sentence quotient_context.
Proof. apply quotient_bounds. exact PAOrderBounds238.bounds_associativity. Qed.
Lemma quotient_cancellation : List.In cancellation_sentence quotient_context.
Proof. unfold quotient_context. apply List.in_app_iff. left. right. right. now left. Qed.
Lemma quotient_strict_weak : List.In strict_weak_sentence quotient_context.
Proof. unfold quotient_context. apply List.in_app_iff. left. right. now left. Qed.
Lemma quotient_order_ir : List.In order_ir_sentence quotient_context.
Proof. unfold quotient_context. apply List.in_app_iff. left. now left. Qed.

Lemma mult_zero_instance G m : List.In ax_mult_zero G -> G ⊢C (zero ⊗ m == zero).
Proof.
  intros H. change (G ⊢C (zero ⊗ $0 == zero)[m..]).
  apply (subst_forall_prv (phi := zero ⊗ $0 == zero) (N := 1)).
  - change (G ⊢C ax_mult_zero). now apply Ctx.
  - solve_bounds.
Qed.
Lemma mult_rec_instance G q m : List.In ax_mult_rec G ->
  G ⊢C (σ q ⊗ m == m ⊕ (q ⊗ m)).
Proof.
  intros H. change (G ⊢C (σ $1 ⊗ $0 == $0 ⊕ ($1 ⊗ $0))[m .: q .: var]).
  apply (subst_forall_prv (phi := σ $1 ⊗ $0 == $0 ⊕ ($1 ⊗ $0)) (N := 2)).
  - change (G ⊢C ax_mult_rec). now apply Ctx.
  - solve_bounds.
Qed.
Lemma cancellation_instance G m a b : List.In cancellation_sentence G ->
  G ⊢C (m ⊕ a == m ⊕ b → a == b).
Proof.
  intros H. change (G ⊢C ($0 ⊕ $1 == $0 ⊕ $2 → $1 == $2)[m .: a .: b .: var]).
  apply (subst_forall_prv (phi := $0 ⊕ $1 == $0 ⊕ $2 → $1 == $2) (N := 3)).
  - change (G ⊢C cancellation_sentence). now apply Ctx.
  - solve_bounds.
Qed.

Lemma row_zero G m r : has_quotient_context G -> G ⊢C (quotient_row zero m r == r).
Proof.
  intros HG. pose proof (quotient_has_equality G HG) as HE.
  pose proof (mult_zero_instance G m (HG ax_mult_zero quotient_mult_zero)) as HM.
  pose proof (PAEqCongruence238.reflexivity_instance G r HE) as HR.
  pose proof (IE (IE (PAEqCongruence238.addition_instance G (zero ⊗ m) zero r r HE) HM) HR) as HA.
  pose proof (PAAddition238.add_zero_instance G r (HG ax_add_zero quotient_add_zero)) as HB.
  exact (PAEqCongruence238.equality_transitivity G (quotient_row zero m r) (zero ⊕ r) r HE HA HB).
Qed.
Lemma row_successor G q m r : has_quotient_context G ->
  G ⊢C (quotient_row (σ q) m r == m ⊕ quotient_row q m r).
Proof.
  intros HG. pose proof (quotient_has_equality G HG) as HE.
  pose proof (mult_rec_instance G q m (HG ax_mult_rec quotient_mult_rec)) as HM.
  pose proof (PAEqCongruence238.reflexivity_instance G r HE) as HR.
  pose proof (IE (IE (PAEqCongruence238.addition_instance G
    (σ q ⊗ m) (m ⊕ (q ⊗ m)) r r HE) HM) HR) as HA.
  pose proof (PAOrderBounds238.associativity_instance G m (q ⊗ m) r
    (HG PAOrderBounds238.associativity_sentence quotient_associative)) as HB.
  pose proof (PAEqCongruence238.equality_symmetry G
    (m ⊕ quotient_row q m r) ((m ⊕ (q ⊗ m)) ⊕ r) HE HB) as HC.
  exact (PAEqCongruence238.equality_transitivity G
    (quotient_row (σ q) m r) ((m ⊕ (q ⊗ m)) ⊕ r) (m ⊕ quotient_row q m r) HE HA HC).
Qed.

Theorem successor_rows_cancel :
  paeq_derivable (∀ ∀ ∀ ∀ ∀
    (quotient_row (σ $0) $2 $3 == quotient_row (σ $1) $2 $4 →
      quotient_row $0 $2 $3 == quotient_row $1 $2 $4)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, quotient_proof, II.
  set (G := List.cons (quotient_row (σ $0) $2 $3 == quotient_row (σ $1) $2 $4) quotient_context).
  change (G ⊢C (quotient_row $0 $2 $3 == quotient_row $1 $2 $4)).
  assert (HG : has_quotient_context G).
  { unfold G. apply has_quotient_cons. exact quotient_context_self. }
  pose proof (quotient_has_equality G HG) as HE.
  assert (HI : G ⊢C (quotient_row (σ $0) $2 $3 == quotient_row (σ $1) $2 $4)).
  { apply Ctx. unfold G. now left. }
  pose proof (row_successor G $0 $2 $3 HG) as HL.
  pose proof (row_successor G $1 $2 $4 HG) as HR.
  pose proof (PAEqCongruence238.equality_symmetry G
    (quotient_row (σ $0) $2 $3) ($2 ⊕ quotient_row $0 $2 $3) HE HL) as HB.
  pose proof (PAEqCongruence238.equality_transitivity G
    ($2 ⊕ quotient_row $0 $2 $3) (quotient_row (σ $0) $2 $3)
    (quotient_row (σ $1) $2 $4) HE HB HI) as HF.
  pose proof (PAEqCongruence238.equality_transitivity G
    ($2 ⊕ quotient_row $0 $2 $3) (quotient_row (σ $1) $2 $4)
    ($2 ⊕ quotient_row $1 $2 $4) HE HF HR) as HH.
  exact (IE (cancellation_instance G $2 (quotient_row $0 $2 $3) (quotient_row $1 $2 $4)
    (HG cancellation_sentence quotient_cancellation)) HH).
Qed.

Theorem zero_successor_rows_disjoint :
  paeq_derivable (∀ ∀ ∀ ∀
    (quotient_row zero $0 $1 == quotient_row (σ $2) $0 $3 → $1 ⧀ $0 → falsity)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize, quotient_proof, II, II.
  set (G := List.cons ($1 ⧀ $0)
    (List.cons (quotient_row zero $0 $1 == quotient_row (σ $2) $0 $3) quotient_context)).
  change (G ⊢C falsity).
  assert (HG : has_quotient_context G).
  { unfold G. apply has_quotient_cons, has_quotient_cons. exact quotient_context_self. }
  pose proof (quotient_has_equality G HG) as HE.
  assert (HI : G ⊢C (quotient_row zero $0 $1 == quotient_row (σ $2) $0 $3)).
  { apply Ctx. unfold G. right. now left. }
  assert (HLT : G ⊢C ($1 ⧀ $0)).
  { apply Ctx. unfold G. now left. }
  pose proof (row_zero G $0 $1 HG) as HL.
  pose proof (row_successor G $2 $0 $3 HG) as HR.
  pose proof (PAEqCongruence238.equality_symmetry G
    (quotient_row zero $0 $1) $1 HE HL) as HB.
  pose proof (PAEqCongruence238.equality_transitivity G
    $1 (quotient_row zero $0 $1) (quotient_row (σ $2) $0 $3) HE HB HI) as HF.
  pose proof (PAEqCongruence238.equality_transitivity G
    $1 (quotient_row (σ $2) $0 $3) ($0 ⊕ quotient_row $2 $0 $3) HE HF HR) as HH.
  pose proof (PAOrderBounds238.weak_order_witness G $0 $1 (quotient_row $2 $0 $3) HH) as HW.
  assert (HT : G ⊢C ($1 ⧀ $0 → $0 ⧀= $1 → $1 ⧀ $1)).
  { change (G ⊢C ($0 ⧀ $1 → $1 ⧀= $2 → $0 ⧀ $2)[$1 .: $0 .: $1 .: var]).
    apply (subst_forall_prv (phi := $0 ⧀ $1 → $1 ⧀= $2 → $0 ⧀ $2) (N := 3)).
    - change (G ⊢C strict_weak_sentence). apply Ctx. exact (HG strict_weak_sentence quotient_strict_weak).
    - unfold PAlt, PAle. solve_bounds. }
  pose proof (IE (IE HT HLT) HW) as HC.
  assert (HIR : G ⊢C order_ir_sentence).
  { apply Ctx. exact (HG order_ir_sentence quotient_order_ir). }
  pose proof (AllE $1 HIR) as HN.
  change (G ⊢C ¬ ($1 ⧀ $1)) in HN. exact (IE HN HC).
Qed.

End PAQuotient238.

Print Assumptions PAQuotient238.quotient_proof.
Print Assumptions PAQuotient238.successor_rows_cancel.
Print Assumptions PAQuotient238.zero_successor_rows_disjoint.
