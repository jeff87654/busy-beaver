(* Original finite ordinary-PA multiplication certificates for the beta
   accumulator.  Each induction recurses on the left multiplication input,
   matching the literal upstream recursion axiom.  No arithmetic theorem
   is supplied by a model or added as a new PA axiom. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238
  PAAddition238 PAOrderBounds238 PAQuotient238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrderBounds238 PAQuotient238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PASemiring238.

Definition product_context : list pa_form := bounds_context.
Definition has_product_context (G : list pa_form) : Prop :=
  forall phi, List.In phi product_context -> List.In phi G.
Lemma product_proof phi : product_context ⊢C phi -> paeq_derivable phi.
Proof. exact (bounds_proof phi). Qed.
Lemma product_context_self : has_product_context product_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_product_cons G phi : has_product_context G ->
  has_product_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma product_has_equality G : has_product_context G -> has_equality G.
Proof. intros HG phi Hphi. apply HG. exact (bounds_has_equality phi Hphi). Qed.
Lemma product_mult_zero : List.In ax_mult_zero product_context.
Proof.
  unfold product_context, bounds_context. apply List.in_app_iff. left.
  unfold FAeq. apply List.in_app_iff. right. unfold FA. right. right. now left.
Qed.
Lemma product_mult_rec : List.In ax_mult_rec product_context.
Proof.
  unfold product_context, bounds_context. apply List.in_app_iff. left.
  unfold FAeq. apply List.in_app_iff. right. unfold FA. right. right. right. now left.
Qed.
Lemma product_add_zero : List.In ax_add_zero product_context.
Proof. exact bounds_add_zero. Qed.
Lemma product_add_rec : List.In ax_add_rec product_context.
Proof. exact bounds_add_rec. Qed.
Lemma product_associativity : List.In associativity_sentence product_context.
Proof. exact bounds_associativity. Qed.

Definition mult_right_zero_formula : pa_form := $0 ⊗ zero == zero.
Lemma mult_right_zero_base : paeq_derivable mult_right_zero_formula[zero..].
Proof. apply product_proof, mult_zero_instance, product_mult_zero. Qed.
Lemma mult_right_zero_step : paeq_derivable
  (∀ (mult_right_zero_formula → mult_right_zero_formula[σ $0 .: S >> var])).
Proof.
  change (paeq_derivable (∀ ($0 ⊗ zero == zero → σ $0 ⊗ zero == zero))).
  apply paeq_generalize, product_proof, II.
  set (G := List.cons ($0 ⊗ zero == zero) product_context).
  assert (HG : has_product_context G).
  { unfold G. apply has_product_cons. exact product_context_self. }
  pose proof (product_has_equality G HG) as HE.
  assert (HI : G ⊢C ($0 ⊗ zero == zero)).
  { apply Ctx. unfold G. now left. }
  pose proof (mult_rec_instance G $0 zero (HG ax_mult_rec product_mult_rec)) as HR.
  pose proof (reflexivity_instance G zero HE) as HZ.
  pose proof (IE (IE (addition_instance G zero zero ($0 ⊗ zero) zero HE) HZ) HI) as HA.
  pose proof (PAAddition238.add_zero_instance G zero (HG ax_add_zero product_add_zero)) as HB.
  pose proof (equality_transitivity G (σ $0 ⊗ zero) (zero ⊕ ($0 ⊗ zero))
    (zero ⊕ zero) HE HR HA) as HF.
  exact (equality_transitivity G (σ $0 ⊗ zero) (zero ⊕ zero) zero HE HF HB).
Qed.
Theorem mult_right_zero : paeq_derivable (∀ ($0 ⊗ zero == zero)).
Proof.
  apply (paeq_induction_rule mult_right_zero_formula).
  - exact mult_right_zero_base.
  - exact mult_right_zero_step.
Qed.

Definition mult_left_distribution_formula : pa_form :=
  ($0 ⊕ $1) ⊗ $2 == ($0 ⊗ $2) ⊕ ($1 ⊗ $2).
Lemma mult_left_distribution_base :
  paeq_derivable mult_left_distribution_formula[zero..].
Proof.
  change (paeq_derivable ((zero ⊕ $0) ⊗ $1 == (zero ⊗ $1) ⊕ ($0 ⊗ $1))).
  apply product_proof.
  pose proof (product_has_equality product_context product_context_self) as HE.
  pose proof (PAAddition238.add_zero_instance product_context $0 product_add_zero) as HZ.
  pose proof (reflexivity_instance product_context $1 HE) as HR.
  pose proof (IE (IE (multiplication_instance product_context (zero ⊕ $0) $0 $1 $1 HE)
    HZ) HR) as HL.
  pose proof (mult_zero_instance product_context $1 product_mult_zero) as HM.
  pose proof (reflexivity_instance product_context ($0 ⊗ $1) HE) as HP.
  pose proof (IE (IE (addition_instance product_context (zero ⊗ $1) zero
    ($0 ⊗ $1) ($0 ⊗ $1) HE) HM) HP) as HA.
  pose proof (PAAddition238.add_zero_instance product_context ($0 ⊗ $1) product_add_zero) as HB.
  pose proof (equality_transitivity product_context ((zero ⊗ $1) ⊕ ($0 ⊗ $1))
    (zero ⊕ ($0 ⊗ $1)) ($0 ⊗ $1) HE HA HB) as Hright.
  pose proof (equality_symmetry product_context ((zero ⊗ $1) ⊕ ($0 ⊗ $1))
    ($0 ⊗ $1) HE Hright) as Hback.
  exact (equality_transitivity product_context ((zero ⊕ $0) ⊗ $1) ($0 ⊗ $1)
    ((zero ⊗ $1) ⊕ ($0 ⊗ $1)) HE HL Hback).
Qed.
Lemma mult_left_distribution_step : paeq_derivable
  (∀ (mult_left_distribution_formula →
    mult_left_distribution_formula[σ $0 .: S >> var])).
Proof.
  change (paeq_derivable (∀
    (($0 ⊕ $1) ⊗ $2 == ($0 ⊗ $2) ⊕ ($1 ⊗ $2) →
      (σ $0 ⊕ $1) ⊗ $2 == (σ $0 ⊗ $2) ⊕ ($1 ⊗ $2)))).
  apply paeq_generalize, product_proof, II.
  set (G := List.cons (($0 ⊕ $1) ⊗ $2 == ($0 ⊗ $2) ⊕ ($1 ⊗ $2)) product_context).
  assert (HG : has_product_context G).
  { unfold G. apply has_product_cons. exact product_context_self. }
  pose proof (product_has_equality G HG) as HE.
  assert (HI : G ⊢C (($0 ⊕ $1) ⊗ $2 == ($0 ⊗ $2) ⊕ ($1 ⊗ $2))).
  { apply Ctx. unfold G. now left. }
  pose proof (PAOrder238.add_rec_instance G $0 $1 (HG ax_add_rec product_add_rec)) as HA.
  pose proof (reflexivity_instance G $2 HE) as HR.
  pose proof (IE (IE (multiplication_instance G (σ $0 ⊕ $1) (σ ($0 ⊕ $1))
    $2 $2 HE) HA) HR) as Hfirst.
  pose proof (mult_rec_instance G ($0 ⊕ $1) $2 (HG ax_mult_rec product_mult_rec)) as Hsecond.
  pose proof (IE (IE (addition_instance G $2 $2 (($0 ⊕ $1) ⊗ $2)
    (($0 ⊗ $2) ⊕ ($1 ⊗ $2)) HE) HR) HI) as Hthird.
  pose proof (associativity_instance G $2 ($0 ⊗ $2) ($1 ⊗ $2)
    (HG associativity_sentence product_associativity)) as Hfourth.
  pose proof (equality_transitivity G ((σ $0 ⊕ $1) ⊗ $2) (σ ($0 ⊕ $1) ⊗ $2)
    ($2 ⊕ (($0 ⊕ $1) ⊗ $2)) HE Hfirst Hsecond) as H12.
  pose proof (equality_transitivity G ((σ $0 ⊕ $1) ⊗ $2)
    ($2 ⊕ (($0 ⊕ $1) ⊗ $2)) ($2 ⊕ (($0 ⊗ $2) ⊕ ($1 ⊗ $2))) HE H12 Hthird) as H123.
  pose proof (equality_transitivity G ((σ $0 ⊕ $1) ⊗ $2)
    ($2 ⊕ (($0 ⊗ $2) ⊕ ($1 ⊗ $2))) (($2 ⊕ ($0 ⊗ $2)) ⊕ ($1 ⊗ $2))
    HE H123 Hfourth) as Hleft.
  pose proof (mult_rec_instance G $0 $2 (HG ax_mult_rec product_mult_rec)) as HM.
  pose proof (reflexivity_instance G ($1 ⊗ $2) HE) as HP.
  pose proof (IE (IE (addition_instance G (σ $0 ⊗ $2) ($2 ⊕ ($0 ⊗ $2))
    ($1 ⊗ $2) ($1 ⊗ $2) HE) HM) HP) as Hright.
  pose proof (equality_symmetry G ((σ $0 ⊗ $2) ⊕ ($1 ⊗ $2))
    (($2 ⊕ ($0 ⊗ $2)) ⊕ ($1 ⊗ $2)) HE Hright) as Hback.
  exact (equality_transitivity G ((σ $0 ⊕ $1) ⊗ $2)
    (($2 ⊕ ($0 ⊗ $2)) ⊕ ($1 ⊗ $2)) ((σ $0 ⊗ $2) ⊕ ($1 ⊗ $2)) HE Hleft Hback).
Qed.
Theorem mult_left_distribution : paeq_derivable
  (∀ ∀ ∀ (($0 ⊕ $1) ⊗ $2 == ($0 ⊗ $2) ⊕ ($1 ⊗ $2))).
Proof.
  apply paeq_generalize, paeq_generalize.
  apply (paeq_induction_rule mult_left_distribution_formula).
  - exact mult_left_distribution_base.
  - exact mult_left_distribution_step.
Qed.

Definition mult_left_distribution_sentence : pa_form :=
  ∀ ∀ ∀ (($0 ⊕ $1) ⊗ $2 == ($0 ⊗ $2) ⊕ ($1 ⊗ $2)).
Definition associative_context : list pa_form :=
  List.cons mult_left_distribution_sentence product_context.
Definition has_associative_context (G : list pa_form) : Prop :=
  forall phi, List.In phi associative_context -> List.In phi G.
Lemma associative_proof phi : associative_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := mult_left_distribution_sentence).
  - apply product_proof, II. exact HD.
  - exact mult_left_distribution.
Qed.
Lemma associative_context_self : has_associative_context associative_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_associative_cons G phi : has_associative_context G ->
  has_associative_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma associative_has_product G : has_associative_context G -> has_product_context G.
Proof. intros HG phi Hphi. apply HG. unfold associative_context. now right. Qed.
Lemma left_distribution_at G a b c : List.In mult_left_distribution_sentence G ->
  G ⊢C ((a ⊕ b) ⊗ c == (a ⊗ c) ⊕ (b ⊗ c)).
Proof.
  intros H. change (G ⊢C (($0 ⊕ $1) ⊗ $2 == ($0 ⊗ $2) ⊕ ($1 ⊗ $2))
    [a .: b .: c .: var]).
  apply (subst_forall_prv
    (phi := ($0 ⊕ $1) ⊗ $2 == ($0 ⊗ $2) ⊕ ($1 ⊗ $2)) (N := 3)).
  - change (G ⊢C mult_left_distribution_sentence). now apply Ctx.
  - solve_bounds.
Qed.

Definition mult_associativity_formula : pa_form :=
  ($0 ⊗ $1) ⊗ $2 == $0 ⊗ ($1 ⊗ $2).
Lemma mult_associativity_base : paeq_derivable mult_associativity_formula[zero..].
Proof.
  change (paeq_derivable ((zero ⊗ $0) ⊗ $1 == zero ⊗ ($0 ⊗ $1))).
  apply product_proof.
  pose proof (product_has_equality product_context product_context_self) as HE.
  pose proof (mult_zero_instance product_context $0 product_mult_zero) as HZ.
  pose proof (reflexivity_instance product_context $1 HE) as HR.
  pose proof (IE (IE (multiplication_instance product_context (zero ⊗ $0) zero
    $1 $1 HE) HZ) HR) as Hfirst.
  pose proof (mult_zero_instance product_context $1 product_mult_zero) as Hsecond.
  pose proof (equality_transitivity product_context ((zero ⊗ $0) ⊗ $1)
    (zero ⊗ $1) zero HE Hfirst Hsecond) as HL.
  pose proof (mult_zero_instance product_context ($0 ⊗ $1) product_mult_zero) as HM.
  pose proof (equality_symmetry product_context (zero ⊗ ($0 ⊗ $1)) zero HE HM) as HB.
  exact (equality_transitivity product_context ((zero ⊗ $0) ⊗ $1) zero
    (zero ⊗ ($0 ⊗ $1)) HE HL HB).
Qed.
Lemma mult_associativity_step : paeq_derivable
  (∀ (mult_associativity_formula → mult_associativity_formula[σ $0 .: S >> var])).
Proof.
  change (paeq_derivable (∀
    (($0 ⊗ $1) ⊗ $2 == $0 ⊗ ($1 ⊗ $2) →
      (σ $0 ⊗ $1) ⊗ $2 == σ $0 ⊗ ($1 ⊗ $2)))).
  apply paeq_generalize, associative_proof, II.
  set (G := List.cons (($0 ⊗ $1) ⊗ $2 == $0 ⊗ ($1 ⊗ $2)) associative_context).
  assert (HG : has_associative_context G).
  { unfold G. apply has_associative_cons. exact associative_context_self. }
  pose proof (associative_has_product G HG) as HP.
  pose proof (product_has_equality G HP) as HE.
  assert (HI : G ⊢C (($0 ⊗ $1) ⊗ $2 == $0 ⊗ ($1 ⊗ $2))).
  { apply Ctx. unfold G. now left. }
  pose proof (mult_rec_instance G $0 $1 (HP ax_mult_rec product_mult_rec)) as HM.
  pose proof (reflexivity_instance G $2 HE) as HR.
  pose proof (IE (IE (multiplication_instance G (σ $0 ⊗ $1)
    ($1 ⊕ ($0 ⊗ $1)) $2 $2 HE) HM) HR) as Hfirst.
  assert (HD : List.In mult_left_distribution_sentence G).
  { apply HG. unfold associative_context. now left. }
  pose proof (left_distribution_at G $1 ($0 ⊗ $1) $2 HD) as Hsecond.
  pose proof (reflexivity_instance G ($1 ⊗ $2) HE) as Hrefl.
  pose proof (IE (IE (addition_instance G ($1 ⊗ $2) ($1 ⊗ $2)
    (($0 ⊗ $1) ⊗ $2) ($0 ⊗ ($1 ⊗ $2)) HE) Hrefl) HI) as Hthird.
  pose proof (equality_transitivity G ((σ $0 ⊗ $1) ⊗ $2)
    (($1 ⊕ ($0 ⊗ $1)) ⊗ $2) (($1 ⊗ $2) ⊕ (($0 ⊗ $1) ⊗ $2))
    HE Hfirst Hsecond) as H12.
  pose proof (equality_transitivity G ((σ $0 ⊗ $1) ⊗ $2)
    (($1 ⊗ $2) ⊕ (($0 ⊗ $1) ⊗ $2)) (($1 ⊗ $2) ⊕ ($0 ⊗ ($1 ⊗ $2)))
    HE H12 Hthird) as Hleft.
  pose proof (mult_rec_instance G $0 ($1 ⊗ $2) (HP ax_mult_rec product_mult_rec)) as Hright.
  pose proof (equality_symmetry G (σ $0 ⊗ ($1 ⊗ $2))
    (($1 ⊗ $2) ⊕ ($0 ⊗ ($1 ⊗ $2))) HE Hright) as Hback.
  exact (equality_transitivity G ((σ $0 ⊗ $1) ⊗ $2)
    (($1 ⊗ $2) ⊕ ($0 ⊗ ($1 ⊗ $2))) (σ $0 ⊗ ($1 ⊗ $2)) HE Hleft Hback).
Qed.
Theorem mult_associative : paeq_derivable
  (∀ ∀ ∀ (($0 ⊗ $1) ⊗ $2 == $0 ⊗ ($1 ⊗ $2))).
Proof.
  apply paeq_generalize, paeq_generalize.
  apply (paeq_induction_rule mult_associativity_formula).
  - exact mult_associativity_base.
  - exact mult_associativity_step.
Qed.

Definition mult_associativity_sentence : pa_form :=
  ∀ ∀ ∀ (($0 ⊗ $1) ⊗ $2 == $0 ⊗ ($1 ⊗ $2)).
Definition divisor_context : list pa_form :=
  List.cons mult_associativity_sentence associative_context.
Definition has_divisor_context (G : list pa_form) : Prop :=
  forall phi, List.In phi divisor_context -> List.In phi G.
Lemma divisor_proof phi : divisor_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := mult_associativity_sentence).
  - apply associative_proof, II. exact HD.
  - exact mult_associative.
Qed.
Lemma divisor_context_self : has_divisor_context divisor_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_divisor_cons G phi : has_divisor_context G ->
  has_divisor_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma divisor_has_product G : has_divisor_context G -> has_product_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold divisor_context, associative_context.
  right. now right.
Qed.
Lemma multiplication_associative_at G a b c : has_divisor_context G ->
  G ⊢C ((a ⊗ b) ⊗ c == a ⊗ (b ⊗ c)).
Proof.
  intros HG. change (G ⊢C (($0 ⊗ $1) ⊗ $2 == $0 ⊗ ($1 ⊗ $2))
    [a .: b .: c .: var]).
  apply (subst_forall_prv
    (phi := ($0 ⊗ $1) ⊗ $2 == $0 ⊗ ($1 ⊗ $2)) (N := 3)).
  - change (G ⊢C mult_associativity_sentence). apply Ctx, HG.
    unfold divisor_context. now left.
  - solve_bounds.
Qed.

Definition divides (d n : pa_term) : pa_form := ∃ (n`[↑] == d`[↑] ⊗ $0).
Lemma divides_subst d n rho : (divides d n)[rho] = divides d`[rho] n`[rho].
Proof. unfold divides. cbn. now rewrite !up_term. Qed.
Lemma divides_introduce G d n q : G ⊢C (n == d ⊗ q) -> G ⊢C divides d n.
Proof.
  intros H. unfold divides. apply (ExI q).
  change (G ⊢C (n`[↑]`[q..] == d`[↑]`[q..] ⊗ q)).
  rewrite !subst_term_shift. exact H.
Qed.
Lemma divides_eliminate G d n (psi : pa_form) : G ⊢C divides d n ->
  (forall q, (List.cons (n == d ⊗ q) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. unfold divides in HX. eapply ExE_named; [exact HX|]. intros q.
  change ((List.cons (n`[↑]`[q..] == d`[↑]`[q..] ⊗ q) G) ⊢C psi).
  rewrite !subst_term_shift. exact (H q).
Qed.

Lemma divisor_right_product G d n r : has_divisor_context G ->
  G ⊢C divides d n -> G ⊢C divides d (n ⊗ r).
Proof.
  intros HG HD. eapply divides_eliminate; [exact HD|]. intros q.
  set (D := List.cons (n == d ⊗ q) G).
  change (D ⊢C divides d (n ⊗ r)).
  assert (HDG : has_divisor_context D).
  { unfold D. apply has_divisor_cons. exact HG. }
  pose proof (product_has_equality D (divisor_has_product D HDG)) as HE.
  assert (HN : D ⊢C (n == d ⊗ q)).
  { apply Ctx. unfold D. now left. }
  pose proof (reflexivity_instance D r HE) as HR.
  pose proof (IE (IE (multiplication_instance D n (d ⊗ q) r r HE) HN) HR) as Hfirst.
  pose proof (multiplication_associative_at D d q r HDG) as Hsecond.
  apply (divides_introduce D d (n ⊗ r) (q ⊗ r)).
  exact (equality_transitivity D (n ⊗ r) ((d ⊗ q) ⊗ r)
    (d ⊗ (q ⊗ r)) HE Hfirst Hsecond).
Qed.
Theorem divides_right_product :
  paeq_derivable (∀ ∀ ∀ (divides $0 $1 → divides $0 ($1 ⊗ $2))).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, divisor_proof, II.
  set (G := List.cons (divides $0 $1) divisor_context).
  apply (divisor_right_product G $0 $1 $2).
  - unfold G. apply has_divisor_cons. exact divisor_context_self.
  - apply Ctx. unfold G. now left.
Qed.

Lemma divisor_composition G d n m : has_divisor_context G ->
  G ⊢C divides d n -> G ⊢C divides n m -> G ⊢C divides d m.
Proof.
  intros HG HD HN. eapply divides_eliminate; [exact HN|]. intros q.
  set (D := List.cons (m == n ⊗ q) G).
  change (D ⊢C divides d m).
  assert (HDG : has_divisor_context D).
  { unfold D. apply has_divisor_cons. exact HG. }
  pose proof (product_has_equality D (divisor_has_product D HDG)) as HE.
  pose proof (weaken_head G (divides d n) (m == n ⊗ q) HD) as Hdiv.
  pose proof (divisor_right_product D d n q HDG Hdiv) as Hprod.
  assert (HM : D ⊢C (m == n ⊗ q)).
  { apply Ctx. unfold D. now left. }
  pose proof (equality_symmetry D m (n ⊗ q) HE HM) as Hback.
  pose proof (formula_substitutivity D (divides d`[↑] $0)
    (n ⊗ q) m HE Hback) as Htransfer.
  rewrite !divides_subst, !subst_term_shift in Htransfer.
  exact (IE (CE1 Htransfer) Hprod).
Qed.
Theorem divides_composition :
  paeq_derivable (∀ ∀ ∀ (divides $0 $1 → divides $1 $2 → divides $0 $2)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, divisor_proof, II, II.
  set (G := List.cons (divides $1 $2) (List.cons (divides $0 $1) divisor_context)).
  apply (divisor_composition G $0 $1 $2).
  - unfold G. apply has_divisor_cons, has_divisor_cons. exact divisor_context_self.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Lemma zero_below_successor G n : has_product_context G -> G ⊢C (zero ⧀ σ n).
Proof.
  intros HG. pose proof (product_has_equality G HG) as HE.
  pose proof (PAAddition238.add_zero_instance G n (HG ax_add_zero product_add_zero)) as HZ.
  pose proof (IE (successor_instance G (zero ⊕ n) n HE) HZ) as HS.
  pose proof (PAOrder238.add_rec_instance G zero n (HG ax_add_rec product_add_rec)) as HR.
  pose proof (equality_transitivity G (σ zero ⊕ n) (σ (zero ⊕ n)) (σ n) HE HR HS) as HF.
  apply (strict_order_witness G zero (σ n) n).
  exact (equality_symmetry G (σ zero ⊕ n) (σ n) HE HF).
Qed.
Lemma positive_product G a b : has_product_context G ->
  G ⊢C (zero ⧀ a) -> G ⊢C (zero ⧀ b) -> G ⊢C (zero ⧀ (a ⊗ b)).
Proof.
  intros HG HA HB. unfold PAlt in HA. eapply ExE_named; [exact HA|]. intros k.
  change ((List.cons (a`[↑]`[k..] == σ zero ⊕ k) G) ⊢C (zero ⧀ (a ⊗ b))).
  rewrite subst_term_shift.
  set (D := List.cons (a == σ zero ⊕ k) G).
  change (D ⊢C (zero ⧀ (a ⊗ b))).
  pose proof (weaken_head G (zero ⧀ b) (a == σ zero ⊕ k) HB) as HBD.
  unfold PAlt in HBD. eapply ExE_named; [exact HBD|]. intros d.
  change ((List.cons (b`[↑]`[d..] == σ zero ⊕ d) D) ⊢C (zero ⧀ (a ⊗ b))).
  rewrite subst_term_shift.
  set (E := List.cons (b == σ zero ⊕ d) D).
  change (E ⊢C (zero ⧀ (a ⊗ b))).
  assert (HEG : has_product_context E).
  { unfold E, D. apply has_product_cons, has_product_cons. exact HG. }
  pose proof (product_has_equality E HEG) as HE.
  assert (Hak : E ⊢C (a == σ zero ⊕ k)).
  { apply Ctx. unfold E, D. right. now left. }
  assert (Hbd : E ⊢C (b == σ zero ⊕ d)).
  { apply Ctx. unfold E. now left. }
  pose proof (PAOrder238.add_rec_instance E zero k
    (HEG ax_add_rec product_add_rec)) as Hrec.
  pose proof (PAAddition238.add_zero_instance E k
    (HEG ax_add_zero product_add_zero)) as Hzero.
  pose proof (IE (successor_instance E (zero ⊕ k) k HE) Hzero) as Hsucc.
  pose proof (equality_transitivity E a (σ zero ⊕ k) (σ (zero ⊕ k))
    HE Hak Hrec) as Ha1.
  pose proof (equality_transitivity E a (σ (zero ⊕ k)) (σ k) HE Ha1 Hsucc) as Ha.
  pose proof (reflexivity_instance E b HE) as Hbref.
  pose proof (IE (IE (multiplication_instance E a (σ k) b b HE) Ha) Hbref) as Hmul.
  pose proof (mult_rec_instance E k b (HEG ax_mult_rec product_mult_rec)) as Hmrec.
  pose proof (equality_transitivity E (a ⊗ b) (σ k ⊗ b)
    (b ⊕ (k ⊗ b)) HE Hmul Hmrec) as Hfront.
  pose proof (reflexivity_instance E (k ⊗ b) HE) as Hkref.
  pose proof (IE (IE (addition_instance E b (σ zero ⊕ d)
    (k ⊗ b) (k ⊗ b) HE) Hbd) Hkref) as Hadd.
  pose proof (associativity_instance E (σ zero) d (k ⊗ b)
    (HEG associativity_sentence product_associativity)) as Hassoc.
  pose proof (equality_symmetry E (σ zero ⊕ (d ⊕ (k ⊗ b)))
    ((σ zero ⊕ d) ⊕ (k ⊗ b)) HE Hassoc) as Hback.
  pose proof (equality_transitivity E (b ⊕ (k ⊗ b)) ((σ zero ⊕ d) ⊕ (k ⊗ b))
    (σ zero ⊕ (d ⊕ (k ⊗ b))) HE Hadd Hback) as Htail.
  apply (strict_order_witness E zero (a ⊗ b) (d ⊕ (k ⊗ b))).
  exact (equality_transitivity E (a ⊗ b) (b ⊕ (k ⊗ b))
    (σ zero ⊕ (d ⊕ (k ⊗ b))) HE Hfront Htail).
Qed.
Theorem mult_positive :
  paeq_derivable (∀ ∀ (zero ⧀ $0 → zero ⧀ $1 → zero ⧀ ($0 ⊗ $1))).
Proof.
  apply paeq_generalize, paeq_generalize, product_proof, II, II.
  set (G := List.cons (zero ⧀ $1) (List.cons (zero ⧀ $0) product_context)).
  apply (positive_product G $0 $1).
  - unfold G. apply has_product_cons, has_product_cons. exact product_context_self.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.
Theorem successor_positive : paeq_derivable (∀ (zero ⧀ σ $0)).
Proof.
  apply paeq_generalize, product_proof, zero_below_successor. exact product_context_self.
Qed.

Lemma positive_product_upper G a L : has_product_context G ->
  G ⊢C (zero ⧀ a) -> G ⊢C (L ⧀ (a ⊗ σ L)).
Proof.
  intros HG HA. unfold PAlt in HA. eapply ExE_named; [exact HA|]. intros k.
  change ((List.cons (a`[↑]`[k..] == σ zero ⊕ k) G) ⊢C (L ⧀ (a ⊗ σ L))).
  rewrite subst_term_shift.
  set (D := List.cons (a == σ zero ⊕ k) G).
  change (D ⊢C (L ⧀ (a ⊗ σ L))).
  assert (HD : has_product_context D).
  { unfold D. apply has_product_cons. exact HG. }
  pose proof (product_has_equality D HD) as HE.
  assert (Hak : D ⊢C (a == σ zero ⊕ k)).
  { apply Ctx. unfold D. now left. }
  pose proof (PAOrder238.add_rec_instance D zero k (HD ax_add_rec product_add_rec)) as Hrec.
  pose proof (PAAddition238.add_zero_instance D k (HD ax_add_zero product_add_zero)) as Hzero.
  pose proof (IE (successor_instance D (zero ⊕ k) k HE) Hzero) as Hsucc.
  pose proof (equality_transitivity D a (σ zero ⊕ k) (σ (zero ⊕ k)) HE Hak Hrec) as Hfirst.
  pose proof (equality_transitivity D a (σ (zero ⊕ k)) (σ k) HE Hfirst Hsucc) as Ha.
  pose proof (reflexivity_instance D (σ L) HE) as HL.
  pose proof (IE (IE (multiplication_instance D a (σ k) (σ L) (σ L) HE) Ha) HL) as Hmul.
  pose proof (mult_rec_instance D k (σ L) (HD ax_mult_rec product_mult_rec)) as Hmrec.
  apply (strict_order_witness D L (a ⊗ σ L) (k ⊗ σ L)).
  exact (equality_transitivity D (a ⊗ σ L) (σ k ⊗ σ L)
    (σ L ⊕ (k ⊗ σ L)) HE Hmul Hmrec).
Qed.
Theorem positive_scale_bound :
  paeq_derivable (∀ ∀ (zero ⧀ $0 → $1 ⧀ ($0 ⊗ σ $1))).
Proof.
  apply paeq_generalize, paeq_generalize, product_proof, II.
  set (G := List.cons (zero ⧀ $0) product_context).
  apply (positive_product_upper G $0 $1).
  - unfold G. apply has_product_cons. exact product_context_self.
  - apply Ctx. unfold G. now left.
Qed.

End PASemiring238.

Print Assumptions PASemiring238.mult_right_zero.
Print Assumptions PASemiring238.mult_left_distribution.
Print Assumptions PASemiring238.mult_associative.
Print Assumptions PASemiring238.divides_right_product.
Print Assumptions PASemiring238.divides_composition.
Print Assumptions PASemiring238.mult_positive.
Print Assumptions PASemiring238.successor_positive.
Print Assumptions PASemiring238.positive_scale_bound.
