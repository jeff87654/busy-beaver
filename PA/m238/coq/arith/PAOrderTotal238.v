(* Original finite ordinary-PA comparison certificates. The comparison
   induction has an arbitrary second input, and every derived context is
   discharged using its displayed finite PA certificates. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238
  PAAddition238 PAOrderBounds238 PACancellation238 PAQuotient238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrderBounds238 PAQuotient238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAOrderTotal238.

Definition trichotomy (x y : pa_term) : pa_form :=
  (x ⧀ y) ∨ ((x == y) ∨ (y ⧀ x)).
Lemma trichotomy_subst x y rho :
  (trichotomy x y)[rho] = trichotomy x`[rho] y`[rho].
Proof. unfold trichotomy. cbn [subst_form]. rewrite !PAlt_subst. reflexivity. Qed.

Lemma proof_formula_transport G phi psi :
  phi = psi -> G ⊢C phi -> G ⊢C psi.
Proof. intros <- H. exact H. Qed.
Lemma comparison_instance x y :
  (trichotomy x`[↑] $0)[y..] = trichotomy x y.
Proof.
  rewrite trichotomy_subst.
  change (trichotomy x`[↑]`[y..] y = trichotomy x y).
  exact (f_equal (fun t => trichotomy t y)
    (@subst_term_shift PA_funcs_signature x y)).
Qed.
Lemma comparison_left_instance x y :
  (trichotomy $0 y`[↑])[x..] = trichotomy x y.
Proof.
  rewrite trichotomy_subst.
  change (trichotomy x y`[↑]`[x..] = trichotomy x y).
  exact (f_equal (fun t => trichotomy x t)
    (@subst_term_shift PA_funcs_signature y x)).
Qed.
Lemma comparison_double_instance x y :
  ((trichotomy $0 $1)[up (y..)])[x..] = trichotomy x y.
Proof.
  rewrite !trichotomy_subst.
  change (trichotomy x y`[↑]`[x..] = trichotomy x y).
  exact (f_equal (fun t => trichotomy x t)
    (@subst_term_shift PA_funcs_signature y x)).
Qed.

Definition comparison_property (x : pa_term) : pa_form :=
  ∀ trichotomy x`[↑] $0.
Lemma comparison_property_subst x rho :
  (comparison_property x)[rho] = comparison_property x`[rho].
Proof.
  unfold comparison_property. cbn [subst_form]. rewrite trichotomy_subst.
  now rewrite up_term.
Qed.
Lemma comparison_introduce G x :
  (forall y, G ⊢C trichotomy x y) -> G ⊢C comparison_property x.
Proof.
  intros H. unfold comparison_property. apply AllI_named. intros y.
  change (G ⊢C (trichotomy x`[↑] $0)[y..]).
  exact (proof_formula_transport G (trichotomy x y)
    ((trichotomy x`[↑] $0)[y..]) (eq_sym (comparison_instance x y)) (H y)).
Qed.
Lemma comparison_at G x y :
  G ⊢C comparison_property x -> G ⊢C trichotomy x y.
Proof.
  intros H. pose proof (AllE y H) as HK.
  change (G ⊢C (trichotomy x`[↑] $0)[y..]) in HK.
  exact (proof_formula_transport G ((trichotomy x`[↑] $0)[y..])
    (trichotomy x y) (comparison_instance x y) HK).
Qed.

Lemma quotient_predecessor : List.In predecessor_sentence quotient_context.
Proof.
  unfold quotient_context. apply List.in_app_iff. left.
  right. right. right. now left.
Qed.
Lemma quotient_add_rec : List.In ax_add_rec quotient_context.
Proof. apply quotient_bounds. exact bounds_add_rec. Qed.
Lemma predecessor_at G x : has_quotient_context G ->
  G ⊢C ((x == zero) ∨ ∃ (x`[↑] == σ $0)).
Proof.
  intros HG. assert (H : G ⊢C predecessor_sentence).
  { apply Ctx, HG, quotient_predecessor. }
  pose proof (AllE x H) as HK. cbn in HK. exact HK.
Qed.
Lemma predecessor_cases G x psi : has_quotient_context G ->
  (List.cons (x == zero) G) ⊢C psi ->
  (forall y, (List.cons (x == σ y) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HG Hzero Hsuccessor.
  eapply DE; [exact (predecessor_at G x HG)|exact Hzero|].
  eapply ExE_named; [apply Ctx; now left|]. intros y.
  change ((List.cons (x`[↑]`[y..] == σ y)
    (List.cons (∃ (x`[↑] == σ $0)) G)) ⊢C psi).
  rewrite subst_term_shift.
  eapply Weak; [exact (Hsuccessor y)|].
  intros chi [<-|Hchi]; [now left|right; now right].
Qed.

Lemma right_zero_at G x : has_quotient_context G -> G ⊢C (x ⊕ zero == x).
Proof.
  intros HG. assert (H : G ⊢C right_zero_sentence).
  { apply Ctx, HG, quotient_bounds, bounds_right_zero. }
  pose proof (AllE x H) as HK. change (G ⊢C (x ⊕ zero == x)) in HK. exact HK.
Qed.

Lemma zero_below_successor G x : has_quotient_context G -> G ⊢C (zero ⧀ σ x).
Proof.
  intros HG. pose proof (quotient_has_equality G HG) as HE.
  pose proof (PAOrder238.add_rec_instance G zero x
    (HG ax_add_rec quotient_add_rec)) as Hrec.
  pose proof (PAAddition238.add_zero_instance G x
    (HG ax_add_zero quotient_add_zero)) as Hzero.
  pose proof (IE (successor_instance G (zero ⊕ x) x HE) Hzero) as Hsucc.
  apply (strict_order_witness G zero (σ x) x).
  exact (equality_symmetry G (σ zero ⊕ x) (σ x) HE
    (equality_transitivity G (σ zero ⊕ x) (σ (zero ⊕ x)) (σ x) HE Hrec Hsucc)).
Qed.

Lemma strict_successors G x y : has_quotient_context G ->
  G ⊢C (x ⧀ y) -> G ⊢C (σ x ⧀ σ y).
Proof.
  intros HG Hxy. unfold PAlt in Hxy.
  eapply ExE_named; [exact Hxy|]. intros d.
  change ((List.cons (y`[↑]`[d..] == σ x`[↑]`[d..] ⊕ d) G)
    ⊢C (σ x ⧀ σ y)).
  rewrite !subst_term_shift.
  set (D := List.cons (y == σ x ⊕ d) G).
  assert (HD : has_quotient_context D).
  { unfold D. apply has_quotient_cons. exact HG. }
  pose proof (quotient_has_equality D HD) as HE.
  assert (Hgap : D ⊢C (y == σ x ⊕ d)).
  { apply Ctx. unfold D. now left. }
  pose proof (IE (successor_instance D y (σ x ⊕ d) HE) Hgap) as HS.
  pose proof (PAOrder238.add_rec_instance D (σ x) d
    (HD ax_add_rec quotient_add_rec)) as HA.
  apply (strict_order_witness D (σ x) (σ y) d).
  exact (equality_transitivity D (σ y) (σ (σ x ⊕ d)) (σ (σ x) ⊕ d) HE HS
    (equality_symmetry D (σ (σ x) ⊕ d) (σ (σ x ⊕ d)) HE HA)).
Qed.

Lemma trichotomy_left_transport G x x' y : has_quotient_context G ->
  G ⊢C (x == x') -> G ⊢C trichotomy x y -> G ⊢C trichotomy x' y.
Proof.
  intros HG Hx Htri.
  pose proof (formula_substitutivity G (trichotomy $0 y`[↑]) x x'
    (quotient_has_equality G HG) Hx) as HT.
  pose proof (f_equal2 (fun phi psi : pa_form => phi ↔ psi)
    (comparison_left_instance x y) (comparison_left_instance x' y)) as HF.
  pose proof (proof_formula_transport G _ _ HF HT) as HT'.
  exact (IE (CE1 HT') Htri).
Qed.
Lemma trichotomy_right_transport G x y y' : has_quotient_context G ->
  G ⊢C (y == y') -> G ⊢C trichotomy x y -> G ⊢C trichotomy x y'.
Proof.
  intros HG Hy Htri.
  pose proof (formula_substitutivity G (trichotomy x`[↑] $0) y y'
    (quotient_has_equality G HG) Hy) as HT.
  pose proof (f_equal2 (fun phi psi : pa_form => phi ↔ psi)
    (comparison_instance x y) (comparison_instance x y')) as HF.
  pose proof (proof_formula_transport G _ _ HF HT) as HT'.
  exact (IE (CE1 HT') Htri).
Qed.

Lemma trichotomy_successors G x y : has_quotient_context G ->
  G ⊢C trichotomy x y -> G ⊢C trichotomy (σ x) (σ y).
Proof.
  intros HG HT. unfold trichotomy in HT |- *.
  eapply DE; [exact HT| |].
  - apply DI1, strict_successors.
    + apply has_quotient_cons. exact HG.
    + apply Ctx. now left.
  - eapply DE; [apply Ctx; now left| |].
    + apply DI2, DI1. eapply IE.
      * apply successor_instance, quotient_has_equality,
          has_quotient_cons, has_quotient_cons. exact HG.
      * apply Ctx. now left.
    + apply DI2, DI2, strict_successors.
      * apply has_quotient_cons, has_quotient_cons. exact HG.
      * apply Ctx. now left.
Qed.

Definition comparison_formula : pa_form := comparison_property $0.
Lemma comparison_base : paeq_derivable comparison_formula[zero..].
Proof.
  unfold comparison_formula. rewrite comparison_property_subst.
  change (paeq_derivable (comparison_property zero)).
  apply quotient_proof, comparison_introduce. intros y.
  eapply (predecessor_cases quotient_context y (trichotomy zero y));
    [exact quotient_context_self| |].
  - set (G := List.cons (y == zero) quotient_context).
    assert (HG : has_quotient_context G).
    { unfold G. apply has_quotient_cons. exact quotient_context_self. }
    change (G ⊢C trichotomy zero y). unfold trichotomy. apply DI2, DI1.
    apply equality_symmetry; [exact (quotient_has_equality G HG)|].
    apply Ctx. unfold G. now left.
  - intros p. set (G := List.cons (y == σ p) quotient_context).
    assert (HG : has_quotient_context G).
    { unfold G. apply has_quotient_cons. exact quotient_context_self. }
    change (G ⊢C trichotomy zero y).
    apply (trichotomy_right_transport G zero (σ p) y HG).
    + apply equality_symmetry; [exact (quotient_has_equality G HG)|].
      apply Ctx. unfold G. now left.
    + unfold trichotomy. apply DI1. exact (zero_below_successor G p HG).
Qed.
Lemma comparison_step : paeq_derivable
  (∀ (comparison_formula → comparison_formula[σ $0 .: S >> var])).
Proof.
  unfold comparison_formula. rewrite comparison_property_subst.
  change (paeq_derivable (∀ (comparison_property $0 → comparison_property (σ $0)))).
  apply paeq_generalize, quotient_proof, II, comparison_introduce. intros y.
  set (G := List.cons (comparison_property $0) quotient_context).
  assert (HG : has_quotient_context G).
  { unfold G. apply has_quotient_cons. exact quotient_context_self. }
  change (G ⊢C trichotomy (σ $0) y).
  eapply (predecessor_cases G y (trichotomy (σ $0) y)); [exact HG| |].
  - set (D := List.cons (y == zero) G).
    assert (HD : has_quotient_context D).
    { unfold D. apply has_quotient_cons. exact HG. }
    change (D ⊢C trichotomy (σ $0) y).
    apply (trichotomy_right_transport D (σ $0) zero y HD).
    + apply equality_symmetry; [exact (quotient_has_equality D HD)|].
      apply Ctx. unfold D. now left.
    + unfold trichotomy. apply DI2, DI2. exact (zero_below_successor D $0 HD).
  - intros p. set (D := List.cons (y == σ p) G).
    assert (HD : has_quotient_context D).
    { unfold D. apply has_quotient_cons. exact HG. }
    change (D ⊢C trichotomy (σ $0) y).
    apply (trichotomy_right_transport D (σ $0) (σ p) y HD).
    + apply equality_symmetry; [exact (quotient_has_equality D HD)|].
      apply Ctx. unfold D. now left.
    + apply (trichotomy_successors D $0 p HD), comparison_at.
      apply Ctx. unfold D, G. right. now left.
Qed.

Definition trichotomy_sentence : pa_form := ∀ ∀ trichotomy $0 $1.
Theorem order_trichotomy : paeq_derivable trichotomy_sentence.
Proof.
  pose proof (paeq_induction_rule comparison_formula comparison_base comparison_step) as H.
  destruct H as (A & HA & HD). exists A. split; [exact HA|].
  apply AllI_named. intros y. apply AllI_named. intros x.
  change (A ⊢C (trichotomy $0 $1)[up (y..)][x..]).
  apply (proof_formula_transport A (trichotomy x y) _
    (eq_sym (comparison_double_instance x y))).
  apply (comparison_at A x y).
  pose proof (AllE x HD) as HK.
  change (A ⊢C comparison_formula[x..]) in HK.
  unfold comparison_formula in HK. rewrite comparison_property_subst in HK. exact HK.
Qed.

Definition total_context : list pa_form := List.cons trichotomy_sentence quotient_context.
Definition has_total_context (G : list pa_form) : Prop :=
  forall phi, List.In phi total_context -> List.In phi G.
Lemma total_proof phi : total_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := trichotomy_sentence).
  - apply quotient_proof, II. exact HD.
  - exact order_trichotomy.
Qed.
Lemma total_context_self : has_total_context total_context.
Proof. intros phi H. exact H. Qed.
Lemma has_total_cons G phi : has_total_context G -> has_total_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma total_has_quotient G : has_total_context G -> has_quotient_context G.
Proof. intros HG phi Hphi. apply HG. unfold total_context. now right. Qed.
Lemma trichotomy_at G x y : has_total_context G -> G ⊢C trichotomy x y.
Proof.
  intros HG. assert (H : G ⊢C trichotomy_sentence).
  { apply Ctx, HG. unfold total_context. now left. }
  assert (HB : bounded 2 (trichotomy $0 $1)).
  { unfold trichotomy, PAlt. solve_bounds. }
  pose proof (subst_forall_prv (phi := trichotomy $0 $1) (N := 2)
    H HB (x .: y .: var)) as HK.
  rewrite trichotomy_subst in HK. exact HK.
Qed.

Lemma strict_to_weak_at G x y : has_quotient_context G ->
  G ⊢C (x ⧀ y) -> G ⊢C (x ⧀= y).
Proof.
  intros HG Hxy. unfold PAlt in Hxy.
  eapply ExE_named; [exact Hxy|]. intros d.
  change ((List.cons (y`[↑]`[d..] == σ x`[↑]`[d..] ⊕ d) G) ⊢C (x ⧀= y)).
  rewrite !subst_term_shift. set (D := List.cons (y == σ x ⊕ d) G).
  assert (HD : has_quotient_context D).
  { unfold D. apply has_quotient_cons. exact HG. }
  pose proof (quotient_has_equality D HD) as HE.
  assert (Hgap : D ⊢C (y == σ x ⊕ d)).
  { apply Ctx. unfold D. now left. }
  pose proof (PAOrder238.add_rec_instance D x d
    (HD ax_add_rec quotient_add_rec)) as HL.
  pose proof (right_successor_instance D x d
    (HD right_successor_sentence (quotient_bounds right_successor_sentence bounds_right_successor))) as HR.
  pose proof (equality_transitivity D y (σ x ⊕ d) (σ (x ⊕ d)) HE Hgap HL) as HF.
  apply (weak_order_witness D x y (σ d)).
  exact (equality_transitivity D y (σ (x ⊕ d)) (x ⊕ σ d) HE HF
    (equality_symmetry D (x ⊕ σ d) (σ (x ⊕ d)) HE HR)).
Qed.
Lemma equality_to_weak_at G x y : has_quotient_context G ->
  G ⊢C (x == y) -> G ⊢C (x ⧀= y).
Proof.
  intros HG Hxy. pose proof (quotient_has_equality G HG) as HE.
  apply (weak_order_witness G x y zero).
  exact (equality_transitivity G y x (x ⊕ zero) HE
    (equality_symmetry G x y HE Hxy)
    (equality_symmetry G (x ⊕ zero) x HE (right_zero_at G x HG))).
Qed.

Lemma weak_to_strict_or_equal_at G x y : has_quotient_context G ->
  G ⊢C (x ⧀= y) -> G ⊢C ((x ⧀ y) ∨ (x == y)).
Proof.
  intros HG Hxy. unfold PAle in Hxy.
  eapply ExE_named; [exact Hxy|]. intros d.
  change ((List.cons (y`[↑]`[d..] == x`[↑]`[d..] ⊕ d) G)
    ⊢C ((x ⧀ y) ∨ (x == y))).
  rewrite !subst_term_shift. set (D := List.cons (y == x ⊕ d) G).
  assert (HD : has_quotient_context D).
  { unfold D. apply has_quotient_cons. exact HG. }
  eapply (predecessor_cases D d ((x ⧀ y) ∨ (x == y))); [exact HD| |].
  - set (E := List.cons (d == zero) D).
    assert (HE : has_quotient_context E).
    { unfold E. apply has_quotient_cons. exact HD. }
    pose proof (quotient_has_equality E HE) as HEquality.
    assert (Hd : E ⊢C (d == zero)). { apply Ctx. unfold E. now left. }
    assert (Hy : E ⊢C (y == x ⊕ d)). { apply Ctx. unfold E, D. right. now left. }
    pose proof (IE (IE (addition_instance E x x d zero HEquality)
      (reflexivity_instance E x HEquality)) Hd) as Hadd.
    pose proof (equality_transitivity E y (x ⊕ d) (x ⊕ zero) HEquality Hy Hadd) as Hfront.
    apply DI2, equality_symmetry; [exact HEquality|].
    exact (equality_transitivity E y (x ⊕ zero) x HEquality Hfront (right_zero_at E x HE)).
  - intros k. set (E := List.cons (d == σ k) D).
    assert (HE : has_quotient_context E).
    { unfold E. apply has_quotient_cons. exact HD. }
    pose proof (quotient_has_equality E HE) as HEquality.
    assert (Hd : E ⊢C (d == σ k)). { apply Ctx. unfold E. now left. }
    assert (Hy : E ⊢C (y == x ⊕ d)). { apply Ctx. unfold E, D. right. now left. }
    pose proof (IE (IE (addition_instance E x x d (σ k) HEquality)
      (reflexivity_instance E x HEquality)) Hd) as Hadd.
    pose proof (right_successor_instance E x k
      (HE right_successor_sentence (quotient_bounds right_successor_sentence bounds_right_successor))) as Hright.
    pose proof (PAOrder238.add_rec_instance E x k (HE ax_add_rec quotient_add_rec)) as Hleft.
    pose proof (equality_transitivity E y (x ⊕ d) (x ⊕ σ k) HEquality Hy Hadd) as Hfront.
    pose proof (equality_transitivity E y (x ⊕ σ k) (σ (x ⊕ k)) HEquality Hfront Hright) as Hmid.
    apply DI1, (strict_order_witness E x y k).
    exact (equality_transitivity E y (σ (x ⊕ k)) (σ x ⊕ k) HEquality Hmid
      (equality_symmetry E (σ x ⊕ k) (σ (x ⊕ k)) HEquality Hleft)).
Qed.
Lemma strict_or_equal_to_weak_at G x y : has_quotient_context G ->
  G ⊢C ((x ⧀ y) ∨ (x == y)) -> G ⊢C (x ⧀= y).
Proof.
  intros HG H. eapply DE; [exact H| |].
  - apply strict_to_weak_at; [apply has_quotient_cons; exact HG|apply Ctx; now left].
  - apply equality_to_weak_at; [apply has_quotient_cons; exact HG|apply Ctx; now left].
Qed.
Theorem weak_strict_split :
  paeq_derivable (∀ ∀ (($0 ⧀= $1) ↔ (($0 ⧀ $1) ∨ ($0 == $1)))).
Proof.
  apply paeq_generalize, paeq_generalize, quotient_proof, CI; apply II.
  - apply weak_to_strict_or_equal_at.
    + apply has_quotient_cons. exact quotient_context_self.
    + apply Ctx. now left.
  - apply strict_or_equal_to_weak_at.
    + apply has_quotient_cons. exact quotient_context_self.
    + apply Ctx. now left.
Qed.

Lemma strict_weak_at G x y z : has_quotient_context G ->
  G ⊢C (x ⧀ y) -> G ⊢C (y ⧀= z) -> G ⊢C (x ⧀ z).
Proof.
  intros HG Hx Hy. assert (H : G ⊢C strict_weak_sentence).
  { apply Ctx, HG, quotient_strict_weak. }
  assert (HB : bounded 3 ($0 ⧀ $1 → $1 ⧀= $2 → $0 ⧀ $2)).
  { unfold PAlt, PAle. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := $0 ⧀ $1 → $1 ⧀= $2 → $0 ⧀ $2) (N := 3)
    H HB (x .: y .: z .: var)) as HK.
  change (G ⊢C (PAlt $0 $1)[x .: y .: z .: var] →
    (PAle $1 $2)[x .: y .: z .: var] →
    (PAlt $0 $2)[x .: y .: z .: var]) in HK.
  rewrite !PAlt_subst, PAle_subst in HK. exact (IE (IE HK Hx) Hy).
Qed.
Lemma irreflexive_at G x : has_quotient_context G -> G ⊢C ¬ (x ⧀ x).
Proof.
  intros HG. assert (H : G ⊢C order_ir_sentence).
  { apply Ctx, HG, quotient_order_ir. }
  pose proof (AllE x H) as HK.
  change (G ⊢C ¬ ((PAlt $0 $0)[x..])) in HK. rewrite PAlt_subst in HK. exact HK.
Qed.
Lemma weak_implies_not_reverse_strict_at G x y : has_quotient_context G ->
  G ⊢C (y ⧀= x) -> G ⊢C ¬ (x ⧀ y).
Proof.
  intros HG Hweak. apply II.
  set (D := List.cons (x ⧀ y) G).
  assert (HD : has_quotient_context D).
  { unfold D. apply has_quotient_cons. exact HG. }
  apply (IE (irreflexive_at D x HD)).
  apply (strict_weak_at D x y x HD).
  - apply Ctx. unfold D. now left.
  - unfold D. apply weaken_head. exact Hweak.
Qed.
Lemma not_strict_implies_reverse_weak_at G x y : has_total_context G ->
  G ⊢C ¬ (x ⧀ y) -> G ⊢C (y ⧀= x).
Proof.
  intros HG Hnot. pose proof (trichotomy_at G x y HG) as HT.
  unfold trichotomy in HT. eapply DE; [exact HT| |].
  - apply Exp. eapply IE; [apply weaken_head; exact Hnot|apply Ctx; now left].
  - eapply DE; [apply Ctx; now left| |].
    + apply equality_to_weak_at.
      * apply total_has_quotient, has_total_cons, has_total_cons. exact HG.
      * apply equality_symmetry.
        -- apply quotient_has_equality, total_has_quotient,
             has_total_cons, has_total_cons. exact HG.
        -- apply Ctx. now left.
    + apply strict_to_weak_at.
      * apply total_has_quotient, has_total_cons, has_total_cons. exact HG.
      * apply Ctx. now left.
Qed.
Theorem strict_complement :
  paeq_derivable (∀ ∀ (¬ ($0 ⧀ $1) ↔ ($1 ⧀= $0))).
Proof.
  apply paeq_generalize, paeq_generalize, total_proof, CI; apply II.
  - apply not_strict_implies_reverse_weak_at.
    + apply has_total_cons. exact total_context_self.
    + apply Ctx. now left.
  - apply weak_implies_not_reverse_strict_at.
    + apply total_has_quotient, has_total_cons. exact total_context_self.
    + apply Ctx. now left.
Qed.

Lemma not_weak_implies_reverse_strict_at G x y : has_total_context G ->
  G ⊢C ¬ (x ⧀= y) -> G ⊢C (y ⧀ x).
Proof.
  intros HG Hnot. apply DN, II.
  set (D := List.cons (¬ (y ⧀ x)) G).
  assert (HD : has_total_context D).
  { unfold D. apply has_total_cons. exact HG. }
  assert (Hnyx : D ⊢C ¬ (y ⧀ x)).
  { apply Ctx. unfold D. now left. }
  pose proof (not_strict_implies_reverse_weak_at D y x HD Hnyx) as Hweak.
  eapply IE; [unfold D; apply weaken_head; exact Hnot|exact Hweak].
Qed.
Lemma strict_implies_not_reverse_weak_at G x y : has_quotient_context G ->
  G ⊢C (y ⧀ x) -> G ⊢C ¬ (x ⧀= y).
Proof.
  intros HG Hstrict. apply II.
  set (D := List.cons (x ⧀= y) G).
  assert (HD : has_quotient_context D).
  { unfold D. apply has_quotient_cons. exact HG. }
  assert (Hweak : D ⊢C (x ⧀= y)).
  { apply Ctx. unfold D. now left. }
  pose proof (weak_implies_not_reverse_strict_at D y x HD Hweak) as Hnot.
  eapply IE; [exact Hnot|unfold D; apply weaken_head; exact Hstrict].
Qed.
Theorem weak_complement :
  paeq_derivable (∀ ∀ (¬ ($0 ⧀= $1) ↔ ($1 ⧀ $0))).
Proof.
  apply paeq_generalize, paeq_generalize, total_proof, CI; apply II.
  - apply not_weak_implies_reverse_strict_at.
    + apply has_total_cons. exact total_context_self.
    + apply Ctx. now left.
  - apply strict_implies_not_reverse_weak_at.
    + apply total_has_quotient, has_total_cons. exact total_context_self.
    + apply Ctx. now left.
Qed.

End PAOrderTotal238.

Print Assumptions PAOrderTotal238.order_trichotomy.
Print Assumptions PAOrderTotal238.total_proof.
Print Assumptions PAOrderTotal238.trichotomy_at.
Print Assumptions PAOrderTotal238.weak_strict_split.
Print Assumptions PAOrderTotal238.strict_complement.
Print Assumptions PAOrderTotal238.weak_complement.
