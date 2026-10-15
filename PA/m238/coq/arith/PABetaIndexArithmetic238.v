(* Original finite ordinary-PA index arithmetic for the bounded beta CRT.
   A strict difference witness g supplies the positive gap S g.  Its bound
   is reconstructed by joining the actual strict and weak differences;
   neither subtraction nor a semantic arithmetic theorem is used. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAAddition238
  PAEqCongruence238 PAOrderBounds238 PAQuotient238 PASemiring238
  PAMultiplicationComm238 PAModuliInverse238 PACommonMultiple238
  CompactInPA238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrderBounds238
  PAQuotient238 PASemiring238 PAMultiplicationComm238 PAModuliInverse238
  PACommonMultiple238 CompactInPA238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PABetaIndexArithmetic238.

(* These eliminators expose literal PA equality witnesses under a finite
   hypothesis context.  They introduce no arithmetic premise. *)
Lemma strict_difference_eliminate G x y (psi : pa_form) :
  G ⊢C (x ⧀ y) ->
  (forall g, (List.cons (y == σ x ⊕ g) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. unfold PAlt in HX. eapply ExE_named; [exact HX|]. intros g.
  change ((List.cons (y`[↑]`[g..] == σ x`[↑]`[g..] ⊕ g) G) ⊢C psi).
  rewrite !subst_term_shift. exact (H g).
Qed.
Lemma weak_difference_eliminate G x y (psi : pa_form) :
  G ⊢C (x ⧀= y) ->
  (forall g, (List.cons (y == x ⊕ g) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. unfold PAle in HX. eapply ExE_named; [exact HX|]. intros g.
  change ((List.cons (y`[↑]`[g..] == x`[↑]`[g..] ⊕ g) G) ⊢C psi).
  rewrite !subst_term_shift. exact (H g).
Qed.

Lemma successor_add_exchange_at G a b : has_inverse_context G ->
  G ⊢C (σ a ⊕ b == σ b ⊕ a).
Proof.
  intros HG. pose proof (inverse_has_product G HG) as HP.
  pose proof (inverse_add_commutative G (σ a) b HG) as Hfirst.
  pose proof (right_successor_instance G b a
    (HP right_successor_sentence bounds_right_successor)) as Hsecond.
  pose proof (inverse_symmetry G (σ b ⊕ a) (σ (b ⊕ a)) HG
    (PAOrder238.add_rec_instance G b a (HP ax_add_rec product_add_rec))) as Hthird.
  pose proof (inverse_transitivity G (σ a ⊕ b) (b ⊕ σ a)
    (σ (b ⊕ a)) HG Hfirst Hsecond) as Hfront.
  exact (inverse_transitivity G (σ a ⊕ b) (σ (b ⊕ a))
    (σ b ⊕ a) HG Hfront Hthird).
Qed.

(* If t = S i + g and t <= k, the actual row index g lies below S k.
   The final strict-order difference is S(i+h), where k=t+h. *)
Lemma strict_gap_bounded_at G i t k g : has_inverse_context G ->
  G ⊢C (t == σ i ⊕ g) -> G ⊢C (t ⧀= k) -> G ⊢C (g ⧀ σ k).
Proof.
  intros HG Hgap Hbound. eapply weak_difference_eliminate; [exact Hbound|]. intros h.
  set (D := List.cons (k == t ⊕ h) G).
  change (D ⊢C (g ⧀ σ k)).
  assert (HD : has_inverse_context D).
  { unfold D. apply has_inverse_cons. exact HG. }
  pose proof (inverse_has_product D HD) as HP.
  assert (Hkh : D ⊢C (k == t ⊕ h)).
  { apply Ctx. unfold D. now left. }
  pose proof (weaken_head G (t == σ i ⊕ g) (k == t ⊕ h) Hgap) as HgapD.
  pose proof (inverse_transitivity D t (σ i ⊕ g) (σ g ⊕ i) HD HgapD
    (successor_add_exchange_at D i g HD)) as Ht.
  pose proof (inverse_addition D t (σ g ⊕ i) h h HD Ht
    (inverse_reflexivity D h HD)) as Hsum.
  pose proof (inverse_symmetry D (σ g ⊕ (i ⊕ h)) ((σ g ⊕ i) ⊕ h) HD
    (inverse_add_associative D (σ g) i h HD)) as Hassoc.
  pose proof (inverse_transitivity D k (t ⊕ h) ((σ g ⊕ i) ⊕ h)
    HD Hkh Hsum) as Hfront.
  pose proof (inverse_transitivity D k ((σ g ⊕ i) ⊕ h)
    (σ g ⊕ (i ⊕ h)) HD Hfront Hassoc) as Hk.
  pose proof (IE (successor_instance D k (σ g ⊕ (i ⊕ h))
    (inverse_equality D HD)) Hk) as Hsucc.
  pose proof (inverse_symmetry D (σ g ⊕ σ (i ⊕ h)) (σ (σ g ⊕ (i ⊕ h))) HD
    (right_successor_instance D (σ g) (i ⊕ h)
      (HP right_successor_sentence bounds_right_successor))) as Hright.
  apply (strict_order_witness D g (σ k) (σ (i ⊕ h))).
  exact (inverse_transitivity D (σ k) (σ (σ g ⊕ (i ⊕ h)))
    (σ g ⊕ σ (i ⊕ h)) HD Hsucc Hright).
Qed.
Theorem strict_gap_bounded : paeq_derivable (∀ ∀ ∀ ∀
  ($1 == σ $0 ⊕ $3 → $1 ⧀= $2 → $3 ⧀ σ $2)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    inverse_proof, II, II.
  set (G := List.cons ($1 ⧀= $2) (List.cons ($1 == σ $0 ⊕ $3) inverse_context)).
  apply (strict_gap_bounded_at G $0 $1 $2 $3).
  - unfold G. apply has_inverse_cons, has_inverse_cons. exact inverse_context_self.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Lemma successor_gap_at G i t g : has_inverse_context G ->
  G ⊢C (t == σ i ⊕ g) -> G ⊢C (σ t == σ i ⊕ σ g).
Proof.
  intros HG Hgap. pose proof (inverse_has_product G HG) as HP.
  pose proof (IE (successor_instance G t (σ i ⊕ g) (inverse_equality G HG)) Hgap) as Hfirst.
  pose proof (inverse_symmetry G (σ i ⊕ σ g) (σ (σ i ⊕ g)) HG
    (right_successor_instance G (σ i) g
      (HP right_successor_sentence bounds_right_successor))) as Hsecond.
  exact (inverse_transitivity G (σ t) (σ (σ i ⊕ g))
    (σ i ⊕ σ g) HG Hfirst Hsecond).
Qed.

Lemma successor_one_sum_at G a : has_inverse_context G ->
  G ⊢C (σ a == σ zero ⊕ a).
Proof.
  intros HG. pose proof (inverse_has_product G HG) as HP.
  pose proof (PAOrder238.add_rec_instance G zero a
    (HP ax_add_rec product_add_rec)) as Hfirst.
  pose proof (PAAddition238.add_zero_instance G a
    (HP ax_add_zero product_add_zero)) as Hzero.
  pose proof (IE (successor_instance G (zero ⊕ a) a (inverse_equality G HG)) Hzero) as Hsecond.
  pose proof (inverse_transitivity G (σ zero ⊕ a) (σ (zero ⊕ a)) (σ a)
    HG Hfirst Hsecond) as Hforward.
  exact (inverse_symmetry G (σ zero ⊕ a) (σ a) HG Hforward).
Qed.

Lemma inverse_exists_transport_at G A B A' B' : has_inverse_context G ->
  G ⊢C (A == A') -> G ⊢C (B == B') ->
  G ⊢C inverse_exists A B -> G ⊢C inverse_exists A' B'.
Proof.
  intros HG HA HB HX.
  pose proof (formula_substitutivity G (inverse_exists $0 B`[↑]) A A'
    (inverse_equality G HG) HA) as Hfirst.
  rewrite !inverse_exists_subst, !subst_term_shift in Hfirst.
  pose proof (IE (CE1 Hfirst) HX) as Hmid.
  pose proof (formula_substitutivity G (inverse_exists A'`[↑] $0) B B'
    (inverse_equality G HG) HB) as Hsecond.
  rewrite !inverse_exists_subst, !subst_term_shift in Hsecond.
  exact (IE (CE1 Hsecond) Hmid).
Qed.

(* The common multiple rows contain S g because g < S k.  Positivity of
   C and both successor indices then feeds the existing exact inverse
   polynomial; no division-totality premise is required. *)
Lemma bounded_moduli_inverse_at G i t k C : has_pairwise_context G ->
  G ⊢C (i ⧀ t) -> G ⊢C (t ⧀= k) ->
  G ⊢C common_multiple (σ k) C ->
  G ⊢C inverse_exists (beta_modulus C i) (beta_modulus C t).
Proof.
  intros HG Hlt Hbound Hmultiple.
  eapply strict_difference_eliminate; [exact Hlt|]. intros g.
  set (D := List.cons (t == σ i ⊕ g) G).
  change (D ⊢C inverse_exists (beta_modulus C i) (beta_modulus C t)).
  assert (HD : has_pairwise_context D).
  { unfold D. apply has_pairwise_cons. exact HG. }
  pose proof (pairwise_has_inverse D HD) as HI.
  pose proof (inverse_has_product D HI) as HP.
  assert (Hgap : D ⊢C (t == σ i ⊕ g)).
  { apply Ctx. unfold D. now left. }
  pose proof (weaken_head G (t ⧀= k) (t == σ i ⊕ g) Hbound) as HboundD.
  pose proof (weaken_head G (common_multiple (σ k) C)
    (t == σ i ⊕ g) Hmultiple) as HM.
  pose proof (strict_gap_bounded_at D i t k g HI Hgap HboundD) as Hrow.
  pose proof (multiple_rows_at D (σ k) C g (CE2 HM) Hrow) as Hdiv.
  pose proof (successor_gap_at D i t g HI Hgap) as Hsuccgap.
  pose proof (special_moduli_inverse_exists_at D (σ i) (σ t) C (σ g) HD
    (PASemiring238.zero_below_successor D i HP)
    (PASemiring238.zero_below_successor D t HP) (CE1 HM) Hsuccgap Hdiv) as Hinv.
  apply (inverse_exists_transport_at D (σ zero ⊕ (σ i ⊗ C))
    (σ zero ⊕ (σ t ⊗ C)) (beta_modulus C i) (beta_modulus C t) HI).
  - unfold beta_modulus. exact (inverse_symmetry D (σ (σ i ⊗ C))
      (σ zero ⊕ (σ i ⊗ C)) HI (successor_one_sum_at D (σ i ⊗ C) HI)).
  - unfold beta_modulus. exact (inverse_symmetry D (σ (σ t ⊗ C))
      (σ zero ⊕ (σ t ⊗ C)) HI (successor_one_sum_at D (σ t ⊗ C) HI)).
  - exact Hinv.
Qed.
Theorem bounded_moduli_inverse : paeq_derivable (∀ ∀ ∀ ∀
  ($0 ⧀ $1 → $1 ⧀= $2 → common_multiple (σ $2) $3 →
    inverse_exists (beta_modulus $3 $0) (beta_modulus $3 $1))).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    pairwise_proof, II, II, II.
  set (G := List.cons (common_multiple (σ $2) $3)
    (List.cons ($1 ⧀= $2) (List.cons ($0 ⧀ $1) pairwise_context))).
  apply (bounded_moduli_inverse_at G $0 $1 $2 $3).
  - unfold G. apply has_pairwise_cons, has_pairwise_cons, has_pairwise_cons.
    exact pairwise_context_self.
  - apply Ctx. unfold G. right. right. now left.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

(* Join v<=L and L<C using their actual witnesses L=v+g and C=S L+h.
   The strict difference from v to C is g+h. *)
Lemma weak_strict_transitive_at G v L C : has_inverse_context G ->
  G ⊢C (v ⧀= L) -> G ⊢C (L ⧀ C) -> G ⊢C (v ⧀ C).
Proof.
  intros HG Hweak Hstrict.
  eapply weak_difference_eliminate; [exact Hweak|]. intros g.
  set (D := List.cons (L == v ⊕ g) G).
  change (D ⊢C (v ⧀ C)).
  pose proof (weaken_head G (L ⧀ C) (L == v ⊕ g) Hstrict) as HstrictD.
  eapply strict_difference_eliminate; [exact HstrictD|]. intros h.
  set (E := List.cons (C == σ L ⊕ h) D).
  change (E ⊢C (v ⧀ C)).
  assert (HE : has_inverse_context E).
  { unfold E, D. apply has_inverse_cons, has_inverse_cons. exact HG. }
  pose proof (inverse_has_product E HE) as HP.
  assert (HL : E ⊢C (L == v ⊕ g)).
  { apply Ctx. unfold E, D. right. now left. }
  assert (HC : E ⊢C (C == σ L ⊕ h)).
  { apply Ctx. unfold E. now left. }
  pose proof (IE (successor_instance E L (v ⊕ g) (inverse_equality E HE)) HL) as HSfirst.
  pose proof (inverse_symmetry E (σ v ⊕ g) (σ (v ⊕ g)) HE
    (PAOrder238.add_rec_instance E v g (HP ax_add_rec product_add_rec))) as HSsecond.
  pose proof (inverse_transitivity E (σ L) (σ (v ⊕ g))
    (σ v ⊕ g) HE HSfirst HSsecond) as HS.
  pose proof (inverse_addition E (σ L) (σ v ⊕ g) h h HE HS
    (inverse_reflexivity E h HE)) as Hsum.
  pose proof (inverse_symmetry E (σ v ⊕ (g ⊕ h)) ((σ v ⊕ g) ⊕ h) HE
    (inverse_add_associative E (σ v) g h HE)) as Hassoc.
  pose proof (inverse_transitivity E C (σ L ⊕ h) ((σ v ⊕ g) ⊕ h)
    HE HC Hsum) as Hfront.
  apply (strict_order_witness E v C (g ⊕ h)).
  exact (inverse_transitivity E C ((σ v ⊕ g) ⊕ h)
    (σ v ⊕ (g ⊕ h)) HE Hfront Hassoc).
Qed.
Theorem weak_strict_transitive : paeq_derivable (∀ ∀ ∀
  ($0 ⧀= $1 → $1 ⧀ $2 → $0 ⧀ $2)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, inverse_proof, II, II.
  set (G := List.cons ($1 ⧀ $2) (List.cons ($0 ⧀= $1) inverse_context)).
  apply (weak_strict_transitive_at G $0 $1 $2).
  - unfold G. apply has_inverse_cons, has_inverse_cons. exact inverse_context_self.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

(* Every new beta modulus is S(C+i*C).  If C=S v+h, its strict
   difference from v is S h+i*C, independent of any bound on i. *)
Lemma strict_modulus_extension_at G v C i : has_inverse_context G ->
  G ⊢C (v ⧀ C) -> G ⊢C (v ⧀ beta_modulus C i).
Proof.
  intros HG Hstrict. eapply strict_difference_eliminate; [exact Hstrict|]. intros h.
  set (D := List.cons (C == σ v ⊕ h) G).
  change (D ⊢C (v ⧀ beta_modulus C i)).
  assert (HD : has_inverse_context D).
  { unfold D. apply has_inverse_cons. exact HG. }
  pose proof (inverse_has_product D HD) as HP.
  assert (HC : D ⊢C (C == σ v ⊕ h)).
  { apply Ctx. unfold D. now left. }
  pose proof (mult_rec_instance D i C (HP ax_mult_rec product_mult_rec)) as Hmul.
  pose proof (IE (successor_instance D (σ i ⊗ C) (C ⊕ (i ⊗ C))
    (inverse_equality D HD)) Hmul) as Hfirst.
  pose proof (inverse_symmetry D (σ C ⊕ (i ⊗ C)) (σ (C ⊕ (i ⊗ C))) HD
    (PAOrder238.add_rec_instance D C (i ⊗ C) (HP ax_add_rec product_add_rec))) as Hsecond.
  pose proof (IE (successor_instance D C (σ v ⊕ h) (inverse_equality D HD)) HC) as HCfirst.
  pose proof (inverse_symmetry D (σ v ⊕ σ h) (σ (σ v ⊕ h)) HD
    (right_successor_instance D (σ v) h
      (HP right_successor_sentence bounds_right_successor))) as HCsecond.
  pose proof (inverse_transitivity D (σ C) (σ (σ v ⊕ h))
    (σ v ⊕ σ h) HD HCfirst HCsecond) as HSC.
  pose proof (inverse_addition D (σ C) (σ v ⊕ σ h) (i ⊗ C) (i ⊗ C) HD
    HSC (inverse_reflexivity D (i ⊗ C) HD)) as Hthird.
  pose proof (inverse_symmetry D (σ v ⊕ (σ h ⊕ (i ⊗ C)))
    ((σ v ⊕ σ h) ⊕ (i ⊗ C)) HD
    (inverse_add_associative D (σ v) (σ h) (i ⊗ C) HD)) as Hfourth.
  pose proof (inverse_transitivity D (beta_modulus C i) (σ (C ⊕ (i ⊗ C)))
    (σ C ⊕ (i ⊗ C)) HD Hfirst Hsecond) as Hfront.
  pose proof (inverse_transitivity D (beta_modulus C i) (σ C ⊕ (i ⊗ C))
    ((σ v ⊕ σ h) ⊕ (i ⊗ C)) HD Hfront Hthird) as Hmid.
  apply (strict_order_witness D v (beta_modulus C i) (σ h ⊕ (i ⊗ C))).
  exact (inverse_transitivity D (beta_modulus C i) ((σ v ⊕ σ h) ⊕ (i ⊗ C))
    (σ v ⊕ (σ h ⊕ (i ⊗ C))) HD Hmid Hfourth).
Qed.

Lemma residue_below_modulus_at G v L C i : has_inverse_context G ->
  G ⊢C (v ⧀= L) -> G ⊢C (L ⧀ C) ->
  G ⊢C (v ⧀ beta_modulus C i).
Proof.
  intros HG Hweak Hstrict. apply (strict_modulus_extension_at G v C i HG).
  exact (weak_strict_transitive_at G v L C HG Hweak Hstrict).
Qed.
Theorem residue_below_modulus : paeq_derivable (∀ ∀ ∀ ∀
  ($0 ⧀= $1 → $1 ⧀ $2 → $0 ⧀ beta_modulus $2 $3)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    inverse_proof, II, II.
  set (G := List.cons ($1 ⧀ $2) (List.cons ($0 ⧀= $1) inverse_context)).
  apply (residue_below_modulus_at G $0 $1 $2 $3).
  - unfold G. apply has_inverse_cons, has_inverse_cons. exact inverse_context_self.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

End PABetaIndexArithmetic238.

Print Assumptions PABetaIndexArithmetic238.strict_gap_bounded.
Print Assumptions PABetaIndexArithmetic238.bounded_moduli_inverse.
Print Assumptions PABetaIndexArithmetic238.weak_strict_transitive.
Print Assumptions PABetaIndexArithmetic238.residue_below_modulus.
