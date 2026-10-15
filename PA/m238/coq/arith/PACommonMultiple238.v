(* Original finite ordinary-PA existence of a positive common multiple.
   Index i denotes the positive divisor S i.  The induction step uses the
   concrete witness C*(S n), preserving old divisor witnesses and adding
   the new endpoint.  No factorial or sequence-existence premise appears. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238
  PASemiring238 PAMultiplicationComm238 PAPowerExtension238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PASemiring238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PACommonMultiple238.

Definition multiplication_commutative_sentence : pa_form :=
  ∀ ∀ ($0 ⊗ $1 == $1 ⊗ $0).
Definition successor_split_sentence : pa_form :=
  ∀ ∀ ($0 ⧀ σ $1 → (($0 ⧀ $1) ∨ ($0 == $1))).
Definition zero_minimal_sentence : pa_form := ∀ ¬ ($0 ⧀ zero).
Definition common_context : list pa_form :=
  [multiplication_commutative_sentence; successor_split_sentence; zero_minimal_sentence]
    ++ divisor_context.
Definition has_common_context (G : list pa_form) : Prop :=
  forall phi, List.In phi common_context -> List.In phi G.
Lemma common_proof phi : common_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD.
  eapply paeq_modus_ponens with (phi := multiplication_commutative_sentence);
    [|exact PAMultiplicationComm238.mult_commutative].
  eapply paeq_modus_ponens with (phi := successor_split_sentence);
    [|exact PAPowerExtension238.order_successor_split].
  eapply paeq_modus_ponens with (phi := zero_minimal_sentence);
    [|exact PAOrder238.zero_minimal].
  apply divisor_proof, II, II, II. exact HD.
Qed.
Lemma common_context_self : has_common_context common_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_common_cons G phi : has_common_context G ->
  has_common_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma common_has_divisor G : has_common_context G -> has_divisor_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold common_context.
  apply List.in_app_iff. now right.
Qed.
Lemma common_has_product G : has_common_context G -> has_product_context G.
Proof. intros HG. apply divisor_has_product, common_has_divisor. exact HG. Qed.

Lemma multiplication_commutative_at G a b : has_common_context G ->
  G ⊢C (a ⊗ b == b ⊗ a).
Proof.
  intros HG. change (G ⊢C ($0 ⊗ $1 == $1 ⊗ $0)[a .: b .: var]).
  apply (subst_forall_prv (phi := $0 ⊗ $1 == $1 ⊗ $0) (N := 2)).
  - change (G ⊢C multiplication_commutative_sentence). apply Ctx, HG.
    unfold common_context. now left.
  - solve_bounds.
Qed.
Lemma successor_split_at G i n : has_common_context G ->
  G ⊢C (i ⧀ σ n) -> G ⊢C ((i ⧀ n) ∨ (i == n)).
Proof.
  intros HG HI. assert (HH : G ⊢C successor_split_sentence).
  { apply Ctx, HG. unfold common_context. right. now left. }
  assert (HB : bounded 2 ($0 ⧀ σ $1 → (($0 ⧀ $1) ∨ ($0 == $1)))).
  { unfold PAlt. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := $0 ⧀ σ $1 → (($0 ⧀ $1) ∨ ($0 == $1))) (N := 2)
    HH HB (i .: n .: var)) as HK.
  change (G ⊢C (PAlt $0 (σ $1))[i .: n .: var] →
    ((PAlt $0 $1)[i .: n .: var] ∨ (i == n))) in HK.
  rewrite !PAlt_subst in HK. exact (IE HK HI).
Qed.

Definition multiple_rows (n C : pa_term) : pa_form :=
  ∀ ($0 ⧀ n`[↑] → divides (σ $0) C`[↑]).
Definition common_multiple (n C : pa_term) : pa_form :=
  (zero ⧀ C) ∧ multiple_rows n C.
Definition common_multiple_exists (n : pa_term) : pa_form :=
  ∃ common_multiple n`[↑] $0.
Lemma multiple_rows_subst n C rho :
  (multiple_rows n C)[rho] = multiple_rows n`[rho] C`[rho].
Proof.
  unfold multiple_rows. cbn [subst_form]. rewrite PAlt_subst, divides_subst.
  now rewrite !up_term.
Qed.
Lemma common_multiple_subst n C rho :
  (common_multiple n C)[rho] = common_multiple n`[rho] C`[rho].
Proof.
  unfold common_multiple. cbn [subst_form]. rewrite PAlt_subst, multiple_rows_subst.
  reflexivity.
Qed.
Lemma common_multiple_exists_subst n rho :
  (common_multiple_exists n)[rho] = common_multiple_exists n`[rho].
Proof.
  unfold common_multiple_exists. cbn [subst_form]. rewrite common_multiple_subst.
  now rewrite !up_term.
Qed.
Lemma multiple_rows_at G n C i : G ⊢C multiple_rows n C ->
  G ⊢C (i ⧀ n) -> G ⊢C divides (σ i) C.
Proof.
  intros HM HI. pose proof (AllE i HM) as HK.
  change (G ⊢C (PAlt $0 n`[↑])[i..] → (divides (σ $0) C`[↑])[i..]) in HK.
  rewrite PAlt_subst, divides_subst, !subst_term_shift in HK. exact (IE HK HI).
Qed.
Lemma multiple_rows_introduce G n C :
  (forall i, G ⊢C (i ⧀ n → divides (σ i) C)) -> G ⊢C multiple_rows n C.
Proof.
  intros H. unfold multiple_rows. apply AllI_named. intros i.
  change (G ⊢C (PAlt $0 n`[↑])[i..] → (divides (σ $0) C`[↑])[i..]).
  rewrite PAlt_subst, divides_subst, !subst_term_shift. exact (H i).
Qed.
Lemma common_multiple_exists_intro G n C :
  G ⊢C common_multiple n C -> G ⊢C common_multiple_exists n.
Proof.
  intros H. unfold common_multiple_exists. apply (ExI C).
  rewrite common_multiple_subst, !subst_term_shift. exact H.
Qed.
Lemma common_multiple_exists_eliminate G n (psi : pa_form) :
  G ⊢C common_multiple_exists n ->
  (forall C, (List.cons (common_multiple n C) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. unfold common_multiple_exists in HX.
  eapply ExE_named; [exact HX|]. intros C.
  rewrite common_multiple_subst, !subst_term_shift.
  change ((List.cons (common_multiple n C) G) ⊢C psi). exact (H C).
Qed.

Lemma common_multiple_forward G n C : has_common_context G ->
  G ⊢C common_multiple n C -> G ⊢C common_multiple (σ n) (C ⊗ σ n).
Proof.
  intros HG HM. unfold common_multiple. apply CI.
  - apply (positive_product G C (σ n) (common_has_product G HG));
      [exact (CE1 HM)|apply zero_below_successor, common_has_product; exact HG].
  - apply multiple_rows_introduce. intros i. apply II.
    set (D := List.cons (i ⧀ σ n) G).
    change (D ⊢C divides (σ i) (C ⊗ σ n)).
    assert (HD : has_common_context D).
    { unfold D. apply has_common_cons. exact HG. }
    assert (HI : D ⊢C (i ⧀ σ n)).
    { apply Ctx. unfold D. now left. }
    pose proof (successor_split_at D i n HD HI) as Hsplit.
    pose proof (weaken_head G (multiple_rows n C) (i ⧀ σ n) (CE2 HM)) as Hrows.
    eapply DE; [exact Hsplit| |].
    + set (E := List.cons (i ⧀ n) D).
      change (E ⊢C divides (σ i) (C ⊗ σ n)).
      assert (HE : has_common_context E).
      { unfold E. apply has_common_cons. exact HD. }
      assert (HIE : E ⊢C (i ⧀ n)).
      { apply Ctx. unfold E. now left. }
      pose proof (weaken_head D (multiple_rows n C) (i ⧀ n) Hrows) as HrowsE.
      apply (divisor_right_product E (σ i) C (σ n) (common_has_divisor E HE)).
      exact (multiple_rows_at E n C i HrowsE HIE).
    + set (E := List.cons (i == n) D).
      change (E ⊢C divides (σ i) (C ⊗ σ n)).
      assert (HE : has_common_context E).
      { unfold E. apply has_common_cons. exact HD. }
      pose proof (product_has_equality E (common_has_product E HE)) as HEQ.
      assert (HIE : E ⊢C (i == n)).
      { apply Ctx. unfold E. now left. }
      pose proof (equality_symmetry E i n HEQ HIE) as Hni.
      assert (Hnew : E ⊢C divides (σ n) (C ⊗ σ n)).
      { apply (divides_introduce E (σ n) (C ⊗ σ n) C).
        exact (multiplication_commutative_at E C (σ n) HE). }
      pose proof (formula_substitutivity E (divides (σ $0) (C ⊗ σ n)`[↑])
        n i HEQ Hni) as Htransfer.
      rewrite !divides_subst, !subst_term_shift in Htransfer.
      exact (IE (CE1 Htransfer) Hnew).
Qed.

Definition common_multiple_formula : pa_form := common_multiple_exists $0.
Lemma common_multiple_base : paeq_derivable common_multiple_formula[zero..].
Proof.
  unfold common_multiple_formula. rewrite common_multiple_exists_subst.
  change (paeq_derivable (common_multiple_exists zero)).
  apply common_proof, (common_multiple_exists_intro common_context zero (σ zero)).
  unfold common_multiple. apply CI.
  - apply zero_below_successor, common_has_product. exact common_context_self.
  - apply multiple_rows_introduce. intros i. apply II.
    set (D := List.cons (i ⧀ zero) common_context).
    assert (HZ : D ⊢C zero_minimal_sentence).
    { apply Ctx. unfold D, common_context. right. right. right. now left. }
    pose proof (AllE i HZ) as HK.
    change (D ⊢C ¬ ((PAlt $0 zero)[i..])) in HK.
    rewrite PAlt_subst in HK. apply Exp. eapply IE; [exact HK|].
    apply Ctx. unfold D. now left.
Qed.
Lemma common_multiple_step : paeq_derivable
  (∀ (common_multiple_formula → common_multiple_formula[σ $0 .: S >> var])).
Proof.
  unfold common_multiple_formula. rewrite common_multiple_exists_subst.
  change (paeq_derivable (∀ (common_multiple_exists $0 → common_multiple_exists (σ $0)))).
  apply paeq_generalize, common_proof, II.
  set (G := List.cons (common_multiple_exists $0) common_context).
  assert (HX : G ⊢C common_multiple_exists $0).
  { apply Ctx. unfold G. now left. }
  eapply common_multiple_exists_eliminate; [exact HX|]. intros C.
  set (D := List.cons (common_multiple $0 C) G).
  change (D ⊢C common_multiple_exists (σ $0)).
  assert (HD : has_common_context D).
  { unfold D, G. apply has_common_cons, has_common_cons. exact common_context_self. }
  assert (HM : D ⊢C common_multiple $0 C).
  { apply Ctx. unfold D. now left. }
  apply (common_multiple_exists_intro D (σ $0) (C ⊗ σ $0)).
  exact (common_multiple_forward D $0 C HD HM).
Qed.
Theorem positive_common_multiple : paeq_derivable (∀ common_multiple_exists $0).
Proof.
  apply (paeq_induction_rule common_multiple_formula).
  - exact common_multiple_base.
  - exact common_multiple_step.
Qed.

Definition large_common_multiple (n L C : pa_term) : pa_form :=
  common_multiple n C ∧ (L ⧀ C).
Definition large_common_multiple_exists (n L : pa_term) : pa_form :=
  ∃ large_common_multiple n`[↑] L`[↑] $0.
Lemma large_common_multiple_subst n L C rho :
  (large_common_multiple n L C)[rho] =
  large_common_multiple n`[rho] L`[rho] C`[rho].
Proof.
  unfold large_common_multiple. cbn [subst_form].
  rewrite common_multiple_subst, PAlt_subst. reflexivity.
Qed.
Lemma large_common_multiple_exists_intro G n L C :
  G ⊢C large_common_multiple n L C -> G ⊢C large_common_multiple_exists n L.
Proof.
  intros H. unfold large_common_multiple_exists. apply (ExI C).
  rewrite large_common_multiple_subst, !subst_term_shift. exact H.
Qed.
Lemma scale_common_multiple G n L C : has_common_context G ->
  G ⊢C common_multiple n C ->
  G ⊢C large_common_multiple n L (C ⊗ σ L).
Proof.
  intros HG HM. unfold large_common_multiple. apply CI.
  - unfold common_multiple. apply CI.
    + apply (positive_product G C (σ L) (common_has_product G HG));
        [exact (CE1 HM)|apply zero_below_successor, common_has_product; exact HG].
    + apply multiple_rows_introduce. intros i. apply II.
      set (D := List.cons (i ⧀ n) G).
      change (D ⊢C divides (σ i) (C ⊗ σ L)).
      assert (HD : has_common_context D).
      { unfold D. apply has_common_cons. exact HG. }
      assert (HI : D ⊢C (i ⧀ n)).
      { apply Ctx. unfold D. now left. }
      pose proof (weaken_head G (multiple_rows n C) (i ⧀ n) (CE2 HM)) as Hrows.
      apply (divisor_right_product D (σ i) C (σ L) (common_has_divisor D HD)).
      exact (multiple_rows_at D n C i Hrows HI).
  - exact (positive_product_upper G C L (common_has_product G HG) (CE1 HM)).
Qed.

Definition positive_common_multiple_sentence : pa_form := ∀ common_multiple_exists $0.
Definition large_context : list pa_form :=
  List.cons positive_common_multiple_sentence common_context.
Lemma large_proof phi : large_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := positive_common_multiple_sentence).
  - apply common_proof, II. exact HD.
  - exact positive_common_multiple.
Qed.
Theorem arbitrarily_large_common_multiple :
  paeq_derivable (∀ ∀ large_common_multiple_exists $0 $1).
Proof.
  apply paeq_generalize, paeq_generalize, large_proof.
  assert (HAll : large_context ⊢C positive_common_multiple_sentence).
  { apply Ctx. unfold large_context. now left. }
  pose proof (AllE $0 HAll) as HX.
  change (large_context ⊢C (common_multiple_exists $0)[$0..]) in HX.
  rewrite common_multiple_exists_subst in HX.
  eapply common_multiple_exists_eliminate; [exact HX|]. intros C.
  set (D := List.cons (common_multiple $0 C) large_context).
  change (D ⊢C large_common_multiple_exists $0 $1).
  assert (HD : has_common_context D).
  { intros phi Hphi. unfold D, large_context. right. now right. }
  assert (HM : D ⊢C common_multiple $0 C).
  { apply Ctx. unfold D. now left. }
  apply (large_common_multiple_exists_intro D $0 $1 (C ⊗ σ $1)).
  exact (scale_common_multiple D $0 $1 C HD HM).
Qed.

End PACommonMultiple238.

Print Assumptions PACommonMultiple238.common_proof.
Print Assumptions PACommonMultiple238.positive_common_multiple.
Print Assumptions PACommonMultiple238.arbitrarily_large_common_multiple.
