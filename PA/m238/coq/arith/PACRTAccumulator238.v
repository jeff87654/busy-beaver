(* Original finite ordinary-PA bounded CRT accumulator.
   A state contains literal positive product and code witnesses.  The
   product begins at one and is enlarged by one modulus at each step;
   no variable-length product or sequence-existence axiom is assumed. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAAddition238 PAEqCongruence238 PAOrderBounds238
  PASemiring238 PAMultiplicationComm238 PAModuliInverse238 PACommonMultiple238
  PACRTMerge238 PAQuotient238 CompactInPA238 PAPowerExtension238
  PABetaAppendGraph238 PABetaIndexArithmetic238 PAPowerTrace238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrderBounds238
  PASemiring238 PAMultiplicationComm238 PAModuliInverse238 PACommonMultiple238
  PACRTMerge238 PAQuotient238 CompactInPA238 PAPowerTrace238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PACRTAccumulator238.

Definition zero_minimal_sentence : pa_form := ∀ ¬ ($0 ⧀ zero).
Definition successor_split_sentence : pa_form :=
  ∀ ∀ ($0 ⧀ σ $1 → (($0 ⧀ $1) ∨ ($0 == $1))).
Definition accumulator_context : list pa_form :=
  [zero_minimal_sentence; successor_split_sentence; ax_succ_inj] ++ pairwise_context.
Definition has_accumulator_context (G : list pa_form) : Prop :=
  forall phi, List.In phi accumulator_context -> List.In phi G.
Lemma accumulator_proof phi : accumulator_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD.
  eapply paeq_modus_ponens with (phi := zero_minimal_sentence);
    [|exact PAOrder238.zero_minimal].
  eapply paeq_modus_ponens with (phi := successor_split_sentence);
    [|exact PAPowerExtension238.order_successor_split].
  eapply paeq_modus_ponens with (phi := ax_succ_inj);
    [|apply paeq_axiom, PAeq_inj].
  apply pairwise_proof, II, II, II. exact HD.
Qed.
Lemma accumulator_context_self : has_accumulator_context accumulator_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_accumulator_cons G phi : has_accumulator_context G ->
  has_accumulator_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma accumulator_has_pairwise G : has_accumulator_context G -> has_pairwise_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold accumulator_context.
  apply List.in_app_iff. now right.
Qed.
Lemma accumulator_has_inverse G : has_accumulator_context G -> has_inverse_context G.
Proof. intros HG. apply pairwise_has_inverse, accumulator_has_pairwise. exact HG. Qed.
Lemma zero_minimal_at G i : has_accumulator_context G -> G ⊢C ¬ (i ⧀ zero).
Proof.
  intros HG. assert (HH : G ⊢C zero_minimal_sentence).
  { apply Ctx, HG. unfold accumulator_context. now left. }
  pose proof (AllE i HH) as HK.
  change (G ⊢C ¬ ((PAlt $0 zero)[i..])) in HK.
  rewrite PAlt_subst in HK. exact HK.
Qed.

Definition prefix_divisors (C j P : pa_term) : pa_form :=
  ∀ ($0 ⧀ j`[↑] → divides (beta_modulus C`[↑] $0) P`[↑]).
Definition desired_rows (b c n r C j z : pa_term) : pa_form :=
  ∀ ($0 ⧀ j`[↑] →
    ∀ (PAPowerExtension238.append_graph b`[↑]`[↑] c`[↑]`[↑]
         n`[↑]`[↑] r`[↑]`[↑] $1 $0 → beta z`[↑]`[↑] C`[↑]`[↑] $1 $0)).
Definition future_inverses (C k j P : pa_term) : pa_form :=
  ∀ (j`[↑] ⧀= $0 → $0 ⧀= k`[↑] → inverse_exists P`[↑] (beta_modulus C`[↑] $0)).
Definition accumulator_state (b c n r C k j P z : pa_term) : pa_form :=
  (zero ⧀ P) ∧ (prefix_divisors C j P ∧
    (desired_rows b c n r C j z ∧ future_inverses C k j P)).
Definition accumulator_exists (b c n r C k j : pa_term) : pa_form :=
  ∃ ∃ accumulator_state b`[↑]`[↑] c`[↑]`[↑] n`[↑]`[↑] r`[↑]`[↑]
    C`[↑]`[↑] k`[↑]`[↑] j`[↑]`[↑] $1 $0.

Lemma append_graph_subst b c n r i v rho :
  (PAPowerExtension238.append_graph b c n r i v)[rho] =
  PAPowerExtension238.append_graph b`[rho] c`[rho] n`[rho] r`[rho] i`[rho] v`[rho].
Proof.
  unfold PAPowerExtension238.append_graph. cbn [subst_form].
  rewrite PAlt_subst, beta_subst. reflexivity.
Qed.
Lemma prefix_divisors_subst C j P rho :
  (prefix_divisors C j P)[rho] = prefix_divisors C`[rho] j`[rho] P`[rho].
Proof.
  unfold prefix_divisors. cbn [subst_form].
  rewrite PAlt_subst, divides_subst, beta_modulus_subst. now rewrite !up_term.
Qed.
Lemma desired_rows_subst b c n r C j z rho :
  (desired_rows b c n r C j z)[rho] =
  desired_rows b`[rho] c`[rho] n`[rho] r`[rho] C`[rho] j`[rho] z`[rho].
Proof.
  unfold desired_rows. cbn [subst_form]. rewrite PAlt_subst, append_graph_subst, beta_subst.
  now rewrite !up_term.
Qed.
Lemma future_inverses_subst C k j P rho :
  (future_inverses C k j P)[rho] =
  future_inverses C`[rho] k`[rho] j`[rho] P`[rho].
Proof.
  unfold future_inverses. cbn [subst_form].
  rewrite !PAle_subst, inverse_exists_subst, beta_modulus_subst. now rewrite !up_term.
Qed.
Lemma accumulator_state_subst b c n r C k j P z rho :
  (accumulator_state b c n r C k j P z)[rho] =
  accumulator_state b`[rho] c`[rho] n`[rho] r`[rho] C`[rho] k`[rho]
    j`[rho] P`[rho] z`[rho].
Proof.
  unfold accumulator_state. cbn [subst_form]. rewrite PAlt_subst, prefix_divisors_subst,
    desired_rows_subst, future_inverses_subst. reflexivity.
Qed.
Lemma accumulator_exists_subst b c n r C k j rho :
  (accumulator_exists b c n r C k j)[rho] =
  accumulator_exists b`[rho] c`[rho] n`[rho] r`[rho] C`[rho] k`[rho] j`[rho].
Proof.
  unfold accumulator_exists. cbn [subst_form]. rewrite accumulator_state_subst.
  now rewrite !up_term.
Qed.

Lemma prefix_divisors_intro G C j P :
  (forall i, G ⊢C (i ⧀ j → divides (beta_modulus C i) P)) ->
  G ⊢C prefix_divisors C j P.
Proof.
  intros H. unfold prefix_divisors. apply AllI_named. intros i.
  change (G ⊢C (PAlt $0 j`[↑])[i..] →
    (divides (beta_modulus C`[↑] $0) P`[↑])[i..]).
  rewrite PAlt_subst, divides_subst, beta_modulus_subst, !subst_term_shift. exact (H i).
Qed.
Lemma desired_rows_intro G b c n r C j z :
  (forall i v, G ⊢C (i ⧀ j →
    PAPowerExtension238.append_graph b c n r i v → beta z C i v)) ->
  G ⊢C desired_rows b c n r C j z.
Proof.
  intros H. unfold desired_rows. apply AllI_named. intros i.
  cbn [subst_form]. rewrite PAlt_subst, append_graph_subst, beta_subst.
  rewrite !up_term, !subst_term_shift.
  change (G ⊢C (i ⧀ j → ∀ (PAPowerExtension238.append_graph b`[↑] c`[↑]
    n`[↑] r`[↑] i`[↑] $0 → beta z`[↑] C`[↑] i`[↑] $0))).
  apply II, AllI_named. intros v.
  change ((List.cons (i ⧀ j) G) ⊢C
    (PAPowerExtension238.append_graph b`[↑] c`[↑] n`[↑] r`[↑] i`[↑] $0)[v..] →
    (beta z`[↑] C`[↑] i`[↑] $0)[v..]).
  rewrite append_graph_subst, beta_subst, !subst_term_shift.
  eapply IE; [apply weaken_head; exact (H i v)|]. apply Ctx. now left.
Qed.
Lemma future_inverses_intro G C k j P :
  (forall t, G ⊢C (j ⧀= t → t ⧀= k → inverse_exists P (beta_modulus C t))) ->
  G ⊢C future_inverses C k j P.
Proof.
  intros H. unfold future_inverses. apply AllI_named. intros t.
  change (G ⊢C (PAle j`[↑] $0)[t..] → (PAle $0 k`[↑])[t..] →
    (inverse_exists P`[↑] (beta_modulus C`[↑] $0))[t..]).
  rewrite !PAle_subst, inverse_exists_subst, beta_modulus_subst, !subst_term_shift.
  exact (H t).
Qed.
Lemma accumulator_exists_intro G b c n r C k j P z :
  G ⊢C accumulator_state b c n r C k j P z ->
  G ⊢C accumulator_exists b c n r C k j.
Proof.
  intros H. unfold accumulator_exists. apply (ExI P).
  cbn [subst_form]. rewrite accumulator_state_subst, !up_term, !subst_term_shift.
  change (G ⊢C ∃ accumulator_state b`[↑] c`[↑] n`[↑] r`[↑]
    C`[↑] k`[↑] j`[↑] P`[↑] $0).
  apply (ExI z). rewrite accumulator_state_subst, !subst_term_shift. exact H.
Qed.

Lemma accumulator_exists_eliminate G b c n r C k j (psi : pa_form) :
  G ⊢C accumulator_exists b c n r C k j ->
  (forall P z, (List.cons (accumulator_state b c n r C k j P z) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. unfold accumulator_exists in HX.
  eapply ExE_named; [exact HX|]. intros P.
  cbn [subst_form]. rewrite accumulator_state_subst, !up_term, !subst_term_shift.
  set (D := List.cons (∃ accumulator_state b`[↑] c`[↑] n`[↑] r`[↑]
    C`[↑] k`[↑] j`[↑] P`[↑] $0) G).
  assert (HY : D ⊢C ∃ accumulator_state b`[↑] c`[↑] n`[↑] r`[↑]
    C`[↑] k`[↑] j`[↑] P`[↑] $0).
  { apply Ctx. unfold D. now left. }
  eapply ExE_named; [exact HY|]. intros z.
  rewrite accumulator_state_subst, !subst_term_shift.
  change ((List.cons (accumulator_state b c n r C k j P z) D) ⊢C psi).
  eapply Weak; [exact (H P z)|]. intros phi Hphi.
  destruct Hphi as [<-|Hphi]; [now left|right; unfold D; now right].
Qed.
Lemma inverse_exists_eliminate G A B (psi : pa_form) : G ⊢C inverse_exists A B ->
  (forall x y, (List.cons (inverse_pair A B x y) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. unfold inverse_exists in HX.
  eapply ExE_named; [exact HX|]. intros x.
  cbn [subst_form]. rewrite inverse_pair_subst, !up_term, !subst_term_shift.
  set (D := List.cons (∃ inverse_pair A`[↑] B`[↑] x`[↑] $0) G).
  assert (HY : D ⊢C ∃ inverse_pair A`[↑] B`[↑] x`[↑] $0).
  { apply Ctx. unfold D. now left. }
  eapply ExE_named; [exact HY|]. intros y. rewrite inverse_pair_subst, !subst_term_shift.
  change ((List.cons (inverse_pair A B x y) D) ⊢C psi).
  eapply Weak; [exact (H x y)|]. intros phi Hphi.
  destruct Hphi as [<-|Hphi]; [now left|right; unfold D; now right].
Qed.
Lemma merge_exists_eliminate G A P C i v (psi : pa_form) :
  G ⊢C merge_exists A P C i v ->
  (forall z, (List.cons (merge_result A z P C i v) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. unfold merge_exists in HX. eapply ExE_named; [exact HX|]. intros z.
  rewrite merge_result_subst, !subst_term_shift.
  change ((List.cons (merge_result A z P C i v) G) ⊢C psi). exact (H z).
Qed.
Lemma inverse_product_exists G P Q m : has_inverse_context G ->
  G ⊢C inverse_exists P m -> G ⊢C inverse_exists Q m ->
  G ⊢C inverse_exists (P ⊗ Q) m.
Proof.
  intros HG HP HQ. eapply inverse_exists_eliminate; [exact HP|]. intros x y.
  set (D := List.cons (inverse_pair P m x y) G).
  pose proof (weaken_head G (inverse_exists Q m) (inverse_pair P m x y) HQ) as HQD.
  eapply inverse_exists_eliminate; [exact HQD|]. intros X Y.
  set (E := List.cons (inverse_pair Q m X Y) D).
  assert (HE : has_inverse_context E).
  { unfold E, D. apply has_inverse_cons, has_inverse_cons. exact HG. }
  assert (Hleft : E ⊢C inverse_pair P m x y).
  { apply Ctx. unfold E, D. right. now left. }
  assert (Hright : E ⊢C inverse_pair Q m X Y).
  { apply Ctx. unfold E. now left. }
  apply (inverse_exists_intro E (P ⊗ Q) m (x ⊗ X) ((((y ⊗ Y) ⊗ m) ⊕ y) ⊕ Y)).
  exact (inverse_product_at E x X P Q y Y m HE Hleft Hright).
Qed.

Lemma prefix_divisors_at G C j P i : G ⊢C prefix_divisors C j P ->
  G ⊢C (i ⧀ j) -> G ⊢C divides (beta_modulus C i) P.
Proof.
  intros HD HI. pose proof (AllE i HD) as HK.
  change (G ⊢C (PAlt $0 j`[↑])[i..] →
    (divides (beta_modulus C`[↑] $0) P`[↑])[i..]) in HK.
  rewrite PAlt_subst, divides_subst, beta_modulus_subst, !subst_term_shift in HK.
  exact (IE HK HI).
Qed.
Lemma append_graph_term_congruence (b b' c c' n n' r r' i i' v v' : pa_term) :
  b = b' -> c = c' -> n = n' -> r = r' -> i = i' -> v = v' ->
  PAPowerExtension238.append_graph b c n r i v =
  PAPowerExtension238.append_graph b' c' n' r' i' v'.
Proof. intros -> -> -> -> -> ->. reflexivity. Qed.
Lemma beta_term_congruence (b b' c c' i i' v v' : pa_term) :
  b = b' -> c = c' -> i = i' -> v = v' -> beta b c i v = beta b' c' i' v'.
Proof. intros -> -> -> ->. reflexivity. Qed.
Lemma desired_rows_at G b c n r C j z i v : G ⊢C desired_rows b c n r C j z ->
  G ⊢C (i ⧀ j) -> G ⊢C PAPowerExtension238.append_graph b c n r i v ->
  G ⊢C beta z C i v.
Proof.
  intros HR HI HQ. pose proof (AllE i HR) as HH.
  cbn [subst_form] in HH. rewrite PAlt_subst, append_graph_subst, beta_subst in HH.
  rewrite !up_term, !subst_term_shift in HH.
  change (G ⊢C (i ⧀ j → ∀ (PAPowerExtension238.append_graph b`[↑] c`[↑]
    n`[↑] r`[↑] i`[↑] $0 → beta z`[↑] C`[↑] i`[↑] $0))) in HH.
  pose proof (AllE v (IE HH HI)) as HK.
  change (G ⊢C
    (PAPowerExtension238.append_graph b`[↑] c`[↑] n`[↑] r`[↑] i`[↑] $0)[v..] →
    (beta z`[↑] C`[↑] i`[↑] $0)[v..]) in HK.
  assert (Hgraph :
    (PAPowerExtension238.append_graph b`[↑] c`[↑] n`[↑] r`[↑] i`[↑] $0)[v..] =
    PAPowerExtension238.append_graph b c n r i v).
  { exact (eq_trans
      (append_graph_subst b`[↑] c`[↑] n`[↑] r`[↑] i`[↑] $0 (v..))
      (append_graph_term_congruence b`[↑]`[v..] b c`[↑]`[v..] c
        n`[↑]`[v..] n r`[↑]`[v..] r i`[↑]`[v..] i $0`[v..] v
        (@subst_term_shift PA_funcs_signature b v)
        (@subst_term_shift PA_funcs_signature c v)
        (@subst_term_shift PA_funcs_signature n v)
        (@subst_term_shift PA_funcs_signature r v)
        (@subst_term_shift PA_funcs_signature i v) eq_refl)). }
  assert (Hbeta : (beta z`[↑] C`[↑] i`[↑] $0)[v..] = beta z C i v).
  { exact (eq_trans (beta_subst z`[↑] C`[↑] i`[↑] $0 (v..))
      (beta_term_congruence z`[↑]`[v..] z C`[↑]`[v..] C i`[↑]`[v..] i $0`[v..] v
        (@subst_term_shift PA_funcs_signature z v)
        (@subst_term_shift PA_funcs_signature C v)
        (@subst_term_shift PA_funcs_signature i v) eq_refl)). }
  rewrite Hgraph, Hbeta in HK. exact (IE HK HQ).
Qed.
Lemma future_inverses_at G C k j P t : G ⊢C future_inverses C k j P ->
  G ⊢C (j ⧀= t) -> G ⊢C (t ⧀= k) -> G ⊢C inverse_exists P (beta_modulus C t).
Proof.
  intros HF Hjt Htk. pose proof (AllE t HF) as HK.
  change (G ⊢C (PAle j`[↑] $0)[t..] → (PAle $0 k`[↑])[t..] →
    (inverse_exists P`[↑] (beta_modulus C`[↑] $0))[t..]) in HK.
  rewrite !PAle_subst, inverse_exists_subst, beta_modulus_subst, !subst_term_shift in HK.
  exact (IE (IE HK Hjt) Htk).
Qed.
Lemma merged_row_at G A z P C i v : G ⊢C preserved_beta_rows A z P C ->
  G ⊢C divides (beta_modulus C i) P -> G ⊢C beta A C i v -> G ⊢C beta z C i v.
Proof.
  intros HM HD HB. pose proof (AllE i HM) as HH.
  cbn [subst_form] in HH. rewrite preservation_row_subst, !up_term, !subst_term_shift in HH.
  change (G ⊢C ∀ preservation_row A`[↑] z`[↑] P`[↑] C`[↑] i`[↑] $0) in HH.
  pose proof (AllE v HH) as HK. rewrite preservation_row_subst, !subst_term_shift in HK.
  exact (IE (IE HK HD) HB).
Qed.

Lemma weak_reflexive G j : has_inverse_context G -> G ⊢C (j ⧀= j).
Proof.
  intros HG. apply (weak_order_witness G j j zero).
  exact (inverse_symmetry G (j ⊕ zero) j HG (inverse_right_zero G j HG)).
Qed.
Lemma weak_lower_predecessor G j t : has_inverse_context G ->
  G ⊢C (σ j ⧀= t) -> G ⊢C (j ⧀= t).
Proof.
  intros HG HW. unfold PAle in HW. eapply ExE_named; [exact HW|]. intros h.
  change ((List.cons (t`[↑]`[h..] == (σ j)`[↑]`[h..] ⊕ h) G) ⊢C (j ⧀= t)).
  rewrite !subst_term_shift. set (D := List.cons (t == σ j ⊕ h) G).
  assert (HD : has_inverse_context D).
  { unfold D. apply has_inverse_cons. exact HG. }
  assert (HT : D ⊢C (t == σ j ⊕ h)).
  { apply Ctx. unfold D. now left. }
  pose proof (inverse_has_product D HD) as HP.
  pose proof (PAOrder238.add_rec_instance D j h (HP ax_add_rec product_add_rec)) as Hfirst.
  pose proof (right_successor_instance D j h
    (HP right_successor_sentence bounds_right_successor)) as Hsecond.
  pose proof (inverse_symmetry D (j ⊕ σ h) (σ (j ⊕ h)) HD Hsecond) as Hback.
  pose proof (inverse_transitivity D t (σ j ⊕ h) (σ (j ⊕ h)) HD HT Hfirst) as Hfront.
  apply (weak_order_witness D j t (σ h)).
  exact (inverse_transitivity D t (σ (j ⊕ h)) (j ⊕ σ h) HD Hfront Hback).
Qed.
Lemma weak_successor_lower_strict G j t : G ⊢C (σ j ⧀= t) -> G ⊢C (j ⧀ t).
Proof.
  intros HW. unfold PAle in HW. eapply ExE_named; [exact HW|]. intros h.
  change ((List.cons (t`[↑]`[h..] == (σ j)`[↑]`[h..] ⊕ h) G) ⊢C (j ⧀ t)).
  rewrite !subst_term_shift. apply (strict_order_witness _ j t h), Ctx. now left.
Qed.
Lemma weak_upper_successor G j k : has_inverse_context G ->
  G ⊢C (j ⧀= k) -> G ⊢C (j ⧀ σ k).
Proof.
  intros HG HW. unfold PAle in HW. eapply ExE_named; [exact HW|]. intros h.
  change ((List.cons (k`[↑]`[h..] == j`[↑]`[h..] ⊕ h) G) ⊢C (j ⧀ σ k)).
  rewrite !subst_term_shift. set (D := List.cons (k == j ⊕ h) G).
  assert (HD : has_inverse_context D).
  { unfold D. apply has_inverse_cons. exact HG. }
  assert (HK : D ⊢C (k == j ⊕ h)).
  { apply Ctx. unfold D. now left. }
  pose proof (IE (successor_instance D k (j ⊕ h) (inverse_equality D HD)) HK) as Hfirst.
  pose proof (PAOrder238.add_rec_instance D j h
    (inverse_has_product D HD ax_add_rec product_add_rec)) as Hsecond.
  pose proof (inverse_symmetry D (σ j ⊕ h) (σ (j ⊕ h)) HD Hsecond) as Hback.
  apply (strict_order_witness D j (σ k) h).
  exact (inverse_transitivity D (σ k) (σ (j ⊕ h)) (σ j ⊕ h) HD Hfirst Hback).
Qed.

Lemma accumulator_has_common G : has_accumulator_context G -> has_common_context G.
Proof.
  intros HG phi Hphi. unfold common_context in Hphi.
  destruct Hphi as [<-|[<-|[<-|Hphi]]].
  - exact (inverse_has_commutative G (accumulator_has_inverse G HG)
      mult_commutativity_sentence commutative_multiplication).
  - apply HG. unfold accumulator_context. right. now left.
  - apply HG. unfold accumulator_context. now left.
  - exact (inverse_has_divisor G (accumulator_has_inverse G HG) phi Hphi).
Qed.
Lemma successor_weak_cancel G j k : has_accumulator_context G ->
  G ⊢C (σ j ⧀= σ k) -> G ⊢C (j ⧀= k).
Proof.
  intros HG HW. unfold PAle in HW. eapply ExE_named; [exact HW|]. intros h.
  change ((List.cons ((σ k)`[↑]`[h..] == (σ j)`[↑]`[h..] ⊕ h) G) ⊢C (j ⧀= k)).
  rewrite !subst_term_shift. set (D := List.cons (σ k == σ j ⊕ h) G).
  assert (HD : has_accumulator_context D).
  { unfold D. apply has_accumulator_cons. exact HG. }
  pose proof (accumulator_has_inverse D HD) as HI.
  assert (HK : D ⊢C (σ k == σ j ⊕ h)).
  { apply Ctx. unfold D. now left. }
  pose proof (PAOrder238.add_rec_instance D j h
    (inverse_has_product D HI ax_add_rec product_add_rec)) as HA.
  pose proof (inverse_transitivity D (σ k) (σ j ⊕ h) (σ (j ⊕ h)) HI HK HA) as HS.
  assert (Hinj : List.In ax_succ_inj D).
  { apply HD. unfold accumulator_context. right. right. now left. }
  apply (weak_order_witness D j k h).
  exact (IE (PAOrder238.succ_inj_instance D k (j ⊕ h) Hinj) HS).
Qed.

Definition append_graph_bound_sentence : pa_form := ∀ ∀ ∀ ∀ ∀ ∀
  (PAPowerExtension238.append_graph $0 $1 $2 $3 $4 $5 → $5 ⧀= ($0 ⊕ $3)).
Definition coding_context : list pa_form :=
  [PABetaAppendGraph238.append_graph_total_sentence;
   PABetaAppendGraph238.append_graph_unique_sentence; append_graph_bound_sentence]
    ++ accumulator_context.
Definition has_coding_context (G : list pa_form) : Prop :=
  forall phi, List.In phi coding_context -> List.In phi G.
Lemma coding_proof phi : coding_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD.
  eapply paeq_modus_ponens with (phi := PABetaAppendGraph238.append_graph_total_sentence);
    [|exact PABetaAppendGraph238.append_graph_total].
  eapply paeq_modus_ponens with (phi := PABetaAppendGraph238.append_graph_unique_sentence);
    [|exact PABetaAppendGraph238.append_graph_unique].
  eapply paeq_modus_ponens with (phi := append_graph_bound_sentence);
    [|exact PAPowerExtension238.append_graph_bound].
  apply accumulator_proof, II, II, II. exact HD.
Qed.
Lemma coding_context_self : has_coding_context coding_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_coding_cons G phi : has_coding_context G -> has_coding_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma coding_has_accumulator G : has_coding_context G -> has_accumulator_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold coding_context. apply List.in_app_iff. now right.
Qed.
Lemma coding_has_inverse G : has_coding_context G -> has_inverse_context G.
Proof. intros HG. apply accumulator_has_inverse, coding_has_accumulator. exact HG. Qed.
Lemma coding_has_pairwise G : has_coding_context G -> has_pairwise_context G.
Proof. intros HG. apply accumulator_has_pairwise, coding_has_accumulator. exact HG. Qed.
Lemma coding_total G : has_coding_context G ->
  List.In PABetaAppendGraph238.append_graph_total_sentence G.
Proof. intros HG. apply HG. unfold coding_context. now left. Qed.
Lemma coding_unique G : has_coding_context G ->
  List.In PABetaAppendGraph238.append_graph_unique_sentence G.
Proof. intros HG. apply HG. unfold coding_context. right. now left. Qed.
Lemma coding_bound G : has_coding_context G -> List.In append_graph_bound_sentence G.
Proof. intros HG. apply HG. unfold coding_context. right. right. now left. Qed.
Lemma append_graph_bound_at G b c n r i v : has_coding_context G ->
  G ⊢C PAPowerExtension238.append_graph b c n r i v -> G ⊢C (v ⧀= (b ⊕ r)).
Proof.
  intros HG HQ. assert (HH : G ⊢C append_graph_bound_sentence).
  { apply Ctx. exact (coding_bound G HG). }
  assert (HB : bounded 6 (PAPowerExtension238.append_graph $0 $1 $2 $3 $4 $5 → $5 ⧀= ($0 ⊕ $3))).
  { unfold PAPowerExtension238.append_graph, beta, beta_modulus, PAlt, PAle. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := PAPowerExtension238.append_graph $0 $1 $2 $3 $4 $5 → $5 ⧀= ($0 ⊕ $3))
    (N := 6) HH HB (b .: c .: n .: r .: i .: v .: var)) as HK.
  change (G ⊢C (PAPowerExtension238.append_graph $0 $1 $2 $3 $4 $5)
    [b .: c .: n .: r .: i .: v .: var] →
    (PAle $5 ($0 ⊕ $3))[b .: c .: n .: r .: i .: v .: var]) in HK.
  rewrite append_graph_subst, PAle_subst in HK. exact (IE HK HQ).
Qed.

Lemma index_divisor_transport G C P i j : has_inverse_context G ->
  G ⊢C (i == j) -> G ⊢C divides (beta_modulus C i) P ->
  G ⊢C divides (beta_modulus C j) P.
Proof.
  intros HG Hij HD.
  pose proof (formula_substitutivity G (divides (beta_modulus C`[↑] $0) P`[↑])
    i j (inverse_equality G HG) Hij) as HK.
  rewrite !divides_subst, !beta_modulus_subst, !subst_term_shift in HK.
  exact (IE (CE1 HK) HD).
Qed.
Lemma endpoint_desired_row G b c n r C j z v i w : has_coding_context G ->
  G ⊢C (i == j) -> G ⊢C PAPowerExtension238.append_graph b c n r i w ->
  G ⊢C PAPowerExtension238.append_graph b c n r j v ->
  G ⊢C beta z C j v -> G ⊢C beta z C i w.
Proof.
  intros HG Hij HQi HQj HB. pose proof (coding_has_inverse G HG) as HI.
  pose proof (formula_substitutivity G
    (PAPowerExtension238.append_graph b`[↑] c`[↑] n`[↑] r`[↑] $0 w`[↑])
    i j (inverse_equality G HI) Hij) as Hgraph.
  rewrite !append_graph_subst, !subst_term_shift in Hgraph.
  pose proof (IE (CE1 Hgraph) HQi) as HQw.
  pose proof (PABetaAppendGraph238.append_graph_unique_at G b c n r j v w
    (coding_unique G HG) HQj HQw) as Hvw.
  pose proof (formula_substitutivity G (beta z`[↑] C`[↑] j`[↑] $0) v w
    (inverse_equality G HI) Hvw) as Hvalue.
  rewrite !beta_subst, !subst_term_shift in Hvalue.
  pose proof (IE (CE1 Hvalue) HB) as HBw.
  pose proof (inverse_symmetry G i j HI Hij) as Hji.
  exact (PAPowerExtension238.beta_index_transport G z C j i w
    (inverse_equality G HI) Hji HBw).
Qed.

Lemma merged_accumulator_state G b c n r C k j P z v znew : has_coding_context G ->
  G ⊢C common_multiple (σ k) C ->
  G ⊢C PAPowerExtension238.append_graph b c n r j v ->
  G ⊢C accumulator_state b c n r C k j P z ->
  G ⊢C merge_result z znew P C j v ->
  G ⊢C accumulator_state b c n r C k (σ j) (P ⊗ beta_modulus C j) znew.
Proof.
  intros HG HC HQ HS HM. pose proof (coding_has_inverse G HG) as HI.
  unfold accumulator_state. apply CI.
  - apply (positive_product G P (beta_modulus C j) (inverse_has_product G HI));
      [exact (CE1 HS)|].
    exact (PASemiring238.zero_below_successor G ((σ j) ⊗ C) (inverse_has_product G HI)).
  - apply CI.
    + apply prefix_divisors_intro. intros i. apply II.
      set (D := List.cons (i ⧀ σ j) G).
      assert (HD : has_coding_context D).
      { unfold D. apply has_coding_cons. exact HG. }
      assert (Hid : D ⊢C (i ⧀ σ j)).
      { apply Ctx. unfold D. now left. }
      pose proof (successor_split_at D i j
        (accumulator_has_common D (coding_has_accumulator D HD)) Hid) as Hsplit.
      pose proof (weaken_head G (prefix_divisors C j P) (i ⧀ σ j) (CE1 (CE2 HS))) as HdivD.
      eapply DE; [exact Hsplit| |].
      * set (E := List.cons (i ⧀ j) D).
        assert (HE : has_coding_context E).
        { unfold E. apply has_coding_cons. exact HD. }
        assert (Hi : E ⊢C (i ⧀ j)).
        { apply Ctx. unfold E. now left. }
        pose proof (weaken_head D (prefix_divisors C j P) (i ⧀ j) HdivD) as HdivE.
        apply (divisor_right_product E (beta_modulus C i) P (beta_modulus C j)
          (inverse_has_divisor E (coding_has_inverse E HE))).
        exact (prefix_divisors_at E C j P i HdivE Hi).
      * set (E := List.cons (i == j) D).
        assert (HE : has_coding_context E).
        { unfold E. apply has_coding_cons. exact HD. }
        pose proof (coding_has_inverse E HE) as HIE.
        assert (Hij : E ⊢C (i == j)).
        { apply Ctx. unfold E. now left. }
        pose proof (inverse_symmetry E i j HIE Hij) as Hji.
        assert (Hnew : E ⊢C divides (beta_modulus C j) (P ⊗ beta_modulus C j)).
        { apply (divides_introduce E (beta_modulus C j) (P ⊗ beta_modulus C j) P).
          exact (inverse_mul_commutative E P (beta_modulus C j) HIE). }
        exact (index_divisor_transport E C (P ⊗ beta_modulus C j) j i HIE Hji Hnew).
    + apply CI.
      * apply desired_rows_intro. intros i w. apply II, II.
        set (D := List.cons (PAPowerExtension238.append_graph b c n r i w)
          (List.cons (i ⧀ σ j) G)).
        assert (HD : has_coding_context D).
        { unfold D. apply has_coding_cons, has_coding_cons. exact HG. }
        assert (Hid : D ⊢C (i ⧀ σ j)).
        { apply Ctx. unfold D. right. now left. }
        assert (HQi : D ⊢C PAPowerExtension238.append_graph b c n r i w).
        { apply Ctx. unfold D. now left. }
        pose proof (successor_split_at D i j
          (accumulator_has_common D (coding_has_accumulator D HD)) Hid) as Hsplit.
        assert (HdivD : D ⊢C prefix_divisors C j P).
        { unfold D. apply weaken_head, weaken_head. exact (CE1 (CE2 HS)). }
        assert (HrowsD : D ⊢C desired_rows b c n r C j z).
        { unfold D. apply weaken_head, weaken_head. exact (CE1 (CE2 (CE2 HS))). }
        assert (HpresD : D ⊢C preserved_beta_rows z znew P C).
        { unfold D. apply weaken_head, weaken_head. exact (CE2 HM). }
        eapply DE; [exact Hsplit| |].
        -- set (E := List.cons (i ⧀ j) D).
           assert (Hi : E ⊢C (i ⧀ j)).
           { apply Ctx. unfold E. now left. }
           pose proof (weaken_head D (PAPowerExtension238.append_graph b c n r i w)
             (i ⧀ j) HQi) as HQE.
           pose proof (weaken_head D (prefix_divisors C j P) (i ⧀ j) HdivD) as HdivE.
           pose proof (weaken_head D (desired_rows b c n r C j z) (i ⧀ j) HrowsD) as HrowsE.
           pose proof (weaken_head D (preserved_beta_rows z znew P C) (i ⧀ j) HpresD) as HpresE.
           exact (merged_row_at E z znew P C i w HpresE
             (prefix_divisors_at E C j P i HdivE Hi)
             (desired_rows_at E b c n r C j z i w HrowsE Hi HQE)).
        -- set (E := List.cons (i == j) D).
           assert (HE : has_coding_context E).
           { unfold E. apply has_coding_cons. exact HD. }
           assert (Hij : E ⊢C (i == j)).
           { apply Ctx. unfold E. now left. }
           pose proof (weaken_head D (PAPowerExtension238.append_graph b c n r i w)
             (i == j) HQi) as HQE.
           assert (HQj : E ⊢C PAPowerExtension238.append_graph b c n r j v).
           { unfold E, D. apply weaken_head, weaken_head, weaken_head. exact HQ. }
           assert (HBj : E ⊢C beta znew C j v).
           { unfold E, D. apply weaken_head, weaken_head, weaken_head. exact (CE1 HM). }
           exact (endpoint_desired_row E b c n r C j znew v i w HE Hij HQE HQj HBj).
      * apply future_inverses_intro. intros t. apply II, II.
        set (D := List.cons (t ⧀= k) (List.cons (σ j ⧀= t) G)).
        assert (HD : has_coding_context D).
        { unfold D. apply has_coding_cons, has_coding_cons. exact HG. }
        pose proof (coding_has_inverse D HD) as HID.
        assert (Hlower : D ⊢C (σ j ⧀= t)).
        { apply Ctx. unfold D. right. now left. }
        assert (Hupper : D ⊢C (t ⧀= k)).
        { apply Ctx. unfold D. now left. }
        pose proof (weak_successor_lower_strict D j t Hlower) as Hjt.
        pose proof (weak_lower_predecessor D j t HID Hlower) as Hweakjt.
        assert (Hfuture : D ⊢C future_inverses C k j P).
        { unfold D. apply weaken_head, weaken_head. exact (CE2 (CE2 (CE2 HS))). }
        assert (HCD : D ⊢C common_multiple (σ k) C).
        { unfold D. apply weaken_head, weaken_head. exact HC. }
        pose proof (future_inverses_at D C k j P t Hfuture Hweakjt Hupper) as HPinv.
        pose proof (PABetaIndexArithmetic238.bounded_moduli_inverse_at D j t k C
          (coding_has_pairwise D HD) Hjt Hupper HCD) as HMinv.
        exact (inverse_product_exists D P (beta_modulus C j) (beta_modulus C t) HID HPinv HMinv).
Qed.

Lemma accumulator_step_at G b c n p r C k j P z : has_coding_context G ->
  G ⊢C trace_body b c n p -> G ⊢C common_multiple (σ k) C ->
  G ⊢C ((b ⊕ r) ⧀ C) -> G ⊢C (j ⧀ σ (σ n)) -> G ⊢C (j ⧀= k) ->
  G ⊢C accumulator_state b c n r C k j P z ->
  G ⊢C accumulator_exists b c n r C k (σ j).
Proof.
  intros HG HT HC HL Hrange Hjk HS.
  pose proof (PABetaAppendGraph238.append_graph_total_at G b c n p r j
    (coding_total G HG) HT Hrange) as Hvalue.
  eapply PABetaAppendGraph238.append_value_exists_eliminate; [exact Hvalue|]. intros v.
  set (D := List.cons (PAPowerExtension238.append_graph b c n r j v) G).
  assert (HD : has_coding_context D).
  { unfold D. apply has_coding_cons. exact HG. }
  pose proof (coding_has_inverse D HD) as HI.
  assert (HQ : D ⊢C PAPowerExtension238.append_graph b c n r j v).
  { apply Ctx. unfold D. now left. }
  pose proof (append_graph_bound_at D b c n r j v HD HQ) as Hvbound.
  pose proof (weaken_head G ((b ⊕ r) ⧀ C)
    (PAPowerExtension238.append_graph b c n r j v) HL) as HLD.
  pose proof (PABetaIndexArithmetic238.residue_below_modulus_at D v (b ⊕ r) C j
    HI Hvbound HLD) as Hmodbound.
  pose proof (weaken_head G (j ⧀= k)
    (PAPowerExtension238.append_graph b c n r j v) Hjk) as HjkD.
  pose proof (weaken_head G (future_inverses C k j P)
    (PAPowerExtension238.append_graph b c n r j v) (CE2 (CE2 (CE2 HS)))) as HfutureD.
  pose proof (future_inverses_at D C k j P j HfutureD (weak_reflexive D j HI) HjkD) as Hcurrent.
  eapply inverse_exists_eliminate; [exact Hcurrent|]. intros x y.
  set (E := List.cons (inverse_pair P (beta_modulus C j) x y) D).
  assert (HE : has_coding_context E).
  { unfold E. apply has_coding_cons. exact HD. }
  assert (Hinv : E ⊢C (x ⊗ P == (y ⊗ beta_modulus C j) ⊕ σ zero)).
  { apply Ctx. unfold E. now left. }
  pose proof (weaken_head D (v ⧀ beta_modulus C j)
    (inverse_pair P (beta_modulus C j) x y) Hmodbound) as HmodE.
  pose proof (binary_crt_merge_at E z x P C j v y (coding_has_inverse E HE) Hinv HmodE) as Hmerge.
  eapply merge_exists_eliminate; [exact Hmerge|]. intros znew.
  set (F := List.cons (merge_result z znew P C j v) E).
  assert (HF : has_coding_context F).
  { unfold F. apply has_coding_cons. exact HE. }
  assert (HCF : F ⊢C common_multiple (σ k) C).
  { unfold F, E, D. apply weaken_head, weaken_head, weaken_head. exact HC. }
  assert (HQF : F ⊢C PAPowerExtension238.append_graph b c n r j v).
  { unfold F, E. apply weaken_head, weaken_head. exact HQ. }
  assert (HSF : F ⊢C accumulator_state b c n r C k j P z).
  { unfold F, E, D. apply weaken_head, weaken_head, weaken_head. exact HS. }
  assert (HMF : F ⊢C merge_result z znew P C j v).
  { apply Ctx. unfold F. now left. }
  apply (accumulator_exists_intro F b c n r C k (σ j) (P ⊗ beta_modulus C j) znew).
  exact (merged_accumulator_state F b c n r C k j P z v znew HF HCF HQF HSF HMF).
Qed.

Theorem bounded_crt_successor_state : paeq_derivable (∀ ∀ ∀ ∀ ∀ ∀ ∀ ∀ ∀ ∀
  (trace_body $0 $1 $2 $3 → common_multiple (σ $6) $5 → ($0 ⊕ $4) ⧀ $5 →
    $7 ⧀ σ (σ $2) → $7 ⧀= $6 → accumulator_state $0 $1 $2 $4 $5 $6 $7 $8 $9 →
    accumulator_exists $0 $1 $2 $4 $5 $6 (σ $7))).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, coding_proof, II, II, II, II, II, II.
  set (G := List.cons (accumulator_state $0 $1 $2 $4 $5 $6 $7 $8 $9)
    (List.cons ($7 ⧀= $6) (List.cons ($7 ⧀ σ (σ $2))
      (List.cons (($0 ⊕ $4) ⧀ $5) (List.cons (common_multiple (σ $6) $5)
        (List.cons (trace_body $0 $1 $2 $3) coding_context)))))).
  apply (accumulator_step_at G $0 $1 $2 $3 $4 $5 $6 $7 $8 $9).
  - unfold G. apply has_coding_cons, has_coding_cons, has_coding_cons,
      has_coding_cons, has_coding_cons, has_coding_cons. exact coding_context_self.
  - apply Ctx. unfold G. right. right. right. right. right. now left.
  - apply Ctx. unfold G. right. right. right. right. now left.
  - apply Ctx. unfold G. right. right. right. now left.
  - apply Ctx. unfold G. right. right. now left.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Lemma unit_inverse G m : has_inverse_context G -> G ⊢C inverse_exists (σ zero) m.
Proof.
  intros HG. apply (inverse_exists_intro G (σ zero) m (σ zero) zero).
  unfold inverse_pair.
  pose proof (mult_zero_instance G m
    (inverse_has_product G HG ax_mult_zero product_mult_zero)) as Hzero.
  pose proof (inverse_addition G (zero ⊗ m) zero (σ zero) (σ zero) HG Hzero
    (inverse_reflexivity G (σ zero) HG)) as Hfirst.
  pose proof (PAAddition238.add_zero_instance G (σ zero)
    (inverse_has_product G HG ax_add_zero product_add_zero)) as Hsecond.
  pose proof (inverse_transitivity G ((zero ⊗ m) ⊕ σ zero) (zero ⊕ σ zero)
    (σ zero) HG Hfirst Hsecond) as Hright.
  exact (inverse_transitivity G (σ zero ⊗ σ zero) (σ zero)
    ((zero ⊗ m) ⊕ σ zero) HG (inverse_left_one G (σ zero) HG)
    (inverse_symmetry G ((zero ⊗ m) ⊕ σ zero) (σ zero) HG Hright)).
Qed.
Lemma accumulator_zero_state G b c n r C k : has_accumulator_context G ->
  G ⊢C accumulator_state b c n r C k zero (σ zero) zero.
Proof.
  intros HG. unfold accumulator_state. apply CI.
  - exact (PASemiring238.zero_below_successor G zero
      (inverse_has_product G (accumulator_has_inverse G HG))).
  - apply CI.
    + apply prefix_divisors_intro. intros i. apply II.
      set (D := List.cons (i ⧀ zero) G).
      assert (HD : has_accumulator_context D).
      { unfold D. apply has_accumulator_cons. exact HG. }
      apply Exp. eapply IE; [exact (zero_minimal_at D i HD)|].
      apply Ctx. unfold D. now left.
    + apply CI.
      * apply desired_rows_intro. intros i v. apply II, II.
        set (D := List.cons (PAPowerExtension238.append_graph b c n r i v)
          (List.cons (i ⧀ zero) G)).
        assert (HD : has_accumulator_context D).
        { unfold D. apply has_accumulator_cons, has_accumulator_cons. exact HG. }
        apply Exp. eapply IE; [exact (zero_minimal_at D i HD)|].
        apply Ctx. unfold D. right. now left.
      * apply future_inverses_intro. intros t. apply II, II.
        set (D := List.cons (t ⧀= k) (List.cons (zero ⧀= t) G)).
        apply (unit_inverse D (beta_modulus C t)).
        unfold D. apply has_inverse_cons, has_inverse_cons, accumulator_has_inverse.
        exact HG.
Qed.
Theorem bounded_crt_zero_state : paeq_derivable (∀ ∀ ∀ ∀ ∀ ∀
  accumulator_exists $0 $1 $2 $3 $4 $5 zero).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, accumulator_proof.
  apply (accumulator_exists_intro accumulator_context $0 $1 $2 $3 $4 $5 zero (σ zero) zero).
  apply accumulator_zero_state. exact accumulator_context_self.
Qed.


(* The induction formula retains every free arithmetic parameter.  The
   upper bound makes the final successor case use only available graph
   rows; the terminal state has covered indices zero through S n. *)
Definition bounded_accumulator (b c n p r C j : pa_term) : pa_form :=
  trace_body b c n p → common_multiple (σ (σ n)) C →
  ((b ⊕ r) ⧀ C) → (j ⧀= σ (σ n)) →
  accumulator_exists b c n r C (σ n) j.
Lemma bounded_accumulator_subst b c n p r C j rho :
  (bounded_accumulator b c n p r C j)[rho] =
  bounded_accumulator b`[rho] c`[rho] n`[rho] p`[rho] r`[rho] C`[rho] j`[rho].
Proof.
  unfold bounded_accumulator. cbn [subst_form].
  rewrite trace_body_subst, common_multiple_subst, PAlt_subst, PAle_subst,
    accumulator_exists_subst. reflexivity.
Qed.
Definition bounded_accumulator_formula : pa_form :=
  bounded_accumulator $1 $2 $3 $4 $5 $6 $0.
Lemma bounded_accumulator_base : paeq_derivable bounded_accumulator_formula[zero..].
Proof.
  unfold bounded_accumulator_formula. rewrite bounded_accumulator_subst.
  change (paeq_derivable (bounded_accumulator $0 $1 $2 $3 $4 $5 zero)).
  unfold bounded_accumulator. apply coding_proof, II, II, II, II.
  set (G := List.cons (zero ⧀= σ (σ $2)) (List.cons (($0 ⊕ $4) ⧀ $5)
    (List.cons (common_multiple (σ (σ $2)) $5)
      (List.cons (trace_body $0 $1 $2 $3) coding_context)))).
  apply (accumulator_exists_intro G $0 $1 $2 $4 $5 (σ $2) zero (σ zero) zero).
  apply accumulator_zero_state, coding_has_accumulator.
  unfold G. apply has_coding_cons, has_coding_cons, has_coding_cons, has_coding_cons.
  exact coding_context_self.
Qed.
Lemma bounded_accumulator_step : paeq_derivable
  (∀ (bounded_accumulator_formula → bounded_accumulator_formula[σ $0 .: S >> var])).
Proof.
  unfold bounded_accumulator_formula. rewrite bounded_accumulator_subst.
  change (paeq_derivable (∀ (bounded_accumulator $1 $2 $3 $4 $5 $6 $0 →
    bounded_accumulator $1 $2 $3 $4 $5 $6 (σ $0)))).
  apply paeq_generalize, coding_proof, II.
  change ((List.cons (bounded_accumulator $1 $2 $3 $4 $5 $6 $0) coding_context) ⊢C
    (trace_body $1 $2 $3 $4 → common_multiple (σ (σ $3)) $6 →
      ($1 ⊕ $5) ⧀ $6 → (σ $0 ⧀= σ (σ $3)) →
      accumulator_exists $1 $2 $3 $5 $6 (σ $3) (σ $0))).
  apply II, II, II, II.
  set (G := List.cons (σ $0 ⧀= σ (σ $3))
    (List.cons (($1 ⊕ $5) ⧀ $6) (List.cons (common_multiple (σ (σ $3)) $6)
      (List.cons (trace_body $1 $2 $3 $4)
        (List.cons (bounded_accumulator $1 $2 $3 $4 $5 $6 $0) coding_context))))).
  assert (HG : has_coding_context G).
  { unfold G. apply has_coding_cons, has_coding_cons, has_coding_cons,
      has_coding_cons, has_coding_cons. exact coding_context_self. }
  pose proof (coding_has_inverse G HG) as HI.
  assert (Hupper : G ⊢C (σ $0 ⧀= σ (σ $3))).
  { apply Ctx. unfold G. now left. }
  assert (HT : G ⊢C trace_body $1 $2 $3 $4).
  { apply Ctx. unfold G. right. right. right. now left. }
  assert (HC : G ⊢C common_multiple (σ (σ $3)) $6).
  { apply Ctx. unfold G. right. right. now left. }
  assert (HL : G ⊢C (($1 ⊕ $5) ⧀ $6)).
  { apply Ctx. unfold G. right. now left. }
  assert (Hind : G ⊢C bounded_accumulator $1 $2 $3 $4 $5 $6 $0).
  { apply Ctx. unfold G. right. right. right. right. now left. }
  pose proof (weak_lower_predecessor G $0 (σ (σ $3)) HI Hupper) as Hprevious.
  pose proof (successor_weak_cancel G $0 (σ $3) (coding_has_accumulator G HG)
    Hupper) as Hindex.
  pose proof (weak_upper_successor G $0 (σ $3) HI Hindex) as Hrange.
  pose proof (IE (IE (IE (IE Hind HT) HC) HL) Hprevious) as HX.
  eapply accumulator_exists_eliminate; [exact HX|]. intros P z.
  set (D := List.cons (accumulator_state $1 $2 $3 $5 $6 (σ $3) $0 P z) G).
  assert (HD : has_coding_context D).
  { unfold D. apply has_coding_cons. exact HG. }
  assert (HTD : D ⊢C trace_body $1 $2 $3 $4).
  { unfold D. apply weaken_head. exact HT. }
  assert (HCD : D ⊢C common_multiple (σ (σ $3)) $6).
  { unfold D. apply weaken_head. exact HC. }
  assert (HLD : D ⊢C (($1 ⊕ $5) ⧀ $6)).
  { unfold D. apply weaken_head. exact HL. }
  assert (HrangeD : D ⊢C ($0 ⧀ σ (σ $3))).
  { unfold D. apply weaken_head. exact Hrange. }
  assert (HindexD : D ⊢C ($0 ⧀= σ $3)).
  { unfold D. apply weaken_head. exact Hindex. }
  assert (HS : D ⊢C accumulator_state $1 $2 $3 $5 $6 (σ $3) $0 P z).
  { apply Ctx. unfold D. now left. }
  exact (accumulator_step_at D $1 $2 $3 $4 $5 $6 (σ $3) $0 P z
    HD HTD HCD HLD HrangeD HindexD HS).
Qed.
Definition bounded_accumulator_sentence : pa_form :=
  ∀ ∀ ∀ ∀ ∀ ∀ ∀ bounded_accumulator_formula.
Theorem bounded_crt_accumulator : paeq_derivable bounded_accumulator_sentence.
Proof.
  unfold bounded_accumulator_sentence.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize.
  apply (paeq_induction_rule bounded_accumulator_formula).
  - exact bounded_accumulator_base.
  - exact bounded_accumulator_step.
Qed.
Lemma bounded_accumulator_at G b c n p r C j :
  List.In bounded_accumulator_sentence G -> G ⊢C bounded_accumulator b c n p r C j.
Proof.
  intros HH. assert (HAll : G ⊢C bounded_accumulator_sentence) by now apply Ctx.
  assert (HB : bounded 7 bounded_accumulator_formula).
  { unfold bounded_accumulator_formula, bounded_accumulator, accumulator_exists,
      accumulator_state, prefix_divisors, desired_rows, future_inverses,
      PAPowerExtension238.append_graph, trace_body, trace_steps, doubling_step,
      doubling_pair, common_multiple, multiple_rows, divides, inverse_exists,
      inverse_pair, beta, beta_modulus, PAlt, PAle. solve_bounds. }
  pose proof (subst_forall_prv (phi := bounded_accumulator_formula) (N := 7)
    HAll HB (j .: b .: c .: n .: p .: r .: C .: var)) as HK.
  unfold bounded_accumulator_formula in HK. rewrite bounded_accumulator_subst in HK.
  exact HK.
Qed.

End PACRTAccumulator238.

Print Assumptions PACRTAccumulator238.accumulator_proof.
Print Assumptions PACRTAccumulator238.bounded_crt_zero_state.
Print Assumptions PACRTAccumulator238.bounded_crt_successor_state.

Print Assumptions PACRTAccumulator238.bounded_crt_accumulator.
