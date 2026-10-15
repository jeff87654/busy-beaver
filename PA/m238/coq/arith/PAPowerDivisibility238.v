(* Original finite ordinary-PA divisibility of decoded doubling traces.
   The induction uses the actual predecessor endpoint of the upper trace.
   No trace existence, arithmetic model, or extra arithmetic axiom is used. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAEqCongruence238 PAOrder238
  PAOrderBounds238 PAQuotient238 PAOrderGrowth238 PASemiring238 PAMultiplicationComm238
  CompactInPA238 PAPowerTrace238 PAPowerBound238 PAPowerUnique238
  PAPowerExtension238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrderBounds238
  PAQuotient238 PASemiring238 CompactInPA238 PAPowerTrace238
  PAPowerBound238 PAPowerUnique238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAPowerDivisibility238.

Definition uniqueness_sentence : pa_form := ∀ uniqueness_formula.
Definition commutativity_sentence : pa_form := ∀ ∀ ($0 ⊗ $1 == $1 ⊗ $0).
Definition right_mult_zero_sentence : pa_form := ∀ ($0 ⊗ zero == zero).
Definition right_mult_successor_sentence : pa_form :=
  ∀ ∀ ($0 ⊗ σ $1 == $0 ⊕ ($0 ⊗ $1)).
Definition zero_minimal_sentence : pa_form := ∀ ¬ ($0 ⧀ zero).
Definition successor_split_sentence : pa_form :=
  ∀ ∀ ($0 ⧀ σ $1 → (($0 ⧀ $1) ∨ ($0 == $1))).
Definition power_divisor_context : list pa_form :=
  [uniqueness_sentence; commutativity_sentence;
   mult_left_distribution_sentence; right_mult_zero_sentence;
   right_mult_successor_sentence; zero_minimal_sentence;
   successor_split_sentence] ++ trace_context.
Definition has_power_divisor_context (G : list pa_form) : Prop :=
  forall phi, List.In phi power_divisor_context -> List.In phi G.

Lemma power_divisor_proof phi :
  power_divisor_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD.
  eapply paeq_modus_ponens with (phi := uniqueness_sentence);
    [|exact actual_pow2_unique].
  eapply paeq_modus_ponens with (phi := commutativity_sentence);
    [|exact PAMultiplicationComm238.mult_commutative].
  eapply paeq_modus_ponens with (phi := mult_left_distribution_sentence);
    [|exact mult_left_distribution].
  eapply paeq_modus_ponens with (phi := right_mult_zero_sentence);
    [|exact mult_right_zero].
  eapply paeq_modus_ponens with (phi := right_mult_successor_sentence);
    [|exact PAMultiplicationComm238.mult_right_successor].
  eapply paeq_modus_ponens with (phi := zero_minimal_sentence);
    [|exact PAOrder238.zero_minimal].
  eapply paeq_modus_ponens with (phi := successor_split_sentence);
    [|exact PAPowerExtension238.order_successor_split].
  apply trace_proof, II, II, II, II, II, II, II. exact HD.
Qed.
Lemma power_divisor_context_self : has_power_divisor_context power_divisor_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_power_divisor_cons G phi : has_power_divisor_context G ->
  has_power_divisor_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma power_divisor_has_trace G : has_power_divisor_context G -> has_trace_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold power_divisor_context.
  apply List.in_app_iff. now right.
Qed.
Lemma power_divisor_has_equality G : has_power_divisor_context G -> has_equality G.
Proof. intros HG. apply trace_has_equality, power_divisor_has_trace. exact HG. Qed.

Lemma power_unique_at G n p q : has_power_divisor_context G ->
  G ⊢C pow2 n p -> G ⊢C pow2 n q -> G ⊢C (p == q).
Proof.
  intros HG HP HQ. assert (HH : G ⊢C uniqueness_sentence).
  { apply Ctx, HG. unfold power_divisor_context. apply List.in_app_iff.
    left. now left. }
  pose proof (AllE n HH) as HI.
  change (G ⊢C uniqueness_formula[n..]) in HI.
  unfold uniqueness_formula in HI. rewrite uniqueness_property_subst in HI.
  change (G ⊢C uniqueness_property n) in HI.
  exact (IE (IE (uniqueness_at G n p q HI) HP) HQ).
Qed.
Lemma power_index_transport G i n p : has_power_divisor_context G ->
  G ⊢C (i == n) -> G ⊢C pow2 i p -> G ⊢C pow2 n p.
Proof.
  intros HG HEQ HP.
  pose proof (formula_substitutivity G (pow2 $0 p`[↑]) i n
    (power_divisor_has_equality G HG) HEQ) as HH.
  rewrite !pow2_subst, !subst_term_shift in HH.
  change (G ⊢C (pow2 i p ↔ pow2 n p)) in HH.
  exact (IE (CE1 HH) HP).
Qed.
Lemma multiplication_commute_at G a b : has_power_divisor_context G ->
  G ⊢C (a ⊗ b == b ⊗ a).
Proof.
  intros HG. apply PAMultiplicationComm238.mult_commutative_at.
  apply HG. unfold power_divisor_context. apply List.in_app_iff.
  left. right. now left.
Qed.
Lemma product_one_at G a : has_power_divisor_context G ->
  G ⊢C (a ⊗ σ zero == a).
Proof.
  intros HG. pose proof (power_divisor_has_equality G HG) as HE.
  assert (HR : List.In PAMultiplicationComm238.mult_right_successor_sentence G).
  { apply HG. unfold power_divisor_context. apply List.in_app_iff. left.
    right. right. right. right. now left. }
  assert (HZ : List.In PAMultiplicationComm238.mult_right_zero_sentence G).
  { apply HG. unfold power_divisor_context. apply List.in_app_iff. left.
    right. right. right. now left. }
  pose proof (PAMultiplicationComm238.mult_right_successor_at G a zero HR) as Hrec.
  pose proof (PAMultiplicationComm238.mult_right_zero_at G a HZ) as Hz.
  pose proof (reflexivity_instance G a HE) as Ha.
  pose proof (IE (IE (addition_instance G a a (a ⊗ zero) zero HE) Ha) Hz) as Hsum.
  pose proof (PAOrderGrowth238.right_zero_at G a
    (trace_has_quotient G (power_divisor_has_trace G HG))) as Hend.
  pose proof (equality_transitivity G (a ⊗ σ zero) (a ⊕ (a ⊗ zero))
    (a ⊕ zero) HE Hrec Hsum) as Hfirst.
  exact (equality_transitivity G (a ⊗ σ zero) (a ⊕ zero) a HE Hfirst Hend).
Qed.
Lemma double_multiple G d r q : has_power_divisor_context G ->
  G ⊢C divides d r -> G ⊢C (q == r ⊕ r) -> G ⊢C divides d q.
Proof.
  intros HG HM HQ. eapply divides_eliminate; [exact HM|]. intros h.
  set (D := List.cons (r == d ⊗ h) G).
  change (D ⊢C divides d q).
  assert (HD : has_power_divisor_context D).
  { unfold D. apply has_power_divisor_cons. exact HG. }
  pose proof (power_divisor_has_equality D HD) as HE.
  assert (Hr : D ⊢C (r == d ⊗ h)).
  { apply Ctx. unfold D. now left. }
  pose proof (IE (IE (addition_instance D r (d ⊗ h) r (d ⊗ h) HE)
    Hr) Hr) as Hdouble.
  pose proof (multiplication_commute_at D d h HD) as Hcomm.
  pose proof (IE (IE (addition_instance D (d ⊗ h) (h ⊗ d)
    (d ⊗ h) (h ⊗ d) HE) Hcomm) Hcomm) as Hswap.
  assert (Hdist : List.In mult_left_distribution_sentence D).
  { apply HD. unfold power_divisor_context. apply List.in_app_iff. left.
    right. right. now left. }
  pose proof (left_distribution_at D h h d Hdist) as Hdistribution.
  pose proof (equality_symmetry D ((h ⊕ h) ⊗ d)
    ((h ⊗ d) ⊕ (h ⊗ d)) HE Hdistribution) as Hback.
  pose proof (multiplication_commute_at D (h ⊕ h) d HD) as Hlast.
  pose proof (weaken_head G (q == r ⊕ r) (r == d ⊗ h) HQ) as Hq.
  pose proof (equality_transitivity D q (r ⊕ r)
    ((d ⊗ h) ⊕ (d ⊗ h)) HE Hq Hdouble) as Hfirst.
  pose proof (equality_transitivity D q ((d ⊗ h) ⊕ (d ⊗ h))
    ((h ⊗ d) ⊕ (h ⊗ d)) HE Hfirst Hswap) as Hsecond.
  pose proof (equality_transitivity D q ((h ⊗ d) ⊕ (h ⊗ d))
    ((h ⊕ h) ⊗ d) HE Hsecond Hback) as Hthird.
  apply (divides_introduce D d q (h ⊕ h)).
  exact (equality_transitivity D q ((h ⊕ h) ⊗ d)
    (d ⊗ (h ⊕ h)) HE Hthird Hlast).
Qed.

Definition divisibility_matrix (n i p q : pa_term) : pa_form :=
  pow2 i p → pow2 n q → i ⧀ n → divides (p ⊕ p) q.
Definition divisibility_values (n i p : pa_term) : pa_form :=
  ∀ divisibility_matrix n`[↑] i`[↑] p`[↑] $0.
Definition divisibility_lower (n i : pa_term) : pa_form :=
  ∀ divisibility_values n`[↑] i`[↑] $0.
Definition divisibility_property (n : pa_term) : pa_form :=
  ∀ divisibility_lower n`[↑] $0.
Lemma divisibility_matrix_subst n i p q rho :
  (divisibility_matrix n i p q)[rho] =
  divisibility_matrix n`[rho] i`[rho] p`[rho] q`[rho].
Proof.
  unfold divisibility_matrix. cbn [subst_form].
  rewrite !pow2_subst, PAlt_subst, divides_subst. reflexivity.
Qed.
Lemma divisibility_values_subst n i p rho :
  (divisibility_values n i p)[rho] =
  divisibility_values n`[rho] i`[rho] p`[rho].
Proof.
  unfold divisibility_values. cbn [subst_form].
  rewrite divisibility_matrix_subst. now rewrite !up_term.
Qed.
Lemma divisibility_lower_subst n i rho :
  (divisibility_lower n i)[rho] = divisibility_lower n`[rho] i`[rho].
Proof.
  unfold divisibility_lower. cbn [subst_form].
  rewrite divisibility_values_subst. now rewrite !up_term.
Qed.
Lemma divisibility_property_subst n rho :
  (divisibility_property n)[rho] = divisibility_property n`[rho].
Proof.
  unfold divisibility_property. cbn [subst_form].
  rewrite divisibility_lower_subst. now rewrite !up_term.
Qed.
Lemma divisibility_lower_instance n i :
  (divisibility_lower n`[↑] $0)[i..] = divisibility_lower n i.
Proof.
  rewrite divisibility_lower_subst.
  change (divisibility_lower n`[↑]`[i..] i = divisibility_lower n i).
  exact (f_equal (fun t : pa_term => divisibility_lower t i)
    (@subst_term_shift PA_funcs_signature n i)).
Qed.
Lemma divisibility_values_instance n i p :
  (divisibility_values n`[↑] i`[↑] $0)[p..] = divisibility_values n i p.
Proof.
  rewrite divisibility_values_subst.
  change (divisibility_values n`[↑]`[p..] i`[↑]`[p..] p =
    divisibility_values n i p).
  exact (f_equal2 (fun a b : pa_term => divisibility_values a b p)
    (@subst_term_shift PA_funcs_signature n p)
    (@subst_term_shift PA_funcs_signature i p)).
Qed.
Lemma divisibility_matrix_instance n i p q :
  (divisibility_matrix n`[↑] i`[↑] p`[↑] $0)[q..] = divisibility_matrix n i p q.
Proof.
  rewrite divisibility_matrix_subst.
  change (divisibility_matrix n`[↑]`[q..] i`[↑]`[q..] p`[↑]`[q..] q =
    divisibility_matrix n i p q).
  transitivity (divisibility_matrix n i p`[↑]`[q..] q).
  - exact (f_equal2 (fun a b : pa_term => divisibility_matrix a b p`[↑]`[q..] q)
      (@subst_term_shift PA_funcs_signature n q)
      (@subst_term_shift PA_funcs_signature i q)).
  - exact (f_equal (fun t : pa_term => divisibility_matrix n i t q)
      (@subst_term_shift PA_funcs_signature p q)).
Qed.
Lemma formula_certificate_transport (G : list pa_form) (phi psi : pa_form) :
  phi = psi -> G ⊢C phi -> G ⊢C psi.
Proof. intros <- H. exact H. Qed.

Lemma divisibility_at G n i p q :
  G ⊢C divisibility_property n -> G ⊢C divisibility_matrix n i p q.
Proof.
  intros HH.
  pose proof (formula_certificate_transport G _ _
    (divisibility_lower_instance n i) (AllE i HH)) as H1.
  pose proof (formula_certificate_transport G _ _
    (divisibility_values_instance n i p) (AllE p H1)) as H2.
  exact (formula_certificate_transport G _ _
    (divisibility_matrix_instance n i p q) (AllE q H2)).
Qed.
Lemma divisibility_introduce G n :
  (forall i p q, G ⊢C divisibility_matrix n i p q) ->
  G ⊢C divisibility_property n.
Proof.
  intros HH. unfold divisibility_property. apply AllI_named. intros i.
  change (G ⊢C (divisibility_lower n`[↑] $0)[i..]).
  apply (formula_certificate_transport G (divisibility_lower n i) _
    (eq_sym (divisibility_lower_instance n i))).
  unfold divisibility_lower. apply AllI_named. intros p.
  change (G ⊢C (divisibility_values n`[↑] i`[↑] $0)[p..]).
  apply (formula_certificate_transport G (divisibility_values n i p) _
    (eq_sym (divisibility_values_instance n i p))).
  unfold divisibility_values. apply AllI_named. intros q.
  change (G ⊢C (divisibility_matrix n`[↑] i`[↑] p`[↑] $0)[q..]).
  exact (formula_certificate_transport G _ _
    (eq_sym (divisibility_matrix_instance n i p q)) (HH i p q)).
Qed.

Definition divisibility_formula : pa_form := divisibility_property $0.
Lemma divisibility_base : paeq_derivable divisibility_formula[zero..].
Proof.
  unfold divisibility_formula. rewrite divisibility_property_subst.
  change (paeq_derivable (divisibility_property zero)).
  apply power_divisor_proof, divisibility_introduce. intros i p q.
  unfold divisibility_matrix. apply II, II, II.
  set (G := List.cons (i ⧀ zero) (List.cons (pow2 zero q)
    (List.cons (pow2 i p) power_divisor_context))).
  change (G ⊢C divides (p ⊕ p) q). apply Exp.
  assert (HH : G ⊢C zero_minimal_sentence).
  { apply Ctx. unfold G. right. right. right.
    unfold power_divisor_context. apply List.in_app_iff. left.
    right. right. right. right. right. now left. }
  pose proof (AllE i HH) as HN.
  change (G ⊢C ¬ ((PAlt $0 zero)[i..])) in HN.
  rewrite PAlt_subst in HN.
  apply (IE HN), Ctx. unfold G. now left.
Qed.

Lemma power_successor_split_at G i n : has_power_divisor_context G ->
  G ⊢C (i ⧀ σ n) -> G ⊢C ((i ⧀ n) ∨ (i == n)).
Proof.
  intros HG HI. assert (HH : G ⊢C successor_split_sentence).
  { apply Ctx, HG. unfold power_divisor_context. apply List.in_app_iff. left.
    right. right. right. right. right. right. now left. }
  assert (HB : bounded 2 ($0 ⧀ σ $1 → (($0 ⧀ $1) ∨ ($0 == $1)))).
  { unfold PAlt. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := $0 ⧀ σ $1 → (($0 ⧀ $1) ∨ ($0 == $1))) (N := 2)
    HH HB (i .: n .: var)) as HK.
  change (G ⊢C (PAlt $0 (σ $1))[i .: n .: var] →
    ((PAlt $0 $1)[i .: n .: var] ∨ (i == n))) in HK.
  rewrite !PAlt_subst in HK. exact (IE HK HI).
Qed.

Lemma divisibility_step : paeq_derivable
  (∀ (divisibility_formula → divisibility_formula[σ $0 .: S >> var])).
Proof.
  unfold divisibility_formula. rewrite divisibility_property_subst.
  change (paeq_derivable
    (∀ (divisibility_property $0 → divisibility_property (σ $0)))).
  apply paeq_generalize, power_divisor_proof, II, divisibility_introduce.
  intros i p q. unfold divisibility_matrix. apply II, II, II.
  set (G := List.cons (i ⧀ σ $0) (List.cons (pow2 (σ $0) q)
    (List.cons (pow2 i p) (List.cons (divisibility_property $0)
      power_divisor_context)))).
  change (G ⊢C divides (p ⊕ p) q).
  assert (HG : has_power_divisor_context G).
  { unfold G. apply has_power_divisor_cons, has_power_divisor_cons,
      has_power_divisor_cons, has_power_divisor_cons.
    exact power_divisor_context_self. }
  assert (HQ : G ⊢C pow2 (σ $0) q).
  { apply Ctx. unfold G. right. now left. }
  pose proof (successor_endpoint G $0 q (power_divisor_has_trace G HG) HQ) as HX.
  eapply predecessor_endpoint_eliminate; [exact HX|]. intros r.
  set (D := List.cons (pow2 $0 r ∧ (q == r ⊕ r)) G).
  change (D ⊢C divides (p ⊕ p) q).
  assert (HD : has_power_divisor_context D).
  { unfold D. apply has_power_divisor_cons. exact HG. }
  assert (HL : D ⊢C (i ⧀ σ $0)).
  { apply Ctx. unfold D, G. right. now left. }
  pose proof (power_successor_split_at D i $0 HD HL) as Hsplit.
  eapply DE; [exact Hsplit| |].
  - set (E := List.cons (i ⧀ $0) D).
    change (E ⊢C divides (p ⊕ p) q).
    assert (HE : has_power_divisor_context E).
    { unfold E. apply has_power_divisor_cons. exact HD. }
    assert (HI : E ⊢C divisibility_property $0).
    { apply Ctx. unfold E, D, G.
      right. right. right. right. right. now left. }
    assert (HP : E ⊢C pow2 i p).
    { apply Ctx. unfold E, D, G. right. right. right. right. now left. }
    assert (HR : E ⊢C (pow2 $0 r ∧ (q == r ⊕ r))).
    { apply Ctx. unfold E, D. right. now left. }
    assert (HL' : E ⊢C (i ⧀ $0)).
    { apply Ctx. unfold E. now left. }
    pose proof (IE (IE (IE (divisibility_at E $0 i p r HI) HP)
      (CE1 HR)) HL') as HM.
    exact (double_multiple E (p ⊕ p) r q HE HM (CE2 HR)).
  - set (E := List.cons (i == $0) D).
    change (E ⊢C divides (p ⊕ p) q).
    assert (HE : has_power_divisor_context E).
    { unfold E. apply has_power_divisor_cons. exact HD. }
    pose proof (power_divisor_has_equality E HE) as HEQ.
    assert (HP : E ⊢C pow2 i p).
    { apply Ctx. unfold E, D, G. right. right. right. right. now left. }
    assert (HR : E ⊢C (pow2 $0 r ∧ (q == r ⊕ r))).
    { apply Ctx. unfold E, D. right. now left. }
    assert (Hindex : E ⊢C (i == $0)).
    { apply Ctx. unfold E. now left. }
    pose proof (power_index_transport E i $0 p HE Hindex HP) as HPn.
    pose proof (power_unique_at E $0 p r HE HPn (CE1 HR)) as Hpr.
    pose proof (IE (IE (addition_instance E p r p r HEQ) Hpr) Hpr) as Hdouble.
    pose proof (equality_symmetry E (p ⊕ p) (r ⊕ r) HEQ Hdouble) as Hback.
    pose proof (equality_transitivity E q (r ⊕ r) (p ⊕ p)
      HEQ (CE2 HR) Hback) as Hq.
    pose proof (product_one_at E (p ⊕ p) HE) as Hone.
    pose proof (equality_symmetry E ((p ⊕ p) ⊗ σ zero) (p ⊕ p)
      HEQ Hone) as Hunit.
    apply (divides_introduce E (p ⊕ p) q (σ zero)).
    exact (equality_transitivity E q (p ⊕ p) ((p ⊕ p) ⊗ σ zero)
      HEQ Hq Hunit).
Qed.

(* The displayed existential quotient is exactly q=(p+p)*h. *)
Theorem pow2_lower_double_divides : paeq_derivable
  (∀ ∀ ∀ ∀ (pow2 $2 $1 → pow2 $3 $0 → $2 ⧀ $3 →
    ∃ ($1 == ($2 ⊕ $2) ⊗ $0))).
Proof.
  change (paeq_derivable (∀ divisibility_formula)).
  apply (paeq_induction_rule divisibility_formula).
  - exact divisibility_base.
  - exact divisibility_step.
Qed.

End PAPowerDivisibility238.

Print Assumptions PAPowerDivisibility238.power_unique_at.
Print Assumptions PAPowerDivisibility238.product_one_at.
Print Assumptions PAPowerDivisibility238.double_multiple.
Print Assumptions PAPowerDivisibility238.divisibility_base.
Print Assumptions PAPowerDivisibility238.divisibility_step.
Print Assumptions PAPowerDivisibility238.pow2_lower_double_divides.
