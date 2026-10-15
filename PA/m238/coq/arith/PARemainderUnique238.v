(* Original quotient induction for uniqueness of a bounded remainder.
   This constructs an ordinary finite PA certificate. It uses neither a
   division algorithm nor existence of a coded power/history witness. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238
  PAAddition238 PAOrderBounds238 PACancellation238 PAQuotient238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAQuotient238 PAEqCongruence238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PARemainderUnique238.

Definition remainder_matrix (q qp m r s : pa_term) : pa_form :=
  quotient_row q m r == quotient_row qp m s → r ⧀ m → s ⧀ m → r == s.
Definition quotient_property (q m r s : pa_term) : pa_form :=
  ∀ remainder_matrix q`[↑] $0 m`[↑] r`[↑] s`[↑].

Lemma matrix_subst q qp m r s rho :
  (remainder_matrix q qp m r s)[rho] =
  remainder_matrix q`[rho] qp`[rho] m`[rho] r`[rho] s`[rho].
Proof. unfold remainder_matrix, quotient_row, PAlt. cbn. now rewrite !up_term. Qed.
Lemma property_subst q m r s rho :
  (quotient_property q m r s)[rho] =
  quotient_property q`[rho] m`[rho] r`[rho] s`[rho].
Proof.
  unfold quotient_property.
  change ((∀ (remainder_matrix q`[↑] $0 m`[↑] r`[↑] s`[↑])[up rho]) =
    ∀ remainder_matrix q`[rho]`[↑] $0 m`[rho]`[↑] r`[rho]`[↑] s`[rho]`[↑]).
  rewrite matrix_subst. now rewrite !up_term.
Qed.
Lemma matrix_instance q m r s qp :
  (remainder_matrix q`[↑] $0 m`[↑] r`[↑] s`[↑])[qp..] = remainder_matrix q qp m r s.
Proof.
  rewrite matrix_subst.
  rewrite (@subst_term_shift PA_funcs_signature q qp),
    (@subst_term_shift PA_funcs_signature m qp),
    (@subst_term_shift PA_funcs_signature r qp),
    (@subst_term_shift PA_funcs_signature s qp). reflexivity.
Qed.
Lemma property_introduce G q m r s :
  (forall qp, G ⊢C remainder_matrix q qp m r s) -> G ⊢C quotient_property q m r s.
Proof.
  intros H. unfold quotient_property. apply AllI_named. intros qp.
  rewrite matrix_instance. exact (H qp).
Qed.
Lemma property_at G q m r s qp :
  G ⊢C quotient_property q m r s -> G ⊢C remainder_matrix q qp m r s.
Proof.
  intros H. pose proof (AllE qp H) as HK. rewrite matrix_instance in HK. exact HK.
Qed.

Lemma predecessor_member : List.In predecessor_sentence quotient_context.
Proof. unfold quotient_context. apply List.in_app_iff. left. right. right. right. now left. Qed.
Lemma predecessor_at G q : has_quotient_context G ->
  G ⊢C (q == zero ∨ ∃ (q`[↑] == σ $0)).
Proof.
  intros HG. assert (HP : G ⊢C predecessor_sentence).
  { apply Ctx. exact (HG predecessor_sentence predecessor_member). }
  pose proof (AllE q HP) as HK.
  change (G ⊢C (q == zero ∨ ∃ (q`[↑] == σ $0))) in HK. exact HK.
Qed.
Lemma predecessor_eliminate G q (psi : pa_form) :
  G ⊢C ∃ (q`[↑] == σ $0) ->
  (forall t, (List.cons (q == σ t) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HE H. eapply ExE_named; [exact HE|]. intros t.
  change ((List.cons (q`[↑]`[t..] == σ t) G) ⊢C psi).
  rewrite (@subst_term_shift PA_funcs_signature q t). exact (H t).
Qed.

Lemma row_quotient_congr G q qp m r : has_quotient_context G ->
  G ⊢C (q == qp) -> G ⊢C (quotient_row q m r == quotient_row qp m r).
Proof.
  intros HG HQ. pose proof (quotient_has_equality G HG) as HE.
  pose proof (PAEqCongruence238.reflexivity_instance G m HE) as HM.
  pose proof (IE (IE (PAEqCongruence238.multiplication_instance G q qp m m HE) HQ) HM) as HP.
  pose proof (PAEqCongruence238.reflexivity_instance G r HE) as HR.
  exact (IE (IE (PAEqCongruence238.addition_instance G (q ⊗ m) (qp ⊗ m) r r HE) HP) HR).
Qed.
Lemma rows_zero_equal G m r s : has_quotient_context G ->
  G ⊢C (quotient_row zero m r == quotient_row zero m s) -> G ⊢C (r == s).
Proof.
  intros HG HQ. pose proof (quotient_has_equality G HG) as HE.
  pose proof (row_zero G m r HG) as HL. pose proof (row_zero G m s HG) as HR.
  pose proof (PAEqCongruence238.equality_symmetry G (quotient_row zero m r) r HE HL) as HB.
  pose proof (PAEqCongruence238.equality_transitivity G r (quotient_row zero m r)
    (quotient_row zero m s) HE HB HQ) as HF.
  exact (PAEqCongruence238.equality_transitivity G r (quotient_row zero m s) s HE HF HR).
Qed.
Lemma rows_successor_cancel G q qp m r s : has_quotient_context G ->
  G ⊢C (quotient_row (σ q) m r == quotient_row (σ qp) m s) ->
  G ⊢C (quotient_row q m r == quotient_row qp m s).
Proof.
  intros HG HI. pose proof (quotient_has_equality G HG) as HE.
  pose proof (row_successor G q m r HG) as HL.
  pose proof (row_successor G qp m s HG) as HR.
  pose proof (PAEqCongruence238.equality_symmetry G (quotient_row (σ q) m r)
    (m ⊕ quotient_row q m r) HE HL) as HB.
  pose proof (PAEqCongruence238.equality_transitivity G (m ⊕ quotient_row q m r)
    (quotient_row (σ q) m r) (quotient_row (σ qp) m s) HE HB HI) as HF.
  pose proof (PAEqCongruence238.equality_transitivity G (m ⊕ quotient_row q m r)
    (quotient_row (σ qp) m s) (m ⊕ quotient_row qp m s) HE HF HR) as HH.
  exact (IE (cancellation_instance G m (quotient_row q m r) (quotient_row qp m s)
    (HG cancellation_sentence quotient_cancellation)) HH).
Qed.

Lemma strict_weak_at G x y z : has_quotient_context G ->
  G ⊢C (x ⧀ y → y ⧀= z → x ⧀ z).
Proof.
  intros HG. assert (HH : G ⊢C strict_weak_sentence).
  { apply Ctx. exact (HG strict_weak_sentence quotient_strict_weak). }
  assert (HB : bounded 3 ($0 ⧀ $1 → $1 ⧀= $2 → $0 ⧀ $2)).
  { unfold PAlt, PAle. solve_bounds. }
  pose proof (subst_forall_prv (phi := $0 ⧀ $1 → $1 ⧀= $2 → $0 ⧀ $2)
    (N := 3) HH HB (x .: y .: z .: var)) as HK.
  assert (HS : ($0 ⧀ $1 → $1 ⧀= $2 → $0 ⧀ $2)[x .: y .: z .: var] =
    (x ⧀ y → y ⧀= z → x ⧀ z)).
  { change (((PAlt $0 $1)[x .: y .: z .: var] →
      (PAle $1 $2)[x .: y .: z .: var] → (PAlt $0 $2)[x .: y .: z .: var]) =
      (x ⧀ y → y ⧀= z → x ⧀ z)).
    rewrite !PAlt_subst, PAle_subst. reflexivity. }
  rewrite HS in HK. exact HK.
Qed.
Lemma order_ir_at G r : has_quotient_context G -> G ⊢C ¬ (r ⧀ r).
Proof.
  intros HG. assert (HH : G ⊢C order_ir_sentence).
  { apply Ctx. exact (HG order_ir_sentence quotient_order_ir). }
  pose proof (AllE r HH) as HK.
  change (G ⊢C ¬ ((PAlt $0 $0)[r..])) in HK.
  rewrite PAlt_subst in HK. exact HK.
Qed.
Lemma rows_zero_successor_absurd G q m r s : has_quotient_context G ->
  G ⊢C (quotient_row zero m r == quotient_row (σ q) m s) ->
  G ⊢C (r ⧀ m) -> G ⊢C falsity.
Proof.
  intros HG HI HLT. pose proof (quotient_has_equality G HG) as HE.
  pose proof (row_zero G m r HG) as HL. pose proof (row_successor G q m s HG) as HR.
  pose proof (PAEqCongruence238.equality_symmetry G (quotient_row zero m r) r HE HL) as HB.
  pose proof (PAEqCongruence238.equality_transitivity G r (quotient_row zero m r)
    (quotient_row (σ q) m s) HE HB HI) as HF.
  pose proof (PAEqCongruence238.equality_transitivity G r (quotient_row (σ q) m s)
    (m ⊕ quotient_row q m s) HE HF HR) as HH.
  pose proof (PAOrderBounds238.weak_order_witness G m r (quotient_row q m s) HH) as HW.
  pose proof (IE (IE (strict_weak_at G r m r HG) HLT) HW) as HC.
  exact (IE (order_ir_at G r HG) HC).
Qed.

Lemma zero_property G m r s : has_quotient_context G -> G ⊢C quotient_property zero m r s.
Proof.
  intros HG. apply property_introduce. intros qp. unfold remainder_matrix. apply II, II, II.
  set (B := List.cons (s ⧀ m) (List.cons (r ⧀ m)
    (List.cons (quotient_row zero m r == quotient_row qp m s) G))).
  change (B ⊢C (r == s)).
  assert (HB : has_quotient_context B).
  { unfold B. apply has_quotient_cons, has_quotient_cons, has_quotient_cons. exact HG. }
  assert (HI : B ⊢C (quotient_row zero m r == quotient_row qp m s)).
  { apply Ctx. unfold B. right. right. now left. }
  assert (HR : B ⊢C (r ⧀ m)).
  { apply Ctx. unfold B. right. now left. }
  eapply DE; [exact (predecessor_at B qp HB)| |].
  - set (D := List.cons (qp == zero) B).
    change (D ⊢C (r == s)).
    assert (HD : has_quotient_context D).
    { unfold D. apply has_quotient_cons. exact HB. }
    assert (HQ : D ⊢C (qp == zero)).
    { apply Ctx. unfold D. now left. }
    pose proof (row_quotient_congr D qp zero m s HD HQ) as HT.
    pose proof (PAEqCongruence238.equality_transitivity D
      (quotient_row zero m r) (quotient_row qp m s) (quotient_row zero m s)
      (quotient_has_equality D HD) (weaken_head B _ _ HI) HT) as HH.
    exact (rows_zero_equal D m r s HD HH).
  - set (D := List.cons (∃ (qp`[↑] == σ $0)) B).
    change (D ⊢C (r == s)).
    eapply predecessor_eliminate; [apply Ctx; unfold D; now left|]. intros t.
    set (E := List.cons (qp == σ t) D).
    change (E ⊢C (r == s)).
    assert (HE : has_quotient_context E).
    { unfold E, D. apply has_quotient_cons, has_quotient_cons. exact HB. }
    assert (HQ : E ⊢C (qp == σ t)).
    { apply Ctx. unfold E. now left. }
    pose proof (row_quotient_congr E qp (σ t) m s HE HQ) as HT.
    assert (HIE : E ⊢C (quotient_row zero m r == quotient_row qp m s)).
    { unfold E, D. exact (weaken_head D _ _ (weaken_head B _ _ HI)). }
    pose proof (PAEqCongruence238.equality_transitivity E
      (quotient_row zero m r) (quotient_row qp m s) (quotient_row (σ t) m s)
      (quotient_has_equality E HE) HIE HT) as HH.
    apply Exp. apply (rows_zero_successor_absurd E t m r s HE HH).
    unfold E, D. exact (weaken_head D _ _ (weaken_head B _ _ HR)).
Qed.

Lemma successor_property G q m r s : has_quotient_context G ->
  G ⊢C quotient_property q m r s -> G ⊢C quotient_property (σ q) m r s.
Proof.
  intros HG IH. apply property_introduce. intros qp. unfold remainder_matrix. apply II, II, II.
  set (B := List.cons (s ⧀ m) (List.cons (r ⧀ m)
    (List.cons (quotient_row (σ q) m r == quotient_row qp m s) G))).
  change (B ⊢C (r == s)).
  assert (HB : has_quotient_context B).
  { unfold B. apply has_quotient_cons, has_quotient_cons, has_quotient_cons. exact HG. }
  assert (HI : B ⊢C (quotient_row (σ q) m r == quotient_row qp m s)).
  { apply Ctx. unfold B. right. right. now left. }
  assert (HR : B ⊢C (r ⧀ m)).
  { apply Ctx. unfold B. right. now left. }
  assert (HS : B ⊢C (s ⧀ m)).
  { apply Ctx. unfold B. now left. }
  assert (HIP : B ⊢C quotient_property q m r s).
  { unfold B. apply weaken_head, weaken_head, weaken_head. exact IH. }
  eapply DE; [exact (predecessor_at B qp HB)| |].
  - set (D := List.cons (qp == zero) B).
    change (D ⊢C (r == s)).
    assert (HD : has_quotient_context D).
    { unfold D. apply has_quotient_cons. exact HB. }
    assert (HQ : D ⊢C (qp == zero)).
    { apply Ctx. unfold D. now left. }
    pose proof (row_quotient_congr D qp zero m s HD HQ) as HT.
    pose proof (PAEqCongruence238.equality_transitivity D
      (quotient_row (σ q) m r) (quotient_row qp m s) (quotient_row zero m s)
      (quotient_has_equality D HD) (weaken_head B _ _ HI) HT) as HH.
    pose proof (PAEqCongruence238.equality_symmetry D
      (quotient_row (σ q) m r) (quotient_row zero m s) (quotient_has_equality D HD) HH) as HZ.
    apply Exp. apply (rows_zero_successor_absurd D q m s r HD HZ).
    unfold D. exact (weaken_head B _ _ HS).
  - set (D := List.cons (∃ (qp`[↑] == σ $0)) B).
    change (D ⊢C (r == s)).
    eapply predecessor_eliminate; [apply Ctx; unfold D; now left|]. intros t.
    set (E := List.cons (qp == σ t) D).
    change (E ⊢C (r == s)).
    assert (HE : has_quotient_context E).
    { unfold E, D. apply has_quotient_cons, has_quotient_cons. exact HB. }
    assert (HQ : E ⊢C (qp == σ t)).
    { apply Ctx. unfold E. now left. }
    pose proof (row_quotient_congr E qp (σ t) m s HE HQ) as HT.
    assert (HIE : E ⊢C (quotient_row (σ q) m r == quotient_row qp m s)).
    { unfold E, D. apply weaken_head, weaken_head. exact HI. }
    pose proof (PAEqCongruence238.equality_transitivity E
      (quotient_row (σ q) m r) (quotient_row qp m s) (quotient_row (σ t) m s)
      (quotient_has_equality E HE) HIE HT) as HH.
    pose proof (rows_successor_cancel E q t m r s HE HH) as HP.
    assert (IHQ : E ⊢C quotient_property q m r s).
    { unfold E, D. apply weaken_head, weaken_head. exact HIP. }
    pose proof (property_at E q m r s t IHQ) as HM.
    unfold remainder_matrix in HM.
    eapply IE; [eapply IE; [eapply IE; [exact HM|exact HP]|]|].
    + unfold E, D. apply weaken_head, weaken_head. exact HR.
    + unfold E, D. apply weaken_head, weaken_head. exact HS.
Qed.

Definition uniqueness_formula : pa_form := quotient_property $0 $1 $2 $3.
Lemma uniqueness_base : paeq_derivable uniqueness_formula[zero..].
Proof.
  unfold uniqueness_formula. rewrite property_subst.
  change (paeq_derivable (quotient_property zero $0 $1 $2)).
  apply quotient_proof. exact (zero_property quotient_context $0 $1 $2 quotient_context_self).
Qed.
Lemma uniqueness_step :
  paeq_derivable (∀ (uniqueness_formula → uniqueness_formula[σ $0 .: S >> var])).
Proof.
  unfold uniqueness_formula. rewrite property_subst.
  change (paeq_derivable (∀ (quotient_property $0 $1 $2 $3 → quotient_property (σ $0) $1 $2 $3))).
  apply paeq_generalize, quotient_proof, II.
  set (G := List.cons (quotient_property $0 $1 $2 $3) quotient_context).
  change (G ⊢C quotient_property (σ $0) $1 $2 $3).
  assert (HG : has_quotient_context G).
  { unfold G. apply has_quotient_cons. exact quotient_context_self. }
  apply (successor_property G $0 $1 $2 $3 HG). apply Ctx. unfold G. now left.
Qed.
Theorem bounded_remainder_unique :
  paeq_derivable (∀ ∀ ∀ ∀ ∀ remainder_matrix $1 $0 $2 $3 $4).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize.
  apply (paeq_induction_rule uniqueness_formula).
  - exact uniqueness_base.
  - exact uniqueness_step.
Qed.

End PARemainderUnique238.

Print Assumptions PARemainderUnique238.uniqueness_base.
Print Assumptions PARemainderUnique238.uniqueness_step.
Print Assumptions PARemainderUnique238.bounded_remainder_unique.
