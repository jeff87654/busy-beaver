(* Original finite ordinary-PA bounded Ackermann comprehension.
   The arithmetic helpers below consume only actual finite PA certificates.
   The one outstanding producer input is the literal trace-append PA proof;
   it is used to derive power totality and successor trace construction. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAEqCongruence238 PAOrder238 PAOrderGrowth238 PAOrderBounds238
  PAQuotient238 PARemainderUnique238 CompactInPA238 PAPowerTrace238
  PAPowerBound238 PABitPosition238 PABitPeriodic238 PAPowerUnique238
  PAPowerExtension238 PAPowerDivisibility238 PASemiring238
  PAMultiplicationComm238 PAFiniteSupport238 PAOrderTotal238 PABetaTraceAppend238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrder238 PAOrderGrowth238 PAOrderBounds238
  PAQuotient238 PARemainderUnique238 CompactInPA238 PAPowerTrace238
  PAPowerBound238 PABitPosition238 PABitPeriodic238 PAPowerUnique238
  PAPowerExtension238 PAPowerDivisibility238 PASemiring238
  PAMultiplicationComm238 PAFiniteSupport238 PAOrderTotal238 PABetaTraceAppend238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PABoundedComprehension238.

(* Finite syntactic cut: the input list is traversed and every sentence is
   replaced by its concrete finite ordinary-PA derivation. *)
Lemma finite_context_discharge G psi :
  (forall phi, List.In phi G -> paeq_derivable phi) ->
  G ⊢C psi -> paeq_derivable psi.
Proof.
  revert psi. induction G as [|phi G IH]; intros psi HA HD.
  - exists []. split; [intros chi Hchi; inversion Hchi|exact HD].
  - eapply paeq_modus_ponens with (phi := phi).
    + apply IH; [intros chi Hchi; apply HA; now right|]. apply II. exact HD.
    + apply HA. now left.
Qed.
Definition multiple_period_sentence : pa_form := ∀ multiple_formula.
Definition lower_double_divides_sentence : pa_form := ∀ divisibility_formula.
Definition bounded_arithmetic_context : list pa_form :=
  [multiple_period_sentence; lower_double_divides_sentence] ++
    periodic_context ++ power_divisor_context.
Definition has_bounded_arithmetic (G : list pa_form) : Prop :=
  forall phi, List.In phi bounded_arithmetic_context -> List.In phi G.
Lemma bounded_arithmetic_proof psi :
  bounded_arithmetic_context ⊢C psi -> paeq_derivable psi.
Proof.
  intros HD. apply (finite_context_discharge bounded_arithmetic_context psi); [|exact HD].
  intros phi Hphi.
  unfold bounded_arithmetic_context in Hphi. apply List.in_app_iff in Hphi as [Hphi|Hphi].
  - destruct Hphi as [<-|[<-|[]]].
    + exact bit_multiple_period.
    + exact pow2_lower_double_divides.
  - apply List.in_app_iff in Hphi as [Hphi|Hphi].
    + apply periodic_proof, Ctx. exact Hphi.
    + apply power_divisor_proof, Ctx. exact Hphi.
Qed.
Lemma bounded_arithmetic_self : has_bounded_arithmetic bounded_arithmetic_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_bounded_cons G phi : has_bounded_arithmetic G ->
  has_bounded_arithmetic (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma bounded_has_periodic G : has_bounded_arithmetic G -> has_periodic_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold bounded_arithmetic_context.
  apply List.in_app_iff. right. apply List.in_app_iff. now left.
Qed.
Lemma bounded_has_power_divisor G : has_bounded_arithmetic G -> has_power_divisor_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold bounded_arithmetic_context.
  apply List.in_app_iff. right. apply List.in_app_iff. now right.
Qed.
Lemma bounded_has_trace G : has_bounded_arithmetic G -> has_trace_context G.
Proof. intros HG. apply power_divisor_has_trace, bounded_has_power_divisor. exact HG. Qed.
Lemma bounded_equality G : has_bounded_arithmetic G -> has_equality G.
Proof. intros HG. apply trace_has_equality, bounded_has_trace. exact HG. Qed.

Lemma literal_member_at_power G C i p : has_bounded_arithmetic G ->
  G ⊢C pow2 i p -> G ⊢C (coded_member C i ↔ bit_tail C p).
Proof.
  intros HG HP. apply CI.
  - apply II. set (D := List.cons (coded_member C i) G).
    change (D ⊢C bit_tail C p).
    assert (HD : has_bounded_arithmetic D).
    { unfold D. apply has_bounded_cons. exact HG. }
    assert (HM : D ⊢C ackermann_bit C i).
    { apply Ctx. unfold D. now left. }
    eapply bit_eliminate; [exact HM|]. intros u.
    set (E := List.cons (bit_witness C i u) D).
    change (E ⊢C bit_tail C p).
    assert (HE : has_bounded_arithmetic E).
    { unfold E. apply has_bounded_cons. exact HD. }
    assert (HW : E ⊢C bit_witness C i u).
    { apply Ctx. unfold E. now left. }
    pose proof (weaken_head D (pow2 i p) (bit_witness C i u)
      (weaken_head G (pow2 i p) (coded_member C i) HP)) as HPE.
    pose proof (power_unique_at E i u p (bounded_has_power_divisor E HE) (CE1 HW) HPE) as Hup.
    pose proof (formula_substitutivity E (bit_tail C`[↑] $0) u p
      (bounded_equality E HE) Hup) as Htransfer.
    rewrite !bit_tail_subst, !subst_term_shift in Htransfer.
    exact (IE (CE1 Htransfer) (CE2 HW)).
  - apply II. set (D := List.cons (bit_tail C p) G).
    change (D ⊢C coded_member C i). unfold coded_member.
    rewrite ackermann_witness. apply (ExI p).
    rewrite bit_witness_subst, !subst_term_shift.
    unfold bit_witness. apply CI.
    + exact (weaken_head G (pow2 i p) (bit_tail C p) HP).
    + apply Ctx. unfold D. now left.
Qed.
Lemma multiple_period_at G h a p : has_bounded_arithmetic G ->
  G ⊢C multiple_matrix h a p.
Proof.
  intros HG. assert (HH : G ⊢C multiple_period_sentence).
  { apply Ctx, HG. unfold bounded_arithmetic_context. apply List.in_app_iff. left. now left. }
  pose proof (AllE h HH) as H.
  change (G ⊢C multiple_formula[h..]) in H.
  unfold multiple_formula in H. rewrite multiple_property_subst in H.
  exact (multiple_property_at G h a p H).
Qed.
Lemma lower_double_divides_at G n i p W : has_bounded_arithmetic G ->
  G ⊢C pow2 i p -> G ⊢C pow2 n W -> G ⊢C (i ⧀ n) ->
  G ⊢C divides (p ⊕ p) W.
Proof.
  intros HG HP HW Hin. assert (HH : G ⊢C lower_double_divides_sentence).
  { apply Ctx, HG. unfold bounded_arithmetic_context. apply List.in_app_iff.
    left. right. now left. }
  pose proof (AllE n HH) as H.
  change (G ⊢C divisibility_formula[n..]) in H.
  unfold divisibility_formula in H. rewrite divisibility_property_subst in H.
  exact (IE (IE (IE (divisibility_at G n i p W H) HP) HW) Hin).
Qed.
Lemma literal_low_tail_period G C i p n W : has_bounded_arithmetic G ->
  G ⊢C pow2 i p -> G ⊢C pow2 n W -> G ⊢C (i ⧀ n) ->
  G ⊢C (bit_tail C p ↔ bit_tail (C ⊕ W) p).
Proof.
  intros HG HP HW Hin.
  pose proof (lower_double_divides_at G n i p W HG HP HW Hin) as Hdiv.
  eapply divides_eliminate; [exact Hdiv|]. intros h.
  set (D := List.cons (W == (p ⊕ p) ⊗ h) G).
  change (D ⊢C (bit_tail C p ↔ bit_tail (C ⊕ W) p)).
  assert (HD : has_bounded_arithmetic D).
  { unfold D. apply has_bounded_cons. exact HG. }
  pose proof (bounded_has_periodic D HD) as Hper.
  assert (HWh : D ⊢C (W == (p ⊕ p) ⊗ h)).
  { apply Ctx. unfold D. now left. }
  pose proof (multiplication_commute_at D (p ⊕ p) h (bounded_has_power_divisor D HD)) as Hcomm.
  pose proof (periodic_transitivity D W ((p ⊕ p) ⊗ h) (h ⊗ (p ⊕ p)) Hper HWh Hcomm) as HWright.
  pose proof (periodic_symmetry D W (h ⊗ (p ⊕ p)) Hper HWright) as Hback.
  pose proof (periodic_addition D C C (h ⊗ (p ⊕ p)) W Hper
    (periodic_reflexivity D C Hper) Hback) as Heq.
  pose proof (bit_tail_equivalence D (C ⊕ (h ⊗ (p ⊕ p))) (C ⊕ W) p Hper Heq) as Hlast.
  pose proof (multiple_period_at D h C p HD) as Hfirst.
  unfold multiple_matrix in Hfirst.
  exact (periodic_equivalence_transitive D (bit_tail C p)
    (bit_tail (C ⊕ (h ⊗ (p ⊕ p))) p) (bit_tail (C ⊕ W) p) Hfirst Hlast).
Qed.
Lemma literal_low_member_period G C i p n W : has_bounded_arithmetic G ->
  G ⊢C pow2 i p -> G ⊢C pow2 n W -> G ⊢C (i ⧀ n) ->
  G ⊢C (coded_member C i ↔ coded_member (C ⊕ W) i).
Proof.
  intros HG HP HW Hin.
  pose proof (literal_member_at_power G C i p HG HP) as Hfirst.
  pose proof (literal_low_tail_period G C i p n W HG HP HW Hin) as Hmiddle.
  pose proof (literal_member_at_power G (C ⊕ W) i p HG HP) as Hlast.
  assert (Hreverse : G ⊢C (bit_tail (C ⊕ W) p ↔ coded_member (C ⊕ W) i)).
  { apply CI; [exact (CE2 Hlast)|exact (CE1 Hlast)]. }
  exact (periodic_equivalence_transitive G (coded_member C i) (bit_tail C p)
    (coded_member (C ⊕ W) i) Hfirst
    (periodic_equivalence_transitive G (bit_tail C p) (bit_tail (C ⊕ W) p)
      (coded_member (C ⊕ W) i) Hmiddle Hreverse)).
Qed.

Theorem actual_low_member_period : paeq_derivable (∀ ∀ ∀ ∀ ∀
  (pow2 $1 $2 → pow2 $3 $4 → $1 ⧀ $3 →
    (coded_member $0 $1 ↔ coded_member ($0 ⊕ $4) $1))).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, bounded_arithmetic_proof, II, II, II.
  set (G := List.cons ($1 ⧀ $3) (List.cons (pow2 $3 $4)
    (List.cons (pow2 $1 $2) bounded_arithmetic_context))).
  apply (literal_low_member_period G $0 $1 $2 $3 $4).
  - unfold G. apply has_bounded_cons, has_bounded_cons, has_bounded_cons.
    exact bounded_arithmetic_self.
  - apply Ctx. unfold G. right. right. now left.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.


Lemma low_member_period_without_totality G C i n W : has_bounded_arithmetic G ->
  G ⊢C pow2 n W -> G ⊢C (i ⧀ n) ->
  G ⊢C (coded_member C i ↔ coded_member (C ⊕ W) i).
Proof.
  intros HG HW Hin. apply CI.
  - apply II. set (D := List.cons (coded_member C i) G).
    change (D ⊢C coded_member (C ⊕ W) i).
    assert (HM : D ⊢C ackermann_bit C i).
    { apply Ctx. unfold D. now left. }
    eapply bit_eliminate; [exact HM|]. intros p.
    set (E := List.cons (bit_witness C i p) D).
    change (E ⊢C coded_member (C ⊕ W) i).
    assert (HE : has_bounded_arithmetic E).
    { unfold E, D. apply has_bounded_cons, has_bounded_cons. exact HG. }
    assert (HC : E ⊢C bit_witness C i p).
    { apply Ctx. unfold E. now left. }
    pose proof (weaken_head D (pow2 n W) (bit_witness C i p)
      (weaken_head G (pow2 n W) (coded_member C i) HW)) as HWE.
    pose proof (weaken_head D (i ⧀ n) (bit_witness C i p)
      (weaken_head G (i ⧀ n) (coded_member C i) Hin)) as HinE.
    pose proof (literal_low_tail_period E C i p n W HE (CE1 HC) HWE HinE) as Hperiod.
    exact (IE (CE2 (literal_member_at_power E (C ⊕ W) i p HE (CE1 HC)))
      (IE (CE1 Hperiod) (CE2 HC))).
  - apply II. set (D := List.cons (coded_member (C ⊕ W) i) G).
    change (D ⊢C coded_member C i).
    assert (HM : D ⊢C ackermann_bit (C ⊕ W) i).
    { apply Ctx. unfold D. now left. }
    eapply bit_eliminate; [exact HM|]. intros p.
    set (E := List.cons (bit_witness (C ⊕ W) i p) D).
    change (E ⊢C coded_member C i).
    assert (HE : has_bounded_arithmetic E).
    { unfold E, D. apply has_bounded_cons, has_bounded_cons. exact HG. }
    assert (HC : E ⊢C bit_witness (C ⊕ W) i p).
    { apply Ctx. unfold E. now left. }
    pose proof (weaken_head D (pow2 n W) (bit_witness (C ⊕ W) i p)
      (weaken_head G (pow2 n W) (coded_member (C ⊕ W) i) HW)) as HWE.
    pose proof (weaken_head D (i ⧀ n) (bit_witness (C ⊕ W) i p)
      (weaken_head G (i ⧀ n) (coded_member (C ⊕ W) i) Hin)) as HinE.
    pose proof (literal_low_tail_period E C i p n W HE (CE1 HC) HWE HinE) as Hperiod.
    exact (IE (CE2 (literal_member_at_power E C i p HE (CE1 HC)))
      (IE (CE2 Hperiod) (CE2 HC))).
Qed.

(* A larger actual doubling trace is at least the smaller endpoint.
   The divisor quotient is zero or a successor; zero contradicts the
   literal trace bound, and a successor directly supplies a weak bound. *)
Lemma larger_power_weak_bound G n W i p : has_bounded_arithmetic G ->
  G ⊢C pow2 n W -> G ⊢C pow2 i p -> G ⊢C (n ⧀ i) ->
  G ⊢C (W ⧀= p).
Proof.
  intros HG HW HP Hni.
  pose proof (lower_double_divides_at G i n W p HG HW HP Hni) as Hdiv.
  eapply divides_eliminate; [exact Hdiv|]. intros h.
  set (D := List.cons (p == (W ⊕ W) ⊗ h) G).
  change (D ⊢C (W ⧀= p)).
  assert (HD : has_bounded_arithmetic D).
  { unfold D. apply has_bounded_cons. exact HG. }
  pose proof (bounded_has_periodic D HD) as Hper.
  pose proof (bounded_has_power_divisor D HD) as Hpow.
  pose proof (predecessor_at D h (periodic_has_quotient D Hper)) as Hsplit.
  eapply DE; [exact Hsplit| |].
  - set (E := List.cons (h == zero) D).
    change (E ⊢C (W ⧀= p)). apply Exp.
    assert (HE : has_bounded_arithmetic E).
    { unfold E. apply has_bounded_cons. exact HD. }
    pose proof (bounded_has_periodic E HE) as HEper.
    pose proof (bounded_has_power_divisor E HE) as HEpow.
    assert (Hh : E ⊢C (h == zero)).
    { apply Ctx. unfold E. now left. }
    assert (Hp : E ⊢C (p == (W ⊕ W) ⊗ h)).
    { apply Ctx. unfold E, D. right. now left. }
    assert (Hzero : List.In PAMultiplicationComm238.mult_right_zero_sentence E).
    { apply HEpow. unfold power_divisor_context. apply List.in_app_iff. left.
      right. right. right. now left. }
    pose proof (IE (IE (multiplication_instance E (W ⊕ W) (W ⊕ W) h zero
      (bounded_equality E HE)) (periodic_reflexivity E (W ⊕ W) HEper)) Hh) as Hmul.
    pose proof (PAMultiplicationComm238.mult_right_zero_at E (W ⊕ W) Hzero) as Hmz.
    pose proof (periodic_transitivity E p ((W ⊕ W) ⊗ h) zero HEper Hp
      (periodic_transitivity E ((W ⊕ W) ⊗ h) ((W ⊕ W) ⊗ zero) zero HEper Hmul Hmz)) as Hpzero.
    pose proof (weaken_head D (pow2 i p) (h == zero)
      (weaken_head G (pow2 i p) (p == (W ⊕ W) ⊗ h) HP)) as HPE.
    pose proof (power_bound_at E i p (periodic_has_bit E HEper) HPE) as Hip.
    pose proof (strict_upper_transport E i p zero (bounded_has_trace E HE) Hip Hpzero) as Hiz.
    assert (HN : E ⊢C zero_minimal_sentence).
    { apply Ctx, HEpow. unfold power_divisor_context. apply List.in_app_iff. left.
      right. right. right. right. right. now left. }
    pose proof (AllE i HN) as Hneg.
    change (E ⊢C ¬ ((PAlt $0 zero)[i..])) in Hneg. rewrite PAlt_subst in Hneg.
    exact (IE Hneg Hiz).
  - eapply predecessor_eliminate; [apply Ctx; now left|]. intros k.
    set (E := List.cons (h == σ k) (List.cons (∃ (h`[↑] == σ $0)) D)).
    change (E ⊢C (W ⧀= p)).
    assert (HE : has_bounded_arithmetic E).
    { unfold E. apply has_bounded_cons, has_bounded_cons. exact HD. }
    pose proof (bounded_has_periodic E HE) as HEper.
    pose proof (bounded_has_power_divisor E HE) as HEpow.
    assert (Hh : E ⊢C (h == σ k)).
    { apply Ctx. unfold E. now left. }
    assert (Hp : E ⊢C (p == (W ⊕ W) ⊗ h)).
    { apply Ctx. unfold E, D. right. right. now left. }
    assert (Hrec : List.In PAMultiplicationComm238.mult_right_successor_sentence E).
    { apply HEpow. unfold power_divisor_context. apply List.in_app_iff. left.
      right. right. right. right. now left. }
    pose proof (IE (IE (multiplication_instance E (W ⊕ W) (W ⊕ W) h (σ k)
      (bounded_equality E HE)) (periodic_reflexivity E (W ⊕ W) HEper)) Hh) as Hmul.
    pose proof (PAMultiplicationComm238.mult_right_successor_at E (W ⊕ W) k Hrec) as Hmr.
    pose proof (periodic_transitivity E p ((W ⊕ W) ⊗ h)
      ((W ⊕ W) ⊕ ((W ⊕ W) ⊗ k)) HEper Hp
      (periodic_transitivity E ((W ⊕ W) ⊗ h) ((W ⊕ W) ⊗ σ k)
        ((W ⊕ W) ⊕ ((W ⊕ W) ⊗ k)) HEper Hmul Hmr)) as Hprow.
    pose proof (right_bound_at E W W (periodic_has_bit E HEper)) as HWdouble.
    pose proof (right_extension_at E W (W ⊕ W) ((W ⊕ W) ⊗ k)
      (periodic_has_bit E HEper) HWdouble) as Hbound.
    exact (weak_upper_transport E W ((W ⊕ W) ⊕ ((W ⊕ W) ⊗ k)) p
      (periodic_has_bit E HEper) Hbound
      (periodic_symmetry E p ((W ⊕ W) ⊕ ((W ⊕ W) ⊗ k)) HEper Hprow)).
Qed.


Definition comparison_context : list pa_form :=
  List.cons PAOrderTotal238.trichotomy_sentence bounded_arithmetic_context.
Definition has_comparison_context (G : list pa_form) : Prop :=
  forall phi, List.In phi comparison_context -> List.In phi G.
Lemma comparison_proof psi : comparison_context ⊢C psi -> paeq_derivable psi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := PAOrderTotal238.trichotomy_sentence).
  - apply bounded_arithmetic_proof, II. exact HD.
  - exact PAOrderTotal238.order_trichotomy.
Qed.
Lemma comparison_context_self : has_comparison_context comparison_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_comparison_cons G phi : has_comparison_context G ->
  has_comparison_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma comparison_has_bounded G : has_comparison_context G -> has_bounded_arithmetic G.
Proof. intros HG phi Hphi. apply HG. unfold comparison_context. now right. Qed.
Lemma comparison_at G i n : has_comparison_context G ->
  G ⊢C ((i ⧀ n) ∨ ((i == n) ∨ (n ⧀ i))).
Proof.
  intros HG. assert (HH : G ⊢C PAOrderTotal238.trichotomy_sentence).
  { apply Ctx, HG. unfold comparison_context. now left. }
  assert (HB : bounded 2 (($0 ⧀ $1) ∨ (($0 == $1) ∨ ($1 ⧀ $0)))).
  { unfold PAlt. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := ($0 ⧀ $1) ∨ (($0 == $1) ∨ ($1 ⧀ $0))) (N := 2)
    HH HB (i .: n .: var)) as H.
  change (G ⊢C ((PAlt $0 $1)[i .: n .: var] ∨
    ((i == n) ∨ (PAlt $1 $0)[i .: n .: var]))) in H.
  rewrite !PAlt_subst in H. exact H.
Qed.
Lemma code_below_endpoint_support G C n W i : has_comparison_context G ->
  G ⊢C pow2 n W -> G ⊢C (C ⧀ W) ->
  G ⊢C coded_member C i -> G ⊢C (i ⧀ n).
Proof.
  intros HG HW HC HM. unfold coded_member in HM.
  eapply bit_eliminate; [exact HM|]. intros p.
  set (D := List.cons (bit_witness C i p) G).
  change (D ⊢C (i ⧀ n)).
  assert (HD : has_comparison_context D).
  { unfold D. apply has_comparison_cons. exact HG. }
  pose proof (comparison_at D i n HD) as Hcases.
  eapply DE; [exact Hcases| |].
  - apply Ctx. now left.
  - set (E := List.cons ((i == n) ∨ (n ⧀ i)) D).
    change (E ⊢C (i ⧀ n)).
    assert (HE : has_comparison_context E).
    { unfold E. apply has_comparison_cons. exact HD. }
    assert (Hchoice : E ⊢C ((i == n) ∨ (n ⧀ i))).
    { apply Ctx. unfold E. now left. }
    eapply DE; [exact Hchoice| |].
    + set (F := List.cons (i == n) E).
      change (F ⊢C (i ⧀ n)). apply Exp.
      assert (HF : has_bounded_arithmetic F).
      { apply comparison_has_bounded. unfold F. apply has_comparison_cons. exact HE. }
      pose proof (bounded_has_periodic F HF) as Hper.
      assert (Hbit : F ⊢C bit_witness C i p).
      { apply Ctx. unfold F, E, D. right. right. now left. }
      assert (Hindex : F ⊢C (i == n)).
      { apply Ctx. unfold F. now left. }
      pose proof (power_index_transport F i n p (bounded_has_power_divisor F HF)
        Hindex (CE1 Hbit)) as Hpn.
      pose proof (weaken_head E (pow2 n W) (i == n)
        (weaken_head D (pow2 n W) ((i == n) ∨ (n ⧀ i))
          (weaken_head G (pow2 n W) (bit_witness C i p) HW))) as HWF.
      pose proof (power_unique_at F n W p (bounded_has_power_divisor F HF) HWF Hpn) as HWp.
      pose proof (weaken_head E (C ⧀ W) (i == n)
        (weaken_head D (C ⧀ W) ((i == n) ∨ (n ⧀ i))
          (weaken_head G (C ⧀ W) (bit_witness C i p) HC))) as HCF.
      pose proof (strict_upper_transport F C W p (bounded_has_trace F HF) HCF HWp) as HCp.
      exact (IE (bit_tail_above_code F C p Hper HCp) (CE2 Hbit)).
    + set (F := List.cons (n ⧀ i) E).
      change (F ⊢C (i ⧀ n)). apply Exp.
      assert (HF : has_bounded_arithmetic F).
      { apply comparison_has_bounded. unfold F. apply has_comparison_cons. exact HE. }
      pose proof (bounded_has_periodic F HF) as Hper.
      assert (Hbit : F ⊢C bit_witness C i p).
      { apply Ctx. unfold F, E, D. right. right. now left. }
      assert (Hindex : F ⊢C (n ⧀ i)).
      { apply Ctx. unfold F. now left. }
      pose proof (weaken_head E (pow2 n W) (n ⧀ i)
        (weaken_head D (pow2 n W) ((i == n) ∨ (n ⧀ i))
          (weaken_head G (pow2 n W) (bit_witness C i p) HW))) as HWF.
      pose proof (larger_power_weak_bound F n W i p HF HWF (CE1 Hbit) Hindex) as HWp.
      pose proof (weaken_head E (C ⧀ W) (n ⧀ i)
        (weaken_head D (C ⧀ W) ((i == n) ∨ (n ⧀ i))
          (weaken_head G (C ⧀ W) (bit_witness C i p) HC))) as HCF.
      pose proof (IE (IE (PARemainderUnique238.strict_weak_at F C W p (periodic_has_quotient F Hper)) HCF) HWp) as HCp.
      exact (IE (bit_tail_above_code F C p Hper HCp) (CE2 Hbit)).
Qed.
Lemma strict_add_right G x y t : has_bounded_arithmetic G ->
  G ⊢C (x ⧀ y) -> G ⊢C ((x ⊕ t) ⧀ (y ⊕ t)).
Proof.
  intros HG Hxy. unfold PAlt in Hxy.
  eapply ExE_named; [exact Hxy|]. intros d.
  change ((List.cons (y`[↑]`[d..] == σ x`[↑]`[d..] ⊕ d) G) ⊢C
    ((x ⊕ t) ⧀ (y ⊕ t))).
  rewrite !subst_term_shift.
  set (D := List.cons (y == σ x ⊕ d) G).
  change (D ⊢C ((x ⊕ t) ⧀ (y ⊕ t))).
  assert (HD : has_bounded_arithmetic D).
  { unfold D. apply has_bounded_cons. exact HG. }
  pose proof (bounded_has_periodic D HD) as Hper.
  assert (Hy : D ⊢C (y == σ x ⊕ d)).
  { apply Ctx. unfold D. now left. }
  pose proof (periodic_addition D y (σ x ⊕ d) t t Hper Hy
    (periodic_reflexivity D t Hper)) as H1.
  pose proof (periodic_symmetry D (σ x ⊕ (d ⊕ t)) ((σ x ⊕ d) ⊕ t) Hper
    (periodic_associative D (σ x) d t Hper)) as H2.
  pose proof (periodic_addition D (σ x) (σ x) (d ⊕ t) (t ⊕ d) Hper
    (periodic_reflexivity D (σ x) Hper) (periodic_commutative D d t Hper)) as H3.
  pose proof (periodic_associative D (σ x) t d Hper) as H4.
  pose proof (PAOrder238.add_rec_instance D x t
    (periodic_has_quotient D Hper ax_add_rec PAOrderGrowth238.quotient_add_rec)) as Hrec.
  pose proof (periodic_addition D (σ x ⊕ t) (σ (x ⊕ t)) d d Hper Hrec
    (periodic_reflexivity D d Hper)) as H5.
  apply (strict_order_witness D (x ⊕ t) (y ⊕ t) d).
  exact (periodic_transitivity D (y ⊕ t) ((σ x ⊕ d) ⊕ t)
    (σ (x ⊕ t) ⊕ d) Hper H1
    (periodic_transitivity D ((σ x ⊕ d) ⊕ t) (σ x ⊕ (d ⊕ t))
      (σ (x ⊕ t) ⊕ d) Hper H2
      (periodic_transitivity D (σ x ⊕ (d ⊕ t)) (σ x ⊕ (t ⊕ d))
        (σ (x ⊕ t) ⊕ d) Hper H3
        (periodic_transitivity D (σ x ⊕ (t ⊕ d)) ((σ x ⊕ t) ⊕ d)
          (σ (x ⊕ t) ⊕ d) Hper H4 H5)))).
Qed.
Theorem actual_code_endpoint_support : paeq_derivable (∀ ∀ ∀ ∀
  (pow2 $1 $2 → $0 ⧀ $2 → coded_member $0 $3 → $3 ⧀ $1)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, comparison_proof, II, II, II.
  set (G := List.cons (coded_member $0 $3) (List.cons ($0 ⧀ $2)
    (List.cons (pow2 $1 $2) comparison_context))).
  apply (code_below_endpoint_support G $0 $1 $2 $3).
  - unfold G. apply has_comparison_cons, has_comparison_cons, has_comparison_cons.
    exact comparison_context_self.
  - apply Ctx. unfold G. right. right. now left.
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.


Lemma bounded_body_subst phi n C rho :
  (bounded_code_body phi n C)[rho] =
  bounded_code_body phi[up rho] n`[rho] C`[rho].
Proof.
  unfold bounded_code_body. cbn [subst_form].
  rewrite coded_member_subst, PAlt_subst, !up_term. reflexivity.
Qed.
Lemma bounded_member_instance C i :
  (coded_member C`[↑] $0)[i..] = coded_member C i.
Proof.
  rewrite coded_member_subst.
  change (coded_member C`[↑]`[i..] i = coded_member C i).
  exact (f_equal (fun t => coded_member t i)
    (@subst_term_shift PA_funcs_signature C i)).
Qed.
Lemma bounded_order_instance n i :
  (PAlt $0 n`[↑])[i..] = (i ⧀ n).
Proof.
  rewrite PAlt_subst.
  change ((i ⧀ n`[↑]`[i..]) = (i ⧀ n)).
  exact (f_equal (fun t => PAlt i t)
    (@subst_term_shift PA_funcs_signature n i)).
Qed.
Lemma bounded_body_at G phi n C i : G ⊢C bounded_code_body phi n C ->
  G ⊢C (coded_member C i ↔ ((i ⧀ n) ∧ phi[i..])).
Proof.
  intros H. pose proof (AllE i H) as HH.
  change (G ⊢C ((coded_member C`[↑] $0)[i..] ↔
    ((PAlt $0 n`[↑])[i..] ∧ phi[i..]))) in HH.
  rewrite bounded_member_instance, bounded_order_instance in HH. exact HH.
Qed.
Lemma bounded_body_introduce G phi n C :
  (forall i, G ⊢C (coded_member C i ↔ ((i ⧀ n) ∧ phi[i..]))) ->
  G ⊢C bounded_code_body phi n C.
Proof.
  intros H. unfold bounded_code_body. apply AllI_named. intros i.
  change (G ⊢C ((coded_member C`[↑] $0)[i..] ↔
    ((PAlt $0 n`[↑])[i..] ∧ phi[i..]))).
  rewrite bounded_member_instance, bounded_order_instance. exact (H i).
Qed.
Definition code_certificate (phi : pa_form) (n W C : pa_term) : pa_form :=
  pow2 n W ∧ ((C ⧀ W) ∧ bounded_code_body phi n C).
Definition code_values (phi : pa_form) (n W : pa_term) : pa_form :=
  ∃ code_certificate phi[up ↑] n`[↑] W`[↑] $0.
Definition code_exists (phi : pa_form) (n : pa_term) : pa_form :=
  ∃ code_values phi[up ↑] n`[↑] $0.
Lemma code_certificate_subst phi n W C rho :
  (code_certificate phi n W C)[rho] =
  code_certificate phi[up rho] n`[rho] W`[rho] C`[rho].
Proof.
  unfold code_certificate. cbn [subst_form].
  rewrite pow2_subst, PAlt_subst, bounded_body_subst. reflexivity.
Qed.
Lemma member_shift_commute (phi : pa_form) (rho : nat -> pa_term) :
  phi[up ↑][up (up rho)] = phi[up rho][up ↑].
Proof.
  rewrite !subst_comp. apply subst_ext. intros [|k];
    cbn [up scons funcomp subst_term].
  - reflexivity.
  - change ((rho k)`[↑]`[↑] = (rho k)`[↑]`[up ↑]).
    symmetry. exact (@up_term PA_funcs_signature (rho k) (S >> var)).
Qed.
Lemma code_values_subst phi n W rho :
  (code_values phi n W)[rho] = code_values phi[up rho] n`[rho] W`[rho].
Proof.
  unfold code_values. cbn [subst_form]. rewrite code_certificate_subst,
    member_shift_commute, !up_term. reflexivity.
Qed.
Lemma code_exists_subst phi n rho :
  (code_exists phi n)[rho] = code_exists phi[up rho] n`[rho].
Proof.
  unfold code_exists. cbn [subst_form]. rewrite code_values_subst,
    member_shift_commute, !up_term. reflexivity.
Qed.
Lemma code_values_introduce G phi n W C :
  G ⊢C code_certificate phi n W C -> G ⊢C code_values phi n W.
Proof.
  intros H. unfold code_values. apply (ExI C).
  rewrite code_certificate_subst, member_shift_cancel, !subst_term_shift. exact H.
Qed.
Lemma code_exists_introduce G phi n W C :
  G ⊢C code_certificate phi n W C -> G ⊢C code_exists phi n.
Proof.
  intros H. unfold code_exists. apply (ExI W).
  rewrite code_values_subst, member_shift_cancel, !subst_term_shift.
  exact (code_values_introduce G phi n W C H).
Qed.
Lemma code_exists_eliminate G phi n (psi : pa_form) :
  G ⊢C code_exists phi n ->
  (forall W C, (List.cons (code_certificate phi n W C) G) ⊢C psi) ->
  G ⊢C psi.
Proof.
  intros HX H. unfold code_exists in HX.
  eapply ExE_named; [exact HX|]. intros W.
  rewrite code_values_subst, member_shift_cancel, !subst_term_shift.
  set (D := List.cons (code_values phi n W) G).
  change (D ⊢C psi).
  assert (HC : D ⊢C code_values phi n W).
  { apply Ctx. unfold D. now left. }
  unfold code_values in HC. eapply ExE_named; [exact HC|]. intros C.
  rewrite code_certificate_subst, member_shift_cancel, !subst_term_shift.
  eapply Weak; [exact (H W C)|]. intros chi Hchi.
  destruct Hchi as [<-|Hchi]; [now left|right; unfold D; now right].
Qed.
Definition power_successor_sentence : pa_form :=
  ∀ ∀ (pow2 $0 $1 → pow2 (σ $0) ($1 ⊕ $1)).
Definition comprehension_context : list pa_form :=
  [pow2 zero (σ zero); power_successor_sentence] ++ comparison_context.
Definition has_comprehension_context (G : list pa_form) : Prop :=
  forall phi, List.In phi comprehension_context -> List.In phi G.
Lemma comprehension_proof psi : paeq_derivable trace_append_sentence ->
  comprehension_context ⊢C psi -> paeq_derivable psi.
Proof.
  intros HP HD. apply (finite_context_discharge comprehension_context psi); [|exact HD].
  intros phi Hphi. unfold comprehension_context in Hphi. apply List.in_app_iff in Hphi as [Hphi|Hphi].
  - destruct Hphi as [<-|[<-|[]]].
    + exact pow2_zero_one.
    + exact (pow2_successor_from_trace_append HP).
  - apply comparison_proof, Ctx. exact Hphi.
Qed.
Lemma comprehension_context_self : has_comprehension_context comprehension_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_comprehension_cons G phi : has_comprehension_context G ->
  has_comprehension_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma comprehension_has_comparison G : has_comprehension_context G -> has_comparison_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold comprehension_context.
  apply List.in_app_iff. now right.
Qed.
Lemma comprehension_has_bounded G : has_comprehension_context G -> has_bounded_arithmetic G.
Proof. intros HG. apply comparison_has_bounded, comprehension_has_comparison. exact HG. Qed.
Lemma comprehension_power_successor G n W : has_comprehension_context G ->
  G ⊢C pow2 n W -> G ⊢C pow2 (σ n) (W ⊕ W).
Proof.
  intros HG HW. assert (HH : G ⊢C power_successor_sentence).
  { apply Ctx, HG. unfold comprehension_context. apply List.in_app_iff. left. right. now left. }
  assert (HB : bounded 2 (pow2 $0 $1 → pow2 (σ $0) ($1 ⊕ $1))).
  { unfold pow2, beta, beta_modulus, PAlt. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := pow2 $0 $1 → pow2 (σ $0) ($1 ⊕ $1)) (N := 2)
    HH HB (n .: W .: var)) as H.
  change (G ⊢C (pow2 $0 $1)[n .: W .: var] →
    (pow2 (σ $0) ($1 ⊕ $1))[n .: W .: var]) in H.
  rewrite !pow2_subst in H. exact (IE H HW).
Qed.
Lemma zero_minimal_at G i : has_bounded_arithmetic G -> G ⊢C ¬ (i ⧀ zero).
Proof.
  intros HG. assert (HH : G ⊢C zero_minimal_sentence).
  { apply Ctx, (bounded_has_power_divisor G HG).
    unfold power_divisor_context. apply List.in_app_iff. left.
    right. right. right. right. right. now left. }
  pose proof (AllE i HH) as H.
  change (G ⊢C ¬ ((PAlt $0 zero)[i..])) in H. rewrite PAlt_subst in H. exact H.
Qed.
Lemma code_zero G phi : has_comprehension_context G -> G ⊢C code_exists phi zero.
Proof.
  intros HG. pose proof (comprehension_has_bounded G HG) as HB.
  pose proof (bounded_has_periodic G HB) as Hper.
  assert (HW : G ⊢C pow2 zero (σ zero)).
  { apply Ctx, HG. unfold comprehension_context. apply List.in_app_iff. left. now left. }
  pose proof (PAOrderGrowth238.successor_self G zero (periodic_has_quotient G Hper)) as H01.
  apply (code_exists_introduce G phi zero (σ zero) zero).
  unfold code_certificate. apply CI; [exact HW|]. apply CI; [exact H01|].
  apply bounded_body_introduce. intros i. apply CI.
  - apply II. set (D := List.cons (coded_member zero i) G).
    apply Exp. assert (HD : has_comprehension_context D).
    { unfold D. apply has_comprehension_cons. exact HG. }
    assert (HM : D ⊢C coded_member zero i).
    { apply Ctx. unfold D. now left. }
    pose proof (code_below_endpoint_support D zero zero (σ zero) i
      (comprehension_has_comparison D HD)
      (weaken_head G (pow2 zero (σ zero)) (coded_member zero i) HW)
      (weaken_head G (zero ⧀ σ zero) (coded_member zero i) H01) HM) as Hiz.
    exact (IE (zero_minimal_at D i (comprehension_has_bounded D HD)) Hiz).
  - apply II. set (D := List.cons ((i ⧀ zero) ∧ phi[i..]) G).
    apply Exp. assert (HD : has_bounded_arithmetic D).
    { apply comprehension_has_bounded. unfold D. apply has_comprehension_cons. exact HG. }
    apply (IE (zero_minimal_at D i HD)). eapply CE1, Ctx. unfold D. now left.
Qed.


Lemma phi_at_equal G (phi : pa_form) a b : has_bounded_arithmetic G ->
  G ⊢C (a == b) -> G ⊢C phi[a..] -> G ⊢C phi[b..].
Proof.
  intros HG HE Hphi.
  exact (IE (CE1 (formula_substitutivity G phi a b (bounded_equality G HG) HE)) Hphi).
Qed.
Lemma member_at_equal G C a b : has_bounded_arithmetic G ->
  G ⊢C (a == b) -> G ⊢C coded_member C a -> G ⊢C coded_member C b.
Proof.
  intros HG HE HM.
  pose proof (formula_substitutivity G (coded_member C`[↑] $0) a b
    (bounded_equality G HG) HE) as H.
  rewrite !coded_member_subst, !subst_term_shift in H. exact (IE (CE1 H) HM).
Qed.
Lemma code_step_positive G phi n W C : has_comprehension_context G ->
  G ⊢C code_certificate phi n W C -> G ⊢C phi[n..] ->
  G ⊢C code_exists phi (σ n).
Proof.
  intros HG Hcode Hphi.
  pose proof (comprehension_has_bounded G HG) as HB.
  pose proof (bounded_has_periodic G HB) as Hper.
  pose proof (CE1 Hcode) as HW.
  pose proof (CE1 (CE2 Hcode)) as HC.
  pose proof (CE2 (CE2 Hcode)) as Hbody.
  pose proof (comprehension_power_successor G n W HG HW) as Hnext.
  pose proof (strict_add_right G C W W HB HC) as Hsmall.
  pose proof (bit_at_new_position G C W Hper HC) as Htailnew.
  pose proof (IE (CE2 (literal_member_at_power G (C ⊕ W) n W HB HW)) Htailnew) as Hnewbit.
  apply (code_exists_introduce G phi (σ n) (W ⊕ W) (C ⊕ W)).
  unfold code_certificate. apply CI; [exact Hnext|]. apply CI; [exact Hsmall|].
  apply bounded_body_introduce. intros i. apply CI.
  - apply II. set (D := List.cons (coded_member (C ⊕ W) i) G).
    change (D ⊢C ((i ⧀ σ n) ∧ phi[i..])).
    assert (HD : has_comprehension_context D).
    { unfold D. apply has_comprehension_cons. exact HG. }
    assert (HM : D ⊢C coded_member (C ⊕ W) i).
    { apply Ctx. unfold D. now left. }
    pose proof (weaken_head G (pow2 (σ n) (W ⊕ W)) (coded_member (C ⊕ W) i) Hnext) as HnextD.
    pose proof (weaken_head G ((C ⊕ W) ⧀ (W ⊕ W)) (coded_member (C ⊕ W) i) Hsmall) as HsmallD.
    pose proof (code_below_endpoint_support D (C ⊕ W) (σ n) (W ⊕ W) i
      (comprehension_has_comparison D HD) HnextD HsmallD HM) as Hin.
    pose proof (power_successor_split_at D i n
      (bounded_has_power_divisor D (comprehension_has_bounded D HD)) Hin) as Hsplit.
    apply CI; [exact Hin|]. eapply DE; [exact Hsplit| |].
    + set (E := List.cons (i ⧀ n) D).
      change (E ⊢C phi[i..]).
      assert (HE : has_bounded_arithmetic E).
      { apply comprehension_has_bounded. unfold E. apply has_comprehension_cons. exact HD. }
      assert (Hi : E ⊢C (i ⧀ n)).
      { apply Ctx. unfold E. now left. }
      pose proof (weaken_head D (pow2 n W) (i ⧀ n)
        (weaken_head G (pow2 n W) (coded_member (C ⊕ W) i) HW)) as HWE.
      assert (HME : E ⊢C coded_member (C ⊕ W) i).
      { apply Ctx. unfold E, D. right. now left. }
      pose proof (low_member_period_without_totality E C i n W HE HWE Hi) as Hperiod.
      pose proof (IE (CE2 Hperiod) HME) as Hold.
      pose proof (weaken_head D (bounded_code_body phi n C) (i ⧀ n)
        (weaken_head G (bounded_code_body phi n C) (coded_member (C ⊕ W) i) Hbody)) as HbodyE.
      exact (CE2 (IE (CE1 (bounded_body_at E phi n C i HbodyE)) Hold)).
    + set (E := List.cons (i == n) D).
      change (E ⊢C phi[i..]).
      assert (HE : has_bounded_arithmetic E).
      { apply comprehension_has_bounded. unfold E. apply has_comprehension_cons. exact HD. }
      assert (Hi : E ⊢C (i == n)).
      { apply Ctx. unfold E. now left. }
      pose proof (periodic_symmetry E i n (bounded_has_periodic E HE) Hi) as Hni.
      pose proof (weaken_head D phi[n..] (i == n)
        (weaken_head G phi[n..] (coded_member (C ⊕ W) i) Hphi)) as HphiE.
      exact (phi_at_equal E phi n i HE Hni HphiE).
  - apply II. set (D := List.cons ((i ⧀ σ n) ∧ phi[i..]) G).
    change (D ⊢C coded_member (C ⊕ W) i).
    assert (HD : has_comprehension_context D).
    { unfold D. apply has_comprehension_cons. exact HG. }
    assert (HR : D ⊢C ((i ⧀ σ n) ∧ phi[i..])).
    { apply Ctx. unfold D. now left. }
    pose proof (power_successor_split_at D i n
      (bounded_has_power_divisor D (comprehension_has_bounded D HD)) (CE1 HR)) as Hsplit.
    eapply DE; [exact Hsplit| |].
    + set (E := List.cons (i ⧀ n) D).
      change (E ⊢C coded_member (C ⊕ W) i).
      assert (HE : has_bounded_arithmetic E).
      { apply comprehension_has_bounded. unfold E. apply has_comprehension_cons. exact HD. }
      assert (Hi : E ⊢C (i ⧀ n)).
      { apply Ctx. unfold E. now left. }
      pose proof (weaken_head D (pow2 n W) (i ⧀ n)
        (weaken_head G (pow2 n W) ((i ⧀ σ n) ∧ phi[i..]) HW)) as HWE.
      pose proof (weaken_head D (bounded_code_body phi n C) (i ⧀ n)
        (weaken_head G (bounded_code_body phi n C) ((i ⧀ σ n) ∧ phi[i..]) Hbody)) as HbodyE.
      assert (HR' : E ⊢C ((i ⧀ σ n) ∧ phi[i..])).
      { apply Ctx. unfold E, D. right. now left. }
      assert (Htarget : E ⊢C ((i ⧀ n) ∧ phi[i..])).
      { apply CI; [exact Hi|exact (CE2 HR')]. }
      pose proof (IE (CE2 (bounded_body_at E phi n C i HbodyE)) Htarget) as Hold.
      exact (IE (CE1 (low_member_period_without_totality E C i n W HE HWE Hi)) Hold).
    + set (E := List.cons (i == n) D).
      change (E ⊢C coded_member (C ⊕ W) i).
      assert (HE : has_bounded_arithmetic E).
      { apply comprehension_has_bounded. unfold E. apply has_comprehension_cons. exact HD. }
      assert (Hi : E ⊢C (i == n)).
      { apply Ctx. unfold E. now left. }
      pose proof (periodic_symmetry E i n (bounded_has_periodic E HE) Hi) as Hni.
      pose proof (weaken_head D (coded_member (C ⊕ W) n) (i == n)
        (weaken_head G (coded_member (C ⊕ W) n) ((i ⧀ σ n) ∧ phi[i..]) Hnewbit)) as HnewE.
      exact (member_at_equal E (C ⊕ W) n i HE Hni HnewE).
Qed.
Lemma code_step_negative G phi n W C : has_comprehension_context G ->
  G ⊢C code_certificate phi n W C -> G ⊢C ¬ phi[n..] ->
  G ⊢C code_exists phi (σ n).
Proof.
  intros HG Hcode Hnot.
  pose proof (comprehension_has_bounded G HG) as HB.
  pose proof (bounded_has_periodic G HB) as Hper.
  pose proof (CE1 Hcode) as HW.
  pose proof (CE1 (CE2 Hcode)) as HC.
  pose proof (CE2 (CE2 Hcode)) as Hbody.
  pose proof (comprehension_power_successor G n W HG HW) as Hnext.
  pose proof (right_bound_at G W W (periodic_has_bit G Hper)) as HWdouble.
  pose proof (IE (IE (PARemainderUnique238.strict_weak_at G C W (W ⊕ W) (periodic_has_quotient G Hper)) HC) HWdouble) as Hsmall.
  apply (code_exists_introduce G phi (σ n) (W ⊕ W) C).
  unfold code_certificate. apply CI; [exact Hnext|]. apply CI; [exact Hsmall|].
  apply bounded_body_introduce. intros i. apply CI.
  - apply II. set (D := List.cons (coded_member C i) G).
    change (D ⊢C ((i ⧀ σ n) ∧ phi[i..])).
    assert (HD : has_comprehension_context D).
    { unfold D. apply has_comprehension_cons. exact HG. }
    assert (HM : D ⊢C coded_member C i).
    { apply Ctx. unfold D. now left. }
    pose proof (weaken_head G (bounded_code_body phi n C) (coded_member C i) Hbody) as HbodyD.
    pose proof (IE (CE1 (bounded_body_at D phi n C i HbodyD)) HM) as Hpair.
    apply CI; [|exact (CE2 Hpair)].
    exact (PAOrderGrowth238.strict_upper_successor D i n
      (trace_has_quotient D (bounded_has_trace D (comprehension_has_bounded D HD))) (CE1 Hpair)).
  - apply II. set (D := List.cons ((i ⧀ σ n) ∧ phi[i..]) G).
    change (D ⊢C coded_member C i).
    assert (HD : has_comprehension_context D).
    { unfold D. apply has_comprehension_cons. exact HG. }
    assert (HR : D ⊢C ((i ⧀ σ n) ∧ phi[i..])).
    { apply Ctx. unfold D. now left. }
    pose proof (power_successor_split_at D i n
      (bounded_has_power_divisor D (comprehension_has_bounded D HD)) (CE1 HR)) as Hsplit.
    eapply DE; [exact Hsplit| |].
    + set (E := List.cons (i ⧀ n) D).
      change (E ⊢C coded_member C i).
      assert (Hi : E ⊢C (i ⧀ n)).
      { apply Ctx. unfold E. now left. }
      pose proof (weaken_head D (bounded_code_body phi n C) (i ⧀ n)
        (weaken_head G (bounded_code_body phi n C) ((i ⧀ σ n) ∧ phi[i..]) Hbody)) as HbodyE.
      assert (HR' : E ⊢C ((i ⧀ σ n) ∧ phi[i..])).
      { apply Ctx. unfold E, D. right. now left. }
      apply (IE (CE2 (bounded_body_at E phi n C i HbodyE))).
      apply CI; [exact Hi|exact (CE2 HR')].
    + set (E := List.cons (i == n) D).
      change (E ⊢C coded_member C i). apply Exp.
      assert (HE : has_bounded_arithmetic E).
      { apply comprehension_has_bounded. unfold E. apply has_comprehension_cons. exact HD. }
      assert (Hi : E ⊢C (i == n)).
      { apply Ctx. unfold E. now left. }
      assert (HR' : E ⊢C ((i ⧀ σ n) ∧ phi[i..])).
      { apply Ctx. unfold E, D. right. now left. }
      pose proof (phi_at_equal E phi i n HE Hi (CE2 HR')) as HphiE.
      pose proof (weaken_head D (¬ phi[n..]) (i == n)
        (weaken_head G (¬ phi[n..]) ((i ⧀ σ n) ∧ phi[i..]) Hnot)) as HnotE.
      exact (IE HnotE HphiE).
Qed.
Lemma code_successor G phi n : has_comprehension_context G ->
  G ⊢C code_exists phi n -> G ⊢C code_exists phi (σ n).
Proof.
  intros HG HC. eapply code_exists_eliminate; [exact HC|]. intros W C.
  set (D := List.cons (code_certificate phi n W C) G).
  change (D ⊢C code_exists phi (σ n)).
  assert (HD : has_comprehension_context D).
  { unfold D. apply has_comprehension_cons. exact HG. }
  assert (Hcertificate : D ⊢C code_certificate phi n W C).
  { apply Ctx. unfold D. now left. }
  eapply XMc with (phi := phi[n..]).
  - set (E := List.cons phi[n..] D).
    apply (code_step_positive E phi n W C).
    + unfold E. apply has_comprehension_cons. exact HD.
    + exact (weaken_head D (code_certificate phi n W C) phi[n..] Hcertificate).
    + apply Ctx. unfold E. now left.
  - set (E := List.cons (¬ phi[n..]) D).
    apply (code_step_negative E phi n W C).
    + unfold E. apply has_comprehension_cons. exact HD.
    + exact (weaken_head D (code_certificate phi n W C) (¬ phi[n..]) Hcertificate).
    + apply Ctx. unfold E. now left.
Qed.


Definition code_induction_formula (phi : pa_form) : pa_form :=
  code_exists phi[up ↑] $0.
Lemma protected_successor_parameters (phi : pa_form) :
  phi[up ↑][up (σ $0 .: S >> var)] = phi[up ↑].
Proof.
  rewrite subst_comp. apply subst_ext. intros [|k];
    cbn [up scons funcomp subst_term]; reflexivity.
Qed.
Lemma code_induction_base phi : paeq_derivable trace_append_sentence ->
  paeq_derivable (code_induction_formula phi)[zero..].
Proof.
  intros HP. unfold code_induction_formula.
  rewrite code_exists_subst, member_shift_cancel.
  apply (comprehension_proof _ HP), code_zero. exact comprehension_context_self.
Qed.
Lemma code_induction_step phi : paeq_derivable trace_append_sentence ->
  paeq_derivable (∀ (code_induction_formula phi →
    (code_induction_formula phi)[σ $0 .: S >> var])).
Proof.
  intros HP. unfold code_induction_formula.
  rewrite code_exists_subst, protected_successor_parameters.
  change (paeq_derivable (∀ (code_exists phi[up ↑] $0 → code_exists phi[up ↑] (σ $0)))).
  apply paeq_generalize, (comprehension_proof _ HP), II.
  set (G := List.cons (code_exists phi[up ↑] $0) comprehension_context).
  apply (code_successor G phi[up ↑] $0).
  - unfold G. apply has_comprehension_cons. exact comprehension_context_self.
  - apply Ctx. unfold G. now left.
Qed.
Theorem bounded_codes_from_trace_append phi : paeq_derivable trace_append_sentence ->
  paeq_derivable (∀ code_induction_formula phi).
Proof.
  intros HP. apply (paeq_induction_rule (code_induction_formula phi)).
  - exact (code_induction_base phi HP).
  - exact (code_induction_step phi HP).
Qed.
Lemma bounded_code_from_invariant G phi n :
  G ⊢C code_exists phi n -> G ⊢C bounded_code phi n.
Proof.
  intros HC. eapply code_exists_eliminate; [exact HC|]. intros W C.
  set (D := List.cons (code_certificate phi n W C) G).
  change (D ⊢C bounded_code phi n). unfold bounded_code.
  apply (ExI C). rewrite bounded_code_witness.
  eapply CE2, CE2, Ctx. unfold D. now left.
Qed.
Theorem bounded_comprehension_from_trace_append phi :
  paeq_derivable trace_append_sentence -> paeq_derivable (bounded_comprehension phi).
Proof.
  intros HP. destruct (bounded_codes_from_trace_append phi HP) as (A & HA & HD).
  exists A. split; [exact HA|]. rewrite bounded_comprehension_body.
  apply AllI_named. intros n. rewrite bounded_axiom_at.
  apply bounded_code_from_invariant.
  pose proof (AllE n HD) as H.
  change (A ⊢C (code_induction_formula phi)[n..]) in H.
  unfold code_induction_formula in H. rewrite code_exists_subst,
    member_shift_cancel in H. exact H.
Qed.
Theorem actual_bounded_comprehension : bounded_comprehension_goal.
Proof.
  intros phi. apply paeq_close, bounded_comprehension_from_trace_append.
  exact PABetaTraceAppend238.trace_append.
Qed.

End PABoundedComprehension238.

Print Assumptions PABoundedComprehension238.finite_context_discharge.
Print Assumptions PABoundedComprehension238.actual_low_member_period.

Print Assumptions PABoundedComprehension238.low_member_period_without_totality.
Print Assumptions PABoundedComprehension238.larger_power_weak_bound.

Print Assumptions PABoundedComprehension238.actual_code_endpoint_support.
Print Assumptions PABoundedComprehension238.strict_add_right.

Print Assumptions PABoundedComprehension238.code_zero.

Print Assumptions PABoundedComprehension238.code_step_positive.
Print Assumptions PABoundedComprehension238.code_step_negative.
Print Assumptions PABoundedComprehension238.code_successor.

Print Assumptions PABoundedComprehension238.actual_bounded_comprehension.
