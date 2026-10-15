(* Original finite ordinary-PA trace append certificate.
   Bounded CRT induction supplies the recoded prefix and the new endpoint.
   Every context supplier below is discharged by an actual PA derivation. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAAddition238 PAEqCongruence238
  PAOrderBounds238 PASemiring238 PAMultiplicationComm238 PAModuliInverse238
  PACommonMultiple238 CompactInPA238 PAPowerTrace238 PAPowerExtension238
  PACRTAccumulator238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrderBounds238
  PASemiring238 PAMultiplicationComm238 PAModuliInverse238 PACommonMultiple238
  CompactInPA238 PAPowerTrace238 PACRTAccumulator238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PABetaTraceAppend238.

Definition large_common_multiple_sentence : pa_form :=
  ∀ ∀ large_common_multiple_exists $0 $1.
Definition trace_append_context : list pa_form :=
  [bounded_accumulator_sentence; large_common_multiple_sentence] ++ coding_context.
Definition has_trace_append_context (G : list pa_form) : Prop :=
  forall phi, List.In phi trace_append_context -> List.In phi G.
Lemma trace_append_proof phi : trace_append_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD.
  eapply paeq_modus_ponens with (phi := bounded_accumulator_sentence);
    [|exact bounded_crt_accumulator].
  eapply paeq_modus_ponens with (phi := large_common_multiple_sentence);
    [|exact arbitrarily_large_common_multiple].
  apply coding_proof, II, II. exact HD.
Qed.
Lemma trace_append_context_self : has_trace_append_context trace_append_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_trace_append_cons G phi : has_trace_append_context G ->
  has_trace_append_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma trace_append_has_coding G : has_trace_append_context G -> has_coding_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold trace_append_context.
  apply List.in_app_iff. now right.
Qed.
Lemma trace_append_has_bounded G : has_trace_append_context G ->
  List.In bounded_accumulator_sentence G.
Proof. intros HG. apply HG. unfold trace_append_context. now left. Qed.
Lemma trace_append_has_large G : has_trace_append_context G ->
  List.In large_common_multiple_sentence G.
Proof. intros HG. apply HG. unfold trace_append_context. right. now left. Qed.

Lemma large_common_multiple_at G n L : List.In large_common_multiple_sentence G ->
  G ⊢C large_common_multiple_exists n L.
Proof.
  intros HH. assert (HAll : G ⊢C large_common_multiple_sentence) by now apply Ctx.
  assert (HB : bounded 2 (large_common_multiple_exists $0 $1)).
  { unfold large_common_multiple_exists, large_common_multiple, common_multiple,
      multiple_rows, divides, PAlt. solve_bounds. }
  pose proof (subst_forall_prv (phi := large_common_multiple_exists $0 $1) (N := 2)
    HAll HB (n .: L .: var)) as HK.
  unfold large_common_multiple_exists in HK.
  change (G ⊢C ∃ (large_common_multiple $0`[↑] $1`[↑] $0)[up (n .: L .: var)]) in HK.
  rewrite large_common_multiple_subst, !up_term in HK.
  exact HK.
Qed.
Lemma large_common_multiple_eliminate G n L (psi : pa_form) :
  G ⊢C large_common_multiple_exists n L ->
  (forall C, (List.cons (large_common_multiple n L C) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. unfold large_common_multiple_exists in HX.
  eapply ExE_named; [exact HX|]. intros C.
  rewrite large_common_multiple_subst, !subst_term_shift. exact (H C).
Qed.

Lemma strict_self_successor G t : has_inverse_context G -> G ⊢C (t ⧀ σ t).
Proof.
  intros HG. apply (strict_order_witness G t (σ t) zero).
  exact (inverse_symmetry G (σ t ⊕ zero) (σ t) HG (inverse_right_zero G (σ t) HG)).
Qed.
Lemma terminal_rows_append_witness G b c n r C z : has_coding_context G ->
  G ⊢C desired_rows b c n r C (σ (σ n)) z ->
  G ⊢C PAPowerExtension238.beta_append_witness b c z C n r.
Proof.
  intros HG HR. pose proof (coding_has_inverse G HG) as HI.
  unfold PAPowerExtension238.beta_append_witness. apply CI.
  - assert (HQ : G ⊢C PAPowerExtension238.append_graph b c n r (σ n) r).
    { unfold PAPowerExtension238.append_graph. apply DI2, CI;
        apply inverse_reflexivity; exact HI. }
    exact (desired_rows_at G b c n r C (σ (σ n)) z (σ n) r HR
      (strict_self_successor G (σ n) HI) HQ).
  - unfold PAPowerExtension238.beta_prefix_recode. apply AllI_named. intros i.
    change (G ⊢C (PAlt $0 (σ n)`[↑])[i..] →
      (PAPowerExtension238.beta_row_transfer b`[↑] c`[↑] z`[↑] C`[↑] $0)[i..]).
    rewrite PAlt_subst, PAPowerExtension238.beta_row_transfer_subst, !subst_term_shift.
    apply II. set (D := List.cons (i ⧀ σ n) G).
    unfold PAPowerExtension238.beta_row_transfer. apply AllI_named. intros v.
    change (D ⊢C (beta b`[↑] c`[↑] i`[↑] $0)[v..] →
      (beta z`[↑] C`[↑] i`[↑] $0)[v..]).
    rewrite !beta_subst, !subst_term_shift. apply II.
    set (E := List.cons (beta b c i v) D).
    assert (HE : has_coding_context E).
    { unfold E, D. apply has_coding_cons, has_coding_cons. exact HG. }
    pose proof (coding_has_inverse E HE) as HIE.
    assert (Hindex : E ⊢C (i ⧀ σ n)).
    { apply Ctx. unfold E, D. right. now left. }
    assert (Hbeta : E ⊢C beta b c i v).
    { apply Ctx. unfold E. now left. }
    assert (Hrows : E ⊢C desired_rows b c n r C (σ (σ n)) z).
    { unfold E, D. apply weaken_head, weaken_head. exact HR. }
    assert (HQ : E ⊢C PAPowerExtension238.append_graph b c n r i v).
    { unfold PAPowerExtension238.append_graph. apply DI1, CI; assumption. }
    pose proof (weak_lower_predecessor E i (σ n) HIE Hindex) as Hweak.
    pose proof (weak_upper_successor E i (σ n) HIE Hweak) as Hrange.
    exact (desired_rows_at E b c n r C (σ (σ n)) z i v Hrows Hrange HQ).
Qed.
Lemma beta_append_exists_intro G b c n r z C :
  G ⊢C PAPowerExtension238.beta_append_witness b c z C n r ->
  G ⊢C PAPowerExtension238.beta_append_exists b c n r.
Proof.
  intros H. unfold PAPowerExtension238.beta_append_exists. apply (ExI z).
  cbn [subst_form]. rewrite PAPowerExtension238.beta_append_witness_subst,
    !up_term, !subst_term_shift.
  change (G ⊢C ∃ PAPowerExtension238.beta_append_witness b`[↑] c`[↑] z`[↑] $0 n`[↑] r`[↑]).
  apply (ExI C). rewrite PAPowerExtension238.beta_append_witness_subst, !subst_term_shift.
  exact H.
Qed.

Lemma trace_append_exists_at G b c n p r : has_trace_append_context G ->
  G ⊢C trace_body b c n p -> G ⊢C PAPowerExtension238.beta_append_exists b c n r.
Proof.
  intros HG HT.
  pose proof (large_common_multiple_at G (σ (σ n)) (b ⊕ r)
    (trace_append_has_large G HG)) as HX.
  eapply large_common_multiple_eliminate; [exact HX|]. intros C.
  set (D := List.cons (large_common_multiple (σ (σ n)) (b ⊕ r) C) G).
  assert (HD : has_trace_append_context D).
  { unfold D. apply has_trace_append_cons. exact HG. }
  assert (Hlarge : D ⊢C large_common_multiple (σ (σ n)) (b ⊕ r) C).
  { apply Ctx. unfold D. now left. }
  assert (HTD : D ⊢C trace_body b c n p).
  { unfold D. apply weaken_head. exact HT. }
  pose proof (bounded_accumulator_at D b c n p r C (σ (σ n))
    (trace_append_has_bounded D HD)) as Hbounded.
  pose proof (weak_reflexive D (σ (σ n))
    (coding_has_inverse D (trace_append_has_coding D HD))) as Hterminal.
  pose proof (IE (IE (IE (IE Hbounded HTD) (CE1 Hlarge)) (CE2 Hlarge)) Hterminal) as Hstate.
  eapply accumulator_exists_eliminate; [exact Hstate|]. intros P z.
  set (E := List.cons (accumulator_state b c n r C (σ n) (σ (σ n)) P z) D).
  assert (HE : has_coding_context E).
  { unfold E. apply has_coding_cons, trace_append_has_coding. exact HD. }
  assert (HS : E ⊢C accumulator_state b c n r C (σ n) (σ (σ n)) P z).
  { apply Ctx. unfold E. now left. }
  apply (beta_append_exists_intro E b c n r z C).
  exact (terminal_rows_append_witness E b c n r C z HE (CE1 (CE2 (CE2 HS)))).
Qed.

Theorem trace_conditioned_beta_append : paeq_derivable (∀ ∀ ∀ ∀ ∀
  (trace_body $0 $1 $2 $3 → PAPowerExtension238.beta_append_exists $0 $1 $2 $4)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, trace_append_proof, II.
  set (G := List.cons (trace_body $0 $1 $2 $3) trace_append_context).
  apply (trace_append_exists_at G $0 $1 $2 $3 $4).
  - unfold G. apply has_trace_append_cons. exact trace_append_context_self.
  - apply Ctx. unfold G. now left.
Qed.
Theorem trace_append : paeq_derivable PAPowerExtension238.trace_append_sentence.
Proof.
  unfold PAPowerExtension238.trace_append_sentence.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, trace_append_proof, II.
  set (G := List.cons (trace_body $0 $1 $2 $3) trace_append_context).
  apply (trace_append_exists_at G $0 $1 $2 $3 ($3 ⊕ $3)).
  - unfold G. apply has_trace_append_cons. exact trace_append_context_self.
  - apply Ctx. unfold G. now left.
Qed.
Theorem pow2_total : paeq_derivable (∀ ∃ pow2 $1 $0).
Proof. exact (PAPowerExtension238.pow2_total_from_trace_append trace_append). Qed.
Theorem pow2_successor : paeq_derivable (∀ ∀
  (pow2 $0 $1 → pow2 (σ $0) ($1 ⊕ $1))).
Proof. exact (PAPowerExtension238.pow2_successor_from_trace_append trace_append). Qed.

End PABetaTraceAppend238.

Print Assumptions PABetaTraceAppend238.trace_append_proof.
Print Assumptions PABetaTraceAppend238.trace_conditioned_beta_append.
Print Assumptions PABetaTraceAppend238.trace_append.
Print Assumptions PABetaTraceAppend238.pow2_total.
Print Assumptions PABetaTraceAppend238.pow2_successor.
