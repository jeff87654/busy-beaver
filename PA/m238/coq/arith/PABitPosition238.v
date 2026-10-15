(* Original finite PA position bound for the literal Ackermann bit formula.
   The code row lies above its power endpoint. Combine that weak bound with
   the actual conditional trace-index certificate to obtain x<a, then the
   already constructed order-irreflexivity proof supplies compact IR. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAEqCongruence238 PAOrderBounds238
  PAQuotient238 PARemainderUnique238 CompactInPA238 PAPowerTrace238 PAPowerBound238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAOrderBounds238
  PAQuotient238 PARemainderUnique238 CompactInPA238 PAPowerTrace238 PAPowerBound238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PABitPosition238.

Definition power_bound_sentence : pa_form := ∀ ∀ (pow2 $1 $0 → $1 ⧀ $0).
Definition right_bound_sentence : pa_form := ∀ ∀ ($1 ⧀= ($0 ⊕ $1)).
Definition right_extension_sentence : pa_form := ∀ ∀ ∀ ($0 ⧀= $1 → $0 ⧀= ($1 ⊕ $2)).
Definition bit_context : list pa_form :=
  List.cons power_bound_sentence (List.cons right_bound_sentence
    (List.cons right_extension_sentence trace_context)).
Definition has_bit_context (G : list pa_form) : Prop :=
  forall phi, List.In phi bit_context -> List.In phi G.
Lemma bit_proof phi : bit_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := power_bound_sentence);
    [|exact pow2_strict_bound].
  eapply paeq_modus_ponens with (phi := right_bound_sentence);
    [|exact addition_right_bound].
  eapply paeq_modus_ponens with (phi := right_extension_sentence);
    [|exact weak_order_right_extension].
  apply trace_proof, II, II, II. exact HD.
Qed.
Lemma bit_context_self : has_bit_context bit_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_bit_cons G phi : has_bit_context G -> has_bit_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma bit_has_trace G : has_bit_context G -> has_trace_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold bit_context.
  right. right. right. exact Hphi.
Qed.
Lemma power_bound_at G n p : has_bit_context G ->
  G ⊢C pow2 n p -> G ⊢C (n ⧀ p).
Proof.
  intros HG HP. assert (HH : G ⊢C power_bound_sentence).
  { apply Ctx, HG. unfold bit_context. now left. }
  assert (HB : bounded 2 (pow2 $1 $0 → $1 ⧀ $0)).
  { unfold pow2, beta, beta_modulus, PAlt. solve_bounds. }
  pose proof (subst_forall_prv (phi := pow2 $1 $0 → $1 ⧀ $0)
    (N := 2) HH HB (p .: n .: var)) as HK.
  change (G ⊢C (pow2 $1 $0)[p .: n .: var] → (PAlt $1 $0)[p .: n .: var]) in HK.
  rewrite pow2_subst, PAlt_subst in HK.
  change (G ⊢C (pow2 n p → n ⧀ p)) in HK. exact (IE HK HP).
Qed.
Lemma right_bound_at G u p : has_bit_context G -> G ⊢C (p ⧀= (u ⊕ p)).
Proof.
  intros HG. assert (HH : G ⊢C right_bound_sentence).
  { apply Ctx, HG. unfold bit_context. right. now left. }
  assert (HB : bounded 2 ($1 ⧀= ($0 ⊕ $1))).
  { unfold PAle. solve_bounds. }
  pose proof (subst_forall_prv (phi := $1 ⧀= ($0 ⊕ $1))
    (N := 2) HH HB (u .: p .: var)) as HK.
  rewrite PAle_subst in HK. change (G ⊢C (p ⧀= (u ⊕ p))) in HK. exact HK.
Qed.
Lemma right_extension_at G x y r : has_bit_context G ->
  G ⊢C (x ⧀= y) -> G ⊢C (x ⧀= (y ⊕ r)).
Proof.
  intros HG HL. assert (HH : G ⊢C right_extension_sentence).
  { apply Ctx, HG. unfold bit_context. right. right. now left. }
  assert (HB : bounded 3 ($0 ⧀= $1 → $0 ⧀= ($1 ⊕ $2))).
  { unfold PAle. solve_bounds. }
  pose proof (subst_forall_prv (phi := $0 ⧀= $1 → $0 ⧀= ($1 ⊕ $2))
    (N := 3) HH HB (x .: y .: r .: var)) as HK.
  change (G ⊢C (PAle $0 $1)[x .: y .: r .: var] →
    (PAle $0 ($1 ⊕ $2))[x .: y .: r .: var]) in HK.
  rewrite !PAle_subst in HK.
  change (G ⊢C (x ⧀= y → x ⧀= (y ⊕ r))) in HK. exact (IE HK HL).
Qed.
Lemma weak_upper_transport G x y z : has_bit_context G ->
  G ⊢C (x ⧀= y) -> G ⊢C (y == z) -> G ⊢C (x ⧀= z).
Proof.
  intros HG HL HEQ. unfold PAle in HL.
  eapply ExE_named; [exact HL|]. intros d.
  change ((List.cons (y`[↑]`[d..] == x`[↑]`[d..] ⊕ d) G) ⊢C (x ⧀= z)).
  rewrite (@subst_term_shift PA_funcs_signature y d),
    (@subst_term_shift PA_funcs_signature x d).
  set (D := List.cons (y == x ⊕ d) G).
  change (D ⊢C (x ⧀= z)).
  assert (HD : has_bit_context D).
  { unfold D. apply has_bit_cons. exact HG. }
  pose proof (trace_has_equality D (bit_has_trace D HD)) as HE.
  pose proof (weaken_head G (y == z) (y == x ⊕ d) HEQ) as HYZ.
  pose proof (equality_symmetry D y z HE HYZ) as HZY.
  assert (HY : D ⊢C (y == x ⊕ d)).
  { apply Ctx. unfold D. now left. }
  apply (weak_order_witness D x z d).
  exact (equality_transitivity D z y (x ⊕ d) HE HZY HY).
Qed.

Definition bit_row (q p r : pa_term) : pa_term := ((q ⊗ (p ⊕ p)) ⊕ p) ⊕ r.
Definition bit_pair (a p q r : pa_term) : pa_form := (a == bit_row q p r) ∧ (r ⧀ p).
Definition bit_tail (a p : pa_term) : pa_form :=
  ∃ ∃ bit_pair a`[↑]`[↑] p`[↑]`[↑] $1 $0.
Definition bit_witness (a x p : pa_term) : pa_form := pow2 x p ∧ bit_tail a p.
Lemma bit_row_subst q p r rho :
  (bit_row q p r)`[rho] = bit_row q`[rho] p`[rho] r`[rho].
Proof. reflexivity. Qed.
Lemma bit_pair_subst a p q r rho :
  (bit_pair a p q r)[rho] = bit_pair a`[rho] p`[rho] q`[rho] r`[rho].
Proof.
  unfold bit_pair. change (((a`[rho] == (bit_row q p r)`[rho]) ∧ (PAlt r p)[rho]) =
    bit_pair a`[rho] p`[rho] q`[rho] r`[rho]).
  rewrite bit_row_subst, PAlt_subst. reflexivity.
Qed.
Lemma bit_tail_subst a p rho :
  (bit_tail a p)[rho] = bit_tail a`[rho] p`[rho].
Proof.
  unfold bit_tail. cbn [subst_form]. rewrite bit_pair_subst. now rewrite !up_term.
Qed.
Lemma bit_witness_subst a x p rho :
  (bit_witness a x p)[rho] = bit_witness a`[rho] x`[rho] p`[rho].
Proof.
  unfold bit_witness. cbn [subst_form]. rewrite pow2_subst, bit_tail_subst. reflexivity.
Qed.
Lemma ackermann_witness a x : ackermann_bit a x = ∃ bit_witness a`[↑] x`[↑] $0.
Proof. reflexivity. Qed.
Lemma bit_eliminate G a x (psi : pa_form) :
  G ⊢C ackermann_bit a x ->
  (forall p, (List.cons (bit_witness a x p) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. rewrite ackermann_witness in HX.
  eapply ExE_named; [exact HX|]. intros p.
  rewrite bit_witness_subst, !subst_term_shift. exact (H p).
Qed.
Lemma bit_tail_eliminate G a p (psi : pa_form) :
  G ⊢C bit_tail a p ->
  (forall q r, (List.cons (bit_pair a p q r) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. unfold bit_tail in HX.
  eapply ExE_named; [exact HX|]. intros q.
  cbn [subst_form]. rewrite bit_pair_subst, !up_term, !subst_term_shift.
  set (D := List.cons (∃ bit_pair a`[↑] p`[↑] q`[↑] $0) G).
  change (D ⊢C psi).
  assert (HY : D ⊢C ∃ bit_pair a`[↑] p`[↑] q`[↑] $0).
  { apply Ctx. unfold D. now left. }
  eapply ExE_named; [exact HY|]. intros r.
  rewrite bit_pair_subst, !subst_term_shift.
  change ((List.cons (bit_pair a p q r) D) ⊢C psi).
  eapply Weak; [exact (H q r)|]. intros chi Hchi.
  destruct Hchi as [<-|Hchi]; [now left|right; unfold D; now right].
Qed.
Lemma bit_row_lower G q p r : has_bit_context G -> G ⊢C (p ⧀= bit_row q p r).
Proof.
  intros HG. pose proof (right_bound_at G (q ⊗ (p ⊕ p)) p HG) as HB.
  exact (right_extension_at G p ((q ⊗ (p ⊕ p)) ⊕ p) r HG HB).
Qed.
Lemma bit_position G a x : has_bit_context G ->
  G ⊢C coded_member a x -> G ⊢C (x ⧀ a).
Proof.
  intros HG HX. unfold coded_member in HX.
  eapply bit_eliminate; [exact HX|]. intros p.
  set (D := List.cons (bit_witness a x p) G).
  change (D ⊢C (x ⧀ a)).
  assert (HD : has_bit_context D).
  { unfold D. apply has_bit_cons. exact HG. }
  assert (HW : D ⊢C bit_witness a x p).
  { apply Ctx. unfold D. now left. }
  pose proof (power_bound_at D x p HD (CE1 HW)) as Hxp.
  pose proof (CE2 HW) as Htail.
  eapply bit_tail_eliminate; [exact Htail|]. intros q r.
  set (E := List.cons (bit_pair a p q r) D).
  change (E ⊢C (x ⧀ a)).
  assert (HE : has_bit_context E).
  { unfold E. apply has_bit_cons. exact HD. }
  assert (HC : E ⊢C bit_pair a p q r).
  { apply Ctx. unfold E. now left. }
  pose proof (CE1 HC) as HEQ.
  pose proof (equality_symmetry E a (bit_row q p r)
    (trace_has_equality E (bit_has_trace E HE)) HEQ) as Hback.
  pose proof (weak_upper_transport E p (bit_row q p r) a HE
    (bit_row_lower E q p r HE) Hback) as Hpa.
  pose proof (weaken_head D (x ⧀ p) (bit_pair a p q r) Hxp) as Hlt.
  exact (IE (IE (strict_weak_at E x p a
    (trace_has_quotient E (bit_has_trace E HE))) Hlt) Hpa).
Qed.

Theorem actual_bit_position : bit_position_goal.
Proof.
  unfold bit_position_goal. apply paeq_generalize, paeq_generalize, bit_proof, II.
  set (G := List.cons (coded_member $1 $0) bit_context).
  apply (bit_position G $1 $0).
  - unfold G. apply has_bit_cons. exact bit_context_self.
  - apply Ctx. unfold G. now left.
Qed.
Corollary actual_ir_producer : ir_producer_goal.
Proof. apply ir_from_position. exact actual_bit_position. Qed.

End PABitPosition238.

Print Assumptions PABitPosition238.bit_proof.
Print Assumptions PABitPosition238.actual_bit_position.
Print Assumptions PABitPosition238.actual_ir_producer.
