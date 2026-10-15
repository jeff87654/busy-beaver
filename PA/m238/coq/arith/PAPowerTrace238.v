(* Original finite PA certificates for the actual beta-coded doubling trace.
   A zero endpoint is one. A successor trace has a predecessor endpoint
   and that endpoint doubles to the current value. Existence of a power
   trace is never assumed globally. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238
  PAOrderBounds238 PAQuotient238 PAOrderGrowth238 PABetaUnique238 CompactInPA238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAQuotient238
  PAOrderGrowth238 PABetaUnique238 CompactInPA238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAPowerTrace238.

Definition doubling_pair (b c i r s : pa_term) : pa_form :=
  beta b c i r ∧ (beta b c (σ i) s ∧ (s == r ⊕ r)).
Definition doubling_step (b c i : pa_term) : pa_form :=
  ∃ ∃ doubling_pair b`[↑]`[↑] c`[↑]`[↑] i`[↑]`[↑] $1 $0.
Definition trace_steps (b c n : pa_term) : pa_form :=
  ∀ ($0 ⧀ n`[↑] → doubling_step b`[↑] c`[↑] $0).
Definition trace_body (b c n p : pa_term) : pa_form :=
  beta b c zero (σ zero) ∧ (beta b c n p ∧ trace_steps b c n).

Lemma doubling_pair_subst b c i r s rho :
  (doubling_pair b c i r s)[rho] =
  doubling_pair b`[rho] c`[rho] i`[rho] r`[rho] s`[rho].
Proof.
  unfold doubling_pair. change ((beta b c i r)[rho] ∧
    ((beta b c (σ i) s)[rho] ∧ (s`[rho] == r`[rho] ⊕ r`[rho])) =
    doubling_pair b`[rho] c`[rho] i`[rho] r`[rho] s`[rho]).
  rewrite !beta_subst. reflexivity.
Qed.
Lemma doubling_step_subst b c i rho :
  (doubling_step b c i)[rho] = doubling_step b`[rho] c`[rho] i`[rho].
Proof.
  unfold doubling_step. cbn [subst_form]. rewrite doubling_pair_subst.
  now rewrite !up_term.
Qed.
Lemma trace_steps_subst b c n rho :
  (trace_steps b c n)[rho] = trace_steps b`[rho] c`[rho] n`[rho].
Proof.
  unfold trace_steps. cbn [subst_form]. rewrite PAlt_subst, doubling_step_subst.
  now rewrite !up_term.
Qed.
Lemma trace_body_subst b c n p rho :
  (trace_body b c n p)[rho] = trace_body b`[rho] c`[rho] n`[rho] p`[rho].
Proof.
  unfold trace_body. cbn [subst_form]. rewrite !beta_subst, trace_steps_subst.
  reflexivity.
Qed.
Lemma pow2_trace n p :
  pow2 n p = ∃ ∃ trace_body $1 $0 n`[↑]`[↑] p`[↑]`[↑].
Proof. reflexivity. Qed.

Definition beta_unique_sentence : pa_form := ∀ ∀ ∀ ∀ ∀
  (beta $0 $1 $2 $3 → beta $0 $1 $2 $4 → $3 == $4).
Definition trace_context : list pa_form := List.cons beta_unique_sentence beta_context.
Definition has_trace_context (G : list pa_form) : Prop :=
  forall phi, List.In phi trace_context -> List.In phi G.
Lemma trace_proof phi : trace_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := beta_unique_sentence).
  - apply beta_proof, II. exact HD.
  - exact beta_unique.
Qed.
Lemma trace_context_self : has_trace_context trace_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_trace_cons G phi : has_trace_context G -> has_trace_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma trace_has_quotient G : has_trace_context G -> has_quotient_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold trace_context, beta_context.
  right. right. exact Hphi.
Qed.
Lemma trace_has_equality G : has_trace_context G -> has_equality G.
Proof. intros HG. apply quotient_has_equality, trace_has_quotient. exact HG. Qed.
Lemma beta_unique_at G b c i r s : has_trace_context G ->
  G ⊢C beta b c i r -> G ⊢C beta b c i s -> G ⊢C (r == s).
Proof.
  intros HG HR HS. assert (HH : G ⊢C beta_unique_sentence).
  { apply Ctx, HG. unfold trace_context. now left. }
  assert (HB : bounded 5 (beta $0 $1 $2 $3 → beta $0 $1 $2 $4 → $3 == $4)).
  { unfold beta, beta_modulus, PAlt. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := beta $0 $1 $2 $3 → beta $0 $1 $2 $4 → $3 == $4)
    (N := 5) HH HB (b .: c .: i .: r .: s .: var)) as HK.
  change (G ⊢C (beta $0 $1 $2 $3)[b .: c .: i .: r .: s .: var] →
    (beta $0 $1 $2 $4)[b .: c .: i .: r .: s .: var] → r == s) in HK.
  rewrite !beta_subst in HK.
  change (G ⊢C (beta b c i r → beta b c i s → r == s)) in HK.
  exact (IE (IE HK HR) HS).
Qed.

(* The named elimination lemmas merely hide the two fresh witness scopes.
   They retain the exact arithmetic trace formula, including its bounded
   universally quantified step clause. *)
Lemma doubling_eliminate G b c i (psi : pa_form) :
  G ⊢C doubling_step b c i ->
  (forall r s, (List.cons (doubling_pair b c i r s) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. unfold doubling_step in HX.
  eapply ExE_named; [exact HX|]. intros r.
  cbn [subst_form]. rewrite doubling_pair_subst.
  rewrite !up_term, !subst_term_shift.
  set (D := List.cons (∃ doubling_pair b`[↑] c`[↑] i`[↑] r`[↑] $0) G).
  change (D ⊢C psi).
  assert (HY : D ⊢C ∃ doubling_pair b`[↑] c`[↑] i`[↑] r`[↑] $0).
  { apply Ctx. unfold D. now left. }
  eapply ExE_named; [exact HY|]. intros s.
  rewrite doubling_pair_subst. rewrite !subst_term_shift.
  change ((List.cons (doubling_pair b c i r s) D) ⊢C psi).
  eapply Weak; [exact (H r s)|]. intros chi Hchi.
  destruct Hchi as [<-|Hchi]; [now left|right; unfold D; now right].
Qed.
Lemma pow2_eliminate G n p (psi : pa_form) :
  G ⊢C pow2 n p ->
  (forall b c, (List.cons (trace_body b c n p) G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros HX H. rewrite pow2_trace in HX.
  eapply ExE_named; [exact HX|]. intros b.
  cbn [subst_form]. rewrite trace_body_subst.
  rewrite !up_term, !subst_term_shift.
  set (D := List.cons (∃ trace_body b`[↑] $0 n`[↑] p`[↑]) G).
  change (D ⊢C psi).
  assert (HY : D ⊢C ∃ trace_body b`[↑] $0 n`[↑] p`[↑]).
  { apply Ctx. unfold D. now left. }
  eapply ExE_named; [exact HY|]. intros c.
  rewrite trace_body_subst. rewrite !subst_term_shift.
  change ((List.cons (trace_body b c n p) D) ⊢C psi).
  eapply Weak; [exact (H b c)|]. intros chi Hchi.
  destruct Hchi as [<-|Hchi]; [now left|right; unfold D; now right].
Qed.
Lemma pow2_introduce G b c n p :
  G ⊢C trace_body b c n p -> G ⊢C pow2 n p.
Proof.
  intros H. rewrite pow2_trace. apply (ExI b).
  cbn [subst_form]. rewrite trace_body_subst.
  rewrite !up_term, !subst_term_shift.
  change (G ⊢C ∃ trace_body b`[↑] $0 n`[↑] p`[↑]).
  apply (ExI c). rewrite trace_body_subst, !subst_term_shift.
  exact H.
Qed.
Lemma trace_steps_at G b c n i :
  G ⊢C trace_steps b c n -> G ⊢C (i ⧀ n → doubling_step b c i).
Proof.
  intros H. pose proof (AllE i H) as HK.
  change (G ⊢C (PAlt $0 n`[↑])[i..] →
    (doubling_step b`[↑] c`[↑] $0)[i..]) in HK.
  rewrite PAlt_subst, doubling_step_subst, !subst_term_shift in HK.
  exact HK.
Qed.
Lemma trace_steps_introduce G b c n :
  (forall i, G ⊢C (i ⧀ n → doubling_step b c i)) -> G ⊢C trace_steps b c n.
Proof.
  intros H. unfold trace_steps. apply AllI_named. intros i.
  change (G ⊢C (PAlt $0 n`[↑])[i..] →
    (doubling_step b`[↑] c`[↑] $0)[i..]).
  rewrite PAlt_subst, doubling_step_subst, !subst_term_shift. exact (H i).
Qed.
Lemma trace_steps_prefix G b c n : has_trace_context G ->
  G ⊢C trace_steps b c (σ n) -> G ⊢C trace_steps b c n.
Proof.
  intros HG Hsteps. apply trace_steps_introduce. intros i. apply II.
  set (D := List.cons (i ⧀ n) G).
  change (D ⊢C doubling_step b c i).
  assert (HD : has_quotient_context D).
  { unfold D. apply has_quotient_cons, trace_has_quotient. exact HG. }
  assert (HI : D ⊢C (i ⧀ n)).
  { apply Ctx. unfold D. now left. }
  pose proof (strict_upper_successor D i n HD HI) as HS.
  pose proof (weaken_head G (trace_steps b c (σ n)) (i ⧀ n) Hsteps) as HT.
  exact (IE (trace_steps_at D b c (σ n) i HT) HS).
Qed.

Lemma zero_endpoint G p : has_trace_context G ->
  G ⊢C pow2 zero p -> G ⊢C (p == σ zero).
Proof.
  intros HG HP. eapply pow2_eliminate; [exact HP|]. intros b c.
  set (D := List.cons (trace_body b c zero p) G).
  change (D ⊢C (p == σ zero)).
  assert (HD : has_trace_context D).
  { unfold D. apply has_trace_cons. exact HG. }
  assert (HI : D ⊢C trace_body b c zero p).
  { apply Ctx. unfold D. now left. }
  assert (Hone : D ⊢C beta b c zero (σ zero)).
  { exact (CE1 HI). }
  assert (Hp : D ⊢C beta b c zero p).
  { exact (CE1 (CE2 HI)). }
  pose proof (beta_unique_at D b c zero (σ zero) p HD Hone Hp) as HEQ.
  exact (equality_symmetry D (σ zero) p (trace_has_equality D HD) HEQ).
Qed.

Definition predecessor_endpoint (n p : pa_term) : pa_form :=
  ∃ (pow2 n`[↑] $0 ∧ (p`[↑] == $0 ⊕ $0)).
Lemma predecessor_endpoint_subst n p rho :
  (predecessor_endpoint n p)[rho] = predecessor_endpoint n`[rho] p`[rho].
Proof.
  unfold predecessor_endpoint.
  change ((∃ ((pow2 n`[↑] $0)[up rho] ∧
    (p`[↑]`[up rho] == $0 ⊕ $0))) =
    ∃ (pow2 n`[rho]`[↑] $0 ∧ (p`[rho]`[↑] == $0 ⊕ $0))).
  rewrite pow2_subst, !up_term. reflexivity.
Qed.
Lemma predecessor_endpoint_intro G n p r :
  G ⊢C pow2 n r -> G ⊢C (p == r ⊕ r) -> G ⊢C predecessor_endpoint n p.
Proof.
  intros HP HE. unfold predecessor_endpoint. apply (ExI r).
  change (G ⊢C ((pow2 n`[↑] $0)[r..] ∧ (p`[↑]`[r..] == r ⊕ r))).
  assert (HN : n`[↑]`[r..] = n) by apply subst_term_shift.
  assert (HEnd : p`[↑]`[r..] = p) by apply subst_term_shift.
  rewrite pow2_subst.
  change (G ⊢C (pow2 n`[↑]`[r..] r ∧ (p`[↑]`[r..] == r ⊕ r))).
  rewrite HN, HEnd. apply CI; assumption.
Qed.
Lemma successor_endpoint G n p : has_trace_context G ->
  G ⊢C pow2 (σ n) p -> G ⊢C predecessor_endpoint n p.
Proof.
  intros HG HP. eapply pow2_eliminate; [exact HP|]. intros b c.
  set (D := List.cons (trace_body b c (σ n) p) G).
  change (D ⊢C predecessor_endpoint n p).
  assert (HD : has_trace_context D).
  { unfold D. apply has_trace_cons. exact HG. }
  assert (Hbody : D ⊢C trace_body b c (σ n) p).
  { apply Ctx. unfold D. now left. }
  pose proof (CE2 (CE2 Hbody)) as Hsteps.
  pose proof (successor_self D n (trace_has_quotient D HD)) as Hns.
  pose proof (IE (trace_steps_at D b c (σ n) n Hsteps) Hns) as Hpair.
  eapply doubling_eliminate; [exact Hpair|]. intros r s.
  set (E := List.cons (doubling_pair b c n r s) D).
  change (E ⊢C predecessor_endpoint n p).
  assert (HE : has_trace_context E).
  { unfold E. apply has_trace_cons. exact HD. }
  assert (HC : E ⊢C doubling_pair b c n r s).
  { apply Ctx. unfold E. now left. }
  pose proof (weaken_head D (trace_body b c (σ n) p) (doubling_pair b c n r s) Hbody) as Hwhole.
  pose proof (CE1 (CE2 Hwhole)) as Hcurrent.
  pose proof (CE1 (CE2 HC)) as Hnext.
  pose proof (beta_unique_at E b c (σ n) p s HE Hcurrent Hnext) as Hps.
  pose proof (CE2 (CE2 HC)) as Hdouble.
  pose proof (equality_transitivity E p s (r ⊕ r) (trace_has_equality E HE) Hps Hdouble) as Hvalue.
  apply (predecessor_endpoint_intro E n p r); [|exact Hvalue].
  apply (pow2_introduce E b c n r), CI.
  - exact (CE1 Hwhole).
  - apply CI.
    + exact (CE1 HC).
    + apply (trace_steps_prefix E b c n HE). exact (CE2 (CE2 Hwhole)).
Qed.

Theorem pow2_zero_endpoint : paeq_derivable (∀ (pow2 zero $0 → $0 == σ zero)).
Proof.
  apply paeq_generalize, trace_proof, II.
  set (G := List.cons (pow2 zero $0) trace_context).
  apply (zero_endpoint G $0).
  - unfold G. apply has_trace_cons. exact trace_context_self.
  - apply Ctx. unfold G. now left.
Qed.
Theorem pow2_predecessor_endpoint :
  paeq_derivable (∀ ∀ (pow2 (σ $0) $1 → predecessor_endpoint $0 $1)).
Proof.
  apply paeq_generalize, paeq_generalize, trace_proof, II.
  set (G := List.cons (pow2 (σ $0) $1) trace_context).
  apply (successor_endpoint G $0 $1).
  - unfold G. apply has_trace_cons. exact trace_context_self.
  - apply Ctx. unfold G. now left.
Qed.

End PAPowerTrace238.

Print Assumptions PAPowerTrace238.trace_proof.
Print Assumptions PAPowerTrace238.pow2_zero_endpoint.
Print Assumptions PAPowerTrace238.pow2_predecessor_endpoint.
