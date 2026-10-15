(* Original syntactic PA proof. No semantic model or meta-level arithmetic
   adequacy hypothesis is used. The final certificate uses a fixed finite
   upstream PAeq context and PA238.paeq_from_upstream closes its axioms. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238.

Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAOrder238.

Definition successor_gap (n : pa_term) : pa_form :=
  ∀ ¬ (n`[↑] == σ n`[↑] ⊕ $0).
Definition gap_induction_formula : pa_form := successor_gap $0.
Definition order_context : list pa_form :=
  [ax_trans; ax_add_rec; ax_zero_succ; ax_succ_inj;
   ax_induction gap_induction_formula].

Lemma successor_gap_subst n rho :
  (successor_gap n)[rho] = successor_gap n`[rho].
Proof. unfold successor_gap. cbn. now rewrite !up_term. Qed.

Lemma eq_trans_instance (G : list pa_form) (a b c : pa_term) :
  List.In ax_trans G -> G ⊢C (a == b → b == c → a == c).
Proof.
  intros H.
  change (G ⊢C ($2 == $1 → $1 == $0 → $2 == $0)
    [c .: b .: a .: var]).
  apply (subst_forall_prv (phi := $2 == $1 → $1 == $0 → $2 == $0) (N := 3)).
  - change (G ⊢C ax_trans). now apply Ctx.
  - solve_bounds.
Qed.

Lemma add_rec_instance (G : list pa_form) (a b : pa_term) :
  List.In ax_add_rec G -> G ⊢C (σ a ⊕ b == σ (a ⊕ b)).
Proof.
  intros H.
  change (G ⊢C (σ $0 ⊕ $1 == σ ($0 ⊕ $1))[a .: b .: var]).
  apply (subst_forall_prv (phi := σ $0 ⊕ $1 == σ ($0 ⊕ $1)) (N := 2)).
  - change (G ⊢C ax_add_rec). now apply Ctx.
  - solve_bounds.
Qed.

Lemma zero_succ_instance (G : list pa_form) (a : pa_term) :
  List.In ax_zero_succ G -> G ⊢C (zero == σ a → falsity).
Proof.
  intros H.
  change (G ⊢C (zero == σ $0 → falsity)[a..]).
  apply (subst_forall_prv (phi := zero == σ $0 → falsity) (N := 1)).
  - change (G ⊢C ax_zero_succ). now apply Ctx.
  - solve_bounds.
Qed.

Lemma succ_inj_instance (G : list pa_form) (a b : pa_term) :
  List.In ax_succ_inj G -> G ⊢C (σ a == σ b → a == b).
Proof.
  intros H.
  change (G ⊢C (σ $1 == σ $0 → $1 == $0)[b .: a .: var]).
  apply (subst_forall_prv (phi := σ $1 == σ $0 → $1 == $0) (N := 2)).
  - change (G ⊢C ax_succ_inj). now apply Ctx.
  - solve_bounds.
Qed.

Lemma gap_instance (G : list pa_form) (n k : pa_term) :
  G ⊢C successor_gap n -> G ⊢C ¬ (n == σ n ⊕ k).
Proof.
  intros H.
  assert (HK : G ⊢C (¬ (n`[↑] == σ n`[↑] ⊕ $0))[k..]).
  { apply AllE with (t := k). exact H. }
  change (G ⊢C ¬
    (n`[↑]`[k..] == σ (n`[↑]`[k..]) ⊕ k)) in HK.
  rewrite <- (@subst_term_shift PA_funcs_signature n k). exact HK.
Qed.

Lemma gap_introduce (G : list pa_form) (n : pa_term) :
  (forall k, G ⊢C ¬ (n == σ n ⊕ k)) -> G ⊢C successor_gap n.
Proof.
  intros H. unfold successor_gap. apply AllI_named. intros k.
  change (G ⊢C ¬
    (n`[↑]`[k..] == σ (n`[↑]`[k..]) ⊕ k)).
  pose proof (H k) as HK.
  rewrite <- (@subst_term_shift PA_funcs_signature n k) in HK. exact HK.
Qed.

Lemma all_gap_instance (G : list pa_form) (n : pa_term) :
  G ⊢C ∀ gap_induction_formula -> G ⊢C successor_gap n.
Proof.
  intros H.
  assert (HN : G ⊢C gap_induction_formula[n..]).
  { apply AllE with (t := n). exact H. }
  unfold gap_induction_formula in HN.
  rewrite successor_gap_subst in HN. cbn in HN. exact HN.
Qed.

Lemma gap_base : order_context ⊢C gap_induction_formula[zero..].
Proof.
  unfold gap_induction_formula. rewrite successor_gap_subst. cbn.
  apply gap_introduce. intros k. apply II.
  eapply IE with (phi := zero == σ (zero ⊕ k)).
  - apply zero_succ_instance. unfold order_context. cbn. auto 12.
  - eapply IE with (phi := σ zero ⊕ k == σ (zero ⊕ k)).
    + eapply IE with (phi := zero == σ zero ⊕ k).
      * apply eq_trans_instance. unfold order_context. cbn. auto 12.
      * apply Ctx. cbn. auto 12.
    + apply add_rec_instance. unfold order_context. cbn. auto 12.
Qed.

Lemma gap_step :
  order_context ⊢C ∀ (gap_induction_formula →
    gap_induction_formula[σ $0 .: S >> var]).
Proof.
  unfold gap_induction_formula. rewrite successor_gap_subst. cbn.
  apply AllI_named. intros n.
  change (order_context ⊢C (successor_gap $0)[n..] →
    (successor_gap (σ $0))[n..]).
  rewrite !successor_gap_subst. cbn. apply II.
  apply gap_introduce. intros k. apply II.
  eapply IE with (phi := n == σ n ⊕ k).
  - apply gap_instance. apply Ctx. cbn. auto 12.
  - eapply IE with (phi := σ n == σ (σ n ⊕ k)).
    + apply succ_inj_instance. unfold order_context. cbn. auto 12.
    + eapply IE with (phi := σ (σ n) ⊕ k == σ (σ n ⊕ k)).
      * eapply IE with (phi := σ n == σ (σ n) ⊕ k).
        -- apply eq_trans_instance. unfold order_context. cbn. auto 12.
        -- apply Ctx. cbn. auto 12.
      * apply add_rec_instance. unfold order_context. cbn. auto 12.
Qed.

Lemma all_successor_gap : order_context ⊢C ∀ gap_induction_formula.
Proof.
  eapply IE; [|exact gap_step].
  eapply IE; [|exact gap_base].
  apply Ctx. unfold order_context. cbn. auto 12.
Qed.

Lemma order_irreflexive_raw : order_context ⊢C ∀ ¬ ($0 ⧀ $0).
Proof.
  apply AllI_named. intros n.
  change (order_context ⊢C ¬ (n ⧀ n)).
  apply II. unfold PAlt.
  eapply ExE_named.
  - apply Ctx. cbn. auto 12.
  - intros k. cbn. rewrite !(@subst_term_shift PA_funcs_signature).
    eapply IE with (phi := n == σ n ⊕ k).
    + apply gap_instance. apply all_gap_instance.
      eapply Weak; [exact all_successor_gap|].
      intros phi Hphi. cbn. auto 12.
    + apply Ctx. cbn. auto 12.
Qed.

Lemma order_context_PAeq phi : List.In phi order_context -> PAeq phi.
Proof.
  unfold order_context.
  intros [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - apply PAeq_FA. unfold FAeq. apply List.in_app_iff. left.
    unfold EQ. right. right. now left.
  - apply PAeq_FA. unfold FAeq. apply List.in_app_iff. right.
    unfold FA. right. now left.
  - apply PAeq_discr.
  - apply PAeq_inj.
  - apply PAeq_induction.
Qed.

Theorem order_irreflexive : paeq_derivable (∀ ¬ ($0 ⧀ $0)).
Proof.
  apply paeq_from_upstream. exists order_context. split.
  - exact order_context_PAeq.
  - exact order_irreflexive_raw.
Qed.

(* The zero cutoff needed by bounded binary comprehension has no witnesses.
   This certificate uses the displayed finite context, with no induction
   step or coding premise required for the arithmetic calculation. *)
Theorem zero_minimal : paeq_derivable (∀ ¬ ($0 ⧀ zero)).
Proof.
  apply paeq_generalize. apply paeq_from_upstream.
  exists order_context. split; [exact order_context_PAeq|].
  apply II. unfold PAlt. eapply ExE_named.
  - apply Ctx. now left.
  - intros k. cbn.
    eapply IE with (phi := zero == σ ($0 ⊕ k)).
    + apply zero_succ_instance. unfold order_context. cbn. auto 12.
    + eapply IE with (phi := σ $0 ⊕ k == σ ($0 ⊕ k)).
      * eapply IE with (phi := zero == σ $0 ⊕ k).
        -- apply eq_trans_instance. unfold order_context. cbn. auto 12.
        -- apply Ctx. cbn. auto 12.
      * apply add_rec_instance. unfold order_context. cbn. auto 12.
Qed.

End PAOrder238.

Print Assumptions PAOrder238.gap_base.
Print Assumptions PAOrder238.gap_step.
Print Assumptions PAOrder238.all_successor_gap.
Print Assumptions PAOrder238.order_irreflexive_raw.
Print Assumptions PAOrder238.order_irreflexive.

Print Assumptions PAOrder238.zero_minimal.
