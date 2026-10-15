(* Original finite ordinary-PA suppliers for the literal append graph.
   Its old values come from the supplied doubling trace.  Its endpoint
   is the given term r.  The two branches are disjoint by the actual PA
   irreflexivity certificate, and old values are unique by beta_unique. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 PAEqCongruence238
  PAQuotient238 CompactInPA238 PAPowerTrace238 PAPowerExtension238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAEqCongruence238 PAQuotient238
  CompactInPA238 PAPowerTrace238 PAPowerExtension238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PABetaAppendGraph238.

Lemma append_graph_subst b c n r i v rho :
  (append_graph b c n r i v)[rho] =
  append_graph b`[rho] c`[rho] n`[rho] r`[rho] i`[rho] v`[rho].
Proof.
  unfold append_graph. change
    ((((PAlt i (σ n))[rho] ∧ (beta b c i v)[rho]) ∨
      ((i`[rho] == σ n`[rho]) ∧ (v`[rho] == r`[rho]))) =
     (((i`[rho] ⧀ σ n`[rho]) ∧
       beta b`[rho] c`[rho] i`[rho] v`[rho]) ∨
      ((i`[rho] == σ n`[rho]) ∧ (v`[rho] == r`[rho])))).
  rewrite PAlt_subst, beta_subst. reflexivity.
Qed.

Definition append_value_exists (b c n r i : pa_term) : pa_form :=
  ∃ append_graph b`[↑] c`[↑] n`[↑] r`[↑] i`[↑] $0.
Lemma append_value_exists_subst b c n r i rho :
  (append_value_exists b c n r i)[rho] =
  append_value_exists b`[rho] c`[rho] n`[rho] r`[rho] i`[rho].
Proof.
  unfold append_value_exists. cbn [subst_form]. rewrite append_graph_subst.
  now rewrite !up_term.
Qed.
Lemma append_value_exists_intro G b c n r i v :
  G ⊢C append_graph b c n r i v -> G ⊢C append_value_exists b c n r i.
Proof.
  intros H. unfold append_value_exists. apply (ExI v).
  rewrite append_graph_subst, !subst_term_shift. exact H.
Qed.
Lemma append_value_exists_eliminate G b c n r i (psi : pa_form) :
  G ⊢C append_value_exists b c n r i ->
  (forall v, (List.cons (append_graph b c n r i v) G) ⊢C psi) ->
  G ⊢C psi.
Proof.
  intros HX H. unfold append_value_exists in HX.
  eapply ExE_named; [exact HX|]. intros v.
  rewrite append_graph_subst, !subst_term_shift. exact (H v).
Qed.

Definition order_irreflexive_sentence : pa_form := ∀ ¬ ($0 ⧀ $0).
Definition graph_context : list pa_form :=
  List.cons order_irreflexive_sentence append_context.
Definition has_graph_context (G : list pa_form) : Prop :=
  forall phi, List.In phi graph_context -> List.In phi G.
Lemma graph_proof phi : graph_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := order_irreflexive_sentence).
  - apply append_proof, II. exact HD.
  - exact PAOrder238.order_irreflexive.
Qed.
Lemma graph_context_self : has_graph_context graph_context.
Proof. intros phi Hphi. exact Hphi. Qed.
Lemma has_graph_cons G phi : has_graph_context G ->
  has_graph_context (List.cons phi G).
Proof. intros HG psi Hpsi. right. exact (HG psi Hpsi). Qed.
Lemma graph_has_extension G : has_graph_context G -> has_extension_context G.
Proof.
  intros HG phi Hphi. apply HG. unfold graph_context. right.
  exact (append_has_extension phi Hphi).
Qed.
Lemma graph_has_quotient G : has_graph_context G -> has_quotient_context G.
Proof. intros HG. apply extension_has_quotient, graph_has_extension. exact HG. Qed.
Lemma graph_has_trace G : has_graph_context G -> has_trace_context G.
Proof. intros HG. apply extension_has_trace, graph_has_extension. exact HG. Qed.
Lemma graph_has_equality G : has_graph_context G -> has_equality G.
Proof. intros HG. apply quotient_has_equality, graph_has_quotient. exact HG. Qed.
Lemma graph_has_injective G : has_graph_context G -> List.In ax_succ_inj G.
Proof. intros HG. apply HG. unfold graph_context. right. exact append_has_injective. Qed.
Lemma graph_has_irreflexive G : has_graph_context G ->
  List.In order_irreflexive_sentence G.
Proof. intros HG. apply HG. unfold graph_context. now left. Qed.
Lemma order_irreflexive_at G i : List.In order_irreflexive_sentence G ->
  G ⊢C ¬ (i ⧀ i).
Proof.
  intros H. assert (HH : G ⊢C order_irreflexive_sentence) by now apply Ctx.
  pose proof (AllE i HH) as HK.
  change (G ⊢C ¬ ((PAlt $0 $0)[i..])) in HK.
  rewrite PAlt_subst in HK. exact HK.
Qed.

(* This is the exact disjointness argument needed by both mixed cases. *)
Lemma old_endpoint_absurd G i n : has_equality G ->
  List.In order_irreflexive_sentence G ->
  G ⊢C (i ⧀ σ n) -> G ⊢C (i == σ n) -> G ⊢C falsity.
Proof.
  intros HE Hir HI Hlast.
  pose proof (equality_symmetry G i (σ n) HE Hlast) as Hback.
  pose proof (formula_substitutivity G (PAlt i`[↑] $0)
    (σ n) i HE Hback) as Htransfer.
  rewrite !PAlt_subst, !subst_term_shift in Htransfer.
  pose proof (IE (CE1 Htransfer) HI) as Hself.
  exact (IE (order_irreflexive_at G i Hir) Hself).
Qed.

Lemma append_graph_total_from_trace G b c n p r i :
  has_quotient_context G -> List.In ax_succ_inj G ->
  G ⊢C trace_body b c n p -> G ⊢C (i ⧀ σ (σ n)) ->
  G ⊢C append_value_exists b c n r i.
Proof.
  intros HG Hinj HT HI.
  pose proof (strict_successor_split G i (σ n) HG Hinj HI) as Hsplit.
  eapply DE; [exact Hsplit| |].
  - set (D := List.cons (i ⧀ σ n) G).
    change (D ⊢C append_value_exists b c n r i).
    assert (HD : has_quotient_context D).
    { unfold D. apply has_quotient_cons. exact HG. }
    assert (HinjD : List.In ax_succ_inj D) by (unfold D; now right).
    assert (HID : D ⊢C (i ⧀ σ n)).
    { apply Ctx. unfold D. now left. }
    pose proof (weaken_head G (trace_body b c n p) (i ⧀ σ n) HT) as HTD.
    pose proof (trace_beta_total D b c n p i HD HinjD HTD HID) as HX.
    unfold beta_value_exists in HX. eapply ExE_named; [exact HX|]. intros v.
    rewrite beta_subst, !subst_term_shift.
    set (E := List.cons (beta b c i v) D).
    change (E ⊢C append_value_exists b c n r i).
    apply (append_value_exists_intro E b c n r i v).
    unfold append_graph. apply DI1, CI.
    + unfold E. apply weaken_head. exact HID.
    + apply Ctx. unfold E. now left.
  - set (D := List.cons (i == σ n) G).
    change (D ⊢C append_value_exists b c n r i).
    apply (append_value_exists_intro D b c n r i r).
    unfold append_graph. apply DI2, CI.
    + apply Ctx. unfold D. now left.
    + apply reflexivity_instance, quotient_has_equality.
      unfold D. apply has_quotient_cons. exact HG.
Qed.

Lemma append_graph_functional G b c n r i v w : has_trace_context G ->
  List.In order_irreflexive_sentence G ->
  G ⊢C append_graph b c n r i v ->
  G ⊢C append_graph b c n r i w -> G ⊢C (v == w).
Proof.
  intros HG Hir HV HW. unfold append_graph in HV.
  eapply DE; [exact HV| |].
  - set (D := List.cons ((i ⧀ σ n) ∧ beta b c i v) G).
    change (D ⊢C (v == w)).
    assert (HD : has_trace_context D).
    { unfold D. apply has_trace_cons. exact HG. }
    assert (HDold : D ⊢C ((i ⧀ σ n) ∧ beta b c i v)).
    { apply Ctx. unfold D. now left. }
    pose proof (weaken_head G (append_graph b c n r i w)
      ((i ⧀ σ n) ∧ beta b c i v) HW) as HWD.
    unfold append_graph in HWD. eapply DE; [exact HWD| |].
    + set (E := List.cons ((i ⧀ σ n) ∧ beta b c i w) D).
      change (E ⊢C (v == w)).
      assert (HE : has_trace_context E).
      { unfold E. apply has_trace_cons. exact HD. }
      assert (HVE : E ⊢C beta b c i v).
      { unfold E. apply weaken_head. exact (CE2 HDold). }
      assert (HWE : E ⊢C beta b c i w).
      { eapply CE2. apply Ctx. unfold E. now left. }
      exact (beta_unique_at E b c i v w HE HVE HWE).
    + set (E := List.cons ((i == σ n) ∧ (w == r)) D).
      change (E ⊢C (v == w)). apply Exp.
      assert (HE : has_equality E).
      { unfold E. apply has_equality_cons, trace_has_equality. exact HD. }
      assert (HirE : List.In order_irreflexive_sentence E).
      { unfold E, D. right. now right. }
      assert (HIE : E ⊢C (i ⧀ σ n)).
      { unfold E. apply weaken_head. exact (CE1 HDold). }
      assert (Hlast : E ⊢C (i == σ n)).
      { eapply CE1. apply Ctx. unfold E. now left. }
      exact (old_endpoint_absurd E i n HE HirE HIE Hlast).
  - set (D := List.cons ((i == σ n) ∧ (v == r)) G).
    change (D ⊢C (v == w)).
    assert (HD : has_trace_context D).
    { unfold D. apply has_trace_cons. exact HG. }
    assert (HDlast : D ⊢C ((i == σ n) ∧ (v == r))).
    { apply Ctx. unfold D. now left. }
    pose proof (weaken_head G (append_graph b c n r i w)
      ((i == σ n) ∧ (v == r)) HW) as HWD.
    unfold append_graph in HWD. eapply DE; [exact HWD| |].
    + set (E := List.cons ((i ⧀ σ n) ∧ beta b c i w) D).
      change (E ⊢C (v == w)). apply Exp.
      assert (HE : has_equality E).
      { unfold E. apply has_equality_cons, trace_has_equality. exact HD. }
      assert (HirE : List.In order_irreflexive_sentence E).
      { unfold E, D. right. now right. }
      assert (HIE : E ⊢C (i ⧀ σ n)).
      { eapply CE1. apply Ctx. unfold E. now left. }
      assert (Hlast : E ⊢C (i == σ n)).
      { unfold E. apply weaken_head. exact (CE1 HDlast). }
      exact (old_endpoint_absurd E i n HE HirE HIE Hlast).
    + set (E := List.cons ((i == σ n) ∧ (w == r)) D).
      change (E ⊢C (v == w)).
      assert (HE : has_equality E).
      { unfold E. apply has_equality_cons, trace_has_equality. exact HD. }
      assert (Hvr : E ⊢C (v == r)).
      { unfold E. apply weaken_head. exact (CE2 HDlast). }
      assert (Hwr : E ⊢C (w == r)).
      { eapply CE2. apply Ctx. unfold E. now left. }
      pose proof (equality_symmetry E w r HE Hwr) as Hrw.
      exact (equality_transitivity E v r w HE Hvr Hrw).
Qed.

Definition append_graph_total_sentence : pa_form :=
  ∀ ∀ ∀ ∀ ∀ ∀ (trace_body $0 $1 $2 $3 → $5 ⧀ σ (σ $2) →
    append_value_exists $0 $1 $2 $4 $5).
Definition append_graph_unique_sentence : pa_form :=
  ∀ ∀ ∀ ∀ ∀ ∀ ∀ (append_graph $0 $1 $2 $3 $4 $5 →
    append_graph $0 $1 $2 $3 $4 $6 → $5 == $6).

Theorem append_graph_total : paeq_derivable append_graph_total_sentence.
Proof.
  unfold append_graph_total_sentence.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, graph_proof, II, II.
  set (G := List.cons ($5 ⧀ σ (σ $2))
    (List.cons (trace_body $0 $1 $2 $3) graph_context)).
  change (G ⊢C append_value_exists $0 $1 $2 $4 $5).
  assert (HG : has_graph_context G).
  { unfold G. apply has_graph_cons, has_graph_cons. exact graph_context_self. }
  apply (append_graph_total_from_trace G $0 $1 $2 $3 $4 $5).
  - exact (graph_has_quotient G HG).
  - exact (graph_has_injective G HG).
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

Theorem append_graph_unique : paeq_derivable append_graph_unique_sentence.
Proof.
  unfold append_graph_unique_sentence.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, paeq_generalize, paeq_generalize,
    graph_proof, II, II.
  set (G := List.cons (append_graph $0 $1 $2 $3 $4 $6)
    (List.cons (append_graph $0 $1 $2 $3 $4 $5) graph_context)).
  change (G ⊢C ($5 == $6)).
  assert (HG : has_graph_context G).
  { unfold G. apply has_graph_cons, has_graph_cons. exact graph_context_self. }
  apply (append_graph_functional G $0 $1 $2 $3 $4 $5 $6).
  - exact (graph_has_trace G HG).
  - exact (graph_has_irreflexive G HG).
  - apply Ctx. unfold G. right. now left.
  - apply Ctx. unfold G. now left.
Qed.

(* Named instances for finite contexts in the bounded CRT induction. *)
Lemma append_graph_total_at G b c n p r i :
  List.In append_graph_total_sentence G -> G ⊢C trace_body b c n p ->
  G ⊢C (i ⧀ σ (σ n)) -> G ⊢C append_value_exists b c n r i.
Proof.
  intros H HT HI.
  assert (HH : G ⊢C append_graph_total_sentence) by now apply Ctx.
  assert (HB : bounded 6 (trace_body $0 $1 $2 $3 → $5 ⧀ σ (σ $2) →
    append_value_exists $0 $1 $2 $4 $5)).
  { unfold trace_body, trace_steps, doubling_step, doubling_pair,
      append_value_exists, append_graph, beta, beta_modulus, PAlt. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := trace_body $0 $1 $2 $3 → $5 ⧀ σ (σ $2) →
      append_value_exists $0 $1 $2 $4 $5) (N := 6)
    HH HB (b .: c .: n .: p .: r .: i .: var)) as HK.
  change (G ⊢C (trace_body $0 $1 $2 $3)[b .: c .: n .: p .: r .: i .: var] →
    (PAlt $5 (σ (σ $2)))[b .: c .: n .: p .: r .: i .: var] →
    (append_value_exists $0 $1 $2 $4 $5)[b .: c .: n .: p .: r .: i .: var]) in HK.
  rewrite trace_body_subst, PAlt_subst, append_value_exists_subst in HK.
  change (G ⊢C (trace_body b c n p → i ⧀ σ (σ n) →
    append_value_exists b c n r i)) in HK.
  exact (IE (IE HK HT) HI).
Qed.

Lemma append_graph_unique_at G b c n r i v w :
  List.In append_graph_unique_sentence G ->
  G ⊢C append_graph b c n r i v -> G ⊢C append_graph b c n r i w ->
  G ⊢C (v == w).
Proof.
  intros H HV HW.
  assert (HH : G ⊢C append_graph_unique_sentence) by now apply Ctx.
  assert (HB : bounded 7 (append_graph $0 $1 $2 $3 $4 $5 →
    append_graph $0 $1 $2 $3 $4 $6 → $5 == $6)).
  { unfold append_graph, beta, beta_modulus, PAlt. solve_bounds. }
  pose proof (subst_forall_prv
    (phi := append_graph $0 $1 $2 $3 $4 $5 →
      append_graph $0 $1 $2 $3 $4 $6 → $5 == $6) (N := 7)
    HH HB (b .: c .: n .: r .: i .: v .: w .: var)) as HK.
  change (G ⊢C (append_graph $0 $1 $2 $3 $4 $5)[b .: c .: n .: r .: i .: v .: w .: var] →
    (append_graph $0 $1 $2 $3 $4 $6)[b .: c .: n .: r .: i .: v .: w .: var] →
    v == w) in HK.
  rewrite !append_graph_subst in HK.
  change (G ⊢C (append_graph b c n r i v → append_graph b c n r i w → v == w)) in HK.
  exact (IE (IE HK HV) HW).
Qed.

End PABetaAppendGraph238.

Print Assumptions PABetaAppendGraph238.append_graph_total.
Print Assumptions PABetaAppendGraph238.append_graph_unique.
