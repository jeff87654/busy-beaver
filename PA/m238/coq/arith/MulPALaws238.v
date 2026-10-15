(** Actual uniformly closed multiplication laws for the pinned PA axioms.
    Independent values are compared by constructed order-isomorphism
    graphs. Every finite source context consists of original S0 axioms. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 TraceGraph238 AddGraph238 MulGraph238 IsoGraph238 MulCoherence238
  CompositionIso238 AddCoherence238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  TraceGraph238.TraceGraph238 AddGraph238.AddGraph238 MulGraph238.MulGraph238
  IsoGraph238.IsoGraph238 MulCoherence238.MulCoherence238
  CompositionIso238.CompositionIso238 AddCoherence238.AddCoherence238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module MulPALaws238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition mul_left_zero_ax : set_form :=
  ∀ ∀ ∀ ∀ (ordinal_representative $3 → raw_zero $3 →
    ordinal_representative $2 → raw_zero $0 → mul_result $3 $2 $1 → order_iso $1 $0).

Lemma S0_mul_left_zero_at e y z e' :
  derivable finite_set_S0
    (ordinal_representative e → raw_zero e → ordinal_representative y →
      raw_zero e' → mul_result e y z → order_iso z e').
Proof.
  destruct (S0_mul_zero_law e y z e') as [G [HG HZ]].
  exists G. split; [exact HG|]. apply II, II, II, II, II.
  eapply IE; [|apply Ctx; now left].
  eapply IE; [|apply Ctx; right; now left].
  eapply IE; [|apply Ctx; right; right; right; now left].
  eapply IE; [inherit HZ|apply Ctx; right; right; right; right; now left].
Qed.

Theorem S0_mul_left_zero_closed : derivable finite_set_S0 mul_left_zero_ax.
Proof.
  unfold mul_left_zero_ax.
  apply S0_generalize, S0_generalize, S0_generalize, S0_generalize.
  exact (S0_mul_left_zero_at $3 $2 $1 $0).
Qed.

Lemma mul_left_zero_instance G e y z e' :
  G ⊢238 mul_left_zero_ax -> G ⊢238 ordinal_representative e ->
  G ⊢238 raw_zero e -> G ⊢238 ordinal_representative y ->
  G ⊢238 raw_zero e' -> G ⊢238 mul_result e y z -> G ⊢238 order_iso z e'.
Proof.
  destruct e as [ie|[]], y as [iy|[]], z as [iz|[]], e' as [ie'|[]].
  intros HT HE HZ HY HZ' HM. unfold mul_left_zero_ax in HT.
  pose proof (AllE $ie' (AllE $iz (AllE $iy (AllE $ie HT)))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HM]. eapply IE; [|exact HZ']. eapply IE; [|exact HY].
  eapply IE; [|exact HZ]. eapply IE; [exact H|exact HE].
Qed.

Lemma mul_left_zero_ax_closed : bounded 0 mul_left_zero_ax.
Proof.
  unfold mul_left_zero_ax, ordinal_representative, representative, member_ir,
    transitive, member_transitive, member_linear, internal_extrema, subset,
    nonempty, least, greatest, raw_zero, raw_successor, mul_result, mul_prefix,
    mul_recurrence, add_result, add_prefix, add_recurrence, graph_domain,
    TraceGraph238.TraceGraph238.graph_functional, graph_range, order_iso,
    order_bijection, graph_entries, entry_witness, graph_typed, graph_left_total,
    graph_right_total, IsoGraph238.IsoGraph238.graph_functional, graph_injective,
    graph_order, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn. fixed_bounds.
Qed.

Definition mul_successor_basis : set_form :=
  mul_predecessor_ax ∧ (mul_comparison_ax ∧ (add_iso_reflexivity_ax ∧
    (add_represented_totality_ax ∧ (add_comparison_ax ∧
      (add_commutation_ax ∧ iso_transitivity_ax))))).

Lemma finite_source_conjunction phi psi :
  derivable finite_set_S0 phi -> derivable finite_set_S0 psi ->
  derivable finite_set_S0 (phi ∧ psi).
Proof.
  intros [G [HG HP]] [D [HD HQ]]. exists (G ++ D). split.
  - intros chi Hchi. apply in_app_or in Hchi as [Hchi|Hchi]; [now apply HG|now apply HD].
  - apply CI.
    + eapply Weak; [exact HP|]. intros chi Hchi. apply in_or_app. now left.
    + eapply Weak; [exact HQ|]. intros chi Hchi. apply in_or_app. now right.
Qed.

Theorem S0_mul_successor_basis : derivable finite_set_S0 mul_successor_basis.
Proof.
  unfold mul_successor_basis. apply finite_source_conjunction;
    [exact S0_mul_predecessor_closed|].
  apply finite_source_conjunction; [exact S0_mul_comparison_closed|].
  apply finite_source_conjunction; [exact S0_add_iso_reflexivity_closed|].
  apply finite_source_conjunction; [exact S0_add_represented_totality_closed|].
  apply finite_source_conjunction; [exact S0_add_comparison_closed|].
  apply finite_source_conjunction; [exact S0_add_commutation_closed|].
  exact S0_order_iso_transitive_closed.
Qed.

(** The pinned PA right-hand side is y + oldproduct. The trace supplies
    previous + y. Their comparison uses the already derived actual Add
    commutation proof, and each intermediate Add output is constructed. *)
Theorem mul_left_successor_at G x sx y p z w :
  G ⊢238 mul_successor_basis -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative sx -> G ⊢238 ordinal_representative y ->
  G ⊢238 raw_successor x sx -> G ⊢238 mul_result x y p ->
  G ⊢238 mul_result sx y z -> G ⊢238 add_result y p w -> G ⊢238 order_iso z w.
Proof.
  destruct x as [ix|[]], sx as [is|[]], y as [iy|[]], p as [ip|[]],
    z as [iz|[]], w as [iw|[]]. intros HB HX HSX HY HS HP HZ HW.
  pose proof (CE1 HB) as Hpred.
  pose proof (CE1 (CE2 HB)) as Hmulcmp.
  pose proof (CE1 (CE2 (CE2 HB))) as Href.
  pose proof (CE1 (CE2 (CE2 (CE2 HB)))) as Htotal.
  pose proof (CE1 (CE2 (CE2 (CE2 (CE2 HB))))) as Haddcmp.
  pose proof (CE1 (CE2 (CE2 (CE2 (CE2 (CE2 HB)))))) as Hcomm.
  pose proof (CE2 (CE2 (CE2 (CE2 (CE2 (CE2 HB)))))) as Htrans.
  assert (HPO : G ⊢238 ordinal_representative $ip).
  { apply (mul_result_ordinal _ $ix $iy $ip). exact HP. }
  assert (HZO : G ⊢238 ordinal_representative $iz).
  { apply (mul_result_ordinal _ $is $iy $iz). exact HZ. }
  eapply ExE_named.
  - apply (mul_predecessor_ax_instance _ $ix $is $iy $iz); assumption.
  - intro q. destruct q as [iq|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HQO : (mul_result $ix $iy $iq ∧ add_result $iq $iy $iz :: G)
      ⊢238 ordinal_representative $iq).
    { apply (mul_result_ordinal _ $ix $iy $iq). eapply CE1, Ctx. now left. }
    assert (HQP : (mul_result $ix $iy $iq ∧ add_result $iq $iy $iz :: G)
      ⊢238 order_iso $iq $ip).
    { apply (mul_comparison_instance _ $ix $ix $iy $iy $iq $ip).
      - inherit Hmulcmp.
      - inherit HX.
      - inherit HX.
      - inherit HY.
      - inherit HY.
      - apply (add_iso_reflexivity_instance _ $ix); [inherit Href|inherit HX].
      - apply (add_iso_reflexivity_instance _ $iy); [inherit Href|inherit HY].
      - eapply CE1, Ctx. now left.
      - inherit HP. }
    eapply ExE_named.
    + apply (add_represented_totality_instance _ $ip $iy);
        [inherit Htotal|inherit HPO|inherit HY].
    + intro v. destruct v as [iv|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (add_iso_transitivity_instance _ $iz $iv $iw).
      * inherit Htrans.
      * inherit HZO.
      * apply (add_comparison_instance _ $iq $ip $iy $iy $iz $iv).
        -- inherit Haddcmp.
        -- inherit HQO.
        -- inherit HPO.
        -- inherit HY.
        -- inherit HY.
        -- inherit HQP.
        -- apply (add_iso_reflexivity_instance _ $iy); [inherit Href|inherit HY].
        -- eapply CE2, Ctx. right. now left.
        -- apply Ctx. now left.
      * apply (add_commutation_instance _ $ip $iy $iv $iw).
        -- inherit Hcomm.
        -- inherit HPO.
        -- inherit HY.
        -- apply Ctx. now left.
        -- inherit HW.
Qed.

Definition mul_left_successor_ax : set_form :=
  ∀ ∀ ∀ ∀ ∀ ∀ (ordinal_representative $5 → ordinal_representative $4 →
    ordinal_representative $3 → raw_successor $5 $4 → mul_result $5 $3 $2 →
    mul_result $4 $3 $1 → add_result $3 $2 $0 → order_iso $1 $0).

Theorem S0_mul_left_successor_closed : derivable finite_set_S0 mul_left_successor_ax.
Proof.
  destruct S0_mul_successor_basis as [G [HG HB]].
  exists G. split; [exact HG|]. unfold mul_left_successor_ax.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro sx. destruct sx as [is|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro p. destruct p as [ip|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro w. destruct w as [iw|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply II, II, II, II, II, II, II.
  apply (mul_left_successor_at _ $ix $is $iy $ip $iz $iw).
  - inherit HB.
  - apply Ctx. right. right. right. right. right. right. now left.
  - apply Ctx. right. right. right. right. right. now left.
  - apply Ctx. right. right. right. right. now left.
  - apply Ctx. right. right. right. now left.
  - apply Ctx. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Lemma mul_left_successor_instance G x sx y p z w :
  G ⊢238 mul_left_successor_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative sx -> G ⊢238 ordinal_representative y ->
  G ⊢238 raw_successor x sx -> G ⊢238 mul_result x y p ->
  G ⊢238 mul_result sx y z -> G ⊢238 add_result y p w -> G ⊢238 order_iso z w.
Proof.
  destruct x as [ix|[]], sx as [is|[]], y as [iy|[]], p as [ip|[]],
    z as [iz|[]], w as [iw|[]]. intros HT HX HSX HY HS HP HZ HW.
  unfold mul_left_successor_ax in HT.
  pose proof (AllE $iw (AllE $iz (AllE $ip (AllE $iy (AllE $is (AllE $ix HT)))))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HW]. eapply IE; [|exact HZ]. eapply IE; [|exact HP].
  eapply IE; [|exact HS]. eapply IE; [|exact HY]. eapply IE; [|exact HSX].
  eapply IE; [exact H|exact HX].
Qed.

Lemma mul_left_successor_ax_closed : bounded 0 mul_left_successor_ax.
Proof.
  unfold mul_left_successor_ax, ordinal_representative, representative, member_ir,
    transitive, member_transitive, member_linear, internal_extrema, subset,
    nonempty, least, greatest, raw_zero, raw_successor, mul_result, mul_prefix,
    mul_recurrence, add_result, add_prefix, add_recurrence, graph_domain,
    TraceGraph238.TraceGraph238.graph_functional, graph_range, order_iso,
    order_bijection, graph_entries, entry_witness, graph_typed, graph_left_total,
    graph_right_total, IsoGraph238.IsoGraph238.graph_functional, graph_injective,
    graph_order, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn. fixed_bounds.
Qed.

Print Assumptions S0_mul_successor_basis.
Print Assumptions mul_left_successor_at.
Print Assumptions S0_mul_left_successor_closed.
Print Assumptions mul_left_successor_instance.
Print Assumptions mul_left_successor_ax_closed.
Print Assumptions S0_mul_left_zero_closed.
Print Assumptions mul_left_zero_instance.
Print Assumptions mul_left_zero_ax_closed.
End MulPALaws238.
