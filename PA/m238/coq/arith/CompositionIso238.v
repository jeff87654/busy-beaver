(** Original order-bijection laws for the constructed composition graph.
    Actual prefix entries and coverage supply the resulting finite graph;
    no functional image or chosen set representative is assumed. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 GraphTransport238 IsoGraph238 InverseGraph238 CompositionGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  GraphTransport238.GraphTransport238 IsoGraph238.IsoGraph238
  InverseGraph238.InverseGraph238 CompositionGraph238.CompositionGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module CompositionIso238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma composition_order_entries G g h a b c k :
  G ⊢238 graph_typed h b c -> G ⊢238 composition_entries g h a k ->
  G ⊢238 graph_entries k a c.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]],
    c as [ic|[]], k as [ik|[]]. intros HT HC.
  unfold graph_entries. apply AllI_named. intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply ExE_named.
  - apply (composition_entries_instance _ $ig $ih $ia $ik $ip);
      [inherit HC|apply Ctx; now left].
  - intro x. destruct x as [ix|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply ExE_named; [apply Ctx; now left|]. intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply ExE_named; [apply Ctx; now left|]. intro z. destruct z as [iz|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (entry_witness_from_components _ $ia $ic $ip $ix $iz).
    + eapply CE1, Ctx. now left.
    + eapply CE2. apply (graph_typed_instance _ $ih $ib $ic $iy $iz); [inherit HT|].
      eapply CE1, CE2, CE2, Ctx. now left.
    + eapply CE2, CE2, CE2, Ctx. now left.
Qed.

Lemma composition_order_typed G g h a b c k :
  G ⊢238 graph_typed g a b -> G ⊢238 graph_typed h b c ->
  G ⊢238 composition_correct g h a k -> G ⊢238 graph_typed k a c.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]],
    c as [ic|[]], k as [ik|[]]. intros HT HU HC.
  unfold graph_typed. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (composition_edge_typed _ $ig $ih $ia $ib $ic $ix $iz).
  - inherit HT.
  - inherit HU.
  - eapply CE2. apply (composition_correct_instance _ $ig $ih $ia $ik $ix $iz);
      [inherit HC|apply Ctx; now left].
Qed.

Lemma composition_order_left_total G g h a k :
  G ⊢238 composition_coverage g h a k -> G ⊢238 graph_left_total k a.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], k as [ik|[]]. intro HC.
  unfold graph_left_total. apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply ExE_named.
  - apply (composition_coverage_instance _ $ig $ih $ia $ik $ix);
      [inherit HC|apply Ctx; now left].
  - intro z. destruct z as [iz|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iz).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply CE1, Ctx. now left.
Qed.

Lemma composition_order_right_total G g h a b c k :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 graph_typed g a b ->
  G ⊢238 graph_typed h b c -> G ⊢238 graph_right_total g b ->
  G ⊢238 graph_right_total h c -> G ⊢238 graph_functional g ->
  G ⊢238 graph_functional h -> G ⊢238 composition_coverage g h a k ->
  G ⊢238 graph_right_total k c.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]],
    c as [ic|[]], k as [ik|[]]. intros HE HEq HEtr HT HU HR HS HF HK HC.
  unfold graph_right_total. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply ExE_named.
  - apply (graph_right_total_instance _ $ih $ic $iz); [inherit HS|apply Ctx; now left].
  - intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HY : (graph_edge $ih $iy $iz :: R $ic $iz :: G) ⊢238 graph_edge $ih $iy $iz).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (graph_right_total_instance _ $ig $ib $iy); [inherit HR|].
      eapply CE1. apply (graph_typed_instance _ $ih $ib $ic $iy $iz);
        [inherit HU|exact HY].
    + intro x. destruct x as [ix|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      assert (HX : (graph_edge $ig $ix $iy :: graph_edge $ih $iy $iz :: R $ic $iz :: G)
        ⊢238 graph_edge $ig $ix $iy).
      { apply Ctx. now left. }
      eapply ExE_named.
      * apply (composition_coverage_instance _ $ig $ih $ia $ik $ix); [inherit HC|].
        eapply CE1. apply (graph_typed_instance _ $ig $ia $ib $ix $iy);
          [inherit HT|exact HX].
      * intro w. destruct w as [iw|[]].
        cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $ix).
        cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
        apply (graph_edge_coordinate_transport _ $ik $ix $iw $ix $iz).
        -- inherit HEq.
        -- inherit HEtr.
        -- inherit (AllE $ix HE).
        -- apply (composition_edge_functional _ $ig $ih $ix $iw $iz).
           ++ inherit HE.
           ++ inherit HEq.
           ++ inherit HEtr.
           ++ inherit HF.
           ++ inherit HK.
           ++ eapply CE2, Ctx. now left.
           ++ apply (composition_edge_intro _ $ig $ih $ix $iy $iz);
                [inherit HX|inherit HY].
        -- eapply CE1, Ctx. now left.
Qed.

Lemma composition_order_functional G g h a k :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 graph_functional g ->
  G ⊢238 graph_functional h -> G ⊢238 composition_correct g h a k ->
  G ⊢238 graph_functional k.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], k as [ik|[]].
  intros HE HEq HEtr HF HK HC. unfold graph_functional.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro w. destruct w as [iw|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (composition_edge_functional _ $ig $ih $ix $iz $iw).
  - inherit HE.
  - inherit HEq.
  - inherit HEtr.
  - inherit HF.
  - inherit HK.
  - eapply CE2. apply (composition_correct_instance _ $ig $ih $ia $ik $ix $iz);
      [inherit HC|eapply CE1, Ctx; now left].
  - eapply CE2. apply (composition_correct_instance _ $ig $ih $ia $ik $ix $iw);
      [inherit HC|eapply CE2, Ctx; now left].
Qed.

Lemma composition_order_injective G g h a k :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 graph_injective g ->
  G ⊢238 graph_injective h -> G ⊢238 composition_correct g h a k ->
  G ⊢238 graph_injective k.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], k as [ik|[]].
  intros HE HEq HEtr HF HK HC. unfold graph_injective.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro u. destruct u as [iu|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (composition_edge_injective _ $ig $ih $ix $iu $iz).
  - inherit HE.
  - inherit HEq.
  - inherit HEtr.
  - inherit HF.
  - inherit HK.
  - eapply CE2. apply (composition_correct_instance _ $ig $ih $ia $ik $ix $iz);
      [inherit HC|eapply CE1, Ctx; now left].
  - eapply CE2. apply (composition_correct_instance _ $ig $ih $ia $ik $iu $iz);
      [inherit HC|eapply CE2, Ctx; now left].
Qed.

Lemma composition_order_preserves G g h a k :
  G ⊢238 graph_order g -> G ⊢238 graph_order h ->
  G ⊢238 composition_correct g h a k -> G ⊢238 graph_order k.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], k as [ik|[]]. intros HO HP HC.
  unfold graph_order. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro u. destruct u as [iu|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro w. destruct w as [iw|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (composition_edge_order _ $ig $ih $ix $iu $iz $iw).
  - inherit HO.
  - inherit HP.
  - eapply CE2. apply (composition_correct_instance _ $ig $ih $ia $ik $ix $iz);
      [inherit HC|eapply CE1, Ctx; now left].
  - eapply CE2. apply (composition_correct_instance _ $ig $ih $ia $ik $iu $iw);
      [inherit HC|eapply CE2, Ctx; now left].
Qed.

Theorem composition_order_bijection G g h a b c k :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 order_bijection g a b ->
  G ⊢238 order_bijection h b c -> G ⊢238 composition_prefix g h a k ->
  G ⊢238 order_bijection k a c.
Proof.
  intros HE HEq HEtr HG HH HP. unfold order_bijection. apply CI.
  - apply (composition_order_entries _ g h a b c k);
      [exact (CE1 (CE2 HH))|exact (CE1 HP)].
  - apply CI.
    + apply (composition_order_typed _ g h a b c k);
        [exact (CE1 (CE2 HG))|exact (CE1 (CE2 HH))|exact (CE1 (CE2 HP))].
    + apply CI.
      * apply (composition_order_left_total _ g h a k). exact (CE2 (CE2 HP)).
      * apply CI.
        -- apply (composition_order_right_total _ g h a b c k).
           ++ exact HE.
           ++ exact HEq.
           ++ exact HEtr.
           ++ exact (CE1 (CE2 HG)).
           ++ exact (CE1 (CE2 HH)).
           ++ exact (CE1 (CE2 (CE2 (CE2 HG)))).
           ++ exact (CE1 (CE2 (CE2 (CE2 HH)))).
           ++ exact (CE1 (CE2 (CE2 (CE2 (CE2 HG))))).
           ++ exact (CE1 (CE2 (CE2 (CE2 (CE2 HH))))).
           ++ exact (CE2 (CE2 HP)).
        -- apply CI.
           ++ apply (composition_order_functional _ g h a k).
              ** exact HE.
              ** exact HEq.
              ** exact HEtr.
              ** exact (CE1 (CE2 (CE2 (CE2 (CE2 HG))))).
              ** exact (CE1 (CE2 (CE2 (CE2 (CE2 HH))))).
              ** exact (CE1 (CE2 HP)).
           ++ apply CI.
              ** apply (composition_order_injective _ g h a k).
                 --- exact HE.
                 --- exact HEq.
                 --- exact HEtr.
                 --- exact (CE1 (CE2 (CE2 (CE2 (CE2 (CE2 HG)))))).
                 --- exact (CE1 (CE2 (CE2 (CE2 (CE2 (CE2 HH)))))).
                 --- exact (CE1 (CE2 HP)).
              ** apply (composition_order_preserves _ g h a k).
                 --- exact (CE2 (CE2 (CE2 (CE2 (CE2 (CE2 HG)))))).
                 --- exact (CE2 (CE2 (CE2 (CE2 (CE2 (CE2 HH)))))).
                 --- exact (CE1 (CE2 HP)).
Qed.

(** Both source graph parameters are generalized before either given Iso
    witness is selected. All instantiations retain the same finite context. *)
Theorem S0_composition_graph_all a b :
  derivable finite_set_S0
    (∀ ∀ (ordinal_representative a`[↑]`[↑] →
      (graph_typed $1 a`[↑]`[↑] b`[↑]`[↑] →
        (graph_left_total $1 a`[↑]`[↑] →
          (graph_left_total $0 b`[↑]`[↑] → composition_exists $1 $0 a`[↑]`[↑]))))).
Proof.
  destruct a as [ia|[]], b as [ib|[]]. apply S0_generalize, S0_generalize.
  exact (S0_composition_graph_exists $1 $0 $(S (S ia)) $(S (S ib))).
Qed.

Theorem S0_order_iso_transitive a b c :
  derivable finite_set_S0
    (ordinal_representative a → (order_iso a b → (order_iso b c → order_iso a c))).
Proof.
  destruct a as [ia|[]], b as [ib|[]], c as [ic|[]].
  destruct (S0_composition_graph_all $ia $ib) as [Gcomp [HGcomp Hcomp]].
  set (G := equality_base ++ Gcomp).
  assert (HE : G ⊢238 (∀ E $0 $0)).
  { apply Ctx. unfold G, equality_base. cbn. now left. }
  assert (HEq : G ⊢238 equality_symmetry_ax).
  { apply Ctx. unfold G, equality_base, equality_symmetry_ax. cbn. right. now left. }
  assert (HEtr : G ⊢238 pair_equality_transitivity_ax).
  { apply Ctx. unfold G, equality_base, pair_equality_transitivity_ax. cbn.
    right. right. now left. }
  assert (Hcomp' : G ⊢238
    (∀ ∀ (ordinal_representative $ia`[↑]`[↑] →
      (graph_typed $1 $ia`[↑]`[↑] $ib`[↑]`[↑] →
        (graph_left_total $1 $ia`[↑]`[↑] →
          (graph_left_total $0 $ib`[↑]`[↑] → composition_exists $1 $0 $ia`[↑]`[↑])))))).
  { eapply Weak; [exact Hcomp|]. intros psi Hpsi. unfold G. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + now apply HGcomp.
  - apply II, II, II. eapply ExE_named; [apply Ctx; right; now left|].
    intro g. destruct g as [ig|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HG : (order_bijection $ig $ia $ib :: order_iso $ib $ic ::
      order_iso $ia $ib :: ordinal_representative $ia :: G) ⊢238 order_bijection $ig $ia $ib).
    { apply Ctx. now left. }
    eapply ExE_named; [apply Ctx; right; now left|].
    intro h. destruct h as [ih|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HH : (order_bijection $ih $ib $ic :: order_bijection $ig $ia $ib ::
      order_iso $ib $ic :: order_iso $ia $ib :: ordinal_representative $ia :: G)
        ⊢238 order_bijection $ih $ib $ic).
    { apply Ctx. now left. }
    pose proof (AllE $ih (AllE $ig Hcomp')) as Hi.
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in Hi.
    eapply ExE_named.
    + eapply IE; [|exact (CE1 (CE2 (CE2 HH)))].
      eapply IE; [|inherit (CE1 (CE2 (CE2 HG)))].
      eapply IE; [|inherit (CE1 (CE2 HG))].
      eapply IE; [inherit Hi|]. apply Ctx. right. right. right. right. now left.
    + intro k. destruct k as [ik|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      unfold order_iso. apply (ExI $ik).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (composition_order_bijection _ $ig $ih $ia $ib $ic $ik).
      * inherit HE.
      * inherit HEq.
      * inherit HEtr.
      * inherit HG.
      * inherit HH.
      * apply Ctx. now left.
Qed.

Definition iso_transitivity_ax : set_form :=
  ∀ ∀ ∀ (ordinal_representative $2 →
    (order_iso $2 $1 → (order_iso $1 $0 → order_iso $2 $0))).

Lemma iso_transitivity_ax_closed : bounded 0 iso_transitivity_ax.
Proof.
  unfold iso_transitivity_ax, ordinal_representative, representative, member_ir,
    transitive, member_transitive, member_linear, internal_extrema, subset,
    nonempty, least, greatest, order_iso, order_bijection, graph_entries,
    entry_witness, graph_typed, graph_left_total, graph_right_total,
    graph_functional, graph_injective, graph_order, graph_edge,
    raw_kuratowski, raw_pair, raw_singleton, R, E. cbn. fixed_bounds.
Qed.

Theorem S0_order_iso_transitive_closed : derivable finite_set_S0 iso_transitivity_ax.
Proof.
  unfold iso_transitivity_ax. apply S0_generalize, S0_generalize, S0_generalize.
  exact (S0_order_iso_transitive $2 $1 $0).
Qed.

Print Assumptions S0_composition_graph_all.
Print Assumptions S0_order_iso_transitive.
Print Assumptions iso_transitivity_ax_closed.
Print Assumptions S0_order_iso_transitive_closed.
Print Assumptions composition_order_entries.
Print Assumptions composition_order_typed.
Print Assumptions composition_order_left_total.
Print Assumptions composition_order_right_total.
Print Assumptions composition_order_functional.
Print Assumptions composition_order_injective.
Print Assumptions composition_order_preserves.
Print Assumptions composition_order_bijection.
End CompositionIso238.
