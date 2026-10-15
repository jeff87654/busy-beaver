(** Empty-ordinal isomorphisms are actual empty graphs.  Empty witnesses
    need not be raw-equal.  Conversely, typed total graphs transport
    emptiness in both directions by finite natural deduction. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 PairGraph238 IsoGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 PairGraph238.PairGraph238
  IsoGraph238.IsoGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module IsoZero238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Theorem empty_order_bijection G g a b :
  G ⊢238 raw_zero g -> G ⊢238 raw_zero a -> G ⊢238 raw_zero b ->
  G ⊢238 order_bijection g a b.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]]. intros HG HA HB.
  unfold order_bijection. apply CI.
  - unfold graph_entries. apply AllI_named. intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply II, Exp. eapply IE; [inherit (zero_excludes_member _ $ig $ip HG)|].
    apply Ctx. now left.
  - apply CI.
    + unfold graph_typed. apply AllI_named. intro x. destruct x as [ix|[]].
      apply AllI_named. intro y. destruct y as [iy|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply II, Exp. apply (graph_edge_empty_false _ $ig $ix $iy).
      * inherit HG.
      * apply Ctx. now left.
    + apply CI.
      * unfold graph_left_total. apply AllI_named. intro x. destruct x as [ix|[]].
        cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
        apply II, Exp. eapply IE; [inherit (zero_excludes_member _ $ia $ix HA)|].
        apply Ctx. now left.
      * apply CI.
        -- unfold graph_right_total. apply AllI_named. intro y. destruct y as [iy|[]].
           cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
           apply II, Exp. eapply IE; [inherit (zero_excludes_member _ $ib $iy HB)|].
           apply Ctx. now left.
        -- apply CI.
           ++ unfold graph_functional. apply AllI_named. intro x. destruct x as [ix|[]].
              apply AllI_named. intro y. destruct y as [iy|[]].
              apply AllI_named. intro z. destruct z as [iz|[]].
              cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
              apply II, Exp. apply (graph_edge_empty_false _ $ig $ix $iy).
              ** inherit HG.
              ** eapply CE1, Ctx. now left.
           ++ apply CI.
              ** unfold graph_injective. apply AllI_named. intro x. destruct x as [ix|[]].
                 apply AllI_named. intro y. destruct y as [iy|[]].
                 apply AllI_named. intro z. destruct z as [iz|[]].
                 cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
                 apply II, Exp. apply (graph_edge_empty_false _ $ig $ix $iz).
                 --- inherit HG.
                 --- eapply CE1, Ctx. now left.
              ** unfold graph_order. apply AllI_named. intro x. destruct x as [ix|[]].
                 apply AllI_named. intro y. destruct y as [iy|[]].
                 apply AllI_named. intro u. destruct u as [iu|[]].
                 apply AllI_named. intro v. destruct v as [iv|[]].
                 cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
                 apply II, Exp. apply (graph_edge_empty_false _ $ig $ix $iu).
                 --- inherit HG.
                 --- eapply CE1, Ctx. now left.
Qed.

Theorem zero_order_iso G a b :
  G ⊢238 empty_ax -> G ⊢238 raw_zero a -> G ⊢238 raw_zero b ->
  G ⊢238 order_iso a b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HA HB.
  eapply ExE_named; [exact HE|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  unfold order_iso. apply (ExI $ig).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply empty_order_bijection; [apply Ctx; now left|inherit HA|inherit HB].
Qed.

Lemma zero_order_bijection_source G g a b :
  G ⊢238 raw_zero b -> G ⊢238 order_bijection g a b -> G ⊢238 raw_zero a.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]]. intros HZ HG.
  unfold raw_zero. apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  assert (HL : G ⊢238 graph_left_total $ig $ia).
  { exact (CE1 (CE2 (CE2 HG))). }
  unfold graph_left_total in HL. pose proof (AllE $ix HL) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply ExE_named.
  - eapply IE; [inherit H|apply Ctx; now left].
  - intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HT : G ⊢238 graph_typed $ig $ia $ib).
    { exact (CE1 (CE2 HG)). }
    unfold graph_typed in HT. pose proof (AllE $iy (AllE $ix HT)) as H'.
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H'.
    eapply IE; [inherit (zero_excludes_member _ $ib $iy HZ)|].
    eapply CE2, IE; [inherit H'|apply Ctx; now left].
Qed.

Lemma zero_order_bijection_target G g a b :
  G ⊢238 raw_zero a -> G ⊢238 order_bijection g a b -> G ⊢238 raw_zero b.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]]. intros HZ HG.
  unfold raw_zero. apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  assert (HR : G ⊢238 graph_right_total $ig $ib).
  { exact (CE1 (CE2 (CE2 (CE2 HG)))). }
  unfold graph_right_total in HR. pose proof (AllE $iy HR) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply ExE_named.
  - eapply IE; [inherit H|apply Ctx; now left].
  - intro x. destruct x as [ix|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HT : G ⊢238 graph_typed $ig $ia $ib).
    { exact (CE1 (CE2 HG)). }
    unfold graph_typed in HT. pose proof (AllE $iy (AllE $ix HT)) as H'.
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H'.
    eapply IE; [inherit (zero_excludes_member _ $ia $ix HZ)|].
    eapply CE1, IE; [inherit H'|apply Ctx; now left].
Qed.

Theorem order_iso_zero_source G a b :
  G ⊢238 raw_zero b -> G ⊢238 order_iso a b -> G ⊢238 raw_zero a.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HZ HI.
  unfold order_iso in HI. eapply ExE_named; [exact HI|].
  intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (zero_order_bijection_source _ $ig $ia $ib); [inherit HZ|apply Ctx; now left].
Qed.

Theorem order_iso_zero_target G a b :
  G ⊢238 raw_zero a -> G ⊢238 order_iso a b -> G ⊢238 raw_zero b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HZ HI.
  unfold order_iso in HI. eapply ExE_named; [exact HI|].
  intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (zero_order_bijection_target _ $ig $ia $ib); [inherit HZ|apply Ctx; now left].
Qed.

Print Assumptions empty_order_bijection.
Print Assumptions zero_order_iso.
Print Assumptions order_iso_zero_source.
Print Assumptions order_iso_zero_target.
End IsoZero238.
