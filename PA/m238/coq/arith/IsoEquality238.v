(** Ordinary raw equality changes the displayed domains of an actual
    order-bijection without changing its graph or choosing new entries. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 IsoGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  IsoGraph238.IsoGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module IsoEquality238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma entry_witness_coordinate_transport G a b a' b' p :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 E a a' -> G ⊢238 E b b' ->
  G ⊢238 entry_witness a b p -> G ⊢238 entry_witness a' b' p.
Proof.
  destruct a as [ia|[]], b as [ib|[]], a' as [ia'|[]], b' as [ib'|[]], p as [ip|[]].
  intros HE HQ Haa Hbb H. unfold entry_witness in H.
  eapply ExE_named; [exact H|]. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  unfold entry_witness. apply (ExI $ix).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (ExI $iy).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply (equality_container_transport _ $ia $ia' $ix).
    + inherit HE.
    + inherit HQ.
    + inherit Haa.
    + eapply CE1, Ctx. now left.
  - apply CI.
    + apply (equality_container_transport _ $ib $ib' $iy).
      * inherit HE.
      * inherit HQ.
      * inherit Hbb.
      * eapply CE1, CE2, Ctx. now left.
    + eapply CE2, CE2, Ctx. now left.
Qed.

Lemma graph_entries_coordinate_transport G g a b a' b' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 E a a' -> G ⊢238 E b b' ->
  G ⊢238 graph_entries g a b -> G ⊢238 graph_entries g a' b'.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]],
    a' as [ia'|[]], b' as [ib'|[]]. intros HE HQ Haa Hbb HG.
  unfold graph_entries. apply AllI_named. intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (entry_witness_coordinate_transport _ $ia $ib $ia' $ib' $ip).
  - inherit HE.
  - inherit HQ.
  - inherit Haa.
  - inherit Hbb.
  - apply (graph_entries_instance _ $ig $ia $ib $ip); [inherit HG|apply Ctx; now left].
Qed.

Lemma graph_typed_coordinate_transport G g a b a' b' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 E a a' -> G ⊢238 E b b' ->
  G ⊢238 graph_typed g a b -> G ⊢238 graph_typed g a' b'.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]],
    a' as [ia'|[]], b' as [ib'|[]]. intros HE HQ Haa Hbb HT.
  unfold graph_typed in HT. unfold graph_typed.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  pose proof (AllE $iy (AllE $ix HT)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  apply CI.
  - apply (equality_container_transport _ $ia $ia' $ix).
    + inherit HE.
    + inherit HQ.
    + inherit Haa.
    + eapply CE1, IE; [inherit H|apply Ctx; now left].
  - apply (equality_container_transport _ $ib $ib' $iy).
    + inherit HE.
    + inherit HQ.
    + inherit Hbb.
    + eapply CE2, IE; [inherit H|apply Ctx; now left].
Qed.

Lemma graph_left_total_coordinate_transport G g a a' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E a a' ->
  G ⊢238 graph_left_total g a -> G ⊢238 graph_left_total g a'.
Proof.
  destruct g as [ig|[]], a as [ia|[]], a' as [ia'|[]]. intros HE HQ HEq Haa HT.
  unfold graph_left_total in HT. unfold graph_left_total.
  apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  pose proof (AllE $ix HT) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [inherit H|]. apply (equality_container_transport _ $ia' $ia $ix).
  - inherit HE.
  - inherit HQ.
  - apply equality_symmetry_instance; [inherit HEq|inherit Haa].
  - apply Ctx. now left.
Qed.

Lemma graph_right_total_coordinate_transport G g b b' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E b b' ->
  G ⊢238 graph_right_total g b -> G ⊢238 graph_right_total g b'.
Proof.
  destruct g as [ig|[]], b as [ib|[]], b' as [ib'|[]]. intros HE HQ HEq Hbb HT.
  unfold graph_right_total in HT. unfold graph_right_total.
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  pose proof (AllE $iy HT) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [inherit H|]. apply (equality_container_transport _ $ib' $ib $iy).
  - inherit HE.
  - inherit HQ.
  - apply equality_symmetry_instance; [inherit HEq|inherit Hbb].
  - apply Ctx. now left.
Qed.

Theorem order_bijection_coordinate_transport G g a b a' b' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E a a' -> G ⊢238 E b b' ->
  G ⊢238 order_bijection g a b -> G ⊢238 order_bijection g a' b'.
Proof.
  intros HE HQ HEq Haa Hbb HG. unfold order_bijection. apply CI.
  - apply (graph_entries_coordinate_transport _ g a b a' b');
      [exact HE|exact HQ|exact Haa|exact Hbb|exact (CE1 HG)].
  - apply CI.
    + apply (graph_typed_coordinate_transport _ g a b a' b');
        [exact HE|exact HQ|exact Haa|exact Hbb|exact (CE1 (CE2 HG))].
    + apply CI.
      * apply (graph_left_total_coordinate_transport _ g a a');
          [exact HE|exact HQ|exact HEq|exact Haa|exact (CE1 (CE2 (CE2 HG)))].
      * apply CI.
        -- apply (graph_right_total_coordinate_transport _ g b b');
             [exact HE|exact HQ|exact HEq|exact Hbb|exact (CE1 (CE2 (CE2 (CE2 HG))))].
        -- exact (CE2 (CE2 (CE2 (CE2 HG)))).
Qed.

Theorem order_iso_coordinate_transport G a b a' b' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E a a' -> G ⊢238 E b b' ->
  G ⊢238 order_iso a b -> G ⊢238 order_iso a' b'.
Proof.
  destruct a as [ia|[]], b as [ib|[]], a' as [ia'|[]], b' as [ib'|[]].
  intros HE HQ HEq Haa Hbb H. unfold order_iso in H.
  eapply ExE_named; [exact H|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  unfold order_iso. apply (ExI $ig).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (order_bijection_coordinate_transport _ $ig $ia $ib $ia' $ib').
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit Haa.
  - inherit Hbb.
  - apply Ctx. now left.
Qed.

Print Assumptions order_bijection_coordinate_transport.
Print Assumptions order_iso_coordinate_transport.
End IsoEquality238.
