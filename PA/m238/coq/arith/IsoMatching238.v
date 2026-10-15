(** Original predecessor matching through actual order-bijection graphs.
    Greatest witnesses are transported by concrete graph totality,
    functionality, and membership-order preservation. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 GraphTransport238 IsoGraph238 InverseGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  GraphTransport238.GraphTransport238 IsoGraph238.IsoGraph238
  InverseGraph238.InverseGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module IsoMatching238.

Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma raw_successor_greatest G p a :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 raw_successor p a -> G ⊢238 greatest a p.
Proof.
  destruct p as [ip|[]], a as [ia|[]]. intros HE HS. unfold greatest. apply CI.
  - apply (raw_successor_point_member _ $ip $ia); assumption.
  - apply AllI_named. intro x. destruct x as [ix|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
    apply disjunction_swap. apply (raw_successor_member_cases _ $ip $ia $ix);
      [inherit HS|apply Ctx; now left].
Qed.

Lemma order_graph_image_greatest G g a b p q :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 order_bijection g a b ->
  G ⊢238 greatest a p -> G ⊢238 graph_edge g p q -> G ⊢238 greatest b q.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]], p as [ip|[]], q as [iq|[]].
  intros HE HEq HEtr HG HP HPQ. unfold greatest. apply CI.
  - eapply CE2. apply (graph_typed_instance _ $ig $ia $ib $ip $iq);
      [exact (CE1 (CE2 HG))|exact HPQ].
  - apply AllI_named. intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
    eapply ExE_named.
    + apply (graph_right_total_instance _ $ig $ib $iy);
        [inherit (CE1 (CE2 (CE2 (CE2 HG))))|apply Ctx; now left].
    + intro x. destruct x as [ix|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. eapply DE.
      * apply (greatest_member_cases _ $ia $ip $ix); [inherit HP|].
        eapply CE1. apply (graph_typed_instance _ $ig $ia $ib $ix $iy);
          [inherit (CE1 (CE2 HG))|apply Ctx; now left].
      * apply DI1, equality_symmetry_instance; [inherit HEq|].
        apply (graph_functional_instance _ $ig $ip $iq $iy).
        -- inherit (CE1 (CE2 (CE2 (CE2 (CE2 HG))))).
        -- inherit HPQ.
        -- apply (graph_edge_coordinate_transport _ $ig $ix $iy $ip $iy).
           ++ inherit HEq.
           ++ inherit HEtr.
           ++ apply Ctx. now left.
           ++ inherit (AllE $iy HE).
           ++ apply Ctx. right. now left.
      * apply DI2. eapply IE; [|apply Ctx; now left].
        eapply CE1. apply (graph_order_instance _ $ig $ip $ix $iq $iy).
        -- inherit (CE2 (CE2 (CE2 (CE2 (CE2 (CE2 HG)))))).
        -- inherit HPQ.
        -- apply Ctx. right. now left.
Qed.

Theorem successor_image_predecessor G g a b p q :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 ordinal_representative b -> G ⊢238 order_bijection g a b ->
  G ⊢238 raw_successor p a -> G ⊢238 graph_edge g p q ->
  G ⊢238 (ordinal_representative q ∧ (raw_successor q b ∧ greatest b q)).
Proof.
  intros HE HQ HEq HEtr HB HG HS HPQ.
  assert (HM : G ⊢238 greatest b q).
  { apply (order_graph_image_greatest _ g a b p q);
      [exact HE|exact HEq|exact HEtr|exact HG| |exact HPQ].
    apply (raw_successor_greatest _ p a); assumption. }
  apply CI.
  - apply (ordinal_member_closed _ b q); [exact HB|exact (CE1 HM)].
  - apply CI; [|exact HM].
    apply (greatest_raw_predecessor _ b q);
      [exact HE|exact HQ|exact HEq|exact (CE1 (CE1 HB))|exact HM].
Qed.

Theorem successor_image_exists G g a b p :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 ordinal_representative b -> G ⊢238 order_bijection g a b ->
  G ⊢238 raw_successor p a ->
  G ⊢238 ∃ (ordinal_representative $0 ∧
    (raw_successor $0 b`[↑] ∧ graph_edge g`[↑] p`[↑] $0)).
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]], p as [ip|[]].
  intros HE HQ HEq HEtr HB HG HS. eapply ExE_named.
  - apply (graph_left_total_instance _ $ig $ia $ip); [exact (CE1 (CE2 (CE2 HG)))|].
    apply (raw_successor_point_member _ $ip $ia); assumption.
  - intro q. destruct q as [iq|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HP : (graph_edge $ig $ip $iq :: G) ⊢238
      (ordinal_representative $iq ∧ (raw_successor $iq $ib ∧ greatest $ib $iq))).
    { apply (successor_image_predecessor _ $ig $ia $ib $ip $iq).
      - inherit HE.
      - inherit HQ.
      - inherit HEq.
      - inherit HEtr.
      - inherit HB.
      - inherit HG.
      - inherit HS.
      - apply Ctx. now left. }
    apply (ExI $iq).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
    + exact (CE1 HP).
    + apply CI; [exact (CE1 (CE2 HP))|apply Ctx; now left].
Qed.

Lemma predecessor_image_member G g p q x y :
  G ⊢238 graph_order g -> G ⊢238 graph_edge g p q ->
  G ⊢238 graph_edge g x y -> G ⊢238 R p x -> G ⊢238 R q y.
Proof.
  intros HO HP HX HM. exact (IE (CE1 (graph_order_instance G g p x q y HO HP HX)) HM).
Qed.

Lemma predecessor_source_member G g p q x y :
  G ⊢238 graph_order g -> G ⊢238 graph_edge g p q ->
  G ⊢238 graph_edge g x y -> G ⊢238 R q y -> G ⊢238 R p x.
Proof.
  intros HO HP HX HM. exact (IE (CE2 (graph_order_instance G g p x q y HO HP HX)) HM).
Qed.

Print Assumptions predecessor_image_member.
Print Assumptions predecessor_source_member.
Print Assumptions raw_successor_greatest.
Print Assumptions order_graph_image_greatest.
Print Assumptions successor_image_predecessor.
Print Assumptions successor_image_exists.
End IsoMatching238.
