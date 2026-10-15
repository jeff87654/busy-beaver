(** Original raw-equality transport for actual finite Kuratowski graphs.
    Graph adjunction is classified by existing decoded entries; no
    Extensionality, Replacement, or canonical pair witness is used. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 PairGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 PairGraph238.PairGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module GraphTransport238.

Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma raw_singleton_coordinate_transport G a b s :
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 E a b -> G ⊢238 raw_singleton a s -> G ⊢238 raw_singleton b s.
Proof.
  destruct a as [ia|[]], b as [ib|[]], s as [is|[]]. intros HEq HEtr Hab HS.
  unfold raw_singleton. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. apply (pair_equality_transitivity _ $iz $ia $ib).
    + inherit HEtr.
    + apply (raw_singleton_member _ $ia $is $iz); [inherit HS|apply Ctx; now left].
    + inherit Hab.
  - apply II. apply (raw_singleton_intro _ $ia $is $iz); [inherit HS|].
    apply (pair_equality_transitivity _ $iz $ib $ia).
    + inherit HEtr.
    + apply Ctx. now left.
    + apply equality_symmetry_instance; [inherit HEq|inherit Hab].
Qed.

Lemma raw_pair_coordinate_transport G a b a' b' p :
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 E a a' -> G ⊢238 E b b' ->
  G ⊢238 raw_pair a b p -> G ⊢238 raw_pair a' b' p.
Proof.
  destruct a as [ia|[]], b as [ib|[]], a' as [ia'|[]],
    b' as [ib'|[]], p as [ip|[]]. intros HEq HEtr Haa Hbb HP.
  unfold raw_pair. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. eapply DE.
    + apply (raw_pair_member _ $ia $ib $ip $iz); [inherit HP|apply Ctx; now left].
    + apply DI1. apply (pair_equality_transitivity _ $iz $ia $ia').
      * inherit HEtr.
      * apply Ctx. now left.
      * inherit Haa.
    + apply DI2. apply (pair_equality_transitivity _ $iz $ib $ib').
      * inherit HEtr.
      * apply Ctx. now left.
      * inherit Hbb.
  - apply II. apply (raw_pair_intro _ $ia $ib $ip $iz); [inherit HP|].
    eapply DE; [apply Ctx; now left| |].
    + apply DI1. apply (pair_equality_transitivity _ $iz $ia' $ia).
      * inherit HEtr.
      * apply Ctx. now left.
      * apply equality_symmetry_instance; [inherit HEq|inherit Haa].
    + apply DI2. apply (pair_equality_transitivity _ $iz $ib' $ib).
      * inherit HEtr.
      * apply Ctx. now left.
      * apply equality_symmetry_instance; [inherit HEq|inherit Hbb].
Qed.

Lemma raw_pair_container_transport G a b p q :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E p q ->
  G ⊢238 raw_pair a b p -> G ⊢238 raw_pair a b q.
Proof.
  destruct a as [ia|[]], b as [ib|[]], p as [ip|[]], q as [iq|[]].
  intros HE HQ HEq Hpq HP. unfold raw_pair.
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. apply (raw_pair_member _ $ia $ib $ip $iz); [inherit HP|].
    apply (pair_container_transport _ $iq $ip $iz).
    + inherit HE.
    + inherit HQ.
    + apply equality_symmetry_instance; [inherit HEq|inherit Hpq].
    + apply Ctx. now left.
  - apply II. apply (pair_container_transport _ $ip $iq $iz).
    + inherit HE.
    + inherit HQ.
    + inherit Hpq.
    + apply (raw_pair_intro _ $ia $ib $ip $iz); [inherit HP|apply Ctx; now left].
Qed.

Lemma raw_kuratowski_coordinate_transport G p a b a' b' :
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 E a a' -> G ⊢238 E b b' ->
  G ⊢238 raw_kuratowski p a b -> G ⊢238 raw_kuratowski p a' b'.
Proof.
  destruct p as [ip|[]], a as [ia|[]], b as [ib|[]],
    a' as [ia'|[]], b' as [ib'|[]]. intros HEq HEtr Haa Hbb HP.
  unfold raw_kuratowski in HP.
  eapply ExE_named; [exact HP|]. intro s. destruct s as [is|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro t. destruct t as [it|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (raw_kuratowski_from_witnesses _ $ip $ia' $ib' $is $it).
  - apply (raw_singleton_coordinate_transport _ $ia $ia' $is).
    + inherit HEq.
    + inherit HEtr.
    + inherit Haa.
    + eapply CE1, Ctx. now left.
  - apply (raw_pair_coordinate_transport _ $ia $ib $ia' $ib' $it).
    + inherit HEq.
    + inherit HEtr.
    + inherit Haa.
    + inherit Hbb.
    + eapply CE1, CE2, Ctx. now left.
  - eapply CE2, CE2, Ctx. now left.
Qed.

Lemma raw_kuratowski_container_transport G p q a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E p q ->
  G ⊢238 raw_kuratowski p a b -> G ⊢238 raw_kuratowski q a b.
Proof.
  destruct p as [ip|[]], q as [iq|[]], a as [ia|[]], b as [ib|[]].
  intros HE HQ HEq Hpq HP. unfold raw_kuratowski in HP.
  eapply ExE_named; [exact HP|]. intro s. destruct s as [is|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro t. destruct t as [it|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (raw_kuratowski_from_witnesses _ $iq $ia $ib $is $it).
  - eapply CE1, Ctx. now left.
  - eapply CE1, CE2, Ctx. now left.
  - apply (raw_pair_container_transport _ $is $it $ip $iq).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit Hpq.
    + eapply CE2, CE2, Ctx. now left.
Qed.

Lemma graph_edge_coordinate_transport G g a b a' b' :
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 E a a' -> G ⊢238 E b b' ->
  G ⊢238 graph_edge g a b -> G ⊢238 graph_edge g a' b'.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]],
    a' as [ia'|[]], b' as [ib'|[]]. intros HEq HEtr Haa Hbb HG.
  unfold graph_edge in HG. eapply ExE_named; [exact HG|].
  intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (graph_edge_from_entry _ $ig $ia' $ib' $ip).
  - eapply CE1, Ctx. now left.
  - apply (raw_kuratowski_coordinate_transport _ $ip $ia $ib $ia' $ib').
    + inherit HEq.
    + inherit HEtr.
    + inherit Haa.
    + inherit Hbb.
    + eapply CE2, Ctx. now left.
Qed.

(** Every decoded edge after one actual Adjunction is an old edge or has
    the coordinates of the adjoined entry.  Noncanonical entry equality is
    handled by container transport and joint decoding. *)
Theorem raw_adjunction_graph_edge_cases G g p h a b x y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 raw_adjunction g p h -> G ⊢238 raw_kuratowski p a b ->
  G ⊢238 graph_edge h x y ->
  G ⊢238 (graph_edge g x y ∨ (E x a ∧ E y b)).
Proof.
  destruct g as [ig|[]], p as [ip|[]], h as [ih|[]], a as [ia|[]],
    b as [ib|[]], x as [ix|[]], y as [iy|[]].
  intros HE HQ HEq HEtr HA HP Hedge. unfold graph_edge in Hedge.
  eapply ExE_named; [exact Hedge|]. intro q. destruct q as [iq|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply DE.
  - apply (raw_adjunction_member _ $ig $ip $ih $iq); [inherit HA|].
    eapply CE1, Ctx. now left.
  - apply DI1. apply (graph_edge_from_entry _ $ig $ix $iy $iq).
    + apply Ctx. now left.
    + eapply CE2, Ctx. right. now left.
  - apply DI2. apply (raw_kuratowski_unique _ $ip $ix $iy $ia $ib).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + apply (raw_kuratowski_container_transport _ $iq $ip $ix $iy).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * apply Ctx. now left.
      * eapply CE2, Ctx. right. now left.
    + inherit HP.
Qed.

Print Assumptions raw_kuratowski_coordinate_transport.
Print Assumptions raw_kuratowski_container_transport.
Print Assumptions graph_edge_coordinate_transport.
Print Assumptions raw_adjunction_graph_edge_cases.
End GraphTransport238.
