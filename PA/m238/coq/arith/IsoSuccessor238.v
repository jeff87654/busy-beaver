(** Actual successor congruence of ordinal isomorphism.  One finite
    Adjunction adds the endpoints to the old order-bijection graph. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 GraphTransport238 TraceGraph238 IsoGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  GraphTransport238.GraphTransport238 TraceGraph238.TraceGraph238
  IsoGraph238.IsoGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module IsoSuccessor238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma order_graph_typed_at G g a b x y :
  G ⊢238 graph_typed g a b -> G ⊢238 graph_edge g x y ->
  G ⊢238 (R a x ∧ R b y).
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]], x as [ix|[]], y as [iy|[]].
  intros HT HX. unfold graph_typed in HT. pose proof (AllE $iy (AllE $ix HT)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HX).
Qed.

Lemma order_graph_functional_at G g x y z :
  G ⊢238 graph_functional g -> G ⊢238 graph_edge g x y ->
  G ⊢238 graph_edge g x z -> G ⊢238 E y z.
Proof.
  destruct g as [ig|[]], x as [ix|[]], y as [iy|[]], z as [iz|[]].
  intros HF HY HZ. unfold graph_functional in HF.
  pose proof (AllE $iz (AllE $iy (AllE $ix HF))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma order_graph_injective_at G g x y z :
  G ⊢238 graph_injective g -> G ⊢238 graph_edge g x z ->
  G ⊢238 graph_edge g y z -> G ⊢238 E x y.
Proof.
  destruct g as [ig|[]], x as [ix|[]], y as [iy|[]], z as [iz|[]].
  intros HF HX HY. unfold graph_injective in HF.
  pose proof (AllE $iz (AllE $iy (AllE $ix HF))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma order_graph_order_at G g x y u v :
  G ⊢238 graph_order g -> G ⊢238 graph_edge g x u ->
  G ⊢238 graph_edge g y v -> G ⊢238 (R x y ↔ R u v).
Proof.
  destruct g as [ig|[]], x as [ix|[]], y as [iy|[]], u as [iu|[]], v as [iv|[]].
  intros HO HX HY. unfold graph_order in HO.
  pose proof (AllE $iv (AllE $iu (AllE $iy (AllE $ix HO)))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma ordinal_member_endpoint_false G a x :
  G ⊢238 transitive a -> G ⊢238 member_ir a -> G ⊢238 R a x ->
  G ⊢238 (¬ R x a).
Proof.
  intros HT HI HX. apply II. eapply IE; [inherit (member_ir_not_self _ a HI)|].
  apply (transitive_member _ a x a); [inherit HT|inherit HX|apply Ctx; now left].
Qed.

Lemma ordinal_member_endpoint_equal_false G a x :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 member_ir a -> G ⊢238 R a x -> G ⊢238 E x a -> G ⊢238 falsity.
Proof.
  intros HE HQ HI HX Hxa. eapply IE; [exact (member_ir_not_self _ a HI)|].
  apply (equality_member_transport _ a x a); assumption.
Qed.

Lemma ordinal_endpoint_pair_excludes G a x y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 member_ir a -> G ⊢238 E x a -> G ⊢238 E y a -> G ⊢238 (¬ R x y).
Proof.
  intros HE HQ HI Hxa Hya. apply II.
  eapply IE; [inherit (member_ir_not_self _ a HI)|].
  apply (equality_member_transport _ a y a); [inherit HE|inherit HQ|inherit Hya|].
  apply (equality_container_transport _ x a y);
    [inherit HE|inherit HQ|inherit Hxa|apply Ctx; now left].
Qed.

Lemma successor_bijection_entries G g p h a sa b sb :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 graph_entries g a b ->
  G ⊢238 raw_successor a sa -> G ⊢238 raw_successor b sb ->
  G ⊢238 raw_adjunction g p h -> G ⊢238 raw_kuratowski p a b ->
  G ⊢238 graph_entries h sa sb.
Proof.
  destruct g as [ig|[]], p as [ip|[]], h as [ih|[]], a as [ia|[]],
    sa as [isa|[]], b as [ib|[]], sb as [isb|[]].
  intros HE HQ HEq HG HSa HSb HA HP. unfold graph_entries.
  apply AllI_named. intro q. destruct q as [iq|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_adjunction_member _ $ig $ip $ih $iq); [inherit HA|apply Ctx; now left].
  - eapply ExE_named.
    + apply (graph_entries_instance _ $ig $ia $ib $iq); [inherit HG|apply Ctx; now left].
    + intro x. destruct x as [ix|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      eapply ExE_named; [apply Ctx; now left|]. intro y. destruct y as [iy|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (entry_witness_from_components _ $isa $isb $iq $ix $iy).
      * apply (raw_successor_old_member _ $ia $isa $ix); [inherit HSa|].
        eapply CE1, Ctx. now left.
      * apply (raw_successor_old_member _ $ib $isb $iy); [inherit HSb|].
        eapply CE1, CE2, Ctx. now left.
      * eapply CE2, CE2, Ctx. now left.
  - apply (entry_witness_from_components _ $isa $isb $iq $ia $ib).
    + apply (raw_successor_point_member _ $ia $isa); [inherit HE|inherit HSa].
    + apply (raw_successor_point_member _ $ib $isb); [inherit HE|inherit HSb].
    + apply (raw_kuratowski_container_transport _ $ip $iq $ia $ib).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
      * inherit HP.
Qed.

Lemma successor_bijection_typed G g h a sa b sb :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 graph_typed g a b ->
  G ⊢238 raw_successor a sa -> G ⊢238 raw_successor b sb ->
  G ⊢238 graph_edge_extension g h a b -> G ⊢238 graph_typed h sa sb.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], sa as [isa|[]],
    b as [ib|[]], sb as [isb|[]]. intros HE HQ HEq HT HSa HSb HX.
  unfold graph_typed. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (graph_extension_cases _ $ig $ih $ia $ib $ix $iy); [inherit HX|apply Ctx; now left].
  - apply CI.
    + apply (raw_successor_old_member _ $ia $isa $ix); [inherit HSa|].
      eapply CE1. apply (order_graph_typed_at _ $ig $ia $ib $ix $iy);
        [inherit HT|apply Ctx; now left].
    + apply (raw_successor_old_member _ $ib $isb $iy); [inherit HSb|].
      eapply CE2. apply (order_graph_typed_at _ $ig $ia $ib $ix $iy);
        [inherit HT|apply Ctx; now left].
  - apply CI.
    + apply (equality_member_transport _ $isa $ia $ix).
      * inherit HE.
      * inherit HQ.
      * apply equality_symmetry_instance; [inherit HEq|eapply CE1, Ctx; now left].
      * apply (raw_successor_point_member _ $ia $isa); [inherit HE|inherit HSa].
    + apply (equality_member_transport _ $isb $ib $iy).
      * inherit HE.
      * inherit HQ.
      * apply equality_symmetry_instance; [inherit HEq|eapply CE2, Ctx; now left].
      * apply (raw_successor_point_member _ $ib $isb); [inherit HE|inherit HSb].
Qed.

Lemma successor_bijection_left_total G g h a sa b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 equality_transitivity_ax -> G ⊢238 graph_left_total g a ->
  G ⊢238 raw_successor a sa -> G ⊢238 graph_edge_extension g h a b ->
  G ⊢238 graph_left_total h sa.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], sa as [isa|[]], b as [ib|[]].
  intros HE HEq HEtr HT HS HX. unfold graph_left_total in HT. unfold graph_left_total.
  apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_successor_member_cases _ $ia $isa $ix); [inherit HS|apply Ctx; now left].
  - pose proof (AllE $ix HT) as H.
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
    eapply ExE_named; [eapply IE; [inherit H|apply Ctx; now left]|].
    intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iy).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (graph_extension_old_edge _ $ig $ih $ia $ib $ix $iy); [inherit HX|apply Ctx; now left].
  - apply (ExI $ib).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (graph_extension_intro _ $ig $ih $ia $ib $ix $ib); [inherit HX|].
    apply DI2, CI; [apply Ctx; now left|inherit (AllE $ib HE)].
Qed.

Lemma successor_bijection_right_total G g h a b sb :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 equality_transitivity_ax -> G ⊢238 graph_right_total g b ->
  G ⊢238 raw_successor b sb -> G ⊢238 graph_edge_extension g h a b ->
  G ⊢238 graph_right_total h sb.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]], sb as [isb|[]].
  intros HE HEq HEtr HT HS HX. unfold graph_right_total in HT. unfold graph_right_total.
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_successor_member_cases _ $ib $isb $iy); [inherit HS|apply Ctx; now left].
  - pose proof (AllE $iy HT) as H.
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
    eapply ExE_named; [eapply IE; [inherit H|apply Ctx; now left]|].
    intro x. destruct x as [ix|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $ix).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (graph_extension_old_edge _ $ig $ih $ia $ib $ix $iy); [inherit HX|apply Ctx; now left].
  - apply (ExI $ia).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (graph_extension_intro _ $ig $ih $ia $ib $ia $iy); [inherit HX|].
    apply DI2, CI; [inherit (AllE $ia HE)|apply Ctx; now left].
Qed.

Lemma successor_bijection_functional G g h a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 member_ir a -> G ⊢238 graph_typed g a b ->
  G ⊢238 graph_functional g -> G ⊢238 graph_edge_extension g h a b ->
  G ⊢238 graph_functional h.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]].
  intros HE HQ HEq HEtr HI HT HF HX. unfold graph_functional.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (graph_extension_cases _ $ig $ih $ia $ib $ix $iy); [inherit HX|].
    eapply CE1, Ctx. now left.
  - eapply DE.
    + apply (graph_extension_cases _ $ig $ih $ia $ib $ix $iz); [inherit HX|].
      eapply CE2, Ctx. right. now left.
    + apply (order_graph_functional_at _ $ig $ix $iy $iz).
      * inherit HF.
      * apply Ctx. right. now left.
      * apply Ctx. now left.
    + apply Exp. apply (ordinal_member_endpoint_equal_false _ $ia $ix).
      * inherit HE.
      * inherit HQ.
      * inherit HI.
      * eapply CE1. apply (order_graph_typed_at _ $ig $ia $ib $ix $iy);
          [inherit HT|apply Ctx; right; now left].
      * eapply CE1, Ctx. now left.
  - eapply DE.
    + apply (graph_extension_cases _ $ig $ih $ia $ib $ix $iz); [inherit HX|].
      eapply CE2, Ctx. right. now left.
    + apply Exp. apply (ordinal_member_endpoint_equal_false _ $ia $ix).
      * inherit HE.
      * inherit HQ.
      * inherit HI.
      * eapply CE1. apply (order_graph_typed_at _ $ig $ia $ib $ix $iz);
          [inherit HT|apply Ctx; now left].
      * eapply CE1, Ctx. right. now left.
    + apply (equality_transitivity_instance _ $iy $ib $iz).
      * inherit HEtr.
      * eapply CE2, Ctx. right. now left.
      * apply equality_symmetry_instance; [inherit HEq|]. eapply CE2, Ctx. now left.
Qed.

Lemma successor_bijection_injective G g h a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 member_ir b -> G ⊢238 graph_typed g a b ->
  G ⊢238 graph_injective g -> G ⊢238 graph_edge_extension g h a b ->
  G ⊢238 graph_injective h.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]].
  intros HE HQ HEq HEtr HI HT HF HX. unfold graph_injective.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (graph_extension_cases _ $ig $ih $ia $ib $ix $iz); [inherit HX|].
    eapply CE1, Ctx. now left.
  - eapply DE.
    + apply (graph_extension_cases _ $ig $ih $ia $ib $iy $iz); [inherit HX|].
      eapply CE2, Ctx. right. now left.
    + apply (order_graph_injective_at _ $ig $ix $iy $iz).
      * inherit HF.
      * apply Ctx. right. now left.
      * apply Ctx. now left.
    + apply Exp. apply (ordinal_member_endpoint_equal_false _ $ib $iz).
      * inherit HE.
      * inherit HQ.
      * inherit HI.
      * eapply CE2. apply (order_graph_typed_at _ $ig $ia $ib $ix $iz);
          [inherit HT|apply Ctx; right; now left].
      * eapply CE2, Ctx. now left.
  - eapply DE.
    + apply (graph_extension_cases _ $ig $ih $ia $ib $iy $iz); [inherit HX|].
      eapply CE2, Ctx. right. now left.
    + apply Exp. apply (ordinal_member_endpoint_equal_false _ $ib $iz).
      * inherit HE.
      * inherit HQ.
      * inherit HI.
      * eapply CE2. apply (order_graph_typed_at _ $ig $ia $ib $iy $iz);
          [inherit HT|apply Ctx; now left].
      * eapply CE2, Ctx. right. now left.
    + apply (equality_transitivity_instance _ $ix $ia $iy).
      * inherit HEtr.
      * eapply CE1, Ctx. right. now left.
      * apply equality_symmetry_instance; [inherit HEq|]. eapply CE1, Ctx. now left.
Qed.

Lemma membership_equivalence_from_negations G phi psi :
  G ⊢238 (¬ phi) -> G ⊢238 (¬ psi) -> G ⊢238 (phi ↔ psi).
Proof.
  intros HP HQ. apply CI; apply II, Exp; eapply IE;
    [inherit HP|apply Ctx; now left|inherit HQ|apply Ctx; now left].
Qed.

Lemma membership_equivalence_from_proofs G phi psi :
  G ⊢238 phi -> G ⊢238 psi -> G ⊢238 (phi ↔ psi).
Proof. intros HP HQ. apply CI; apply II; [inherit HQ|inherit HP]. Qed.

Lemma ordinal_old_endpoint_equal_excludes G a x y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 transitive a -> G ⊢238 member_ir a ->
  G ⊢238 R a x -> G ⊢238 E y a -> G ⊢238 (¬ R x y).
Proof.
  intros HE HQ HT HI HX Hya. apply II.
  eapply IE; [inherit (ordinal_member_endpoint_false _ a x HT HI HX)|].
  apply (equality_member_transport _ x y a);
    [inherit HE|inherit HQ|inherit Hya|apply Ctx; now left].
Qed.

Lemma successor_bijection_order G g h a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 transitive a -> G ⊢238 member_ir a ->
  G ⊢238 transitive b -> G ⊢238 member_ir b -> G ⊢238 graph_typed g a b ->
  G ⊢238 graph_order g -> G ⊢238 graph_edge_extension g h a b -> G ⊢238 graph_order h.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]].
  intros HE HQ HEq HTa HIa HTb HIb HT HO HX. unfold graph_order.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro u. destruct u as [iu|[]].
  apply AllI_named. intro v. destruct v as [iv|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (graph_extension_cases _ $ig $ih $ia $ib $ix $iu); [inherit HX|].
    eapply CE1, Ctx. now left.
  - eapply DE.
    + apply (graph_extension_cases _ $ig $ih $ia $ib $iy $iv); [inherit HX|].
      eapply CE2, Ctx. right. now left.
    + apply (order_graph_order_at _ $ig $ix $iy $iu $iv);
        [inherit HO|apply Ctx; right; now left|apply Ctx; now left].
    + apply membership_equivalence_from_negations.
      * apply (ordinal_old_endpoint_equal_excludes _ $ia $ix $iy).
        -- inherit HE.
        -- inherit HQ.
        -- inherit HTa.
        -- inherit HIa.
        -- eapply CE1. apply (order_graph_typed_at _ $ig $ia $ib $ix $iu);
             [inherit HT|apply Ctx; right; now left].
        -- eapply CE1, Ctx. now left.
      * apply (ordinal_old_endpoint_equal_excludes _ $ib $iu $iv).
        -- inherit HE.
        -- inherit HQ.
        -- inherit HTb.
        -- inherit HIb.
        -- eapply CE2. apply (order_graph_typed_at _ $ig $ia $ib $ix $iu);
             [inherit HT|apply Ctx; right; now left].
        -- eapply CE2, Ctx. now left.
  - eapply DE.
    + apply (graph_extension_cases _ $ig $ih $ia $ib $iy $iv); [inherit HX|].
      eapply CE2, Ctx. right. now left.
    + apply membership_equivalence_from_proofs.
      * apply (equality_container_transport _ $ia $ix $iy).
        -- inherit HE.
        -- inherit HQ.
        -- apply equality_symmetry_instance; [inherit HEq|]. eapply CE1, Ctx. right. now left.
        -- eapply CE1. apply (order_graph_typed_at _ $ig $ia $ib $iy $iv);
             [inherit HT|apply Ctx; now left].
      * apply (equality_container_transport _ $ib $iu $iv).
        -- inherit HE.
        -- inherit HQ.
        -- apply equality_symmetry_instance; [inherit HEq|]. eapply CE2, Ctx. right. now left.
        -- eapply CE2. apply (order_graph_typed_at _ $ig $ia $ib $iy $iv);
             [inherit HT|apply Ctx; now left].
    + apply membership_equivalence_from_negations.
      * apply (ordinal_endpoint_pair_excludes _ $ia $ix $iy).
        -- inherit HE.
        -- inherit HQ.
        -- inherit HIa.
        -- eapply CE1, Ctx. right. now left.
        -- eapply CE1, Ctx. now left.
      * apply (ordinal_endpoint_pair_excludes _ $ib $iu $iv).
        -- inherit HE.
        -- inherit HQ.
        -- inherit HIb.
        -- eapply CE2, Ctx. right. now left.
        -- eapply CE2, Ctx. now left.
Qed.

Print Assumptions successor_bijection_functional.
Print Assumptions successor_bijection_injective.
Print Assumptions successor_bijection_order.
Theorem successor_order_bijection G g p h a sa b sb :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 ordinal_representative b ->
  G ⊢238 raw_successor a sa -> G ⊢238 raw_successor b sb ->
  G ⊢238 raw_adjunction g p h -> G ⊢238 raw_kuratowski p a b ->
  G ⊢238 order_bijection g a b -> G ⊢238 order_bijection h sa sb.
Proof.
  intros HE HQ HEq HEtr HA HB HSa HSb HAdj HK HG.
  assert (HX : G ⊢238 graph_edge_extension g h a b).
  { apply (raw_adjunction_exact_graph_extension _ g p h a b); assumption. }
  assert (HT : G ⊢238 graph_typed g a b).
  { exact (CE1 (CE2 HG)). }
  unfold order_bijection. apply CI.
  - apply (successor_bijection_entries _ g p h a sa b sb);
      [exact HE|exact HQ|exact HEq|exact (CE1 HG)|exact HSa|exact HSb|exact HAdj|exact HK].
  - apply CI.
    + apply (successor_bijection_typed _ g h a sa b sb); assumption.
    + apply CI.
      * apply (successor_bijection_left_total _ g h a sa b);
          [exact HE|exact HEq|exact HEtr|exact (CE1 (CE2 (CE2 HG)))|exact HSa|exact HX].
      * apply CI.
        -- apply (successor_bijection_right_total _ g h a b sb);
             [exact HE|exact HEq|exact HEtr|exact (CE1 (CE2 (CE2 (CE2 HG))))|exact HSb|exact HX].
        -- apply CI.
           ++ apply (successor_bijection_functional _ g h a b);
                [exact HE|exact HQ|exact HEq|exact HEtr|exact (CE2 HA)|exact HT|
                 exact (CE1 (CE2 (CE2 (CE2 (CE2 HG)))))|exact HX].
           ++ apply CI.
              ** apply (successor_bijection_injective _ g h a b);
                   [exact HE|exact HQ|exact HEq|exact HEtr|exact (CE2 HB)|exact HT|
                    exact (CE1 (CE2 (CE2 (CE2 (CE2 (CE2 HG))))))|exact HX].
              ** apply (successor_bijection_order _ g h a b);
                   [exact HE|exact HQ|exact HEq|exact (CE1 (CE1 HA))|exact (CE2 HA)|
                    exact (CE1 (CE1 HB))|exact (CE2 HB)|exact HT|
                    exact (CE2 (CE2 (CE2 (CE2 (CE2 (CE2 HG))))))|exact HX].
Qed.

(** The extension graph is genuinely produced by a Kuratowski constructor
    and one Adjunction.  Neither graph nor law is supplied externally. *)
Theorem order_iso_successor_congruence G a sa b sb :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 ordinal_representative b ->
  G ⊢238 raw_successor a sa -> G ⊢238 raw_successor b sb ->
  G ⊢238 order_iso a b -> G ⊢238 order_iso sa sb.
Proof.
  destruct a as [ia|[]], sa as [isa|[]], b as [ib|[]], sb as [isb|[]].
  intros HE HQ HEq HEtr Hempty HAdj HA HB HSa HSb HI.
  unfold order_iso in HI. eapply ExE_named; [exact HI|].
  intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HG : (order_bijection $ig $ia $ib :: G) ⊢238 order_bijection $ig $ia $ib).
  { apply Ctx. now left. }
  eapply ExE_named; [inherit Hempty|]. intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named.
  - apply (raw_kuratowski_exists _ $ie $ia $ib); [apply Ctx; now left|inherit HAdj].
  - intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply ExE_named; [apply (raw_adjunction_exists _ $ig $ip); inherit HAdj|].
    intro h. destruct h as [ih|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    unfold order_iso. apply (ExI $ih).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (successor_order_bijection _ $ig $ip $ih $ia $isa $ib $isb).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit HA.
    + inherit HB.
    + inherit HSa.
    + inherit HSb.
    + apply Ctx. now left.
    + apply Ctx. right. now left.
    + inherit HG.
Qed.

Print Assumptions order_iso_successor_congruence.
Print Assumptions successor_order_bijection.
Print Assumptions successor_bijection_order.
Print Assumptions successor_bijection_functional.
Print Assumptions successor_bijection_injective.
Print Assumptions successor_bijection_entries.
Print Assumptions successor_bijection_typed.
Print Assumptions successor_bijection_left_total.
Print Assumptions successor_bijection_right_total.
End IsoSuccessor238.
