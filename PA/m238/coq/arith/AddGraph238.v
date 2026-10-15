(** Actual finite addition traces, with recursion in the first PA operand.
    Trace entries are source Kuratowski sets.  Adjunction extends a trace;
    full S0 ordinal induction constructs it.  Raw equality is used inside
    one trace and concrete order isomorphism compares different traces. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  OrdinalTrace238 PairGraph238 GraphTransport238 TraceGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 OrdinalTrace238.OrdinalTrace238
  PairGraph238.PairGraph238 GraphTransport238.GraphTransport238
  TraceGraph238.TraceGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module AddGraph238.

Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition add_recurrence (g : set_term) : set_form :=
  ∀ ∀ ∀ ((graph_edge g`[↑]`[↑]`[↑] $2 $1 ∧ raw_successor $0 $2) →
    ∃ (graph_edge g`[↑]`[↑]`[↑]`[↑] $1 $0 ∧ raw_successor $0 $2)).
Definition add_prefix (top base zero g : set_term) : set_form :=
  graph_domain top g ∧ (graph_functional g ∧ (graph_range g ∧
    (graph_edge g zero base ∧ add_recurrence g))).
Definition add_result (x y z : set_term) : set_form :=
  ∃ ∃ (raw_zero $1 ∧ (add_prefix x`[↑]`[↑] y`[↑]`[↑] $1 $0 ∧
    graph_edge $0 x`[↑]`[↑] z`[↑]`[↑])).
Definition add_prefix_exists (x y : set_term) : set_form :=
  ∃ ∃ (raw_zero $1 ∧ add_prefix x`[↑]`[↑] y`[↑]`[↑] $1 $0).
Definition add_total_property (x : set_term) : set_form :=
  ∀ (ordinal_representative $0 → add_prefix_exists x`[↑] $0).

Lemma add_prefix_subst top base zero g sigma :
  (add_prefix top base zero g)[sigma] =
  add_prefix top`[sigma] base`[sigma] zero`[sigma] g`[sigma].
Proof.
  unfold add_prefix, graph_domain, graph_functional, graph_range,
    add_recurrence, ordinal_representative, member_ir, representative,
    transitive, member_transitive, member_linear, internal_extrema, subset,
    nonempty, least, greatest, raw_successor, graph_edge, raw_kuratowski,
    raw_pair, raw_singleton, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma add_prefix_exists_subst x y sigma :
  (add_prefix_exists x y)[sigma] = add_prefix_exists x`[sigma] y`[sigma].
Proof.
  unfold add_prefix_exists, raw_zero. cbn [subst_form].
  rewrite add_prefix_subst. cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma add_total_property_subst x sigma :
  (add_total_property x)[sigma] = add_total_property x`[sigma].
Proof.
  unfold add_total_property. cbn [subst_form].
  rewrite add_prefix_exists_subst.
  unfold ordinal_representative, member_ir, representative, transitive,
    member_transitive, member_linear, internal_extrema, subset, nonempty,
    least, greatest, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma add_total_property_at x :
  (add_total_property $0)[x..] = add_total_property x.
Proof. rewrite add_total_property_subst. reflexivity. Qed.

Lemma add_total_property_instance G x y :
  G ⊢238 add_total_property x -> G ⊢238 ordinal_representative y ->
  G ⊢238 add_prefix_exists x y.
Proof.
  destruct x as [ix|[]], y as [iy|[]]. intros HT HY.
  unfold add_total_property in HT. pose proof (AllE $iy HT) as H.
  cbn [subst_form] in H. rewrite add_prefix_exists_subst in H.
  cbn [subst_term up scons funcomp] in H.
  eapply IE; [exact H|exact HY].
Qed.

Lemma raw_zero_coordinate_transport G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E a b ->
  G ⊢238 raw_zero a -> G ⊢238 raw_zero b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HQ HEq Hab HZ.
  unfold raw_zero. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply IE; [inherit (zero_excludes_member _ $ia $iz HZ)|].
  apply (equality_container_transport _ $ib $ia $iz).
  - inherit HE.
  - inherit HQ.
  - apply equality_symmetry_instance; [inherit HEq|inherit Hab].
  - apply Ctx. now left.
Qed.

Lemma raw_successor_coordinate_transport G a b a' b' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 E a a' -> G ⊢238 E b b' ->
  G ⊢238 raw_successor a b -> G ⊢238 raw_successor a' b'.
Proof.
  destruct a as [ia|[]], b as [ib|[]], a' as [ia'|[]], b' as [ib'|[]].
  intros HE HQ HEq HEtr Haa Hbb HS. unfold raw_successor.
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. eapply DE.
    + apply (raw_successor_member_cases _ $ia $ib $iz); [inherit HS|].
      apply (equality_container_transport _ $ib' $ib $iz).
      * inherit HE.
      * inherit HQ.
      * apply equality_symmetry_instance; [inherit HEq|inherit Hbb].
      * apply Ctx. now left.
    + apply DI1. apply (equality_container_transport _ $ia $ia' $iz).
      * inherit HE.
      * inherit HQ.
      * inherit Haa.
      * apply Ctx. now left.
    + apply DI2. apply (equality_transitivity_instance _ $iz $ia $ia').
      * inherit HEtr.
      * apply Ctx. now left.
      * inherit Haa.
  - apply II. apply (equality_container_transport _ $ib $ib' $iz).
    + inherit HE.
    + inherit HQ.
    + inherit Hbb.
    + apply (raw_successor_member_intro _ $ia $ib $iz); [inherit HS|].
      eapply DE; [apply Ctx; now left| |].
      * apply DI1. apply (equality_container_transport _ $ia' $ia $iz).
        -- inherit HE.
        -- inherit HQ.
        -- apply equality_symmetry_instance; [inherit HEq|inherit Haa].
        -- apply Ctx. now left.
      * apply DI2. apply (equality_transitivity_instance _ $iz $ia' $ia).
        -- inherit HEtr.
        -- apply Ctx. now left.
        -- apply equality_symmetry_instance; [inherit HEq|inherit Haa].
Qed.

(** Two actual predecessors of the same successor inside a strict
    transitive ordinal agree by raw equality.  Extensionality is absent. *)
Lemma ordinal_successor_predecessor_unique G a b p :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 ordinal_representative a ->
  G ⊢238 raw_successor a b -> G ⊢238 raw_successor p b -> G ⊢238 E p a.
Proof.
  intros HE HQ HEq HR HS HP.
  assert (Hnot : G ⊢238 (¬ R a a)).
  { apply member_ir_not_self. exact (CE2 HR). }
  eapply DE.
  - apply (raw_successor_member_cases _ a b p); [exact HS|].
    apply (raw_successor_point_member _ p b); assumption.
  - eapply DE.
    + apply (raw_successor_member_cases _ p b a); [inherit HP|].
      apply (raw_successor_point_member _ a b); [inherit HE|inherit HS].
    + apply Exp. eapply IE; [inherit Hnot|].
      apply (transitive_member _ a p a).
      * inherit (CE1 (CE1 HR)).
      * apply Ctx. right. now left.
      * apply Ctx. now left.
    + apply Exp. eapply IE; [inherit Hnot|].
      apply (equality_member_transport _ a p a).
      * inherit HE.
      * inherit HQ.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
      * apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Lemma add_recurrence_instance G g i v p :
  G ⊢238 add_recurrence g -> G ⊢238 graph_edge g i v ->
  G ⊢238 raw_successor p i ->
  G ⊢238 ∃ (graph_edge g`[↑] p`[↑] $0 ∧ raw_successor $0 v`[↑]).
Proof.
  destruct g as [ig|[]], i as [ii|[]], v as [iv|[]], p as [ip|[]].
  intros HR HE HS. unfold add_recurrence in HR.
  pose proof (AllE $ip (AllE $iv (AllE $ii HR))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma graph_extension_old_edge G g h a b i v :
  G ⊢238 graph_edge_extension g h a b ->
  G ⊢238 graph_edge g i v -> G ⊢238 graph_edge h i v.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]],
    i as [ii|[]], v as [iv|[]]. intros HX HE.
  unfold graph_edge_extension in HX. pose proof (AllE $iv (AllE $ii HX)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact (CE2 H)|]. apply DI1. exact HE.
Qed.

Lemma graph_extension_edge_cases G g h a b i v :
  G ⊢238 graph_edge_extension g h a b -> G ⊢238 graph_edge h i v ->
  G ⊢238 (graph_edge g i v ∨ (E i a ∧ E v b)).
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]],
    i as [ii|[]], v as [iv|[]]. intros HX HE.
  unfold graph_edge_extension in HX. pose proof (AllE $iv (AllE $ii HX)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (CE1 H) HE).
Qed.

Lemma singleton_add_recurrence G g zero :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 raw_zero zero ->
  G ⊢238 (∀ ∀ (graph_edge g`[↑]`[↑] $1 $0 → E $1 zero`[↑]`[↑])) ->
  G ⊢238 add_recurrence g.
Proof.
  destruct g as [ig|[]], zero as [ie|[]].
  intros HE HQ HEq HZ Hkey. unfold add_recurrence.
  apply AllI_named. intro i. destruct i as [ii|[]].
  apply AllI_named. intro v. destruct v as [iv|[]].
  apply AllI_named. intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply II, Exp.
  assert (Hi : (graph_edge $ig $ii $iv ∧ raw_successor $ip $ii :: G)
    ⊢238 E $ii $ie).
  { pose proof (AllE $iv (AllE $ii Hkey)) as H.
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
    eapply IE; [inherit H|]. eapply CE1, Ctx. now left. }
  eapply IE; [inherit (zero_excludes_member _ $ie $ip HZ)|].
  apply (equality_container_transport _ $ii $ie $ip).
  - inherit HE.
  - inherit HQ.
  - exact Hi.
  - apply (raw_successor_point_member _ $ip $ii); [inherit HE|].
    eapply CE2, Ctx. now left.
Qed.

(** The only new recurrence case is the adjoined top index.  Its actual
    predecessor is the old top; the old endpoint and the freshly built
    successor value witness the required backwards edge. *)
Theorem add_recurrence_successor_extension G g h a b z w :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 raw_successor a b ->
  G ⊢238 add_recurrence g -> G ⊢238 graph_edge g a z ->
  G ⊢238 raw_successor z w -> G ⊢238 graph_edge_extension g h b w ->
  G ⊢238 add_recurrence h.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]],
    z as [iz|[]], w as [iw|[]].
  intros HE HQ HEq HEtr HR HS Hrec Htop Hsw HX. unfold add_recurrence.
  apply AllI_named. intro i. destruct i as [ii|[]].
  apply AllI_named. intro v. destruct v as [iv|[]].
  apply AllI_named. intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (graph_extension_edge_cases _ $ig $ih $ib $iw $ii $iv).
    + inherit HX.
    + eapply CE1, Ctx. now left.
  - eapply ExE_named.
    + apply (add_recurrence_instance _ $ig $ii $iv $ip).
      * inherit Hrec.
      * apply Ctx. now left.
      * eapply CE2, Ctx. right. now left.
    + intro q. destruct q as [iq|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (ExI $iq).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * apply (graph_extension_old_edge _ $ig $ih $ib $iw $ip $iq).
        -- inherit HX.
        -- eapply CE1, Ctx. now left.
      * eapply CE2, Ctx. now left.
  - assert (Hpi : (E $ii $ib ∧ E $iv $iw ::
        graph_edge $ih $ii $iv ∧ raw_successor $ip $ii :: G)
        ⊢238 raw_successor $ip $ib).
    { apply (raw_successor_coordinate_transport _ $ip $ii $ip $ib).
      - inherit HE.
      - inherit HQ.
      - inherit HEq.
      - inherit HEtr.
      - inherit (AllE $ip HE).
      - eapply CE1, Ctx. now left.
      - eapply CE2, Ctx. right. now left. }
    assert (Hpa : (E $ii $ib ∧ E $iv $iw ::
        graph_edge $ih $ii $iv ∧ raw_successor $ip $ii :: G) ⊢238 E $ip $ia).
    { apply (ordinal_successor_predecessor_unique _ $ia $ib $ip).
      - inherit HE.
      - inherit HQ.
      - inherit HEq.
      - inherit HR.
      - inherit HS.
      - exact Hpi. }
    apply (ExI $iz).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
    + apply (graph_extension_old_edge _ $ig $ih $ib $iw $ip $iz).
      * inherit HX.
      * apply (graph_edge_coordinate_transport _ $ig $ia $iz $ip $iz).
        -- inherit HEq.
        -- inherit HEtr.
        -- apply equality_symmetry_instance; [inherit HEq|exact Hpa].
        -- inherit (AllE $iz HE).
        -- inherit Htop.
    + apply (raw_successor_coordinate_transport _ $iz $iw $iz $iv).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HEtr.
      * inherit (AllE $iz HE).
      * apply equality_symmetry_instance; [inherit HEq|]. eapply CE2, Ctx. now left.
      * inherit Hsw.
Qed.

(** The base graph is a singleton source set containing one actual
    Kuratowski entry.  An empty index makes the recurrence guard impossible. *)
Theorem add_prefix_base_exists G e y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 raw_zero e -> G ⊢238 ordinal_representative y ->
  G ⊢238 ∃ add_prefix e`[↑] y`[↑] e`[↑] $0.
Proof.
  destruct e as [ie|[]], y as [iy|[]]. intros HE HQ HEq HEtr Hempty HA HZ HY.
  eapply ExE_named.
  - apply (singleton_graph_exists _ $ie $iy); assumption.
  - intro g. destruct g as [ig|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HG : (singleton_graph $ie $iy $ig :: G) ⊢238 singleton_graph $ie $iy $ig).
    { apply Ctx. now left. }
    apply (ExI $ig).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    unfold add_prefix. apply CI.
    + apply (singleton_graph_domain _ $ie $iy $ig); [inherit HE|inherit HZ|exact HG].
    + apply CI.
      * apply (singleton_graph_functional _ $ie $iy $ig);
          [inherit HEq|inherit HEtr|exact HG].
      * apply CI.
        -- apply (singleton_graph_range _ $ie $iy $ig);
             [inherit HE|inherit HQ|inherit HEq|inherit HY|exact HG].
        -- apply CI.
           ++ apply (singleton_graph_intro _ $ie $iy $ig $ie $iy); [exact HG|].
              apply CI; [inherit (AllE $ie HE)|inherit (AllE $iy HE)].
           ++ apply (singleton_add_recurrence _ $ig $ie).
              ** inherit HE.
              ** inherit HQ.
              ** inherit HEq.
              ** inherit HZ.
              ** apply AllI_named. intro i. destruct i as [ii|[]].
                 apply AllI_named. intro v. destruct v as [iv|[]].
                 cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
                 apply II. eapply CE1.
                 apply (singleton_graph_cases _ $ie $iy $ig $ii $iv).
                 --- inherit HG.
                 --- apply Ctx. now left.
Qed.

Lemma add_prefix_top_value G x y e g :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 add_prefix x y e g ->
  G ⊢238 ∃ graph_edge g`[↑] x`[↑] $0.
Proof.
  intros HE HP. apply (graph_domain_value _ x g x); [exact (CE1 HP)|].
  apply DI2. exact (AllE x HE).
Qed.

Lemma add_prefix_value_ordinal G x y e g i z :
  G ⊢238 add_prefix x y e g -> G ⊢238 graph_edge g i z ->
  G ⊢238 ordinal_representative z.
Proof.
  intros HP Hz. apply (graph_range_at _ g i z); [|exact Hz].
  exact (CE1 (CE2 (CE2 HP))).
Qed.

Lemma add_prefix_exists_result G x y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 add_prefix_exists x y ->
  G ⊢238 ∃ add_result x`[↑] y`[↑] $0.
Proof.
  destruct x as [ix|[]], y as [iy|[]]. intros HE HP.
  unfold add_prefix_exists in HP. eapply ExE_named; [exact HP|].
  intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HZ : (raw_zero $ie ∧ add_prefix $ix $iy $ie $ig ::
      (∃ (raw_zero $ie`[↑] ∧ add_prefix $ix`[↑] $iy`[↑] $ie`[↑] $0)) :: G)
      ⊢238 raw_zero $ie).
  { eapply CE1, Ctx. now left. }
  assert (Hpref : (raw_zero $ie ∧ add_prefix $ix $iy $ie $ig ::
      (∃ (raw_zero $ie`[↑] ∧ add_prefix $ix`[↑] $iy`[↑] $ie`[↑] $0)) :: G)
      ⊢238 add_prefix $ix $iy $ie $ig).
  { eapply CE2, Ctx. now left. }
  eapply ExE_named.
  - apply (add_prefix_top_value _ $ix $iy $ie $ig); [inherit HE|exact Hpref].
  - intro z. destruct z as [iz|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (ExI $iz).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    unfold add_result. apply (ExI $ie).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (ExI $ig).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply CI; [inherit HZ|]. apply CI; [inherit Hpref|apply Ctx; now left].
Qed.

Lemma add_result_ordinal G x y z :
  G ⊢238 add_result x y z -> G ⊢238 ordinal_representative z.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]]. intro H.
  unfold add_result in H. eapply ExE_named; [exact H|].
  intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (add_prefix_value_ordinal _ $ix $iy $ie $ig $ix $iz).
  - eapply CE1, CE2, Ctx. now left.
  - eapply CE2, CE2, Ctx. now left.
Qed.

(** The successor value and the graph are both produced here.  The input
    ordinal and every value in its trace retain their concrete witnesses. *)
Theorem add_prefix_successor_extension G a b y e g z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 intersection_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 raw_successor a b ->
  G ⊢238 add_prefix a y e g -> G ⊢238 graph_edge g a z ->
  G ⊢238 ∃ ∃ (raw_successor z`[↑]`[↑] $1 ∧
    (add_prefix b`[↑]`[↑] y`[↑]`[↑] e`[↑]`[↑] $0 ∧ graph_edge $0 b`[↑]`[↑] $1)).
Proof.
  destruct a as [ia|[]], b as [ib|[]], y as [iy|[]], e as [ie|[]],
    g as [ig|[]], z as [iz|[]].
  intros HE HQ HEq HEtr Hempty HA HI HR HS HP Hz.
  assert (HZ : G ⊢238 ordinal_representative $iz).
  { apply (add_prefix_value_ordinal _ $ia $iy $ie $ig $ia $iz); assumption. }
  eapply ExE_named.
  - apply (ordinal_successor_exists _ $iz); assumption.
  - intro w. destruct w as [iw|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HW : (ordinal_representative $iw ∧ raw_successor $iz $iw :: G)
      ⊢238 ordinal_representative $iw).
    { eapply CE1, Ctx. now left. }
    assert (HSW : (ordinal_representative $iw ∧ raw_successor $iz $iw :: G)
      ⊢238 raw_successor $iz $iw).
    { eapply CE2, Ctx. now left. }
    eapply ExE_named.
    + apply (exact_graph_extension_exists _ $ig $ib $iw);
        [inherit HE|inherit HQ|inherit HEq|inherit HEtr|inherit Hempty|inherit HA].
    + intro h. destruct h as [ih|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      assert (HX : (graph_edge_extension $ig $ih $ib $iw ::
        ordinal_representative $iw ∧ raw_successor $iz $iw :: G)
        ⊢238 graph_edge_extension $ig $ih $ib $iw).
      { apply Ctx. now left. }
      apply (ExI $iw).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (ExI $ih).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply CI; [inherit HSW|]. apply CI.
      * unfold add_prefix. apply CI.
        -- apply (graph_extension_domain _ $ia $ib $ig $ih $iw).
           ++ inherit HE.
           ++ inherit HS.
           ++ inherit (CE1 HP).
           ++ exact HX.
        -- apply CI.
           ++ apply (graph_extension_functional _ $ia $ib $ig $ih $iw).
              ** inherit HE.
              ** inherit HQ.
              ** inherit HEq.
              ** inherit HEtr.
              ** inherit HR.
              ** inherit HS.
              ** inherit (CE1 HP).
              ** inherit (CE1 (CE2 HP)).
              ** exact HX.
           ++ apply CI.
              ** apply (graph_extension_range _ $ig $ih $ib $iw).
                 --- inherit HE.
                 --- inherit HQ.
                 --- inherit HEq.
                 --- inherit (CE1 (CE2 (CE2 HP))).
                 --- inherit HW.
                 --- exact HX.
              ** apply CI.
                 --- apply (graph_extension_old_edge _ $ig $ih $ib $iw $ie $iy).
                     +++ exact HX.
                     +++ inherit (CE1 (CE2 (CE2 (CE2 HP)))).
                 --- apply (add_recurrence_successor_extension _ $ig $ih $ia $ib $iz $iw).
                     +++ inherit HE.
                     +++ inherit HQ.
                     +++ inherit HEq.
                     +++ inherit HEtr.
                     +++ inherit HR.
                     +++ inherit HS.
                     +++ inherit (CE2 (CE2 (CE2 (CE2 HP)))).
                     +++ inherit Hz.
                     +++ inherit HSW.
                     +++ exact HX.
      * apply (graph_extension_new_edge _ $ig $ih $ib $iw); [inherit HE|exact HX].
Qed.

Lemma add_prefix_exists_successor G a b y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 intersection_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 raw_successor a b ->
  G ⊢238 add_prefix_exists a y -> G ⊢238 add_prefix_exists b y.
Proof.
  destruct a as [ia|[]], b as [ib|[]], y as [iy|[]].
  intros HE HQ HEq HEtr Hempty HA HI HR HS HP.
  unfold add_prefix_exists in HP. eapply ExE_named; [exact HP|].
  intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (Hpref : (raw_zero $ie ∧ add_prefix $ia $iy $ie $ig ::
      (∃ (raw_zero $ie`[↑] ∧ add_prefix $ia`[↑] $iy`[↑] $ie`[↑] $0)) :: G)
      ⊢238 add_prefix $ia $iy $ie $ig).
  { eapply CE2, Ctx. now left. }
  assert (HZ : (raw_zero $ie ∧ add_prefix $ia $iy $ie $ig ::
      (∃ (raw_zero $ie`[↑] ∧ add_prefix $ia`[↑] $iy`[↑] $ie`[↑] $0)) :: G)
      ⊢238 raw_zero $ie).
  { eapply CE1, Ctx. now left. }
  eapply ExE_named.
  - apply (add_prefix_top_value _ $ia $iy $ie $ig); [inherit HE|exact Hpref].
  - intro z. destruct z as [iz|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply ExE_named.
    + apply (add_prefix_successor_extension _ $ia $ib $iy $ie $ig $iz).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HEtr.
      * inherit Hempty.
      * inherit HA.
      * inherit HI.
      * inherit HR.
      * inherit HS.
      * inherit Hpref.
      * apply Ctx. now left.
    + intro w. destruct w as [iw|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      eapply ExE_named; [apply Ctx; now left|]. intro h. destruct h as [ih|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      unfold add_prefix_exists. apply (ExI $ie).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (ExI $ih).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * inherit HZ.
      * eapply CE1, CE2, Ctx. now left.
Qed.

Lemma add_ordinal_step_intro G phi :
  (forall m b,
    (phi[m..] :: (ordinal_representative m ∧
      (ordinal_representative b ∧ raw_successor m b)) :: G) ⊢238 phi[b..]) ->
  G ⊢238 ordinal_step phi.
Proof.
  intro H. unfold ordinal_step. apply AllI_named. intro m. destruct m as [im|[]].
  apply AllI_named. intro b. destruct b as [ib|[]].
  cbn [subst_form R E terms2 subst_term].
  rewrite predecessor_slots_specialize, successor_slots_specialize.
  apply II, II. apply H.
Qed.

Lemma add_induction_base G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 ordinal_base (add_total_property $0).
Proof.
  intros HE HQ HEq HEtr Hempty HA. unfold ordinal_base.
  apply AllI_named. intro a. destruct a as [ia|[]].
  change (G ⊢238 ((ordinal_representative $ia ∧ raw_zero $ia) →
    (add_total_property $0)[$ia..])).
  rewrite add_total_property_at. apply II. unfold add_total_property.
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [subst_form]. rewrite add_prefix_exists_subst.
  cbn [subst_term up scons funcomp]. apply II.
  assert (HZa : (ordinal_representative $iy ::
      ordinal_representative $ia ∧ raw_zero $ia :: G) ⊢238 raw_zero $ia).
  { eapply CE2, Ctx. right. now left. }
  eapply ExE_named.
  - apply (add_prefix_base_exists _ $ia $iy).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Hempty.
    + inherit HA.
    + exact HZa.
    + apply Ctx. now left.
  - intro g. destruct g as [ig|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    unfold add_prefix_exists. apply (ExI $ia).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (ExI $ig).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
    + inherit HZa.
    + apply Ctx. now left.
Qed.

Lemma add_induction_step G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 intersection_ax ->
  G ⊢238 ordinal_step (add_total_property $0).
Proof.
  intros HE HQ HEq HEtr Hempty HA HI. apply add_ordinal_step_intro.
  intros a b. destruct a as [ia|[]], b as [ib|[]]. rewrite !add_total_property_at.
  unfold add_total_property at 1. apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [subst_form]. rewrite add_prefix_exists_subst.
  cbn [subst_term up scons funcomp]. apply II.
  apply (add_prefix_exists_successor _ $ia $ib $iy).
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit Hempty.
  - inherit HA.
  - inherit HI.
  - eapply CE1, Ctx. right. right. now left.
  - eapply CE2, CE2, Ctx. right. right. now left.
  - apply (add_total_property_instance _ $ia $iy).
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Lemma add_total_property_bounded : bounded 1 (add_total_property $0).
Proof.
  unfold add_total_property, add_prefix_exists, add_prefix, graph_domain,
    graph_functional, graph_range, add_recurrence, ordinal_representative,
    member_ir, representative, raw_zero, raw_successor, transitive,
    member_transitive, member_linear, internal_extrema, subset, nonempty,
    least, greatest, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn. fixed_bounds.
Qed.

Lemma S0_add_induction_base :
  derivable finite_set_S0 (ordinal_base (add_total_property $0)).
Proof.
  destruct S0_empty as [Gempty [HGempty Hempty]].
  set (G := equality_base ++ (adjunction_ax :: Gempty)).
  assert (HE : G ⊢238 (∀ E $0 $0)).
  { apply Ctx. unfold G, equality_base. cbn. now left. }
  assert (HQ : G ⊢238 equality_membership_ax).
  { apply Ctx. unfold G, equality_base, equality_membership_ax. cbn.
    right. right. right. now left. }
  assert (HEq : G ⊢238 equality_symmetry_ax).
  { apply Ctx. unfold G, equality_base, equality_symmetry_ax. cbn. right. now left. }
  assert (HEtr : G ⊢238 equality_transitivity_ax).
  { apply Ctx. unfold G, equality_base, equality_transitivity_ax. cbn.
    right. right. now left. }
  assert (HA : G ⊢238 adjunction_ax).
  { apply Ctx. unfold G, equality_base. cbn. right. right. right. right. now left. }
  assert (Hempty' : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|[<-|Hpsi]].
    + apply S0_base. apply in_or_app. now left.
    + apply S0_base. apply in_or_app. right. now left.
    + now apply HGempty.
  - apply add_induction_base; assumption.
Qed.

Lemma S0_add_induction_step :
  derivable finite_set_S0 (ordinal_step (add_total_property $0)).
Proof.
  destruct S0_empty as [Gempty [HGempty Hempty]].
  set (G := equality_base ++ [adjunction_ax; intersection_ax] ++ Gempty).
  assert (HE : G ⊢238 (∀ E $0 $0)).
  { apply Ctx. unfold G, equality_base. cbn. now left. }
  assert (HQ : G ⊢238 equality_membership_ax).
  { apply Ctx. unfold G, equality_base, equality_membership_ax. cbn.
    right. right. right. now left. }
  assert (HEq : G ⊢238 equality_symmetry_ax).
  { apply Ctx. unfold G, equality_base, equality_symmetry_ax. cbn. right. now left. }
  assert (HEtr : G ⊢238 equality_transitivity_ax).
  { apply Ctx. unfold G, equality_base, equality_transitivity_ax. cbn.
    right. right. now left. }
  assert (HA : G ⊢238 adjunction_ax).
  { apply Ctx. unfold G, equality_base. cbn. right. right. right. right. now left. }
  assert (HI : G ⊢238 intersection_ax).
  { apply Ctx. unfold G, equality_base. cbn.
    right. right. right. right. right. now left. }
  assert (Hempty' : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + apply in_app_or in Hpsi as [[<-|[<-|[]]]|Hpsi].
      * apply S0_base. apply in_or_app. right. now left.
      * apply S0_intersection_allowed.
      * now apply HGempty.
  - apply add_induction_step; assumption.
Qed.

(** Closed finite S0 induction supplies the whole graph construction.
    This theorem has no theorem-rule witness or arithmetic law suppliers. *)
Theorem S0_add_prefix_total x y :
  derivable finite_set_S0
    (ordinal_representative x → ordinal_representative y → add_prefix_exists x y).
Proof.
  pose proof (S0_ordinal_induction 0 (add_total_property $0)
    add_total_property_bounded) as HI.
  pose proof (derivable_mp finite_set_S0 _ _ HI S0_add_induction_base) as HS.
  destruct (derivable_mp finite_set_S0 _ _ HS S0_add_induction_step)
    as [G [HG Hforall]].
  exists G. split; [exact HG|]. destruct x as [ix|[]], y as [iy|[]].
  pose proof (AllE $ix Hforall) as H.
  change (G ⊢238 (ordinal_representative $ix →
    (add_total_property $0)[$ix..])) in H.
  rewrite add_total_property_at in H. apply II, II.
  apply (add_total_property_instance _ $ix $iy).
  - eapply IE; [inherit H|]. apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Theorem S0_add_total x y :
  derivable finite_set_S0
    ((ordinal_representative x ∧ ordinal_representative y) →
      ∃ add_result x`[↑] y`[↑] $0).
Proof.
  destruct (S0_add_prefix_total x y) as [Gp [HGp HP]].
  exists ((∀ E $0 $0) :: Gp). split.
  - intros phi [<-|Hphi].
    + apply S0_base. apply in_or_app. left. now left.
    + now apply HGp.
  - apply II, add_prefix_exists_result.
    + apply Ctx. right. now left.
    + eapply IE; [|eapply CE2, Ctx; now left].
      eapply IE; [inherit HP|eapply CE1, Ctx; now left].
Qed.

Lemma add_prefix_coordinate_transport G x y e g x' y' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 E x x' -> G ⊢238 E y y' ->
  G ⊢238 add_prefix x y e g -> G ⊢238 add_prefix x' y' e g.
Proof.
  intros HE HQ HEq HEtr Hxx Hyy HP. unfold add_prefix. apply CI.
  - apply (graph_domain_coordinate_transport _ x x' g);
      [exact HE|exact HQ|exact HEq|exact HEtr|exact Hxx|exact (CE1 HP)].
  - apply CI; [exact (CE1 (CE2 HP))|].
    apply CI; [exact (CE1 (CE2 (CE2 HP)))|]. apply CI.
    + apply (graph_edge_coordinate_transport _ g e y e y');
        [exact HEq|exact HEtr|exact (AllE e HE)|exact Hyy|].
      exact (CE1 (CE2 (CE2 (CE2 HP)))).
    + exact (CE2 (CE2 (CE2 (CE2 HP)))).
Qed.

(** Literal operand and result aliases are eliminated by a finite proof
    of congruence.  The same actual zero and graph witnesses are retained. *)
Theorem add_result_coordinate_transport G x y z x' y' z' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 E x x' -> G ⊢238 E y y' -> G ⊢238 E z z' ->
  G ⊢238 add_result x y z -> G ⊢238 add_result x' y' z'.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]],
    x' as [ix'|[]], y' as [iy'|[]], z' as [iz'|[]].
  intros HE HQ HEq HEtr Hxx Hyy Hzz H.
  unfold add_result in H. eapply ExE_named; [exact H|].
  intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  unfold add_result. apply (ExI $ie).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (ExI $ig).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - eapply CE1, Ctx. now left.
  - apply CI.
    + apply (add_prefix_coordinate_transport _ $ix $iy $ie $ig $ix' $iy').
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HEtr.
      * inherit Hxx.
      * inherit Hyy.
      * eapply CE1, CE2, Ctx. now left.
    + apply (graph_edge_coordinate_transport _ $ig $ix $iz $ix' $iz').
      * inherit HEq.
      * inherit HEtr.
      * inherit Hxx.
      * inherit Hzz.
      * eapply CE2, CE2, Ctx. now left.
Qed.

(** Empty objects are not globally identified.  Two empty indices in the
    inclusive domain of one ordinal are equal because its members are
    linearly ordered; strict alternatives contradict their emptiness. *)
Lemma ordinal_inclusive_zero_unique G top i e :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_representative top -> G ⊢238 raw_zero i -> G ⊢238 raw_zero e ->
  G ⊢238 (R top i ∨ E i top) -> G ⊢238 (R top e ∨ E e top) -> G ⊢238 E i e.
Proof.
  intros HE HQ HEq HEtr HT HZi HZe Hi He. eapply DE; [exact Hi| |].
  - eapply DE; [inherit He| |].
    + eapply DE.
      * apply (linear_member_cases _ top i e).
        -- inherit (CE1 (CE2 (CE2 (CE1 HT)))).
        -- apply Ctx. right. now left.
        -- apply Ctx. now left.
      * apply Ctx. now left.
      * eapply DE; [apply Ctx; now left| |].
        -- apply Exp. eapply IE; [inherit (zero_excludes_member _ e i HZe)|].
           apply Ctx. now left.
        -- apply Exp. eapply IE; [inherit (zero_excludes_member _ i e HZi)|].
           apply Ctx. now left.
    + apply Exp. eapply IE; [inherit (zero_excludes_member _ e i HZe)|].
      apply (equality_container_transport _ top e i).
      * inherit HE.
      * inherit HQ.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
      * apply Ctx. right. now left.
  - eapply DE; [inherit He| |].
    + apply Exp. eapply IE; [inherit (zero_excludes_member _ i e HZi)|].
      apply (equality_container_transport _ top i e).
      * inherit HE.
      * inherit HQ.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; right; now left].
      * apply Ctx. now left.
    + apply (equality_transitivity_instance _ i top e).
      * inherit HEtr.
      * apply Ctx. right. now left.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
Qed.

Lemma add_prefix_zero_value G top y e g i v :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_representative top -> G ⊢238 raw_zero e -> G ⊢238 raw_zero i ->
  G ⊢238 add_prefix top y e g -> G ⊢238 graph_edge g i v -> G ⊢238 E v y.
Proof.
  intros HE HQ HEq HEtr HT HZe HZi HP Hv.
  assert (Hinitial : G ⊢238 graph_edge g e y).
  { exact (CE1 (CE2 (CE2 (CE2 HP)))). }
  assert (Hie : G ⊢238 E i e).
  { apply (ordinal_inclusive_zero_unique _ top i e).
    - exact HE.
    - exact HQ.
    - exact HEq.
    - exact HEtr.
    - exact HT.
    - exact HZi.
    - exact HZe.
    - apply (graph_domain_edge _ top g i v); [exact (CE1 HP)|exact Hv].
    - apply (graph_domain_edge _ top g e y); [exact (CE1 HP)|exact Hinitial]. }
  apply (graph_functional_at _ g e v y).
  - exact (CE1 (CE2 HP)).
  - apply (graph_edge_coordinate_transport _ g i v e v);
      [exact HEq|exact HEtr|exact Hie|exact (AllE v HE)|exact Hv].
  - exact Hinitial.
Qed.

Theorem add_result_zero_value G x y z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_representative x -> G ⊢238 raw_zero x ->
  G ⊢238 add_result x y z -> G ⊢238 E z y.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]].
  intros HE HQ HEq HEtr HX HZ H. unfold add_result in H.
  eapply ExE_named; [exact H|]. intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (add_prefix_zero_value _ $ix $iy $ie $ig $ix $iz).
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit HX.
  - eapply CE1, Ctx. now left.
  - inherit HZ.
  - eapply CE1, CE2, Ctx. now left.
  - eapply CE2, CE2, Ctx. now left.
Qed.

Print Assumptions ordinal_inclusive_zero_unique.
Print Assumptions add_result_zero_value.
Print Assumptions add_result_coordinate_transport.
Print Assumptions S0_add_total.
Print Assumptions S0_add_prefix_total.
Print Assumptions add_prefix_successor_extension.
Print Assumptions add_prefix_base_exists.
Print Assumptions add_prefix_exists_result.
Print Assumptions raw_successor_coordinate_transport.
Print Assumptions ordinal_successor_predecessor_unique.
Print Assumptions add_recurrence_successor_extension.
End AddGraph238.
