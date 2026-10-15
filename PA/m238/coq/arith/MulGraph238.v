(** Actual finite multiplication traces, transposed to recursion on the
    first upstream PA operand. The recurrence adds the fixed second
    operand to the preceding value. No multiplication commutativity is
    used. Each trace is a real finite set of Kuratowski entries. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  OrdinalTrace238 PairGraph238 GraphTransport238 TraceGraph238 TraceRestriction238 AddGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 OrdinalTrace238.OrdinalTrace238
  PairGraph238.PairGraph238 GraphTransport238.GraphTransport238
  TraceGraph238.TraceGraph238 TraceRestriction238.TraceRestriction238 AddGraph238.AddGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module MulGraph238.

Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition mul_recurrence (g base : set_term) : set_form :=
  ∀ ∀ ∀ ((graph_edge g`[↑]`[↑]`[↑] $2 $1 ∧ raw_successor $0 $2) →
    ∃ (graph_edge g`[↑]`[↑]`[↑]`[↑] $1 $0 ∧
      add_result $0 base`[↑]`[↑]`[↑]`[↑] $2)).
Definition mul_prefix (top base zero g : set_term) : set_form :=
  graph_domain top g ∧ (graph_functional g ∧ (graph_range g ∧
    (graph_edge g zero zero ∧ mul_recurrence g base))).
Definition mul_result (x y z : set_term) : set_form :=
  ∃ ∃ (raw_zero $1 ∧ (mul_prefix x`[↑]`[↑] y`[↑]`[↑] $1 $0 ∧
    graph_edge $0 x`[↑]`[↑] z`[↑]`[↑])).
Definition mul_prefix_exists (x y : set_term) : set_form :=
  ∃ ∃ (raw_zero $1 ∧ mul_prefix x`[↑]`[↑] y`[↑]`[↑] $1 $0).
Definition mul_total_property (x : set_term) : set_form :=
  ∀ (ordinal_representative $0 → mul_prefix_exists x`[↑] $0).

Lemma mul_prefix_subst top base zero g sigma :
  (mul_prefix top base zero g)[sigma] =
  mul_prefix top`[sigma] base`[sigma] zero`[sigma] g`[sigma].
Proof.
  unfold mul_prefix, mul_recurrence, add_result, add_prefix, add_recurrence,
    graph_domain, graph_functional, graph_range, ordinal_representative,
    member_ir, representative, raw_zero, raw_successor, transitive,
    member_transitive, member_linear, internal_extrema, subset, nonempty,
    least, greatest, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma mul_prefix_exists_subst x y sigma :
  (mul_prefix_exists x y)[sigma] = mul_prefix_exists x`[sigma] y`[sigma].
Proof.
  unfold mul_prefix_exists, raw_zero. cbn [subst_form].
  rewrite mul_prefix_subst. cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma mul_total_property_subst x sigma :
  (mul_total_property x)[sigma] = mul_total_property x`[sigma].
Proof.
  unfold mul_total_property. cbn [subst_form].
  rewrite mul_prefix_exists_subst.
  unfold ordinal_representative, member_ir, representative, transitive,
    member_transitive, member_linear, internal_extrema, subset, nonempty,
    least, greatest, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma mul_total_property_at x :
  (mul_total_property $0)[x..] = mul_total_property x.
Proof. rewrite mul_total_property_subst. reflexivity. Qed.

Lemma mul_total_property_instance G x y :
  G ⊢238 mul_total_property x -> G ⊢238 ordinal_representative y ->
  G ⊢238 mul_prefix_exists x y.
Proof.
  destruct x as [ix|[]], y as [iy|[]]. intros HT HY.
  unfold mul_total_property in HT. pose proof (AllE $iy HT) as H.
  cbn [subst_form] in H. rewrite mul_prefix_exists_subst in H.
  cbn [subst_term up scons funcomp] in H.
  eapply IE; [exact H|exact HY].
Qed.

Lemma mul_recurrence_instance G g base i v p :
  G ⊢238 mul_recurrence g base -> G ⊢238 graph_edge g i v ->
  G ⊢238 raw_successor p i ->
  G ⊢238 ∃ (graph_edge g`[↑] p`[↑] $0 ∧ add_result $0 base`[↑] v`[↑]).
Proof.
  destruct g as [ig|[]], base as [ib|[]], i as [ii|[]], v as [iv|[]], p as [ip|[]].
  intros HR HE HS. unfold mul_recurrence in HR.
  pose proof (AllE $ip (AllE $iv (AllE $ii HR))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

(** A singleton zero-domain trace has no predecessor row, regardless of
    the fixed multiplier. Its recurrence is proved by the impossible
    successor member, and is not an assumed finite-recursion principle. *)
Lemma singleton_mul_recurrence G g zero base :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 raw_zero zero -> G ⊢238 singleton_graph zero zero g ->
  G ⊢238 mul_recurrence g base.
Proof.
  destruct g as [ig|[]], zero as [ie|[]], base as [ib|[]]. intros HE HQ HZ HG.
  unfold mul_recurrence. apply AllI_named. intro i. destruct i as [ii|[]].
  apply AllI_named. intro v. destruct v as [iv|[]].
  apply AllI_named. intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, Exp.
  eapply IE; [inherit (zero_excludes_member G $ie $ip HZ)|].
  apply (equality_container_transport _ $ii $ie $ip).
  - inherit HE.
  - inherit HQ.
  - eapply CE1. apply (singleton_graph_cases _ $ie $ie $ig $ii $iv).
    + inherit HG.
    + eapply CE1, Ctx. now left.
  - apply (raw_successor_point_member _ $ip $ii).
    + inherit HE.
    + eapply CE2, Ctx. now left.
Qed.

Lemma singleton_mul_prefix G zero base g :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 raw_zero zero -> G ⊢238 singleton_graph zero zero g ->
  G ⊢238 mul_prefix zero base zero g.
Proof.
  intros HE HQ HEq HEtr HZ HG. apply CI.
  - apply (singleton_graph_domain _ zero zero g); assumption.
  - apply CI.
    + apply (singleton_graph_functional _ zero zero g); assumption.
    + apply CI.
      * apply (singleton_graph_range _ zero zero g); try assumption.
        apply empty_ordinal_representative. exact HZ.
      * apply CI.
        -- apply (singleton_graph_intro _ zero zero g zero zero); [exact HG|].
           apply CI; exact (AllE zero HE).
        -- apply (singleton_mul_recurrence _ g zero base); assumption.
Qed.

Theorem mul_prefix_base G zero base :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 raw_zero zero ->
  G ⊢238 ∃ mul_prefix zero`[↑] base`[↑] zero`[↑] $0.
Proof.
  destruct zero as [ie|[]], base as [ib|[]]. intros HE HQ HEq HEtr Hempty HA HZ.
  eapply ExE_named.
  - apply (singleton_graph_exists _ $ie $ie); assumption.
  - intro g. destruct g as [ig|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (ExI $ig).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (singleton_mul_prefix _ $ie $ib $ig).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit HZ.
    + apply Ctx. now left.
Qed.

Lemma mul_prefix_domain G t base zero g :
  G ⊢238 mul_prefix t base zero g -> G ⊢238 graph_domain t g.
Proof. intro H. exact (CE1 H). Qed.
Lemma mul_prefix_functional G t base zero g :
  G ⊢238 mul_prefix t base zero g -> G ⊢238 graph_functional g.
Proof. intro H. exact (CE1 (CE2 H)). Qed.
Lemma mul_prefix_range G t base zero g :
  G ⊢238 mul_prefix t base zero g -> G ⊢238 graph_range g.
Proof. intro H. exact (CE1 (CE2 (CE2 H))). Qed.
Lemma mul_prefix_initial G t base zero g :
  G ⊢238 mul_prefix t base zero g -> G ⊢238 graph_edge g zero zero.
Proof. intro H. exact (CE1 (CE2 (CE2 (CE2 H)))). Qed.
Lemma mul_prefix_recurrence G t base zero g :
  G ⊢238 mul_prefix t base zero g -> G ⊢238 mul_recurrence g base.
Proof. intro H. exact (CE2 (CE2 (CE2 (CE2 H)))). Qed.

Lemma mul_prefix_top_value G t base zero g :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 mul_prefix t base zero g ->
  G ⊢238 ∃ graph_edge g`[↑] t`[↑] $0.
Proof.
  intros HE HP. apply (graph_domain_value _ t g t).
  - exact (mul_prefix_domain G t base zero g HP).
  - apply DI2. exact (AllE t HE).
Qed.

Lemma mul_result_from_witnesses G x y z zero g :
  G ⊢238 raw_zero zero -> G ⊢238 mul_prefix x y zero g ->
  G ⊢238 graph_edge g x z -> G ⊢238 mul_result x y z.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]], zero as [ie|[]], g as [ig|[]].
  intros HZ HP HE. unfold mul_result. apply (ExI $ie).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $ig).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply CI; [exact HZ|]. apply CI; assumption.
Qed.

Theorem mul_recurrence_successor_extension G g h a b base z w :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 raw_successor a b ->
  G ⊢238 mul_recurrence g base -> G ⊢238 graph_edge_extension g h b w ->
  G ⊢238 graph_edge g a z -> G ⊢238 add_result z base w ->
  G ⊢238 mul_recurrence h base.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]],
    base as [iy|[]], z as [iz|[]], w as [iw|[]].
  intros HE HQ HEq HEtr HA HS HR HX Hz Hzw. unfold mul_recurrence.
  apply AllI_named. intro i. destruct i as [ii|[]].
  apply AllI_named. intro v. destruct v as [iv|[]].
  apply AllI_named. intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  assert (Hpi : (graph_edge $ih $ii $iv ∧ raw_successor $ip $ii :: G)
    ⊢238 raw_successor $ip $ii).
  { eapply CE2, Ctx. now left. }
  eapply DE.
  - apply (graph_extension_cases _ $ig $ih $ib $iw $ii $iv); [inherit HX|].
    eapply CE1, Ctx. now left.
  - eapply ExE_named.
    + apply (mul_recurrence_instance _ $ig $iy $ii $iv $ip).
      * inherit HR.
      * apply Ctx. now left.
      * inherit Hpi.
    + intro q. destruct q as [iq|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (ExI $iq).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * apply (graph_extension_old_edge _ $ig $ih $ib $iw $ip $iq); [inherit HX|].
        eapply CE1, Ctx. now left.
      * eapply CE2, Ctx. now left.
  - assert (Hpb : (E $ii $ib ∧ E $iv $iw ::
        graph_edge $ih $ii $iv ∧ raw_successor $ip $ii :: G)
        ⊢238 raw_successor $ip $ib).
    { apply (raw_successor_coordinate_transport _ $ip $ii $ip $ib).
      - inherit HE.
      - inherit HQ.
      - inherit HEq.
      - inherit HEtr.
      - inherit (AllE $ip HE).
      - eapply CE1, Ctx. now left.
      - inherit Hpi. }
    assert (Hpa : (E $ii $ib ∧ E $iv $iw ::
        graph_edge $ih $ii $iv ∧ raw_successor $ip $ii :: G) ⊢238 E $ip $ia).
    { apply (ordinal_successor_predecessor_unique _ $ia $ib $ip).
      - inherit HE.
      - inherit HQ.
      - inherit HEq.
      - inherit HA.
      - inherit HS.
      - exact Hpb. }
    apply (ExI $iz).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
    + apply (graph_edge_coordinate_transport _ $ih $ia $iz $ip $iz).
      * inherit HEq.
      * inherit HEtr.
      * apply equality_symmetry_instance; [inherit HEq|exact Hpa].
      * inherit (AllE $iz HE).
      * apply (graph_extension_old_edge _ $ig $ih $ib $iw $ia $iz);
          [inherit HX|inherit Hz].
    + apply (add_result_coordinate_transport _ $iz $iy $iw $iz $iy $iv).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HEtr.
      * inherit (AllE $iz HE).
      * inherit (AllE $iy HE).
      * apply equality_symmetry_instance; [inherit HEq|eapply CE2, Ctx; now left].
      * inherit Hzw.
Qed.

Theorem mul_prefix_given_extension G a b base zero g h z w :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 raw_successor a b ->
  G ⊢238 mul_prefix a base zero g -> G ⊢238 graph_edge_extension g h b w ->
  G ⊢238 graph_edge g a z -> G ⊢238 add_result z base w ->
  G ⊢238 mul_prefix b base zero h.
Proof.
  intros HE HQ HEq HEtr HA HS HP HX Hz Hzw. apply CI.
  - apply (graph_extension_domain _ a b g h w); try assumption.
    exact (mul_prefix_domain G a base zero g HP).
  - apply CI.
    + apply (graph_extension_functional _ a b g h w); try assumption.
      * exact (mul_prefix_domain G a base zero g HP).
      * exact (mul_prefix_functional G a base zero g HP).
    + apply CI.
      * apply (graph_extension_range _ g h b w); try assumption.
        -- exact (mul_prefix_range G a base zero g HP).
        -- exact (add_result_ordinal G z base w Hzw).
      * apply CI.
        -- apply (graph_extension_old_edge _ g h b w zero zero); [exact HX|].
           exact (mul_prefix_initial G a base zero g HP).
        -- apply (mul_recurrence_successor_extension _ g h a b base z w); try assumption.
           exact (mul_prefix_recurrence G a base zero g HP).
Qed.

Definition closed_add_totality : set_form :=
  ∀ ∀ ((ordinal_representative $1 ∧ ordinal_representative $0) →
    ∃ add_result $2 $1 $0).

Lemma S0_closed_add_totality : derivable finite_set_S0 closed_add_totality.
Proof.
  unfold closed_add_totality. apply S0_generalize, S0_generalize.
  exact (S0_add_total $1 $0).
Qed.

Lemma closed_add_totality_instance G x y :
  G ⊢238 closed_add_totality -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative y -> G ⊢238 ∃ add_result x`[↑] y`[↑] $0.
Proof.
  destruct x as [ix|[]], y as [iy|[]]. intros HT HX HY.
  unfold closed_add_totality in HT. pose proof (AllE $iy (AllE $ix HT)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

(** Both new witnesses are produced: total addition constructs the value,
    and finite Adjunction constructs the extended graph. *)
Theorem mul_prefix_successor_extension G a b base zero g z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 closed_add_totality ->
  G ⊢238 ordinal_representative a -> G ⊢238 ordinal_representative base ->
  G ⊢238 raw_successor a b -> G ⊢238 mul_prefix a base zero g ->
  G ⊢238 graph_edge g a z ->
  G ⊢238 ∃ ∃ (add_result z`[↑]`[↑] base`[↑]`[↑] $1 ∧
    (mul_prefix b`[↑]`[↑] base`[↑]`[↑] zero`[↑]`[↑] $0 ∧ graph_edge $0 b`[↑]`[↑] $1)).
Proof.
  destruct a as [ia|[]], b as [ib|[]], base as [iy|[]], zero as [ie|[]],
    g as [ig|[]], z as [iz|[]]. intros HE HQ HEq HEtr Hempty HAD HT HA HY HS HP Hz.
  assert (HZ : G ⊢238 ordinal_representative $iz).
  { apply (graph_range_at _ $ig $ia $iz); [|exact Hz].
    exact (mul_prefix_range G $ia $iy $ie $ig HP). }
  eapply ExE_named.
  - apply (closed_add_totality_instance _ $iz $iy); assumption.
  - intro w. destruct w as [iw|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (Hzw : (add_result $iz $iy $iw :: G) ⊢238 add_result $iz $iy $iw).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (exact_graph_extension_exists _ $ig $ib $iw);
        [inherit HE|inherit HQ|inherit HEq|inherit HEtr|inherit Hempty|inherit HAD].
    + intro h. destruct h as [ih|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (ExI $iw).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (ExI $ih).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * inherit Hzw.
      * apply CI.
        -- apply (mul_prefix_given_extension _ $ia $ib $iy $ie $ig $ih $iz $iw).
           ++ inherit HE.
           ++ inherit HQ.
           ++ inherit HEq.
           ++ inherit HEtr.
           ++ inherit HA.
           ++ inherit HS.
           ++ inherit HP.
           ++ apply Ctx. now left.
           ++ inherit Hz.
           ++ inherit Hzw.
        -- apply (graph_extension_new_edge _ $ig $ih $ib $iw);
             [inherit HE|apply Ctx; now left].
Qed.

Lemma mul_prefix_exists_result G x y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 mul_prefix_exists x y ->
  G ⊢238 ∃ mul_result x`[↑] y`[↑] $0.
Proof.
  destruct x as [ix|[]], y as [iy|[]]. intros HE HP.
  unfold mul_prefix_exists in HP. eapply ExE_named; [exact HP|].
  intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HZ : (raw_zero $ie ∧ mul_prefix $ix $iy $ie $ig ::
      (∃ (raw_zero $ie`[↑] ∧ mul_prefix $ix`[↑] $iy`[↑] $ie`[↑] $0)) :: G)
      ⊢238 raw_zero $ie).
  { eapply CE1, Ctx. now left. }
  assert (Hpref : (raw_zero $ie ∧ mul_prefix $ix $iy $ie $ig ::
      (∃ (raw_zero $ie`[↑] ∧ mul_prefix $ix`[↑] $iy`[↑] $ie`[↑] $0)) :: G)
      ⊢238 mul_prefix $ix $iy $ie $ig).
  { eapply CE2, Ctx. now left. }
  eapply ExE_named.
  - apply (mul_prefix_top_value _ $ix $iy $ie $ig); [inherit HE|exact Hpref].
  - intro z. destruct z as [iz|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (ExI $iz).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (mul_result_from_witnesses _ $ix $iy $iz $ie $ig);
      [inherit HZ|inherit Hpref|apply Ctx; now left].
Qed.

Theorem mul_result_ordinal G x y z :
  G ⊢238 mul_result x y z -> G ⊢238 ordinal_representative z.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]]. intro H.
  unfold mul_result in H. eapply ExE_named; [exact H|].
  intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (graph_range_at _ $ig $ix $iz).
  - apply (mul_prefix_range _ $ix $iy $ie $ig). eapply CE1, CE2, Ctx. now left.
  - eapply CE2, CE2, Ctx. now left.
Qed.

Lemma mul_prefix_exists_successor G a b base :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 closed_add_totality ->
  G ⊢238 ordinal_representative a -> G ⊢238 ordinal_representative base ->
  G ⊢238 raw_successor a b -> G ⊢238 mul_prefix_exists a base ->
  G ⊢238 mul_prefix_exists b base.
Proof.
  destruct a as [ia|[]], b as [ib|[]], base as [iy|[]].
  intros HE HQ HEq HEtr Hempty HAD HT HA HY HS HP.
  unfold mul_prefix_exists in HP. eapply ExE_named; [exact HP|].
  intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HZ : (raw_zero $ie ∧ mul_prefix $ia $iy $ie $ig ::
      (∃ (raw_zero $ie`[↑] ∧ mul_prefix $ia`[↑] $iy`[↑] $ie`[↑] $0)) :: G)
      ⊢238 raw_zero $ie).
  { eapply CE1, Ctx. now left. }
  assert (Hpref : (raw_zero $ie ∧ mul_prefix $ia $iy $ie $ig ::
      (∃ (raw_zero $ie`[↑] ∧ mul_prefix $ia`[↑] $iy`[↑] $ie`[↑] $0)) :: G)
      ⊢238 mul_prefix $ia $iy $ie $ig).
  { eapply CE2, Ctx. now left. }
  eapply ExE_named.
  - apply (mul_prefix_top_value _ $ia $iy $ie $ig); [inherit HE|exact Hpref].
  - intro z. destruct z as [iz|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply ExE_named.
    + apply (mul_prefix_successor_extension _ $ia $ib $iy $ie $ig $iz).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HEtr.
      * inherit Hempty.
      * inherit HAD.
      * inherit HT.
      * inherit HA.
      * inherit HY.
      * inherit HS.
      * inherit Hpref.
      * apply Ctx. now left.
    + intro w. destruct w as [iw|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      eapply ExE_named; [apply Ctx; now left|]. intro h. destruct h as [ih|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      unfold mul_prefix_exists. apply (ExI $ie).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (ExI $ih).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * inherit HZ.
      * eapply CE1, CE2, Ctx. now left.
Qed.

Lemma mul_induction_base G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 ordinal_base (mul_total_property $0).
Proof.
  intros HE HQ HEq HEtr Hempty HAD. unfold ordinal_base.
  apply AllI_named. intro a. destruct a as [ia|[]].
  change (G ⊢238 ((ordinal_representative $ia ∧ raw_zero $ia) →
    (mul_total_property $0)[$ia..])).
  rewrite mul_total_property_at. apply II. unfold mul_total_property.
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [subst_form]. rewrite mul_prefix_exists_subst.
  cbn [subst_term up scons funcomp]. apply II.
  assert (HZa : (ordinal_representative $iy ::
      ordinal_representative $ia ∧ raw_zero $ia :: G) ⊢238 raw_zero $ia).
  { eapply CE2, Ctx. right. now left. }
  eapply ExE_named.
  - apply (mul_prefix_base _ $ia $iy).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Hempty.
    + inherit HAD.
    + exact HZa.
  - intro g. destruct g as [ig|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    unfold mul_prefix_exists. apply (ExI $ia).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (ExI $ig).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
    + inherit HZa.
    + apply Ctx. now left.
Qed.

Lemma mul_induction_step G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 closed_add_totality ->
  G ⊢238 ordinal_step (mul_total_property $0).
Proof.
  intros HE HQ HEq HEtr Hempty HAD HT. apply add_ordinal_step_intro.
  intros a b. destruct a as [ia|[]], b as [ib|[]]. rewrite !mul_total_property_at.
  unfold mul_total_property at 1. apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [subst_form]. rewrite mul_prefix_exists_subst.
  cbn [subst_term up scons funcomp]. apply II.
  apply (mul_prefix_exists_successor _ $ia $ib $iy).
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit Hempty.
  - inherit HAD.
  - inherit HT.
  - eapply CE1, Ctx. right. right. now left.
  - apply Ctx. now left.
  - eapply CE2, CE2, Ctx. right. right. now left.
  - apply (mul_total_property_instance _ $ia $iy).
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Lemma mul_total_property_bounded : bounded 1 (mul_total_property $0).
Proof.
  unfold mul_total_property, mul_prefix_exists, mul_prefix, mul_recurrence,
    add_result, add_prefix, add_recurrence, graph_domain, graph_functional,
    graph_range, ordinal_representative, member_ir, representative, raw_zero,
    raw_successor, transitive, member_transitive, member_linear,
    internal_extrema, subset, nonempty, least, greatest, graph_edge,
    raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn. fixed_bounds.
Qed.

Lemma S0_mul_induction_base :
  derivable finite_set_S0 (ordinal_base (mul_total_property $0)).
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
  assert (HAD : G ⊢238 adjunction_ax).
  { apply Ctx. unfold G, equality_base. cbn. right. right. right. right. now left. }
  assert (Hempty' : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|[<-|Hpsi]].
    + apply S0_base. apply in_or_app. now left.
    + apply S0_base. apply in_or_app. right. now left.
    + now apply HGempty.
  - apply mul_induction_base; assumption.
Qed.

Lemma S0_mul_induction_step :
  derivable finite_set_S0 (ordinal_step (mul_total_property $0)).
Proof.
  destruct S0_empty as [Gempty [HGempty Hempty]].
  destruct S0_closed_add_totality as [Gadd [HGadd Hadt]].
  set (G := equality_base ++ (adjunction_ax :: (Gempty ++ Gadd))).
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
  assert (HAD : G ⊢238 adjunction_ax).
  { apply Ctx. unfold G, equality_base. cbn. right. right. right. right. now left. }
  assert (Hempty' : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. right. apply in_or_app. now left. }
  assert (Hadt' : G ⊢238 closed_add_totality).
  { eapply Weak; [exact Hadt|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. right. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|[<-|Hpsi]].
    + apply S0_base. apply in_or_app. now left.
    + apply S0_base. apply in_or_app. right. now left.
    + apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGempty|now apply HGadd].
  - apply mul_induction_step; assumption.
Qed.

(** Full finite S0 induction constructs the multiplication trace for
    every pair of ordinal representatives. All Add proofs are actual
    previously derived finite proofs, merged into the finite S0 context. *)
Theorem S0_mul_prefix_total x y :
  derivable finite_set_S0
    (ordinal_representative x → ordinal_representative y → mul_prefix_exists x y).
Proof.
  pose proof (S0_ordinal_induction 0 (mul_total_property $0)
    mul_total_property_bounded) as HI.
  pose proof (derivable_mp finite_set_S0 _ _ HI S0_mul_induction_base) as HS.
  destruct (derivable_mp finite_set_S0 _ _ HS S0_mul_induction_step)
    as [G [HG Hforall]].
  exists G. split; [exact HG|]. destruct x as [ix|[]], y as [iy|[]].
  pose proof (AllE $ix Hforall) as H.
  change (G ⊢238 (ordinal_representative $ix →
    (mul_total_property $0)[$ix..])) in H.
  rewrite mul_total_property_at in H. apply II, II.
  apply (mul_total_property_instance _ $ix $iy).
  - eapply IE; [inherit H|]. apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Theorem S0_mul_total x y :
  derivable finite_set_S0
    ((ordinal_representative x ∧ ordinal_representative y) →
      ∃ mul_result x`[↑] y`[↑] $0).
Proof.
  destruct (S0_mul_prefix_total x y) as [Gp [HGp HP]].
  exists ((∀ E $0 $0) :: Gp). split.
  - intros phi [<-|Hphi].
    + apply S0_base. apply in_or_app. left. now left.
    + now apply HGp.
  - apply II, mul_prefix_exists_result.
    + apply Ctx. right. now left.
    + eapply IE; [|eapply CE2, Ctx; now left].
      eapply IE; [inherit HP|eapply CE1, Ctx; now left].
Qed.

Lemma mul_recurrence_base_transport G g base base' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 E base base' -> G ⊢238 mul_recurrence g base ->
  G ⊢238 mul_recurrence g base'.
Proof.
  destruct g as [ig|[]], base as [iy|[]], base' as [iy'|[]].
  intros HE HQ HEq HEtr Hyy HR. unfold mul_recurrence.
  apply AllI_named. intro i. destruct i as [ii|[]].
  apply AllI_named. intro v. destruct v as [iv|[]].
  apply AllI_named. intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply ExE_named.
  - apply (mul_recurrence_instance _ $ig $iy $ii $iv $ip).
    + inherit HR.
    + eapply CE1, Ctx. now left.
    + eapply CE2, Ctx. now left.
  - intro q. destruct q as [iq|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (ExI $iq).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
    + eapply CE1, Ctx. now left.
    + apply (add_result_coordinate_transport _ $iq $iy $iv $iq $iy' $iv).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HEtr.
      * inherit (AllE $iq HE).
      * inherit Hyy.
      * inherit (AllE $iv HE).
      * eapply CE2, Ctx. now left.
Qed.

Lemma mul_prefix_coordinate_transport G x y e g x' y' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 E x x' -> G ⊢238 E y y' -> G ⊢238 mul_prefix x y e g ->
  G ⊢238 mul_prefix x' y' e g.
Proof.
  intros HE HQ HEq HEtr Hxx Hyy HP. apply CI.
  - apply (graph_domain_coordinate_transport _ x x' g); try assumption.
    exact (mul_prefix_domain G x y e g HP).
  - apply CI; [exact (mul_prefix_functional G x y e g HP)|].
    apply CI; [exact (mul_prefix_range G x y e g HP)|].
    apply CI; [exact (mul_prefix_initial G x y e g HP)|].
    apply (mul_recurrence_base_transport _ g y y'); try assumption.
    exact (mul_prefix_recurrence G x y e g HP).
Qed.

Theorem mul_result_coordinate_transport G x y z x' y' z' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 E x x' -> G ⊢238 E y y' -> G ⊢238 E z z' ->
  G ⊢238 mul_result x y z -> G ⊢238 mul_result x' y' z'.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]], x' as [ix'|[]],
    y' as [iy'|[]], z' as [iz'|[]]. intros HE HQ HEq HEtr Hxx Hyy Hzz H.
  unfold mul_result in H. eapply ExE_named; [exact H|].
  intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (mul_result_from_witnesses _ $ix' $iy' $iz' $ie $ig).
  - eapply CE1, Ctx. now left.
  - apply (mul_prefix_coordinate_transport _ $ix $iy $ie $ig $ix' $iy').
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Hxx.
    + inherit Hyy.
    + eapply CE1, CE2, Ctx. now left.
  - apply (graph_edge_coordinate_transport _ $ig $ix $iz $ix' $iz').
    + inherit HEq.
    + inherit HEtr.
    + inherit Hxx.
    + inherit Hzz.
    + eapply CE2, CE2, Ctx. now left.
Qed.

Lemma mul_prefix_zero_value G top base e g i v :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_representative top -> G ⊢238 raw_zero i -> G ⊢238 raw_zero e ->
  G ⊢238 mul_prefix top base e g -> G ⊢238 graph_edge g i v -> G ⊢238 raw_zero v.
Proof.
  intros HE HQ HEq HEtr HT HZi HZe HP Hv.
  assert (Hinitial : G ⊢238 graph_edge g e e).
  { exact (mul_prefix_initial G top base e g HP). }
  assert (Hie : G ⊢238 E i e).
  { apply (ordinal_inclusive_zero_unique _ top i e).
    - exact HE.
    - exact HQ.
    - exact HEq.
    - exact HEtr.
    - exact HT.
    - exact HZi.
    - exact HZe.
    - apply (graph_domain_edge _ top g i v);
        [exact (mul_prefix_domain G top base e g HP)|exact Hv].
    - apply (graph_domain_edge _ top g e e);
        [exact (mul_prefix_domain G top base e g HP)|exact Hinitial]. }
  assert (Hve : G ⊢238 E v e).
  { apply (graph_functional_at _ g e v e).
    - exact (mul_prefix_functional G top base e g HP).
    - apply (graph_edge_coordinate_transport _ g i v e v);
        [exact HEq|exact HEtr|exact Hie|exact (AllE v HE)|exact Hv].
    - exact Hinitial. }
  apply (raw_zero_coordinate_transport _ e v); try assumption.
  apply equality_symmetry_instance; assumption.
Qed.

Theorem mul_result_zero_value G x y z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_representative x -> G ⊢238 raw_zero x ->
  G ⊢238 mul_result x y z -> G ⊢238 raw_zero z.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]].
  intros HE HQ HEq HEtr HX HZ H. unfold mul_result in H.
  eapply ExE_named; [exact H|]. intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (mul_prefix_zero_value _ $ix $iy $ie $ig $ix $iz).
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit HX.
  - inherit HZ.
  - eapply CE1, Ctx. now left.
  - eapply CE1, CE2, Ctx. now left.
  - eapply CE2, CE2, Ctx. now left.
Qed.

Theorem mul_recurrence_restriction G top base g h :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 ordinal_representative top -> G ⊢238 mul_recurrence g base ->
  G ⊢238 graph_restriction top g h -> G ⊢238 mul_recurrence h base.
Proof.
  destruct top as [it|[]], base as [ib|[]], g as [ig|[]], h as [ih|[]].
  intros HE HQ HT HM HR. unfold mul_recurrence.
  apply AllI_named. intro i. destruct i as [ii|[]].
  apply AllI_named. intro v. destruct v as [iv|[]].
  apply AllI_named. intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  assert (Hcut : (graph_edge $ih $ii $iv ∧ raw_successor $ip $ii :: G)
      ⊢238 (graph_edge $ig $ii $iv ∧ inclusive_domain $it $ii)).
  { apply (graph_restriction_cases _ $it $ig $ih $ii $iv);
      [inherit HR|eapply CE1, Ctx; now left]. }
  assert (Hp : (graph_edge $ih $ii $iv ∧ raw_successor $ip $ii :: G) ⊢238 R $it $ip).
  { apply (inclusive_predecessor_member _ $it $ii $ip).
    - inherit HE.
    - inherit HQ.
    - inherit HT.
    - exact (CE2 Hcut).
    - eapply CE2, Ctx. now left. }
  eapply ExE_named.
  - apply (mul_recurrence_instance _ $ig $ib $ii $iv $ip).
    + inherit HM.
    + exact (CE1 Hcut).
    + eapply CE2, Ctx. now left.
  - intro q. destruct q as [iq|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (ExI $iq).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
    + apply (graph_restriction_intro _ $it $ig $ih $ip $iq).
      * inherit HR.
      * eapply CE1, Ctx. now left.
      * apply DI1. inherit Hp.
    + eapply CE2, Ctx. now left.
Qed.

Theorem mul_prefix_predecessor_restriction G top tp base zero g h :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 ordinal_representative top ->
  G ⊢238 raw_successor top tp -> G ⊢238 raw_zero zero ->
  G ⊢238 mul_prefix tp base zero g -> G ⊢238 graph_restriction top g h ->
  G ⊢238 mul_prefix top base zero h.
Proof.
  intros HE HQ HEq HT HS HZ HP HR. apply CI.
  - apply (restriction_domain _ top tp g h); try assumption.
    exact (mul_prefix_domain G tp base zero g HP).
  - apply CI.
    + apply (restriction_functional _ top g h); [|exact HR].
      exact (mul_prefix_functional G tp base zero g HP).
    + apply CI.
      * apply (restriction_range _ top g h); [|exact HR].
        exact (mul_prefix_range G tp base zero g HP).
      * apply CI.
        -- apply (graph_restriction_intro _ top g h zero zero).
           ++ exact HR.
           ++ exact (mul_prefix_initial G tp base zero g HP).
           ++ apply (successor_inclusive_zero_predecessor _ top tp zero); try assumption.
              apply (graph_domain_edge _ tp g zero zero).
              ** exact (mul_prefix_domain G tp base zero g HP).
              ** exact (mul_prefix_initial G tp base zero g HP).
        -- apply (mul_recurrence_restriction _ top base g h); try assumption.
           exact (mul_prefix_recurrence G tp base zero g HP).
Qed.

(** The backwards multiplication row constructs the shorter trace by
    actual Separation. Its output is the value read from the old graph,
    rather than a separately selected arithmetic representative. *)
Theorem mul_result_predecessor_witness G x sx y z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 separation_ax (domain_entry_property x) ->
  G ⊢238 ordinal_representative x -> G ⊢238 raw_successor x sx ->
  G ⊢238 mul_result sx y z ->
  G ⊢238 ∃ (mul_result x`[↑] y`[↑] $0 ∧ add_result $0 y`[↑] z`[↑]).
Proof.
  destruct x as [ix|[]], sx as [is|[]], y as [iy|[]], z as [iz|[]].
  intros HE HQ HEq HEtr Hsep HX HS HM. unfold mul_result in HM.
  eapply ExE_named; [exact HM|]. intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HZ : (raw_zero $ie ∧ (mul_prefix $is $iy $ie $ig ∧ graph_edge $ig $is $iz) ::
      (∃ (raw_zero $ie`[↑] ∧ (mul_prefix $is`[↑] $iy`[↑] $ie`[↑] $0 ∧
        graph_edge $0 $is`[↑] $iz`[↑]))) :: G) ⊢238 raw_zero $ie).
  { eapply CE1, Ctx. now left. }
  assert (HP : (raw_zero $ie ∧ (mul_prefix $is $iy $ie $ig ∧ graph_edge $ig $is $iz) ::
      (∃ (raw_zero $ie`[↑] ∧ (mul_prefix $is`[↑] $iy`[↑] $ie`[↑] $0 ∧
        graph_edge $0 $is`[↑] $iz`[↑]))) :: G) ⊢238 mul_prefix $is $iy $ie $ig).
  { eapply CE1, CE2, Ctx. now left. }
  eapply ExE_named.
  - apply (graph_restriction_exists _ $ix $ig);
      [inherit HE|inherit HQ|inherit HEq|inherit HEtr|inherit Hsep].
  - intro h. destruct h as [ih|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HR : (graph_restriction $ix $ig $ih ::
        raw_zero $ie ∧ (mul_prefix $is $iy $ie $ig ∧ graph_edge $ig $is $iz) ::
        (∃ (raw_zero $ie`[↑] ∧ (mul_prefix $is`[↑] $iy`[↑] $ie`[↑] $0 ∧
          graph_edge $0 $is`[↑] $iz`[↑]))) :: G) ⊢238 graph_restriction $ix $ig $ih).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (mul_recurrence_instance _ $ig $iy $is $iz $ix).
      * apply (mul_prefix_recurrence _ $is $iy $ie $ig). inherit HP.
      * eapply CE2, CE2, Ctx. right. now left.
      * inherit HS.
    + intro q. destruct q as [iq|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (ExI $iq).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * apply (mul_result_from_witnesses _ $ix $iy $iq $ie $ih).
        -- inherit HZ.
        -- apply (mul_prefix_predecessor_restriction _ $ix $is $iy $ie $ig $ih).
           ++ inherit HE.
           ++ inherit HQ.
           ++ inherit HEq.
           ++ inherit HX.
           ++ inherit HS.
           ++ inherit HZ.
           ++ inherit HP.
           ++ inherit HR.
        -- apply (graph_restriction_intro _ $ix $ig $ih $ix $iq).
           ++ inherit HR.
           ++ eapply CE1, Ctx. now left.
           ++ apply DI2. inherit (AllE $ix HE).
      * eapply CE2, Ctx. now left.
Qed.

Theorem S0_mul_predecessor_witness x sx y z :
  derivable finite_set_S0
    (ordinal_representative x → raw_successor x sx → mul_result sx y z →
      ∃ (mul_result x`[↑] y`[↑] $0 ∧ add_result $0 y`[↑] z`[↑])).
Proof.
  destruct x as [ix|[]].
  destruct (S0_separation_instance (S ix) (domain_entry_property $ix)
    (domain_entry_property_bounded ix)) as [Gsep [HGsep Hsep]].
  set (G := equality_base ++ Gsep).
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
  assert (Hsep' : G ⊢238 separation_ax (domain_entry_property $ix)).
  { eapply Weak; [exact Hsep|]. intros psi Hpsi. unfold G. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + now apply HGsep.
  - apply II, II, II. apply (mul_result_predecessor_witness _ $ix sx y z).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Hsep'.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Definition mul_predecessor_ax : set_form :=
  ∀ ∀ ∀ ∀ (ordinal_representative $3 → raw_successor $3 $2 → mul_result $2 $1 $0 →
    ∃ (mul_result $4 $2 $0 ∧ add_result $0 $2 $1)).

Theorem S0_mul_predecessor_closed : derivable finite_set_S0 mul_predecessor_ax.
Proof.
  unfold mul_predecessor_ax.
  apply S0_generalize, S0_generalize, S0_generalize, S0_generalize.
  exact (S0_mul_predecessor_witness $3 $2 $1 $0).
Qed.

Lemma mul_predecessor_ax_instance G x sx y z :
  G ⊢238 mul_predecessor_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 raw_successor x sx -> G ⊢238 mul_result sx y z ->
  G ⊢238 ∃ (mul_result x`[↑] y`[↑] $0 ∧ add_result $0 y`[↑] z`[↑]).
Proof.
  destruct x as [ix|[]], sx as [is|[]], y as [iy|[]], z as [iz|[]].
  intros HT HX HS HM. unfold mul_predecessor_ax in HT.
  pose proof (AllE $iz (AllE $iy (AllE $is (AllE $ix HT)))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HM]. eapply IE; [|exact HS]. eapply IE; [exact H|exact HX].
Qed.

Print Assumptions S0_mul_predecessor_closed.
Print Assumptions S0_mul_predecessor_witness.
Print Assumptions mul_recurrence_restriction.
Print Assumptions mul_prefix_predecessor_restriction.
Print Assumptions mul_result_predecessor_witness.
Print Assumptions mul_result_coordinate_transport.
Print Assumptions mul_prefix_zero_value.
Print Assumptions mul_result_zero_value.
Print Assumptions S0_mul_total.
Print Assumptions S0_mul_prefix_total.
Print Assumptions mul_result_ordinal.
Print Assumptions mul_recurrence_successor_extension.
Print Assumptions mul_prefix_given_extension.
Print Assumptions S0_closed_add_totality.
Print Assumptions mul_prefix_successor_extension.
Print Assumptions singleton_mul_recurrence.
Print Assumptions singleton_mul_prefix.
Print Assumptions mul_prefix_base.
Print Assumptions mul_result_from_witnesses.
End MulGraph238.
