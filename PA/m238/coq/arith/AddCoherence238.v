(** Joint comparison of actual addition traces.  Raw functional equality
    identifies values inside one graph; a concrete order-isomorphism
    compares outputs of two independently constructed graphs. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  OrdinalTrace238 PairGraph238 GraphTransport238 TraceGraph238 AddGraph238
  IsoGraph238 IsoZero238 IsoEquality238 IsoSuccessor238
  TraceRestriction238 IsoMatchSupply238 CompositionIso238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 OrdinalTrace238.OrdinalTrace238
  PairGraph238.PairGraph238 GraphTransport238.GraphTransport238
  TraceGraph238.TraceGraph238 AddGraph238.AddGraph238
  IsoGraph238.IsoGraph238 IsoZero238.IsoZero238 IsoEquality238.IsoEquality238
  IsoSuccessor238.IsoSuccessor238 TraceRestriction238.TraceRestriction238
  IsoMatchSupply238.IsoMatchSupply238 CompositionIso238.CompositionIso238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module AddCoherence238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Theorem add_prefix_zero_coherence G top top' y y' e e' g g' i i' v v' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_representative top -> G ⊢238 ordinal_representative top' ->
  G ⊢238 raw_zero e -> G ⊢238 raw_zero e' ->
  G ⊢238 add_prefix top y e g -> G ⊢238 add_prefix top' y' e' g' ->
  G ⊢238 raw_zero i -> G ⊢238 order_iso i i' -> G ⊢238 order_iso y y' ->
  G ⊢238 graph_edge g i v -> G ⊢238 graph_edge g' i' v' ->
  G ⊢238 order_iso v v'.
Proof.
  intros HE HQ HEq HEtr HT HT' HZe HZe' HP HP' HZi HI HY Hv Hv'.
  assert (Hvi : G ⊢238 E v y).
  { apply (add_prefix_zero_value _ top y e g i v); assumption. }
  assert (Hv'i : G ⊢238 E v' y').
  { apply (add_prefix_zero_value _ top' y' e' g' i' v').
    - exact HE.
    - exact HQ.
    - exact HEq.
    - exact HEtr.
    - exact HT'.
    - exact HZe'.
    - apply (order_iso_zero_target _ i i'); assumption.
    - exact HP'.
    - exact Hv'. }
  apply (order_iso_coordinate_transport _ y y' v v').
  - exact HE.
  - exact HQ.
  - exact HEq.
  - apply equality_symmetry_instance; assumption.
  - apply equality_symmetry_instance; assumption.
  - exact HY.
Qed.

Theorem add_results_zero_coherence G x x' y y' z z' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_representative x -> G ⊢238 ordinal_representative x' ->
  G ⊢238 raw_zero x -> G ⊢238 order_iso x x' -> G ⊢238 order_iso y y' ->
  G ⊢238 add_result x y z -> G ⊢238 add_result x' y' z' -> G ⊢238 order_iso z z'.
Proof.
  intros HE HQ HEq HEtr HX HX' HZ HI HY HA HA'.
  assert (Hz : G ⊢238 E z y).
  { apply (add_result_zero_value _ x y z); assumption. }
  assert (Hz' : G ⊢238 E z' y').
  { apply (add_result_zero_value _ x' y' z').
    - exact HE.
    - exact HQ.
    - exact HEq.
    - exact HEtr.
    - exact HX'.
    - apply (order_iso_zero_target _ x x'); assumption.
    - exact HA'. }
  apply (order_iso_coordinate_transport _ y y' z z').
  - exact HE.
  - exact HQ.
  - exact HEq.
  - apply equality_symmetry_instance; assumption.
  - apply equality_symmetry_instance; assumption.
  - exact HY.
Qed.

Lemma add_result_from_witnesses G x y z e g :
  G ⊢238 raw_zero e -> G ⊢238 add_prefix x y e g ->
  G ⊢238 graph_edge g x z -> G ⊢238 add_result x y z.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]], e as [ie|[]], g as [ig|[]].
  intros HZ HP HE. unfold add_result. apply (ExI $ie).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (ExI $ig).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply CI; [exact HZ|]. apply CI; assumption.
Qed.

Theorem add_recurrence_restriction G top g h :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 ordinal_representative top -> G ⊢238 add_recurrence g ->
  G ⊢238 graph_restriction top g h -> G ⊢238 add_recurrence h.
Proof.
  destruct top as [it|[]], g as [ig|[]], h as [ih|[]].
  intros HE HQ HT HM HR. unfold add_recurrence.
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
  - apply (add_recurrence_instance _ $ig $ii $iv $ip).
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

Theorem add_prefix_predecessor_restriction G top tp base zero g h :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 ordinal_representative top ->
  G ⊢238 raw_successor top tp -> G ⊢238 raw_zero zero ->
  G ⊢238 add_prefix tp base zero g -> G ⊢238 graph_restriction top g h ->
  G ⊢238 add_prefix top base zero h.
Proof.
  intros HE HQ HEq HT HS HZ HP HR. unfold add_prefix. apply CI.
  - apply (restriction_domain _ top tp g h); try assumption. exact (CE1 HP).
  - apply CI.
    + apply (restriction_functional _ top g h); [|exact HR]. exact (CE1 (CE2 HP)).
    + apply CI.
      * apply (restriction_range _ top g h); [|exact HR]. exact (CE1 (CE2 (CE2 HP))).
      * apply CI.
        -- apply (graph_restriction_intro _ top g h zero base).
           ++ exact HR.
           ++ exact (CE1 (CE2 (CE2 (CE2 HP)))).
           ++ apply (successor_inclusive_zero_predecessor _ top tp zero); try assumption.
              apply (graph_domain_edge _ tp g zero base).
              ** exact (CE1 HP).
              ** exact (CE1 (CE2 (CE2 (CE2 HP)))).
        -- apply (add_recurrence_restriction _ top g h); try assumption.
           exact (CE2 (CE2 (CE2 (CE2 HP)))).
Qed.

(** One universally derived cut family is specialized after each trace
    witness is selected.  It produces the actual shorter graph and reads
    its result from the old graph's backwards recurrence. *)
Theorem add_result_predecessor_witness G x sx y z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 graph_restriction_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 raw_successor x sx -> G ⊢238 add_result sx y z ->
  G ⊢238 ∃ (add_result x`[↑] y`[↑] $0 ∧ raw_successor $0 z`[↑]).
Proof.
  destruct x as [ix|[]], sx as [is|[]], y as [iy|[]], z as [iz|[]].
  intros HE HQ HEq HEtr Hcuts HX HS HM. unfold add_result in HM.
  eapply ExE_named; [exact HM|]. intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HZ : (raw_zero $ie ∧ (add_prefix $is $iy $ie $ig ∧ graph_edge $ig $is $iz) ::
      (∃ (raw_zero $ie`[↑] ∧ (add_prefix $is`[↑] $iy`[↑] $ie`[↑] $0 ∧
        graph_edge $0 $is`[↑] $iz`[↑]))) :: G) ⊢238 raw_zero $ie).
  { eapply CE1, Ctx. now left. }
  assert (HP : (raw_zero $ie ∧ (add_prefix $is $iy $ie $ig ∧ graph_edge $ig $is $iz) ::
      (∃ (raw_zero $ie`[↑] ∧ (add_prefix $is`[↑] $iy`[↑] $ie`[↑] $0 ∧
        graph_edge $0 $is`[↑] $iz`[↑]))) :: G) ⊢238 add_prefix $is $iy $ie $ig).
  { eapply CE1, CE2, Ctx. now left. }
  eapply ExE_named.
  - apply (graph_restriction_ax_instance _ $ix $ig). inherit Hcuts.
  - intro h. destruct h as [ih|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HR : (graph_restriction $ix $ig $ih ::
        raw_zero $ie ∧ (add_prefix $is $iy $ie $ig ∧ graph_edge $ig $is $iz) ::
        (∃ (raw_zero $ie`[↑] ∧ (add_prefix $is`[↑] $iy`[↑] $ie`[↑] $0 ∧
          graph_edge $0 $is`[↑] $iz`[↑]))) :: G) ⊢238 graph_restriction $ix $ig $ih).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (add_recurrence_instance _ $ig $is $iz $ix).
      * inherit (CE2 (CE2 (CE2 (CE2 HP)))).
      * eapply CE2, CE2, Ctx. right. now left.
      * inherit HS.
    + intro q. destruct q as [iq|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (ExI $iq).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * apply (add_result_from_witnesses _ $ix $iy $iq $ie $ih).
        -- inherit HZ.
        -- apply (add_prefix_predecessor_restriction _ $ix $is $iy $ie $ig $ih).
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

Definition add_comparison_property (x : set_term) : set_form :=
  ∀ ∀ ∀ ∀ ∀ (ordinal_representative $4 → ordinal_representative $3 →
    ordinal_representative $2 → order_iso x`[↑]`[↑]`[↑]`[↑]`[↑] $4 →
    order_iso $3 $2 → add_result x`[↑]`[↑]`[↑]`[↑]`[↑] $3 $1 →
    add_result $4 $2 $0 → order_iso $1 $0).

Lemma add_comparison_property_subst x sigma :
  (add_comparison_property x)[sigma] = add_comparison_property x`[sigma].
Proof.
  unfold add_comparison_property, order_iso, order_bijection, graph_entries,
    entry_witness, graph_typed, graph_left_total, graph_right_total,
    IsoGraph238.IsoGraph238.graph_functional, graph_injective, graph_order,
    add_result, add_prefix, add_recurrence, graph_domain,
    TraceGraph238.TraceGraph238.graph_functional, graph_range,
    ordinal_representative, member_ir, representative, raw_zero, raw_successor,
    transitive, member_transitive, member_linear, internal_extrema, subset,
    nonempty, least, greatest, graph_edge, raw_kuratowski, raw_pair,
    raw_singleton, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma add_comparison_property_at x :
  (add_comparison_property $0)[x..] = add_comparison_property x.
Proof. rewrite add_comparison_property_subst. reflexivity. Qed.

Lemma add_comparison_property_instance G x x' y y' z z' :
  G ⊢238 add_comparison_property x -> G ⊢238 ordinal_representative x' ->
  G ⊢238 ordinal_representative y -> G ⊢238 ordinal_representative y' ->
  G ⊢238 order_iso x x' -> G ⊢238 order_iso y y' ->
  G ⊢238 add_result x y z -> G ⊢238 add_result x' y' z' -> G ⊢238 order_iso z z'.
Proof.
  destruct x as [ix|[]], x' as [ix'|[]], y as [iy|[]], y' as [iy'|[]],
    z as [iz|[]], z' as [iz'|[]]. intros HC HX' HY HY' Hxx Hyy HM HM'.
  unfold add_comparison_property in HC.
  pose proof (AllE $iz' (AllE $iz (AllE $iy' (AllE $iy (AllE $ix' HC))))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HM']. eapply IE; [|exact HM].
  eapply IE; [|exact Hyy]. eapply IE; [|exact Hxx].
  eapply IE; [|exact HY']. eapply IE; [|exact HY]. eapply IE; [exact H|exact HX'].
Qed.

Lemma add_iso_successor_match_instance G a b p :
  G ⊢238 iso_successor_match_ax -> G ⊢238 ordinal_representative a ->
  G ⊢238 ordinal_representative b -> G ⊢238 raw_successor p a ->
  G ⊢238 order_iso a b ->
  G ⊢238 ∃ (ordinal_representative $0 ∧
    (raw_successor $0 b`[↑] ∧ order_iso p`[↑] $0)).
Proof.
  destruct a as [ia|[]], b as [ib|[]], p as [ip|[]]. intros HM HA HB HS HI.
  unfold iso_successor_match_ax in HM.
  pose proof (AllE $ip (AllE $ib (AllE $ia HM))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HI]. eapply IE; [|exact HS].
  eapply IE; [|exact HB]. eapply IE; [exact H|exact HA].
Qed.

(** The paired successor proof chooses neither arithmetic output nor
    isomorphism by fiat. Matching constructs an actual predecessor,
    Separation constructs both shorter traces, and endpoint adjunction
    constructs the final comparison graph. *)
Theorem add_comparison_successor_at G a b x' y y' z z' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 graph_restriction_ax ->
  G ⊢238 iso_successor_match_ax -> G ⊢238 ordinal_representative a ->
  G ⊢238 ordinal_representative b -> G ⊢238 raw_successor a b ->
  G ⊢238 add_comparison_property a -> G ⊢238 ordinal_representative x' ->
  G ⊢238 ordinal_representative y -> G ⊢238 ordinal_representative y' ->
  G ⊢238 order_iso b x' -> G ⊢238 order_iso y y' ->
  G ⊢238 add_result b y z -> G ⊢238 add_result x' y' z' -> G ⊢238 order_iso z z'.
Proof.
  destruct a as [ia|[]], b as [ib|[]], x' as [ix'|[]], y as [iy|[]], y' as [iy'|[]],
    z as [iz|[]], z' as [iz'|[]].
  intros HE HQ HEq HEtr Hempty HAdj Hcuts Hmatch HA HB HS HC HX' HY HY' Hxx Hyy HM HM'.
  eapply ExE_named.
  - apply (add_iso_successor_match_instance _ $ib $ix' $ia); assumption.
  - intro p'. destruct p' as [ip'|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    set (Kp := (ordinal_representative $ip' ∧
      (raw_successor $ip' $ix' ∧ order_iso $ia $ip')) :: G).
    change (Kp ⊢238 order_iso $iz $iz').
    assert (Hp' : Kp ⊢238 ordinal_representative $ip').
    { eapply CE1, Ctx. unfold Kp. now left. }
    assert (Hsp' : Kp ⊢238 raw_successor $ip' $ix').
    { eapply CE1, CE2, Ctx. unfold Kp. now left. }
    assert (Hip' : Kp ⊢238 order_iso $ia $ip').
    { eapply CE2, CE2, Ctx. unfold Kp. now left. }
    eapply ExE_named.
    + apply (add_result_predecessor_witness _ $ia $ib $iy $iz);
        [inherit HE|inherit HQ|inherit HEq|inherit HEtr|inherit Hcuts|
         inherit HA|inherit HS|inherit HM].
    + intro q. destruct q as [iq|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      set (Kq := (add_result $ia $iy $iq ∧ raw_successor $iq $iz) :: Kp).
      change (Kq ⊢238 order_iso $iz $iz').
      assert (Hqa : Kq ⊢238 add_result $ia $iy $iq).
      { eapply CE1, Ctx. unfold Kq. now left. }
      assert (Hqs : Kq ⊢238 raw_successor $iq $iz).
      { eapply CE2, Ctx. unfold Kq. now left. }
      eapply ExE_named.
      * apply (add_result_predecessor_witness _ $ip' $ix' $iy' $iz').
        -- inherit HE.
        -- inherit HQ.
        -- inherit HEq.
        -- inherit HEtr.
        -- inherit Hcuts.
        -- inherit Hp'.
        -- inherit Hsp'.
        -- inherit HM'.
      * intro q'. destruct q' as [iq'|[]].
        cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
        set (Kq' := (add_result $ip' $iy' $iq' ∧ raw_successor $iq' $iz') :: Kq).
        change (Kq' ⊢238 order_iso $iz $iz').
        assert (Hq'a : Kq' ⊢238 add_result $ip' $iy' $iq').
        { eapply CE1, Ctx. unfold Kq'. now left. }
        assert (Hq's : Kq' ⊢238 raw_successor $iq' $iz').
        { eapply CE2, Ctx. unfold Kq'. now left. }
        apply (order_iso_successor_congruence _ $iq $iz $iq' $iz').
        -- inherit HE.
        -- inherit HQ.
        -- inherit HEq.
        -- inherit HEtr.
        -- inherit Hempty.
        -- inherit HAdj.
        -- apply (add_result_ordinal _ $ia $iy $iq). inherit Hqa.
        -- apply (add_result_ordinal _ $ip' $iy' $iq'). exact Hq'a.
        -- inherit Hqs.
        -- exact Hq's.
        -- apply (add_comparison_property_instance _ $ia $ip' $iy $iy' $iq $iq').
           ++ inherit HC.
           ++ inherit Hp'.
           ++ inherit HY.
           ++ inherit HY'.
           ++ inherit Hip'.
           ++ inherit Hyy.
           ++ inherit Hqa.
           ++ exact Hq'a.
Qed.

Theorem add_comparison_induction_base G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 ordinal_base (add_comparison_property $0).
Proof.
  intros HE HQ HEq HEtr. unfold ordinal_base.
  apply AllI_named. intro x. destruct x as [ix|[]].
  change (G ⊢238 ((ordinal_representative $ix ∧ raw_zero $ix) →
    (add_comparison_property $0)[$ix..])).
  rewrite add_comparison_property_at. apply II.
  assert (HX : (ordinal_representative $ix ∧ raw_zero $ix :: G)
    ⊢238 ordinal_representative $ix).
  { eapply CE1, Ctx. now left. }
  assert (HZ : (ordinal_representative $ix ∧ raw_zero $ix :: G) ⊢238 raw_zero $ix).
  { eapply CE2, Ctx. now left. }
  unfold add_comparison_property. apply AllI_named. intro x'. destruct x' as [ix'|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro y'. destruct y' as [iy'|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro z'. destruct z' as [iz'|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply II, II, II, II, II, II, II.
  apply (add_results_zero_coherence _ $ix $ix' $iy $iy' $iz $iz').
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit HX.
  - apply Ctx. right. right. right. right. right. right. now left.
  - inherit HZ.
  - apply Ctx. right. right. right. now left.
  - apply Ctx. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Theorem add_comparison_induction_step G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 graph_restriction_ax ->
  G ⊢238 iso_successor_match_ax -> G ⊢238 ordinal_step (add_comparison_property $0).
Proof.
  intros HE HQ HEq HEtr Hempty HAdj Hcuts Hmatch. apply add_ordinal_step_intro.
  intros a b. destruct a as [ia|[]], b as [ib|[]]. rewrite !add_comparison_property_at.
  assert (HA : (add_comparison_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 ordinal_representative $ia).
  { eapply CE1, Ctx. right. now left. }
  assert (HB : (add_comparison_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 ordinal_representative $ib).
  { eapply CE1, CE2, Ctx. right. now left. }
  assert (HS : (add_comparison_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 raw_successor $ia $ib).
  { eapply CE2, CE2, Ctx. right. now left. }
  assert (HC : (add_comparison_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 add_comparison_property $ia).
  { apply Ctx. now left. }
  unfold add_comparison_property at 1.
  apply AllI_named. intro x'. destruct x' as [ix'|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro y'. destruct y' as [iy'|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro z'. destruct z' as [iz'|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply II, II, II, II, II, II, II.
  apply (add_comparison_successor_at _ $ia $ib $ix' $iy $iy' $iz $iz').
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit Hempty.
  - inherit HAdj.
  - inherit Hcuts.
  - inherit Hmatch.
  - inherit HA.
  - inherit HB.
  - inherit HS.
  - inherit HC.
  - apply Ctx. right. right. right. right. right. right. now left.
  - apply Ctx. right. right. right. right. right. now left.
  - apply Ctx. right. right. right. right. now left.
  - apply Ctx. right. right. right. now left.
  - apply Ctx. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Lemma add_comparison_property_bounded : bounded 1 (add_comparison_property $0).
Proof.
  unfold add_comparison_property, order_iso, order_bijection, graph_entries,
    entry_witness, graph_typed, graph_left_total, graph_right_total,
    IsoGraph238.IsoGraph238.graph_functional, graph_injective, graph_order,
    add_result, add_prefix, add_recurrence, graph_domain,
    TraceGraph238.TraceGraph238.graph_functional, graph_range,
    ordinal_representative, member_ir, representative, raw_zero, raw_successor,
    transitive, member_transitive, member_linear, internal_extrema, subset,
    nonempty, least, greatest, graph_edge, raw_kuratowski, raw_pair,
    raw_singleton, R, E.
  cbn. fixed_bounds.
Qed.

Theorem S0_add_comparison_base :
  derivable finite_set_S0 (ordinal_base (add_comparison_property $0)).
Proof.
  exists equality_base. split.
  - intros psi Hpsi. apply S0_base. apply in_or_app. now left.
  - apply add_comparison_induction_base.
    + apply Ctx. unfold equality_base. cbn. now left.
    + apply Ctx. unfold equality_base, equality_membership_ax. cbn.
      right. right. right. now left.
    + apply Ctx. unfold equality_base, equality_symmetry_ax. cbn. right. now left.
    + apply Ctx. unfold equality_base, equality_transitivity_ax. cbn. right. right. now left.
Qed.

Theorem S0_add_comparison_step :
  derivable finite_set_S0 (ordinal_step (add_comparison_property $0)).
Proof.
  destruct S0_empty as [Gempty [HGempty Hempty]].
  destruct S0_graph_restriction_closed as [Gcut [HGcut Hcut]].
  destruct S0_order_iso_successor_match_closed as [Gmatch [HGmatch Hmatch]].
  set (G := equality_base ++ (adjunction_ax :: Gempty) ++ Gcut ++ Gmatch).
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
  assert (HAdj : G ⊢238 adjunction_ax).
  { apply Ctx. unfold G, equality_base. cbn. right. right. right. right. now left. }
  assert (Hempty' : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. left. now right. }
  assert (Hcut' : G ⊢238 graph_restriction_ax).
  { eapply Weak; [exact Hcut|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. now left. }
  assert (Hmatch' : G ⊢238 iso_successor_match_ax).
  { eapply Weak; [exact Hmatch|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + apply in_app_or in Hpsi as [[<-|Hpsi]|Hpsi].
      * apply S0_base. apply in_or_app. right. now left.
      * now apply HGempty.
      * apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGcut|now apply HGmatch].
  - apply add_comparison_induction_step; assumption.
Qed.

Definition add_comparison_ax : set_form :=
  ∀ (ordinal_representative $0 → add_comparison_property $0).

(** This is the joint arithmetic coherence theorem. The full S0 induction
    schema is applied to the displayed bodyful base and step. All cut and
    matching contexts are finite actual S0 derivations and are discharged. *)
Theorem S0_add_comparison_closed : derivable finite_set_S0 add_comparison_ax.
Proof.
  pose proof (S0_ordinal_induction 0 (add_comparison_property $0)
    add_comparison_property_bounded) as HI.
  pose proof (derivable_mp finite_set_S0 _ _ HI S0_add_comparison_base) as HS.
  exact (derivable_mp finite_set_S0 _ _ HS S0_add_comparison_step).
Qed.

Lemma add_comparison_instance G x x' y y' z z' :
  G ⊢238 add_comparison_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative x' -> G ⊢238 ordinal_representative y ->
  G ⊢238 ordinal_representative y' -> G ⊢238 order_iso x x' ->
  G ⊢238 order_iso y y' -> G ⊢238 add_result x y z ->
  G ⊢238 add_result x' y' z' -> G ⊢238 order_iso z z'.
Proof.
  destruct x as [ix|[]]. intros HC HX HX' HY HY' Hxx Hyy HM HM'.
  unfold add_comparison_ax in HC. pose proof (AllE $ix HC) as H.
  change (G ⊢238 (ordinal_representative $ix →
    (add_comparison_property $0)[$ix..])) in H.
  rewrite add_comparison_property_at in H.
  apply (add_comparison_property_instance _ $ix x' y y' z z'); try assumption.
  exact (IE H HX).
Qed.

Theorem S0_add_covariance x x' y y' z z' :
  derivable finite_set_S0
    (ordinal_representative x → ordinal_representative x' →
      ordinal_representative y → ordinal_representative y' →
      order_iso x x' → order_iso y y' → add_result x y z →
      add_result x' y' z' → order_iso z z').
Proof.
  destruct S0_add_comparison_closed as [G [HG HC]]. exists G. split; [exact HG|].
  apply II, II, II, II, II, II, II, II.
  apply (add_comparison_instance _ x x' y y' z z').
  - inherit HC.
  - apply Ctx. right. right. right. right. right. right. right. now left.
  - apply Ctx. right. right. right. right. right. right. now left.
  - apply Ctx. right. right. right. right. right. now left.
  - apply Ctx. right. right. right. right. now left.
  - apply Ctx. right. right. right. now left.
  - apply Ctx. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

(** Determinacy for fixed operands uses the actual identity graphs. It
    concludes numerical equality and never identifies independent raw
    successor or empty-set encodings by literal equality. *)
Theorem S0_add_determinacy x y z z' :
  derivable finite_set_S0
    (ordinal_representative x → ordinal_representative y →
      add_result x y z → add_result x y z' → order_iso z z').
Proof.
  destruct S0_add_comparison_closed as [Gc [HGc HC]].
  destruct (S0_order_iso_reflexive x) as [Gx [HGx HX]].
  destruct (S0_order_iso_reflexive y) as [Gy [HGy HY]].
  set (G := Gc ++ Gx ++ Gy).
  assert (HC' : G ⊢238 add_comparison_ax).
  { eapply Weak; [exact HC|]. intros psi Hpsi. unfold G. apply in_or_app. now left. }
  assert (HX' : G ⊢238 (ordinal_representative x → order_iso x x)).
  { eapply Weak; [exact HX|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. now left. }
  assert (HY' : G ⊢238 (ordinal_representative y → order_iso y y)).
  { eapply Weak; [exact HY|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + now apply HGc.
    + apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGx|now apply HGy].
  - apply II, II, II, II. apply (add_comparison_instance _ x x y y z z').
    + inherit HC'.
    + apply Ctx. right. right. right. now left.
    + apply Ctx. right. right. right. now left.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. right. now left.
    + eapply IE; [inherit HX'|apply Ctx; right; right; right; now left].
    + eapply IE; [inherit HY'|apply Ctx; right; right; now left].
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Definition add_right_zero_property (x : set_term) : set_form :=
  ∀ ∀ (raw_zero $1 → add_result x`[↑]`[↑] $1 $0 → order_iso x`[↑]`[↑] $0).

Ltac unfold_add_iso_syntax :=
  unfold order_iso, order_bijection, graph_entries, entry_witness, graph_typed,
    graph_left_total, graph_right_total, IsoGraph238.IsoGraph238.graph_functional,
    graph_injective, graph_order, add_result, add_prefix, add_recurrence,
    graph_domain, TraceGraph238.TraceGraph238.graph_functional, graph_range,
    ordinal_representative, member_ir, representative, raw_zero, raw_successor,
    transitive, member_transitive, member_linear, internal_extrema, subset,
    nonempty, least, greatest, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.

Lemma add_right_zero_property_subst x sigma :
  (add_right_zero_property x)[sigma] = add_right_zero_property x`[sigma].
Proof.
  unfold add_right_zero_property. unfold_add_iso_syntax.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma add_right_zero_property_at x :
  (add_right_zero_property $0)[x..] = add_right_zero_property x.
Proof. rewrite add_right_zero_property_subst. reflexivity. Qed.

Lemma add_right_zero_property_instance G x e z :
  G ⊢238 add_right_zero_property x -> G ⊢238 raw_zero e ->
  G ⊢238 add_result x e z -> G ⊢238 order_iso x z.
Proof.
  destruct x as [ix|[]], e as [ie|[]], z as [iz|[]]. intros HR HZ HA.
  unfold add_right_zero_property in HR.
  pose proof (AllE $iz (AllE $ie HR)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (IE H HZ) HA).
Qed.

Lemma add_right_zero_property_bounded : bounded 1 (add_right_zero_property $0).
Proof. unfold add_right_zero_property. unfold_add_iso_syntax. cbn. fixed_bounds. Qed.

Theorem add_right_zero_induction_base G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 ordinal_base (add_right_zero_property $0).
Proof.
  intros HE HQ HEq HEtr Hempty. unfold ordinal_base.
  apply AllI_named. intro x. destruct x as [ix|[]].
  change (G ⊢238 ((ordinal_representative $ix ∧ raw_zero $ix) →
    (add_right_zero_property $0)[$ix..])).
  rewrite add_right_zero_property_at. apply II.
  assert (HX : (ordinal_representative $ix ∧ raw_zero $ix :: G)
    ⊢238 ordinal_representative $ix).
  { eapply CE1, Ctx. now left. }
  assert (HZ : (ordinal_representative $ix ∧ raw_zero $ix :: G) ⊢238 raw_zero $ix).
  { eapply CE2, Ctx. now left. }
  unfold add_right_zero_property. apply AllI_named. intro e. destruct e as [ie|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, II.
  apply (zero_order_iso _ $ix $iz); [inherit Hempty|inherit HZ|].
  apply (raw_zero_coordinate_transport _ $ie $iz).
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - apply equality_symmetry_instance; [inherit HEq|].
    apply (add_result_zero_value _ $ix $ie $iz).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit HX.
    + inherit HZ.
    + apply Ctx. now left.
  - apply Ctx. right. now left.
Qed.

Theorem add_right_zero_induction_step G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 graph_restriction_ax ->
  G ⊢238 ordinal_step (add_right_zero_property $0).
Proof.
  intros HE HQ HEq HEtr Hempty HAdj Hcuts. apply add_ordinal_step_intro.
  intros a b. destruct a as [ia|[]], b as [ib|[]]. rewrite !add_right_zero_property_at.
  assert (HA : (add_right_zero_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 ordinal_representative $ia).
  { eapply CE1, Ctx. right. now left. }
  assert (HS : (add_right_zero_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 raw_successor $ia $ib).
  { eapply CE2, CE2, Ctx. right. now left. }
  assert (HC : (add_right_zero_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 add_right_zero_property $ia).
  { apply Ctx. now left. }
  unfold add_right_zero_property at 1.
  apply AllI_named. intro e. destruct e as [ie|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, II.
  eapply ExE_named.
  - apply (add_result_predecessor_witness _ $ia $ib $ie $iz).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Hcuts.
    + inherit HA.
    + inherit HS.
    + apply Ctx. now left.
  - intro q. destruct q as [iq|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (order_iso_successor_congruence _ $ia $ib $iq $iz).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Hempty.
    + inherit HAdj.
    + inherit HA.
    + apply (add_result_ordinal _ $ia $ie $iq). eapply CE1, Ctx. now left.
    + inherit HS.
    + eapply CE2, Ctx. now left.
    + apply (add_right_zero_property_instance _ $ia $ie $iq).
      * inherit HC.
      * apply Ctx. right. right. now left.
      * eapply CE1, Ctx. now left.
Qed.

Definition add_right_zero_ax : set_form :=
  ∀ (ordinal_representative $0 → add_right_zero_property $0).

Theorem S0_add_right_zero_closed : derivable finite_set_S0 add_right_zero_ax.
Proof.
  destruct S0_empty as [Gempty [HGempty Hempty]].
  destruct S0_graph_restriction_closed as [Gcuts [HGcuts Hcuts]].
  set (G := equality_base ++ (adjunction_ax :: Gempty) ++ Gcuts).
  assert (HG : forall psi, In psi G -> finite_set_S0 psi).
  { intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    - apply S0_base. apply in_or_app. now left.
    - apply in_app_or in Hpsi as [[<-|Hpsi]|Hpsi].
      + apply S0_base. apply in_or_app. right. now left.
      + now apply HGempty.
      + now apply HGcuts. }
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
  assert (HAdj : G ⊢238 adjunction_ax).
  { apply Ctx. unfold G, equality_base. cbn. right. right. right. right. now left. }
  assert (Hempty' : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. left. now right. }
  assert (Hcuts' : G ⊢238 graph_restriction_ax).
  { eapply Weak; [exact Hcuts|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. now right. }
  assert (HB : derivable finite_set_S0 (ordinal_base (add_right_zero_property $0))).
  { exists G. split; [exact HG|apply add_right_zero_induction_base; assumption]. }
  assert (HS : derivable finite_set_S0 (ordinal_step (add_right_zero_property $0))).
  { exists G. split; [exact HG|apply add_right_zero_induction_step; assumption]. }
  pose proof (S0_ordinal_induction 0 (add_right_zero_property $0)
    add_right_zero_property_bounded) as HI.
  exact (derivable_mp finite_set_S0 _ _ (derivable_mp finite_set_S0 _ _ HI HB) HS).
Qed.

Lemma add_right_zero_instance G x e z :
  G ⊢238 add_right_zero_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 raw_zero e -> G ⊢238 add_result x e z -> G ⊢238 order_iso x z.
Proof.
  destruct x as [ix|[]]. intros HC HX HZ HA. unfold add_right_zero_ax in HC.
  pose proof (AllE $ix HC) as H.
  change (G ⊢238 (ordinal_representative $ix →
    (add_right_zero_property $0)[$ix..])) in H.
  rewrite add_right_zero_property_at in H.
  apply (add_right_zero_property_instance _ $ix e z); [exact (IE H HX)|exact HZ|exact HA].
Qed.

Definition add_iso_reflexivity_ax : set_form :=
  ∀ (ordinal_representative $0 → order_iso $0 $0).

Theorem S0_add_iso_reflexivity_closed : derivable finite_set_S0 add_iso_reflexivity_ax.
Proof. unfold add_iso_reflexivity_ax. apply S0_generalize, S0_order_iso_reflexive. Qed.

Lemma add_iso_reflexivity_instance G x :
  G ⊢238 add_iso_reflexivity_ax -> G ⊢238 ordinal_representative x -> G ⊢238 order_iso x x.
Proof.
  destruct x as [ix|[]]. intros HC HX. unfold add_iso_reflexivity_ax in HC.
  pose proof (AllE $ix HC) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HX).
Qed.

Definition add_right_successor_property (x : set_term) : set_form :=
  ∀ ∀ ∀ ∀ (ordinal_representative $3 → raw_successor $3 $2 →
    add_result x`[↑]`[↑]`[↑]`[↑] $3 $1 → add_result x`[↑]`[↑]`[↑]`[↑] $2 $0 →
    ∃ (ordinal_representative $0 ∧ (raw_successor $0 $1 ∧ order_iso $2 $0))).

Lemma add_right_successor_property_subst x sigma :
  (add_right_successor_property x)[sigma] = add_right_successor_property x`[sigma].
Proof.
  unfold add_right_successor_property. unfold_add_iso_syntax.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma add_right_successor_property_at x :
  (add_right_successor_property $0)[x..] = add_right_successor_property x.
Proof. rewrite add_right_successor_property_subst. reflexivity. Qed.

Lemma add_right_successor_property_bounded : bounded 1 (add_right_successor_property $0).
Proof. unfold add_right_successor_property. unfold_add_iso_syntax. cbn. fixed_bounds. Qed.

Lemma add_right_successor_property_instance G x y sy z w :
  G ⊢238 add_right_successor_property x -> G ⊢238 ordinal_representative y ->
  G ⊢238 raw_successor y sy -> G ⊢238 add_result x y z -> G ⊢238 add_result x sy w ->
  G ⊢238 ∃ (ordinal_representative $0 ∧ (raw_successor $0 w`[↑] ∧ order_iso z`[↑] $0)).
Proof.
  destruct x as [ix|[]], y as [iy|[]], sy as [is|[]], z as [iz|[]], w as [iw|[]].
  intros HC HY HS HA HA'. unfold add_right_successor_property in HC.
  pose proof (AllE $iw (AllE $iz (AllE $is (AllE $iy HC)))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (IE (IE (IE H HY) HS) HA) HA').
Qed.

Theorem add_right_successor_base_at G x y sy z w :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 add_iso_reflexivity_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 raw_zero x -> G ⊢238 ordinal_representative y ->
  G ⊢238 raw_successor y sy -> G ⊢238 add_result x y z -> G ⊢238 add_result x sy w ->
  G ⊢238 ∃ (ordinal_representative $0 ∧ (raw_successor $0 w`[↑] ∧ order_iso z`[↑] $0)).
Proof.
  destruct x as [ix|[]], y as [iy|[]], sy as [is|[]], z as [iz|[]], w as [iw|[]].
  intros HE HQ HEq HEtr Href HX HZ HY HS HA HA'.
  assert (Hzy : G ⊢238 E $iz $iy).
  { apply (add_result_zero_value _ $ix $iy $iz); assumption. }
  assert (Hws : G ⊢238 E $iw $is).
  { apply (add_result_zero_value _ $ix $is $iw); assumption. }
  apply (ExI $iy).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI; [exact HY|].
  apply CI.
  - apply (raw_successor_coordinate_transport _ $iy $is $iy $iw).
    + exact HE.
    + exact HQ.
    + exact HEq.
    + exact HEtr.
    + exact (AllE $iy HE).
    + apply equality_symmetry_instance; assumption.
    + exact HS.
  - apply (order_iso_coordinate_transport _ $iy $iy $iz $iy).
    + exact HE.
    + exact HQ.
    + exact HEq.
    + apply equality_symmetry_instance; assumption.
    + exact (AllE $iy HE).
    + apply (add_iso_reflexivity_instance _ $iy); assumption.
Qed.

Theorem add_right_successor_step_at G a b y sy z w :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 graph_restriction_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 raw_successor a b ->
  G ⊢238 add_right_successor_property a -> G ⊢238 ordinal_representative y ->
  G ⊢238 raw_successor y sy -> G ⊢238 add_result b y z -> G ⊢238 add_result b sy w ->
  G ⊢238 ∃ (ordinal_representative $0 ∧ (raw_successor $0 w`[↑] ∧ order_iso z`[↑] $0)).
Proof.
  destruct a as [ia|[]], b as [ib|[]], y as [iy|[]], sy as [is|[]], z as [iz|[]], w as [iw|[]].
  intros HE HQ HEq HEtr Hempty HAdj Hcuts HA HS HC HY Hsy HM HM'.
  eapply ExE_named.
  - apply (add_result_predecessor_witness _ $ia $ib $iy $iz); assumption.
  - intro q. destruct q as [iq|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    set (Kq := (add_result $ia $iy $iq ∧ raw_successor $iq $iz) :: G).
    change (Kq ⊢238 ∃ (ordinal_representative $0 ∧
      (raw_successor $0 $iw`[↑] ∧ order_iso $iz`[↑] $0))).
    assert (Hqa : Kq ⊢238 add_result $ia $iy $iq).
    { eapply CE1, Ctx. unfold Kq. now left. }
    assert (Hqs : Kq ⊢238 raw_successor $iq $iz).
    { eapply CE2, Ctx. unfold Kq. now left. }
    eapply ExE_named.
    + apply (add_result_predecessor_witness _ $ia $ib $is $iw);
        [inherit HE|inherit HQ|inherit HEq|inherit HEtr|inherit Hcuts|
         inherit HA|inherit HS|inherit HM'].
    + intro r. destruct r as [ir|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      set (Kr := (add_result $ia $is $ir ∧ raw_successor $ir $iw) :: Kq).
      change (Kr ⊢238 ∃ (ordinal_representative $0 ∧
        (raw_successor $0 $iw`[↑] ∧ order_iso $iz`[↑] $0))).
      assert (Hra : Kr ⊢238 add_result $ia $is $ir).
      { eapply CE1, Ctx. unfold Kr. now left. }
      assert (Hrs : Kr ⊢238 raw_successor $ir $iw).
      { eapply CE2, Ctx. unfold Kr. now left. }
      eapply ExE_named.
      * apply (add_right_successor_property_instance _ $ia $iy $is $iq $ir).
        -- inherit HC.
        -- inherit HY.
        -- inherit Hsy.
        -- inherit Hqa.
        -- exact Hra.
      * intro s. destruct s as [is'|[]].
        cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
        set (Ks := (ordinal_representative $is' ∧
          (raw_successor $is' $ir ∧ order_iso $iq $is')) :: Kr).
        change (Ks ⊢238 ∃ (ordinal_representative $0 ∧
          (raw_successor $0 $iw`[↑] ∧ order_iso $iz`[↑] $0))).
        apply (ExI $ir).
        cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
        -- apply (add_result_ordinal _ $ia $is $ir). inherit Hra.
        -- apply CI; [inherit Hrs|].
           apply (order_iso_successor_congruence _ $iq $iz $is' $ir).
           ++ inherit HE.
           ++ inherit HQ.
           ++ inherit HEq.
           ++ inherit HEtr.
           ++ inherit Hempty.
           ++ inherit HAdj.
           ++ apply (add_result_ordinal _ $ia $iy $iq). inherit Hqa.
           ++ eapply CE1, Ctx. unfold Ks. now left.
           ++ inherit Hqs.
           ++ eapply CE1, CE2, Ctx. unfold Ks. now left.
           ++ eapply CE2, CE2, Ctx. unfold Ks. now left.
Qed.

Theorem add_right_successor_induction_base G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 add_iso_reflexivity_ax -> G ⊢238 ordinal_base (add_right_successor_property $0).
Proof.
  intros HE HQ HEq HEtr Href. unfold ordinal_base.
  apply AllI_named. intro x. destruct x as [ix|[]].
  change (G ⊢238 ((ordinal_representative $ix ∧ raw_zero $ix) →
    (add_right_successor_property $0)[$ix..])).
  rewrite add_right_successor_property_at. apply II.
  assert (HX : (ordinal_representative $ix ∧ raw_zero $ix :: G)
    ⊢238 ordinal_representative $ix).
  { eapply CE1, Ctx. now left. }
  assert (HZ : (ordinal_representative $ix ∧ raw_zero $ix :: G) ⊢238 raw_zero $ix).
  { eapply CE2, Ctx. now left. }
  unfold add_right_successor_property. apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro sy. destruct sy as [is|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro w. destruct w as [iw|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, II, II, II.
  apply (add_right_successor_base_at _ $ix $iy $is $iz $iw).
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit Href.
  - inherit HX.
  - inherit HZ.
  - apply Ctx. right. right. right. now left.
  - apply Ctx. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Theorem add_right_successor_induction_step G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 graph_restriction_ax ->
  G ⊢238 ordinal_step (add_right_successor_property $0).
Proof.
  intros HE HQ HEq HEtr Hempty HAdj Hcuts. apply add_ordinal_step_intro.
  intros a b. destruct a as [ia|[]], b as [ib|[]]. rewrite !add_right_successor_property_at.
  assert (HA : (add_right_successor_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 ordinal_representative $ia).
  { eapply CE1, Ctx. right. now left. }
  assert (HS : (add_right_successor_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 raw_successor $ia $ib).
  { eapply CE2, CE2, Ctx. right. now left. }
  assert (HC : (add_right_successor_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 add_right_successor_property $ia).
  { apply Ctx. now left. }
  unfold add_right_successor_property at 1.
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro sy. destruct sy as [is|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro w. destruct w as [iw|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, II, II, II.
  apply (add_right_successor_step_at _ $ia $ib $iy $is $iz $iw).
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit Hempty.
  - inherit HAdj.
  - inherit Hcuts.
  - inherit HA.
  - inherit HS.
  - inherit HC.
  - apply Ctx. right. right. right. now left.
  - apply Ctx. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Definition add_right_successor_ax : set_form :=
  ∀ (ordinal_representative $0 → add_right_successor_property $0).

Theorem S0_add_right_successor_closed : derivable finite_set_S0 add_right_successor_ax.
Proof.
  destruct S0_empty as [Gempty [HGempty Hempty]].
  destruct S0_graph_restriction_closed as [Gcuts [HGcuts Hcuts]].
  destruct S0_add_iso_reflexivity_closed as [Gref [HGref Href]].
  set (G := equality_base ++ (adjunction_ax :: Gempty) ++ Gcuts ++ Gref).
  assert (HG : forall psi, In psi G -> finite_set_S0 psi).
  { intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    - apply S0_base. apply in_or_app. now left.
    - apply in_app_or in Hpsi as [[<-|Hpsi]|Hpsi].
      + apply S0_base. apply in_or_app. right. now left.
      + now apply HGempty.
      + apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGcuts|now apply HGref]. }
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
  assert (HAdj : G ⊢238 adjunction_ax).
  { apply Ctx. unfold G, equality_base. cbn. right. right. right. right. now left. }
  assert (Hempty' : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. left. now right. }
  assert (Hcuts' : G ⊢238 graph_restriction_ax).
  { eapply Weak; [exact Hcuts|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. now left. }
  assert (Href' : G ⊢238 add_iso_reflexivity_ax).
  { eapply Weak; [exact Href|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. now right. }
  assert (HB : derivable finite_set_S0 (ordinal_base (add_right_successor_property $0))).
  { exists G. split; [exact HG|apply add_right_successor_induction_base; assumption]. }
  assert (HS : derivable finite_set_S0 (ordinal_step (add_right_successor_property $0))).
  { exists G. split; [exact HG|apply add_right_successor_induction_step; assumption]. }
  pose proof (S0_ordinal_induction 0 (add_right_successor_property $0)
    add_right_successor_property_bounded) as HI.
  exact (derivable_mp finite_set_S0 _ _ (derivable_mp finite_set_S0 _ _ HI HB) HS).
Qed.

Lemma add_right_successor_instance G x y sy z w :
  G ⊢238 add_right_successor_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative y -> G ⊢238 raw_successor y sy ->
  G ⊢238 add_result x y z -> G ⊢238 add_result x sy w ->
  G ⊢238 ∃ (ordinal_representative $0 ∧ (raw_successor $0 w`[↑] ∧ order_iso z`[↑] $0)).
Proof.
  destruct x as [ix|[]]. intros HC HX HY HS HA HA'. unfold add_right_successor_ax in HC.
  pose proof (AllE $ix HC) as H.
  change (G ⊢238 (ordinal_representative $ix →
    (add_right_successor_property $0)[$ix..])) in H.
  rewrite add_right_successor_property_at in H.
  apply (add_right_successor_property_instance _ $ix y sy z w);
    [exact (IE H HX)|exact HY|exact HS|exact HA|exact HA'].
Qed.

Definition add_represented_totality_ax : set_form :=
  ∀ ∀ ((ordinal_representative $1 ∧ ordinal_representative $0) →
    ∃ add_result $2 $1 $0).

Theorem S0_add_represented_totality_closed : derivable finite_set_S0 add_represented_totality_ax.
Proof.
  unfold add_represented_totality_ax. apply S0_generalize, S0_generalize.
  exact (S0_add_total $1 $0).
Qed.

Lemma add_represented_totality_instance G x y :
  G ⊢238 add_represented_totality_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative y -> G ⊢238 ∃ add_result x`[↑] y`[↑] $0.
Proof.
  destruct x as [ix|[]], y as [iy|[]]. intros HT HX HY.
  unfold add_represented_totality_ax in HT. pose proof (AllE $iy (AllE $ix HT)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma add_iso_transitivity_instance G x y z :
  G ⊢238 iso_transitivity_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 order_iso x y -> G ⊢238 order_iso y z -> G ⊢238 order_iso x z.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]]. intros HT HX HI HJ.
  unfold iso_transitivity_ax in HT.
  pose proof (AllE $iz (AllE $iy (AllE $ix HT))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (IE (IE H HX) HI) HJ).
Qed.

Definition add_commutation_property (x : set_term) : set_form :=
  ∀ ∀ ∀ (ordinal_representative $2 →
    add_result x`[↑]`[↑]`[↑] $2 $1 → add_result $2 x`[↑]`[↑]`[↑] $0 → order_iso $1 $0).

Lemma add_commutation_property_subst x sigma :
  (add_commutation_property x)[sigma] = add_commutation_property x`[sigma].
Proof.
  unfold add_commutation_property. unfold_add_iso_syntax.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma add_commutation_property_at x :
  (add_commutation_property $0)[x..] = add_commutation_property x.
Proof. rewrite add_commutation_property_subst. reflexivity. Qed.

Lemma add_commutation_property_bounded : bounded 1 (add_commutation_property $0).
Proof. unfold add_commutation_property. unfold_add_iso_syntax. cbn. fixed_bounds. Qed.

Lemma add_commutation_property_instance G x y z z' :
  G ⊢238 add_commutation_property x -> G ⊢238 ordinal_representative y ->
  G ⊢238 add_result x y z -> G ⊢238 add_result y x z' -> G ⊢238 order_iso z z'.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]], z' as [iz'|[]]. intros HC HY HA HA'.
  unfold add_commutation_property in HC.
  pose proof (AllE $iz' (AllE $iz (AllE $iy HC))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (IE (IE H HY) HA) HA').
Qed.

Theorem add_commutation_base_at G x y z z' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 add_right_zero_ax -> G ⊢238 ordinal_representative x -> G ⊢238 raw_zero x ->
  G ⊢238 ordinal_representative y -> G ⊢238 add_result x y z ->
  G ⊢238 add_result y x z' -> G ⊢238 order_iso z z'.
Proof.
  intros HE HQ HEq HEtr Hrightzero HX HZ HY HA HA'.
  apply (order_iso_coordinate_transport _ y z' z z').
  - exact HE.
  - exact HQ.
  - exact HEq.
  - apply equality_symmetry_instance; [exact HEq|].
    apply (add_result_zero_value _ x y z); assumption.
  - exact (AllE z' HE).
  - apply (add_right_zero_instance _ y x z'); assumption.
Qed.

(** The swap induction selects the missing old sum by the actual Add
    totality theorem. The right-successor law reads a predecessor from
    the other trace. One actually constructed composition joins the two
    predecessor comparisons, and endpoint adjunction closes the result. *)
Theorem add_commutation_step_at G a b y z z' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 graph_restriction_ax ->
  G ⊢238 add_represented_totality_ax -> G ⊢238 add_right_successor_ax ->
  G ⊢238 iso_transitivity_ax -> G ⊢238 ordinal_representative a ->
  G ⊢238 raw_successor a b -> G ⊢238 add_commutation_property a ->
  G ⊢238 ordinal_representative y -> G ⊢238 add_result b y z ->
  G ⊢238 add_result y b z' -> G ⊢238 order_iso z z'.
Proof.
  destruct a as [ia|[]], b as [ib|[]], y as [iy|[]], z as [iz|[]], z' as [iz'|[]].
  intros HE HQ HEq HEtr Hempty HAdj Hcuts Htotal Hrightsucc Htrans HA HS HC HY HM HM'.
  eapply ExE_named.
  - apply (add_result_predecessor_witness _ $ia $ib $iy $iz); assumption.
  - intro q. destruct q as [iq|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    set (Kq := (add_result $ia $iy $iq ∧ raw_successor $iq $iz) :: G).
    change (Kq ⊢238 order_iso $iz $iz').
    assert (Hqa : Kq ⊢238 add_result $ia $iy $iq).
    { eapply CE1, Ctx. unfold Kq. now left. }
    assert (Hqs : Kq ⊢238 raw_successor $iq $iz).
    { eapply CE2, Ctx. unfold Kq. now left. }
    eapply ExE_named.
    + apply (add_represented_totality_instance _ $iy $ia);
        [inherit Htotal|inherit HY|inherit HA].
    + intro r. destruct r as [ir|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      set (Kr := add_result $iy $ia $ir :: Kq).
      change (Kr ⊢238 order_iso $iz $iz').
      assert (Hra : Kr ⊢238 add_result $iy $ia $ir).
      { apply Ctx. unfold Kr. now left. }
      assert (Hqr : Kr ⊢238 order_iso $iq $ir).
      { apply (add_commutation_property_instance _ $ia $iy $iq $ir).
        - inherit HC.
        - inherit HY.
        - inherit Hqa.
        - exact Hra. }
      eapply ExE_named.
      * apply (add_right_successor_instance _ $iy $ia $ib $ir $iz').
        -- inherit Hrightsucc.
        -- inherit HY.
        -- inherit HA.
        -- inherit HS.
        -- exact Hra.
        -- inherit HM'.
      * intro s. destruct s as [is|[]].
        cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
        set (Ks := (ordinal_representative $is ∧
          (raw_successor $is $iz' ∧ order_iso $ir $is)) :: Kr).
        change (Ks ⊢238 order_iso $iz $iz').
        apply (order_iso_successor_congruence _ $iq $iz $is $iz').
        -- inherit HE.
        -- inherit HQ.
        -- inherit HEq.
        -- inherit HEtr.
        -- inherit Hempty.
        -- inherit HAdj.
        -- apply (add_result_ordinal _ $ia $iy $iq). inherit Hqa.
        -- eapply CE1, Ctx. unfold Ks. now left.
        -- inherit Hqs.
        -- eapply CE1, CE2, Ctx. unfold Ks. now left.
        -- apply (add_iso_transitivity_instance _ $iq $ir $is).
           ++ inherit Htrans.
           ++ apply (add_result_ordinal _ $ia $iy $iq). inherit Hqa.
           ++ inherit Hqr.
           ++ eapply CE2, CE2, Ctx. unfold Ks. now left.
Qed.

Theorem add_commutation_induction_base G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 add_right_zero_ax -> G ⊢238 ordinal_base (add_commutation_property $0).
Proof.
  intros HE HQ HEq HEtr Hzero. unfold ordinal_base.
  apply AllI_named. intro x. destruct x as [ix|[]].
  change (G ⊢238 ((ordinal_representative $ix ∧ raw_zero $ix) →
    (add_commutation_property $0)[$ix..])).
  rewrite add_commutation_property_at. apply II.
  assert (HX : (ordinal_representative $ix ∧ raw_zero $ix :: G)
    ⊢238 ordinal_representative $ix).
  { eapply CE1, Ctx. now left. }
  assert (HZ : (ordinal_representative $ix ∧ raw_zero $ix :: G) ⊢238 raw_zero $ix).
  { eapply CE2, Ctx. now left. }
  unfold add_commutation_property. apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro z'. destruct z' as [iz'|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, II, II.
  apply (add_commutation_base_at _ $ix $iy $iz $iz').
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit Hzero.
  - inherit HX.
  - inherit HZ.
  - apply Ctx. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Theorem add_commutation_induction_step G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 graph_restriction_ax ->
  G ⊢238 add_represented_totality_ax -> G ⊢238 add_right_successor_ax ->
  G ⊢238 iso_transitivity_ax -> G ⊢238 ordinal_step (add_commutation_property $0).
Proof.
  intros HE HQ HEq HEtr Hempty HAdj Hcuts Htotal Hrightsucc Htrans.
  apply add_ordinal_step_intro. intros a b. destruct a as [ia|[]], b as [ib|[]].
  rewrite !add_commutation_property_at.
  assert (HA : (add_commutation_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 ordinal_representative $ia).
  { eapply CE1, Ctx. right. now left. }
  assert (HS : (add_commutation_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 raw_successor $ia $ib).
  { eapply CE2, CE2, Ctx. right. now left. }
  assert (HC : (add_commutation_property $ia ::
      (ordinal_representative $ia ∧ (ordinal_representative $ib ∧ raw_successor $ia $ib)) :: G)
      ⊢238 add_commutation_property $ia).
  { apply Ctx. now left. }
  unfold add_commutation_property at 1.
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro z'. destruct z' as [iz'|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, II, II.
  apply (add_commutation_step_at _ $ia $ib $iy $iz $iz').
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit Hempty.
  - inherit HAdj.
  - inherit Hcuts.
  - inherit Htotal.
  - inherit Hrightsucc.
  - inherit Htrans.
  - inherit HA.
  - inherit HS.
  - inherit HC.
  - apply Ctx. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Definition add_commutation_ax : set_form :=
  ∀ (ordinal_representative $0 → add_commutation_property $0).

(** Commutation is derived in the represented S0 arithmetic itself. Its
    only composition input is the finite, graph-constructing Iso theorem;
    no ordinary-PA commutativity theorem is imported or presumed. *)
Theorem S0_add_commutation_closed : derivable finite_set_S0 add_commutation_ax.
Proof.
  destruct S0_empty as [Gempty [HGempty Hempty]].
  destruct S0_graph_restriction_closed as [Gcuts [HGcuts Hcuts]].
  destruct S0_add_represented_totality_closed as [Gtotal [HGtotal Htotal]].
  destruct S0_add_right_zero_closed as [Gzero [HGzero Hzero]].
  destruct S0_add_right_successor_closed as [Gsucc [HGsucc Hsucc]].
  destruct S0_order_iso_transitive_closed as [Gtrans [HGtrans Htrans]].
  set (G := equality_base ++ (adjunction_ax :: Gempty) ++ Gcuts ++ Gtotal ++ Gzero ++ Gsucc ++ Gtrans).
  assert (HG : forall psi, In psi G -> finite_set_S0 psi).
  { intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    - apply S0_base. apply in_or_app. now left.
    - apply in_app_or in Hpsi as [[<-|Hpsi]|Hpsi].
      + apply S0_base. apply in_or_app. right. now left.
      + now apply HGempty.
      + apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGcuts|].
        apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGtotal|].
        apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGzero|].
        apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGsucc|now apply HGtrans]. }
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
  assert (HAdj : G ⊢238 adjunction_ax).
  { apply Ctx. unfold G, equality_base. cbn. right. right. right. right. now left. }
  assert (Hempty' : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. left. now right. }
  assert (Hcuts' : G ⊢238 graph_restriction_ax).
  { eapply Weak; [exact Hcuts|]. intros psi Hpsi. unfold G.
    do 2 (apply in_or_app; right). apply in_or_app. now left. }
  assert (Htotal' : G ⊢238 add_represented_totality_ax).
  { eapply Weak; [exact Htotal|]. intros psi Hpsi. unfold G.
    do 3 (apply in_or_app; right). apply in_or_app. now left. }
  assert (Hzero' : G ⊢238 add_right_zero_ax).
  { eapply Weak; [exact Hzero|]. intros psi Hpsi. unfold G.
    do 4 (apply in_or_app; right). apply in_or_app. now left. }
  assert (Hsucc' : G ⊢238 add_right_successor_ax).
  { eapply Weak; [exact Hsucc|]. intros psi Hpsi. unfold G.
    do 5 (apply in_or_app; right). apply in_or_app. now left. }
  assert (Htrans' : G ⊢238 iso_transitivity_ax).
  { eapply Weak; [exact Htrans|]. intros psi Hpsi. unfold G.
    do 6 (apply in_or_app; right). exact Hpsi. }
  assert (HB : derivable finite_set_S0 (ordinal_base (add_commutation_property $0))).
  { exists G. split; [exact HG|apply add_commutation_induction_base; assumption]. }
  assert (HS : derivable finite_set_S0 (ordinal_step (add_commutation_property $0))).
  { exists G. split; [exact HG|apply add_commutation_induction_step; assumption]. }
  pose proof (S0_ordinal_induction 0 (add_commutation_property $0)
    add_commutation_property_bounded) as HI.
  exact (derivable_mp finite_set_S0 _ _ (derivable_mp finite_set_S0 _ _ HI HB) HS).
Qed.

Lemma add_commutation_instance G x y z z' :
  G ⊢238 add_commutation_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative y -> G ⊢238 add_result x y z ->
  G ⊢238 add_result y x z' -> G ⊢238 order_iso z z'.
Proof.
  destruct x as [ix|[]]. intros HC HX HY HA HA'. unfold add_commutation_ax in HC.
  pose proof (AllE $ix HC) as H.
  change (G ⊢238 (ordinal_representative $ix →
    (add_commutation_property $0)[$ix..])) in H.
  rewrite add_commutation_property_at in H.
  apply (add_commutation_property_instance _ $ix y z z');
    [exact (IE H HX)|exact HY|exact HA|exact HA'].
Qed.

Theorem S0_add_commutation x y z z' :
  derivable finite_set_S0
    (ordinal_representative x → ordinal_representative y →
      add_result x y z → add_result y x z' → order_iso z z').
Proof.
  destruct S0_add_commutation_closed as [G [HG HC]]. exists G. split; [exact HG|].
  apply II, II, II, II. apply (add_commutation_instance _ x y z z').
  - inherit HC.
  - apply Ctx. right. right. right. now left.
  - apply Ctx. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Lemma add_swap_result_exists G x y z :
  G ⊢238 add_represented_totality_ax -> G ⊢238 add_commutation_ax ->
  G ⊢238 ordinal_representative x -> G ⊢238 ordinal_representative y ->
  G ⊢238 add_result x y z ->
  G ⊢238 ∃ (add_result y`[↑] x`[↑] $0 ∧ order_iso z`[↑] $0).
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]]. intros HT HC HX HY HA.
  eapply ExE_named; [apply (add_represented_totality_instance _ $iy $ix); assumption|].
  intro w. destruct w as [iw|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iw).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply Ctx. now left.
  - apply (add_commutation_instance _ $ix $iy $iz $iw);
      [inherit HC|inherit HX|inherit HY|inherit HA|apply Ctx; now left].
Qed.

Lemma add_commutation_ax_closed : bounded 0 add_commutation_ax.
Proof.
  unfold add_commutation_ax. constructor. constructor.
  - unfold ordinal_representative. constructor; [exact representative_bounded|].
    unfold member_ir, R. cbn. fixed_bounds.
  - exact add_commutation_property_bounded.
Qed.

Theorem S0_add_swap_result x y z :
  derivable finite_set_S0
    (ordinal_representative x → ordinal_representative y → add_result x y z →
      ∃ (add_result y`[↑] x`[↑] $0 ∧ order_iso z`[↑] $0)).
Proof.
  destruct S0_add_represented_totality_closed as [Gt [HGt HT]].
  destruct S0_add_commutation_closed as [Gc [HGc HC]].
  set (G := Gt ++ Gc).
  assert (HT' : G ⊢238 add_represented_totality_ax).
  { eapply Weak; [exact HT|]. intros psi Hpsi. unfold G. apply in_or_app. now left. }
  assert (HC' : G ⊢238 add_commutation_ax).
  { eapply Weak; [exact HC|]. intros psi Hpsi. unfold G. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGt|now apply HGc].
  - apply II, II, II. apply (add_swap_result_exists _ x y z).
    + inherit HT'.
    + inherit HC'.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Print Assumptions add_commutation_ax_closed.
Print Assumptions S0_add_swap_result.
Print Assumptions S0_add_commutation_closed.
Print Assumptions S0_add_commutation.
Print Assumptions add_commutation_instance.
Print Assumptions add_swap_result_exists.
Print Assumptions add_commutation_base_at.
Print Assumptions add_commutation_step_at.
Print Assumptions add_commutation_induction_base.
Print Assumptions add_commutation_induction_step.
Print Assumptions S0_add_right_successor_closed.
Print Assumptions add_right_successor_induction_base.
Print Assumptions add_right_successor_induction_step.
Print Assumptions add_right_successor_base_at.
Print Assumptions add_right_successor_step_at.
Print Assumptions S0_add_right_zero_closed.
Print Assumptions add_right_zero_induction_base.
Print Assumptions add_right_zero_induction_step.
Print Assumptions S0_add_determinacy.
Print Assumptions S0_add_comparison_closed.
Print Assumptions S0_add_covariance.
Print Assumptions add_comparison_instance.
Print Assumptions add_comparison_successor_at.
Print Assumptions add_comparison_induction_base.
Print Assumptions add_comparison_induction_step.
Print Assumptions add_result_predecessor_witness.
Print Assumptions add_prefix_predecessor_restriction.
Print Assumptions add_recurrence_restriction.
Print Assumptions add_prefix_zero_coherence.
Print Assumptions add_results_zero_coherence.
End AddCoherence238.
