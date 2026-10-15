(** Numerical multiplication coherence uses actual order-isomorphism
    graphs. The zero comparison constructs an empty graph even when the
    two empty objects and their trace encodings are unrelated by raw Eq. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 TraceGraph238 AddGraph238 MulGraph238 IsoGraph238 IsoZero238
  IsoMatchSupply238 AddCoherence238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  TraceGraph238.TraceGraph238 AddGraph238.AddGraph238 MulGraph238.MulGraph238
  IsoZero238.IsoZero238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module MulCoherence238.

Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition mul_comparison_property (x : set_term) : set_form :=
  ∀ ∀ ∀ ∀ ∀ (ordinal_representative $4 → ordinal_representative $3 →
    ordinal_representative $2 →
    IsoGraph238.IsoGraph238.order_iso x`[↑]`[↑]`[↑]`[↑]`[↑] $4 →
    IsoGraph238.IsoGraph238.order_iso $3 $2 →
    mul_result x`[↑]`[↑]`[↑]`[↑]`[↑] $3 $1 → mul_result $4 $2 $0 →
    IsoGraph238.IsoGraph238.order_iso $1 $0).

Lemma mul_comparison_property_subst x sigma :
  (mul_comparison_property x)[sigma] = mul_comparison_property x`[sigma].
Proof.
  unfold mul_comparison_property, IsoGraph238.IsoGraph238.order_iso,
    IsoGraph238.IsoGraph238.order_bijection, IsoGraph238.IsoGraph238.graph_entries,
    IsoGraph238.IsoGraph238.entry_witness, IsoGraph238.IsoGraph238.graph_typed,
    IsoGraph238.IsoGraph238.graph_left_total, IsoGraph238.IsoGraph238.graph_right_total,
    IsoGraph238.IsoGraph238.graph_functional, IsoGraph238.IsoGraph238.graph_injective,
    IsoGraph238.IsoGraph238.graph_order, mul_result, mul_prefix, mul_recurrence,
    add_result, add_prefix, add_recurrence, graph_domain, graph_functional,
    graph_range, ordinal_representative, member_ir, representative, raw_zero,
    raw_successor, transitive, member_transitive, member_linear, internal_extrema,
    subset, nonempty, least, greatest, graph_edge, raw_kuratowski, raw_pair,
    raw_singleton, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma mul_comparison_property_at x :
  (mul_comparison_property $0)[x..] = mul_comparison_property x.
Proof. rewrite mul_comparison_property_subst. reflexivity. Qed.

Theorem mul_prefix_zero_compare G top top' base base' e e' g h i i' v v' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 ordinal_representative top ->
  G ⊢238 ordinal_representative top' -> G ⊢238 raw_zero e -> G ⊢238 raw_zero e' ->
  G ⊢238 raw_zero i -> G ⊢238 raw_zero i' ->
  G ⊢238 mul_prefix top base e g -> G ⊢238 mul_prefix top' base' e' h ->
  G ⊢238 graph_edge g i v -> G ⊢238 graph_edge h i' v' ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso v v'.
Proof.
  intros HE HQ HEq HEtr Hempty HT HT' HZe HZe' HZi HZi' HP HP' Hv Hv'.
  apply (zero_order_iso _ v v'); [exact Hempty| |].
  - apply (mul_prefix_zero_value _ top base e g i v); assumption.
  - apply (mul_prefix_zero_value _ top' base' e' h i' v'); assumption.
Qed.

Theorem mul_result_zero_law G x y z e :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 raw_zero x -> G ⊢238 raw_zero e -> G ⊢238 mul_result x y z ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso z e.
Proof.
  intros HE HQ HEq HEtr Hempty HX HZ HZe Hmul.
  apply (zero_order_iso _ z e); [exact Hempty| |exact HZe].
  apply (mul_result_zero_value _ x y z); assumption.
Qed.

Theorem mul_result_zero_coherent G x x' y y' z z' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative x' -> G ⊢238 raw_zero x ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso x x' ->
  G ⊢238 mul_result x y z -> G ⊢238 mul_result x' y' z' ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso z z'.
Proof.
  intros HE HQ HEq HEtr Hempty HX HX' HZ HI Hmul Hmul'.
  apply (zero_order_iso _ z z'); [exact Hempty| |].
  - apply (mul_result_zero_value _ x y z); assumption.
  - apply (mul_result_zero_value _ x' y' z'); try assumption.
    apply (order_iso_zero_target _ x x'); assumption.
Qed.

Lemma mul_comparison_property_instance G x x' y y' z z' :
  G ⊢238 mul_comparison_property x -> G ⊢238 ordinal_representative x' ->
  G ⊢238 ordinal_representative y -> G ⊢238 ordinal_representative y' ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso x x' ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso y y' ->
  G ⊢238 mul_result x y z -> G ⊢238 mul_result x' y' z' ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso z z'.
Proof.
  destruct x as [ix|[]], x' as [ix'|[]], y as [iy|[]], y' as [iy'|[]],
    z as [iz|[]], z' as [iz'|[]]. intros HC HX' HY HY' Hxx Hyy HM HM'.
  unfold mul_comparison_property in HC.
  pose proof (AllE $iz' (AllE $iz (AllE $iy' (AllE $iy (AllE $ix' HC))))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HM']. eapply IE; [|exact HM].
  eapply IE; [|exact Hyy]. eapply IE; [|exact Hxx].
  eapply IE; [|exact HY']. eapply IE; [|exact HY]. eapply IE; [exact H|exact HX'].
Qed.

Theorem mul_comparison_induction_base G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 ordinal_base (mul_comparison_property $0).
Proof.
  intros HE HQ HEq HEtr Hempty. unfold ordinal_base.
  apply AllI_named. intro x. destruct x as [ix|[]].
  change (G ⊢238 ((ordinal_representative $ix ∧ raw_zero $ix) →
    (mul_comparison_property $0)[$ix..])).
  rewrite mul_comparison_property_at. apply II.
  assert (HX : (ordinal_representative $ix ∧ raw_zero $ix :: G)
    ⊢238 ordinal_representative $ix).
  { eapply CE1, Ctx. now left. }
  assert (HZ : (ordinal_representative $ix ∧ raw_zero $ix :: G) ⊢238 raw_zero $ix).
  { eapply CE2, Ctx. now left. }
  unfold mul_comparison_property. apply AllI_named. intro x'. destruct x' as [ix'|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro y'. destruct y' as [iy'|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro z'. destruct z' as [iz'|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply II, II, II, II, II, II, II.
  apply (mul_result_zero_coherent _ $ix $ix' $iy $iy' $iz $iz').
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit Hempty.
  - inherit HX.
  - apply Ctx. right. right. right. right. right. right. now left.
  - inherit HZ.
  - apply Ctx. right. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Lemma mul_comparison_property_bounded : bounded 1 (mul_comparison_property $0).
Proof.
  unfold mul_comparison_property, IsoGraph238.IsoGraph238.order_iso,
    IsoGraph238.IsoGraph238.order_bijection, IsoGraph238.IsoGraph238.graph_entries,
    IsoGraph238.IsoGraph238.entry_witness, IsoGraph238.IsoGraph238.graph_typed,
    IsoGraph238.IsoGraph238.graph_left_total, IsoGraph238.IsoGraph238.graph_right_total,
    IsoGraph238.IsoGraph238.graph_functional, IsoGraph238.IsoGraph238.graph_injective,
    IsoGraph238.IsoGraph238.graph_order, mul_result, mul_prefix, mul_recurrence,
    add_result, add_prefix, add_recurrence, graph_domain, graph_functional,
    graph_range, ordinal_representative, member_ir, representative, raw_zero,
    raw_successor, transitive, member_transitive, member_linear, internal_extrema,
    subset, nonempty, least, greatest, graph_edge, raw_kuratowski, raw_pair,
    raw_singleton, R, E.
  cbn. fixed_bounds.
Qed.

Theorem S0_mul_comparison_base :
  derivable finite_set_S0 (ordinal_base (mul_comparison_property $0)).
Proof.
  destruct S0_empty as [Gempty [HGempty Hempty]].
  set (G := equality_base ++ Gempty).
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
  assert (Hempty' : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + now apply HGempty.
  - apply mul_comparison_induction_base; assumption.
Qed.

Lemma mul_successor_match_instance G a b p :
  G ⊢238 IsoMatchSupply238.IsoMatchSupply238.iso_successor_match_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 ordinal_representative b ->
  G ⊢238 raw_successor p a -> G ⊢238 IsoGraph238.IsoGraph238.order_iso a b ->
  G ⊢238 ∃ (ordinal_representative $0 ∧
    (raw_successor $0 b`[↑] ∧ IsoGraph238.IsoGraph238.order_iso p`[↑] $0)).
Proof.
  destruct a as [ia|[]], b as [ib|[]], p as [ip|[]]. intros HT HA HB HS HI.
  unfold IsoMatchSupply238.IsoMatchSupply238.iso_successor_match_ax in HT.
  pose proof (AllE $ip (AllE $ib (AllE $ia HT))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HI]. eapply IE; [|exact HS].
  eapply IE; [|exact HB]. eapply IE; [exact H|exact HA].
Qed.

(** Matching constructs an actual predecessor of the other index. Each
    multiplication predecessor law then constructs its shorter trace. The
    induction hypothesis compares those values, and actual Add covariance
    compares the two supplied successor-row outputs. *)
Theorem mul_comparison_successor G p sx sx' y y' z z' :
  G ⊢238 IsoMatchSupply238.IsoMatchSupply238.iso_successor_match_ax ->
  G ⊢238 mul_predecessor_ax -> G ⊢238 AddCoherence238.AddCoherence238.add_comparison_ax ->
  G ⊢238 mul_comparison_property p -> G ⊢238 ordinal_representative p ->
  G ⊢238 ordinal_representative sx -> G ⊢238 ordinal_representative sx' ->
  G ⊢238 ordinal_representative y -> G ⊢238 ordinal_representative y' ->
  G ⊢238 raw_successor p sx -> G ⊢238 IsoGraph238.IsoGraph238.order_iso sx sx' ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso y y' ->
  G ⊢238 mul_result sx y z -> G ⊢238 mul_result sx' y' z' ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso z z'.
Proof.
  destruct p as [ip|[]], sx as [is|[]], sx' as [is'|[]], y as [iy|[]],
    y' as [iy'|[]], z as [iz|[]], z' as [iz'|[]].
  intros Hmatch Hpred Hadd HC HP HS HS' HY HY' Hps Hss Hyy HM HM'.
  eapply ExE_named.
  - apply (mul_successor_match_instance _ $is $is' $ip); assumption.
  - intro p'. destruct p' as [ip'|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply ExE_named.
    + apply (mul_predecessor_ax_instance _ $ip $is $iy $iz);
        [inherit Hpred|inherit HP|inherit Hps|inherit HM].
    + intro q. destruct q as [iq|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      eapply ExE_named.
      * apply (mul_predecessor_ax_instance _ $ip' $is' $iy' $iz').
        -- inherit Hpred.
        -- eapply CE1, Ctx. right. now left.
        -- eapply CE1, CE2, Ctx. right. now left.
        -- inherit HM'.
      * intro q'. destruct q' as [iq'|[]].
        cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
        apply (AddCoherence238.AddCoherence238.add_comparison_instance _
          $iq $iq' $iy $iy' $iz $iz').
        -- inherit Hadd.
        -- apply (mul_result_ordinal _ $ip $iy $iq). eapply CE1, Ctx. right. now left.
        -- apply (mul_result_ordinal _ $ip' $iy' $iq'). eapply CE1, Ctx. now left.
        -- inherit HY.
        -- inherit HY'.
        -- apply (mul_comparison_property_instance _ $ip $ip' $iy $iy' $iq $iq').
           ++ inherit HC.
           ++ eapply CE1, Ctx. right. right. now left.
           ++ inherit HY.
           ++ inherit HY'.
           ++ eapply CE2, CE2, Ctx. right. right. now left.
           ++ inherit Hyy.
           ++ eapply CE1, Ctx. right. now left.
           ++ eapply CE1, Ctx. now left.
        -- inherit Hyy.
        -- eapply CE2, Ctx. right. now left.
        -- eapply CE2, Ctx. now left.
Qed.

Theorem mul_comparison_induction_step G :
  G ⊢238 IsoMatchSupply238.IsoMatchSupply238.iso_successor_match_ax ->
  G ⊢238 mul_predecessor_ax -> G ⊢238 AddCoherence238.AddCoherence238.add_comparison_ax ->
  G ⊢238 ordinal_step (mul_comparison_property $0).
Proof.
  intros Hmatch Hpred Hadd. apply add_ordinal_step_intro.
  intros p sx. destruct p as [ip|[]], sx as [is|[]].
  rewrite !mul_comparison_property_at. unfold mul_comparison_property at 1.
  apply AllI_named. intro sx'. destruct sx' as [is'|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro y'. destruct y' as [iy'|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro z'. destruct z' as [iz'|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply II, II, II, II, II, II, II.
  apply (mul_comparison_successor _ $ip $is $is' $iy $iy' $iz $iz').
  - inherit Hmatch.
  - inherit Hpred.
  - inherit Hadd.
  - apply Ctx. right. right. right. right. right. right. right. now left.
  - eapply CE1, Ctx. right. right. right. right. right. right. right. right. now left.
  - eapply CE1, CE2, Ctx. right. right. right. right. right. right. right. right. now left.
  - apply Ctx. right. right. right. right. right. right. now left.
  - apply Ctx. right. right. right. right. right. now left.
  - apply Ctx. right. right. right. right. now left.
  - eapply CE2, CE2, Ctx. right. right. right. right. right. right. right. right. now left.
  - apply Ctx. right. right. right. now left.
  - apply Ctx. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Theorem S0_mul_comparison_step :
  derivable finite_set_S0 (ordinal_step (mul_comparison_property $0)).
Proof.
  destruct IsoMatchSupply238.IsoMatchSupply238.S0_order_iso_successor_match_closed
    as [Gmatch [HGmatch Hmatch]].
  destruct S0_mul_predecessor_closed as [Gpred [HGpred Hpred]].
  destruct AddCoherence238.AddCoherence238.S0_add_comparison_closed
    as [Gadd [HGadd Hadd]].
  set (G := Gmatch ++ Gpred ++ Gadd).
  exists G. split.
  - intros phi Hphi. unfold G in Hphi. apply in_app_or in Hphi as [Hphi|Hphi].
    + now apply HGmatch.
    + apply in_app_or in Hphi as [Hphi|Hphi]; [now apply HGpred|now apply HGadd].
  - apply mul_comparison_induction_step.
    + eapply Weak; [exact Hmatch|]. intros phi Hphi. unfold G. apply in_or_app. now left.
    + eapply Weak; [exact Hpred|]. intros phi Hphi. unfold G.
      apply in_or_app. right. apply in_or_app. now left.
    + eapply Weak; [exact Hadd|]. intros phi Hphi. unfold G.
      apply in_or_app. right. apply in_or_app. now right.
Qed.

Definition mul_comparison_ax : set_form :=
  ∀ (ordinal_representative $0 → mul_comparison_property $0).

Theorem S0_mul_comparison_closed : derivable finite_set_S0 mul_comparison_ax.
Proof.
  unfold mul_comparison_ax.
  pose proof (OrdinalTrace238.OrdinalTrace238.S0_ordinal_induction 0
    (mul_comparison_property $0) mul_comparison_property_bounded) as HI.
  pose proof (derivable_mp finite_set_S0 _ _ HI S0_mul_comparison_base) as HS.
  exact (derivable_mp finite_set_S0 _ _ HS S0_mul_comparison_step).
Qed.

Lemma mul_comparison_instance G x x' y y' z z' :
  G ⊢238 mul_comparison_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative x' -> G ⊢238 ordinal_representative y ->
  G ⊢238 ordinal_representative y' ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso x x' ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso y y' ->
  G ⊢238 mul_result x y z -> G ⊢238 mul_result x' y' z' ->
  G ⊢238 IsoGraph238.IsoGraph238.order_iso z z'.
Proof.
  destruct x as [ix|[]]. intros HC HX HX' HY HY' Hxx Hyy HM HM'.
  unfold mul_comparison_ax in HC. pose proof (AllE $ix HC) as H.
  change (G ⊢238 (ordinal_representative $ix →
    (mul_comparison_property $0)[$ix..])) in H.
  rewrite mul_comparison_property_at in H.
  apply (mul_comparison_property_instance _ $ix x' y y' z z'); try assumption.
  exact (IE H HX).
Qed.

Theorem S0_mul_coherent x x' y y' z z' :
  derivable finite_set_S0
    (ordinal_representative x → ordinal_representative x' →
      ordinal_representative y → ordinal_representative y' →
      IsoGraph238.IsoGraph238.order_iso x x' → IsoGraph238.IsoGraph238.order_iso y y' →
      mul_result x y z → mul_result x' y' z' → IsoGraph238.IsoGraph238.order_iso z z').
Proof.
  destruct S0_mul_comparison_closed as [G [HG HC]]. exists G. split; [exact HG|].
  apply II, II, II, II, II, II, II, II.
  apply (mul_comparison_instance _ x x' y y' z z').
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

Theorem S0_mul_determinacy x y z z' :
  derivable finite_set_S0
    (ordinal_representative x → ordinal_representative y →
      mul_result x y z → mul_result x y z' → IsoGraph238.IsoGraph238.order_iso z z').
Proof.
  destruct S0_mul_comparison_closed as [Gc [HGc HC]].
  destruct (IsoGraph238.IsoGraph238.S0_order_iso_reflexive x) as [Gx [HGx HX]].
  destruct (IsoGraph238.IsoGraph238.S0_order_iso_reflexive y) as [Gy [HGy HY]].
  set (G := Gc ++ Gx ++ Gy).
  assert (HC' : G ⊢238 mul_comparison_ax).
  { eapply Weak; [exact HC|]. intros psi Hpsi. unfold G. apply in_or_app. now left. }
  assert (HX' : G ⊢238 (ordinal_representative x → IsoGraph238.IsoGraph238.order_iso x x)).
  { eapply Weak; [exact HX|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. now left. }
  assert (HY' : G ⊢238 (ordinal_representative y → IsoGraph238.IsoGraph238.order_iso y y)).
  { eapply Weak; [exact HY|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + now apply HGc.
    + apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGx|now apply HGy].
  - apply II, II, II, II. apply (mul_comparison_instance _ x x y y z z').
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

Theorem S0_mul_zero_law x y z e :
  derivable finite_set_S0
    (ordinal_representative x → raw_zero x → raw_zero e → mul_result x y z →
      IsoGraph238.IsoGraph238.order_iso z e).
Proof.
  destruct S0_empty as [Gempty [HGempty Hempty]].
  set (G := equality_base ++ Gempty).
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
  assert (Hempty' : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + now apply HGempty.
  - apply II, II, II, II. apply (mul_result_zero_law _ x y z e).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Hempty'.
    + apply Ctx. right. right. right. now left.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Print Assumptions mul_prefix_zero_compare.
Print Assumptions S0_mul_determinacy.
Print Assumptions mul_comparison_successor.
Print Assumptions mul_comparison_induction_step.
Print Assumptions S0_mul_comparison_closed.
Print Assumptions S0_mul_coherent.
Print Assumptions mul_comparison_property_instance.
Print Assumptions mul_comparison_induction_base.
Print Assumptions mul_comparison_property_bounded.
Print Assumptions S0_mul_comparison_base.
Print Assumptions mul_result_zero_coherent.
Print Assumptions S0_mul_zero_law.
End MulCoherence238.
