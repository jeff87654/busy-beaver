(** Actual graph restrictions by full parameter Separation.
    The filter tests a source entry's decoded first coordinate. Shared
    Kuratowski decoding proves that every retained encoding has exactly
    the required inclusive domain. No graph image or Replacement is used. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  OrdinalTrace238 PairGraph238 GraphTransport238 TraceGraph238 IsoGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 OrdinalTrace238.OrdinalTrace238
  PairGraph238.PairGraph238 GraphTransport238.GraphTransport238
  TraceGraph238.TraceGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module TraceRestriction238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition inclusive_domain (top x : set_term) : set_form := R top x ∨ E x top.
Definition domain_entry (top p : set_term) : set_form :=
  ∃ ∃ (raw_kuratowski p`[↑]`[↑] $1 $0 ∧ inclusive_domain top`[↑]`[↑] $1).
Definition domain_entry_property (top : set_term) : set_form :=
  domain_entry top`[↑] $0.
Definition entry_filter (h g : set_term) (phi : set_form) : set_form :=
  ∀ (R h`[↑] $0 ↔ (R g`[↑] $0 ∧ phi)).
Definition graph_restriction (top g h : set_term) : set_form :=
  ∀ ∀ (graph_edge h`[↑]`[↑] $1 $0 ↔
    (graph_edge g`[↑]`[↑] $1 $0 ∧ inclusive_domain top`[↑]`[↑] $1)).

Lemma separation_entry_filter_equation g phi :
  (∃ ∀ (R $1 $0 ↔ (R $2 $0 ∧ phi[separation_slots])))[g..] =
  ∃ entry_filter $0 g`[↑] (phi[up ↑]).
Proof.
  destruct g as [ig|[]].
  change
    ((∃ ∀ (R $1 $0 ↔
      (R $(S (S ig)) $0 ∧ ((phi[separation_slots])[up (up ($ig..))])))) =
     (∃ ∀ (R $1 $0 ↔ (R $(S (S ig)) $0 ∧ phi[up ↑])))).
  rewrite separation_property_subst. reflexivity.
Qed.

Lemma separation_entry_filter_exists G g phi :
  G ⊢238 separation_ax phi ->
  G ⊢238 ∃ entry_filter $0 g`[↑] (phi[up ↑]).
Proof.
  intro HS. rewrite <- separation_entry_filter_equation. exact (AllE g HS).
Qed.

Lemma entry_filter_witness_specialize h g phi :
  (entry_filter $0 g`[↑] (phi[up ↑]))[h..] = entry_filter h g phi.
Proof.
  destruct h as [ih|[]], g as [ig|[]].
  change
    ((∀ (R $(S ih) $0 ↔
      (R $(S ig) $0 ∧ ((phi[up ↑])[up ($ih..)])))) =
     (∀ (R $(S ih) $0 ↔ (R $(S ig) $0 ∧ phi)))).
  rewrite bad_trace_property_specialize. reflexivity.
Qed.

Lemma entry_filter_member G h g phi p :
  G ⊢238 entry_filter h g phi -> G ⊢238 R h p ->
  G ⊢238 (R g p ∧ phi[p..]).
Proof.
  destruct h as [ih|[]], g as [ig|[]], p as [ip|[]]. intros HF Hp.
  unfold entry_filter in HF. pose proof (AllE $ip HF) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (CE1 H) Hp).
Qed.

Lemma entry_filter_intro G h g phi p :
  G ⊢238 entry_filter h g phi -> G ⊢238 (R g p ∧ phi[p..]) -> G ⊢238 R h p.
Proof.
  destruct h as [ih|[]], g as [ig|[]], p as [ip|[]]. intros HF Hp.
  unfold entry_filter in HF. pose proof (AllE $ip HF) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (CE2 H) Hp).
Qed.

Lemma domain_entry_property_at top p :
  (domain_entry_property top)[p..] = domain_entry top p.
Proof.
  destruct top as [it|[]], p as [ip|[]].
  unfold domain_entry_property, domain_entry, inclusive_domain, raw_kuratowski,
    raw_singleton, raw_pair, R, E.
  cbn [terms2 Vector.map subst_form subst_term up scons funcomp]. reflexivity.
Qed.

Lemma domain_entry_from_coordinates G top p x y :
  G ⊢238 raw_kuratowski p x y -> G ⊢238 inclusive_domain top x ->
  G ⊢238 domain_entry top p.
Proof.
  destruct top as [it|[]], p as [ip|[]], x as [ix|[]], y as [iy|[]]. intros HP HX.
  unfold domain_entry. apply (ExI $ix).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iy).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI; assumption.
Qed.

Lemma inclusive_domain_coordinate_transport G top x y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 E x y -> G ⊢238 inclusive_domain top x -> G ⊢238 inclusive_domain top y.
Proof.
  intros HE HQ HEq HEtr Hxy HX. unfold inclusive_domain in *. eapply DE; [exact HX| |].
  - apply DI1. apply (equality_member_transport _ top x y);
      [inherit HE|inherit HQ|inherit Hxy|apply Ctx; now left].
  - apply DI2. apply (pair_equality_transitivity _ y x top).
    + inherit HEtr.
    + apply equality_symmetry_instance; [inherit HEq|inherit Hxy].
    + apply Ctx. now left.
Qed.

Lemma domain_entry_decoded_inside G top p x y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 domain_entry top p -> G ⊢238 raw_kuratowski p x y ->
  G ⊢238 inclusive_domain top x.
Proof.
  destruct top as [it|[]], p as [ip|[]], x as [ix|[]], y as [iy|[]].
  intros HE HQ HEq HEtr HD HP. unfold domain_entry in HD.
  eapply ExE_named; [exact HD|]. intro a. destruct a as [ia|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro b. destruct b as [ib|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (inclusive_domain_coordinate_transport _ $it $ia $ix).
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - apply (raw_kuratowski_first_unique _ $ip $ia $ib $ix $iy).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + eapply CE1, Ctx. now left.
    + inherit HP.
  - eapply CE2, Ctx. now left.
Qed.

Theorem entry_filter_graph_restriction G top g h :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 entry_filter h g (domain_entry_property top) ->
  G ⊢238 graph_restriction top g h.
Proof.
  destruct top as [it|[]], g as [ig|[]], h as [ih|[]]. intros HE HQ HEq HEtr HF.
  unfold graph_restriction. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. unfold graph_edge. eapply ExE_named; [apply Ctx; now left|].
    intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (Hfiltered : (R $ih $ip ∧ raw_kuratowski $ip $ix $iy ::
        graph_edge $ih $ix $iy :: G)
        ⊢238 (R $ig $ip ∧ domain_entry $it $ip)).
    { rewrite <- domain_entry_property_at.
      apply (entry_filter_member _ $ih $ig (domain_entry_property $it) $ip);
        [inherit HF|eapply CE1, Ctx; now left]. }
    apply CI.
    + apply (graph_edge_from_entry _ $ig $ix $iy $ip).
      * exact (CE1 Hfiltered).
      * eapply CE2, Ctx. now left.
    + apply (domain_entry_decoded_inside _ $it $ip $ix $iy).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HEtr.
      * exact (CE2 Hfiltered).
      * eapply CE2, Ctx. now left.
  - apply II.
    assert (Hold : (graph_edge $ig $ix $iy ∧ inclusive_domain $it $ix :: G)
      ⊢238 graph_edge $ig $ix $iy).
    { eapply CE1, Ctx. now left. }
    assert (Hinside : (graph_edge $ig $ix $iy ∧ inclusive_domain $it $ix :: G)
      ⊢238 inclusive_domain $it $ix).
    { eapply CE2, Ctx. now left. }
    unfold graph_edge in Hold. eapply ExE_named; [exact Hold|].
    intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (graph_edge_from_entry _ $ih $ix $iy $ip).
    + apply (entry_filter_intro _ $ih $ig (domain_entry_property $it) $ip);
        [inherit HF|].
      rewrite domain_entry_property_at. apply CI; [eapply CE1, Ctx; now left|].
      apply (domain_entry_from_coordinates _ $it $ip $ix $iy);
        [eapply CE2, Ctx; now left|inherit Hinside].
    + eapply CE2, Ctx. now left.
Qed.

Theorem graph_restriction_exists G top g :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 separation_ax (domain_entry_property top) ->
  G ⊢238 ∃ graph_restriction top`[↑] g`[↑] $0.
Proof.
  destruct top as [it|[]], g as [ig|[]]. intros HE HQ HEq HEtr HS.
  eapply ExE_named.
  - apply (separation_entry_filter_exists _ $ig (domain_entry_property $it)). exact HS.
  - intro h. destruct h as [ih|[]]. rewrite entry_filter_witness_specialize.
    apply (ExI $ih).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (entry_filter_graph_restriction _ $it $ig $ih).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + apply Ctx. now left.
Qed.

Lemma domain_entry_property_bounded i :
  bounded (S (S i)) (domain_entry_property $i).
Proof.
  unfold domain_entry_property, domain_entry, inclusive_domain, raw_kuratowski,
    raw_singleton, raw_pair, R, E.
  cbn. fixed_bounds.
Qed.

Theorem S0_graph_restriction_exists top g :
  derivable finite_set_S0 (∃ graph_restriction top`[↑] g`[↑] $0).
Proof.
  destruct top as [it|[]].
  destruct (S0_separation_instance (S it) (domain_entry_property $it)
    (domain_entry_property_bounded it)) as [Gsep [HGsep HS]].
  set (G := equality_base ++ Gsep).
  assert (HE : G ⊢238 (∀ E $0 $0)).
  { apply Ctx. unfold G, equality_base. cbn. now left. }
  assert (HQ : G ⊢238 equality_membership_ax).
  { apply Ctx. unfold G, equality_base, equality_membership_ax. cbn.
    right. right. right. now left. }
  assert (HEq : G ⊢238 equality_symmetry_ax).
  { apply Ctx. unfold G, equality_base, equality_symmetry_ax. cbn. right. now left. }
  assert (HEtr : G ⊢238 pair_equality_transitivity_ax).
  { apply Ctx. unfold G, equality_base, pair_equality_transitivity_ax. cbn.
    right. right. now left. }
  assert (HS' : G ⊢238 separation_ax (domain_entry_property $it)).
  { eapply Weak; [exact HS|]. intros psi Hpsi. unfold G. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + now apply HGsep.
  - apply graph_restriction_exists; assumption.
Qed.

Definition graph_restriction_ax : set_form :=
  ∀ ∀ ∃ graph_restriction $2 $1 $0.

Theorem S0_graph_restriction_closed : derivable finite_set_S0 graph_restriction_ax.
Proof.
  unfold graph_restriction_ax. apply S0_generalize, S0_generalize.
  exact (S0_graph_restriction_exists $1 $0).
Qed.

Lemma graph_restriction_ax_instance G top g :
  G ⊢238 graph_restriction_ax -> G ⊢238 ∃ graph_restriction top`[↑] g`[↑] $0.
Proof.
  destruct top as [it|[]], g as [ig|[]]. intro H. unfold graph_restriction_ax in H.
  pose proof (AllE $ig (AllE $it H)) as H'.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H'. exact H'.
Qed.

Lemma graph_restriction_cases G top g h x y :
  G ⊢238 graph_restriction top g h -> G ⊢238 graph_edge h x y ->
  G ⊢238 (graph_edge g x y ∧ inclusive_domain top x).
Proof.
  destruct top as [it|[]], g as [ig|[]], h as [ih|[]], x as [ix|[]], y as [iy|[]].
  intros HR HE. unfold graph_restriction in HR.
  pose proof (AllE $iy (AllE $ix HR)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (CE1 H) HE).
Qed.

Lemma graph_restriction_intro G top g h x y :
  G ⊢238 graph_restriction top g h -> G ⊢238 graph_edge g x y ->
  G ⊢238 inclusive_domain top x -> G ⊢238 graph_edge h x y.
Proof.
  destruct top as [it|[]], g as [ig|[]], h as [ih|[]], x as [ix|[]], y as [iy|[]].
  intros HR HE HI. unfold graph_restriction in HR.
  pose proof (AllE $iy (AllE $ix HR)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact (CE2 H)|]. apply CI; assumption.
Qed.

Definition strict_entry (top p : set_term) : set_form :=
  ∃ ∃ (raw_kuratowski p`[↑]`[↑] $1 $0 ∧ R top`[↑]`[↑] $1).
Definition strict_entry_property (top : set_term) : set_form :=
  strict_entry top`[↑] $0.
Definition strict_graph_cut (top g h : set_term) : set_form :=
  entry_filter h g (strict_entry_property top).
Definition strict_graph_restriction (top g h : set_term) : set_form :=
  ∀ ∀ (graph_edge h`[↑]`[↑] $1 $0 ↔
    (graph_edge g`[↑]`[↑] $1 $0 ∧ R top`[↑]`[↑] $1)).

Lemma strict_graph_cut_subst top g h sigma :
  (strict_graph_cut top g h)[sigma] =
  strict_graph_cut top`[sigma] g`[sigma] h`[sigma].
Proof.
  unfold strict_graph_cut, entry_filter, strict_entry_property, strict_entry,
    raw_kuratowski, raw_singleton, raw_pair, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma strict_graph_cut_witness_specialize top g h :
  (strict_graph_cut top`[↑] g`[↑] $0)[h..] = strict_graph_cut top g h.
Proof.
  rewrite strict_graph_cut_subst. cbn [subst_term].
  rewrite !subst_term_shift. reflexivity.
Qed.

Lemma strict_entry_property_at top p :
  (strict_entry_property top)[p..] = strict_entry top p.
Proof.
  destruct top as [it|[]], p as [ip|[]].
  unfold strict_entry_property, strict_entry, raw_kuratowski,
    raw_singleton, raw_pair, R, E.
  cbn [terms2 Vector.map subst_form subst_term up scons funcomp]. reflexivity.
Qed.

Lemma strict_entry_from_coordinates G top p x y :
  G ⊢238 raw_kuratowski p x y -> G ⊢238 R top x -> G ⊢238 strict_entry top p.
Proof.
  destruct top as [it|[]], p as [ip|[]], x as [ix|[]], y as [iy|[]]. intros HP HX.
  unfold strict_entry. apply (ExI $ix).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iy).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI; assumption.
Qed.

Lemma strict_entry_decoded_inside G top p x y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 strict_entry top p -> G ⊢238 raw_kuratowski p x y -> G ⊢238 R top x.
Proof.
  destruct top as [it|[]], p as [ip|[]], x as [ix|[]], y as [iy|[]].
  intros HE HQ HEq HEtr HD HP. unfold strict_entry in HD.
  eapply ExE_named; [exact HD|]. intro a. destruct a as [ia|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro b. destruct b as [ib|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (equality_member_transport _ $it $ia $ix).
  - inherit HE.
  - inherit HQ.
  - apply (raw_kuratowski_first_unique _ $ip $ia $ib $ix $iy).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + eapply CE1, Ctx. now left.
    + inherit HP.
  - eapply CE2, Ctx. now left.
Qed.

Theorem strict_cut_edges G top g h :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 strict_graph_cut top g h -> G ⊢238 strict_graph_restriction top g h.
Proof.
  destruct top as [it|[]], g as [ig|[]], h as [ih|[]]. intros HE HQ HEq HEtr HF.
  unfold strict_graph_restriction. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. unfold graph_edge. eapply ExE_named; [apply Ctx; now left|].
    intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (Hfiltered : (R $ih $ip ∧ raw_kuratowski $ip $ix $iy ::
        graph_edge $ih $ix $iy :: G) ⊢238 (R $ig $ip ∧ strict_entry $it $ip)).
    { rewrite <- strict_entry_property_at.
      apply (entry_filter_member _ $ih $ig (strict_entry_property $it) $ip);
        [inherit HF|eapply CE1, Ctx; now left]. }
    apply CI.
    + apply (graph_edge_from_entry _ $ig $ix $iy $ip).
      * exact (CE1 Hfiltered).
      * eapply CE2, Ctx. now left.
    + apply (strict_entry_decoded_inside _ $it $ip $ix $iy).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HEtr.
      * exact (CE2 Hfiltered).
      * eapply CE2, Ctx. now left.
  - apply II.
    assert (Hold : (graph_edge $ig $ix $iy ∧ R $it $ix :: G) ⊢238 graph_edge $ig $ix $iy).
    { eapply CE1, Ctx. now left. }
    assert (Hinside : (graph_edge $ig $ix $iy ∧ R $it $ix :: G) ⊢238 R $it $ix).
    { eapply CE2, Ctx. now left. }
    unfold graph_edge in Hold. eapply ExE_named; [exact Hold|].
    intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (graph_edge_from_entry _ $ih $ix $iy $ip).
    + apply (entry_filter_intro _ $ih $ig (strict_entry_property $it) $ip); [inherit HF|].
      rewrite strict_entry_property_at. apply CI; [eapply CE1, Ctx; now left|].
      apply (strict_entry_from_coordinates _ $it $ip $ix $iy);
        [eapply CE2, Ctx; now left|inherit Hinside].
    + eapply CE2, Ctx. now left.
Qed.

Lemma strict_cut_cases G top g h x y :
  G ⊢238 strict_graph_restriction top g h -> G ⊢238 graph_edge h x y ->
  G ⊢238 (graph_edge g x y ∧ R top x).
Proof.
  destruct top as [it|[]], g as [ig|[]], h as [ih|[]], x as [ix|[]], y as [iy|[]].
  intros HR HE. unfold strict_graph_restriction in HR.
  pose proof (AllE $iy (AllE $ix HR)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (CE1 H) HE).
Qed.

Lemma strict_cut_intro G top g h x y :
  G ⊢238 strict_graph_restriction top g h -> G ⊢238 graph_edge g x y ->
  G ⊢238 R top x -> G ⊢238 graph_edge h x y.
Proof.
  destruct top as [it|[]], g as [ig|[]], h as [ih|[]], x as [ix|[]], y as [iy|[]].
  intros HR HE HI. unfold strict_graph_restriction in HR.
  pose proof (AllE $iy (AllE $ix HR)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact (CE2 H)|]. apply CI; assumption.
Qed.

(** The member filter contains an actual decoding witness. Thus the new
    graph has no undecoded members, even if the source graph had them. *)
Theorem strict_cut_entries G top g h a b :
  G ⊢238 strict_graph_cut top g h ->
  G ⊢238 IsoGraph238.IsoGraph238.graph_typed g a b ->
  G ⊢238 IsoGraph238.IsoGraph238.graph_entries h top b.
Proof.
  destruct top as [it|[]], g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]].
  intros HC HT. unfold IsoGraph238.IsoGraph238.graph_entries.
  apply AllI_named. intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  assert (HD : (R $ih $ip :: G) ⊢238 strict_entry $it $ip).
  { rewrite <- strict_entry_property_at. eapply CE2.
    apply (entry_filter_member _ $ih $ig (strict_entry_property $it) $ip);
      [inherit HC|apply Ctx; now left]. }
  assert (HM : (R $ih $ip :: G) ⊢238 R $ig $ip).
  { eapply CE1. apply (entry_filter_member _ $ih $ig (strict_entry_property $it) $ip);
      [inherit HC|apply Ctx; now left]. }
  unfold strict_entry in HD. eapply ExE_named; [exact HD|].
  intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (IsoGraph238.IsoGraph238.entry_witness_from_components _ $it $ib $ip $ix $iy).
  - eapply CE2, Ctx. now left.
  - unfold IsoGraph238.IsoGraph238.graph_typed in HT.
    pose proof (AllE $iy (AllE $ix HT)) as H.
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
    eapply CE2, IE; [inherit H|]. apply (graph_edge_from_entry _ $ig $ix $iy $ip).
    + inherit HM.
    + eapply CE1, Ctx. now left.
  - eapply CE1, Ctx. now left.
Qed.

Theorem strict_graph_cut_exists G top g :
  G ⊢238 separation_ax (strict_entry_property top) ->
  G ⊢238 ∃ strict_graph_cut top`[↑] g`[↑] $0.
Proof.
  destruct top as [it|[]], g as [ig|[]]. intro HS.
  eapply ExE_named.
  - apply (separation_entry_filter_exists _ $ig (strict_entry_property $it)). exact HS.
  - intro h. destruct h as [ih|[]]. rewrite entry_filter_witness_specialize.
    apply (ExI $ih).
    change ((entry_filter $ih $ig (strict_entry_property $it) :: G)
      ⊢238 strict_graph_cut $it $ig $ih).
    apply Ctx. now left.
Qed.

Lemma strict_entry_property_bounded i :
  bounded (S (S i)) (strict_entry_property $i).
Proof.
  unfold strict_entry_property, strict_entry, raw_kuratowski, raw_singleton, raw_pair, R, E.
  cbn. fixed_bounds.
Qed.

Theorem S0_strict_graph_cut_exists top g :
  derivable finite_set_S0 (∃ strict_graph_cut top`[↑] g`[↑] $0).
Proof.
  destruct top as [it|[]].
  destruct (S0_separation_instance (S it) (strict_entry_property $it)
    (strict_entry_property_bounded it)) as [Gsep [HGsep HS]].
  exists Gsep. split; [exact HGsep|]. apply strict_graph_cut_exists. exact HS.
Qed.

Theorem restriction_domain G t tp g h :
  G ⊢238 raw_successor t tp -> G ⊢238 graph_domain tp g ->
  G ⊢238 graph_restriction t g h -> G ⊢238 graph_domain t h.
Proof.
  destruct t as [it|[]], tp as [ip|[]], g as [ig|[]], h as [ih|[]]. intros HS HD HR.
  unfold graph_domain. apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. eapply ExE_named; [apply Ctx; now left|].
    intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply CE2. apply (graph_restriction_cases _ $it $ig $ih $ix $iy);
      [inherit HR|apply Ctx; now left].
  - apply II.
    assert (HI : (inclusive_domain $it $ix :: G) ⊢238 inclusive_domain $it $ix).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (graph_domain_value _ $ip $ig $ix); [inherit HD|].
      apply DI1. apply (raw_successor_member_intro _ $it $ip $ix);
        [inherit HS|exact HI].
    + intro y. destruct y as [iy|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (ExI $iy).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (graph_restriction_intro _ $it $ig $ih $ix $iy);
        [inherit HR|apply Ctx; now left|inherit HI].
Qed.

Theorem restriction_functional G top g h :
  G ⊢238 graph_functional g -> G ⊢238 graph_restriction top g h ->
  G ⊢238 graph_functional h.
Proof.
  destruct top as [it|[]], g as [ig|[]], h as [ih|[]]. intros HF HR.
  unfold graph_functional. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (graph_functional_at _ $ig $ix $iy $iz); [inherit HF| |].
  - eapply CE1. apply (graph_restriction_cases _ $it $ig $ih $ix $iy);
      [inherit HR|eapply CE1, Ctx; now left].
  - eapply CE1. apply (graph_restriction_cases _ $it $ig $ih $ix $iz);
      [inherit HR|eapply CE2, Ctx; now left].
Qed.

Theorem restriction_range G top g h :
  G ⊢238 graph_range g -> G ⊢238 graph_restriction top g h -> G ⊢238 graph_range h.
Proof.
  destruct top as [it|[]], g as [ig|[]], h as [ih|[]]. intros HG HR.
  unfold graph_range. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (graph_range_at _ $ig $ix $iy); [inherit HG|].
  eapply CE1. apply (graph_restriction_cases _ $it $ig $ih $ix $iy);
    [inherit HR|apply Ctx; now left].
Qed.

Lemma successor_inclusive_zero_predecessor G t tp e :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 raw_successor t tp ->
  G ⊢238 raw_zero e -> G ⊢238 inclusive_domain tp e -> G ⊢238 inclusive_domain t e.
Proof.
  intros HE HQ HEq HS HZ HI. unfold inclusive_domain in *. eapply DE; [exact HI| |].
  - apply (raw_successor_member_cases _ t tp e); [inherit HS|apply Ctx; now left].
  - apply Exp. eapply IE; [inherit (zero_excludes_member G e t HZ)|].
    apply (equality_container_transport _ tp e t).
    + inherit HE.
    + inherit HQ.
    + apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
    + apply (raw_successor_point_member _ t tp); [inherit HE|inherit HS].
Qed.

Lemma inclusive_predecessor_member G top i p :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 ordinal_representative top -> G ⊢238 inclusive_domain top i ->
  G ⊢238 raw_successor p i -> G ⊢238 R top p.
Proof.
  intros HE HQ HT HI HS. unfold inclusive_domain in HI. eapply DE; [exact HI| |].
  - apply (transitive_member _ top i p).
    + inherit (CE1 (CE1 HT)).
    + apply Ctx. now left.
    + apply (raw_successor_point_member _ p i); [inherit HE|inherit HS].
  - apply (equality_container_transport _ i top p).
    + inherit HE.
    + inherit HQ.
    + apply Ctx. now left.
    + apply (raw_successor_point_member _ p i); [inherit HE|inherit HS].
Qed.

Print Assumptions restriction_domain.
Print Assumptions restriction_functional.
Print Assumptions restriction_range.
Print Assumptions successor_inclusive_zero_predecessor.
Print Assumptions inclusive_predecessor_member.
Print Assumptions strict_cut_edges.
Print Assumptions strict_cut_entries.
Print Assumptions strict_graph_cut_exists.
Print Assumptions S0_strict_graph_cut_exists.
Print Assumptions graph_restriction_exists.
Print Assumptions S0_graph_restriction_exists.
Print Assumptions S0_graph_restriction_closed.
Print Assumptions graph_restriction_cases.
Print Assumptions graph_restriction_intro.
End TraceRestriction238.
