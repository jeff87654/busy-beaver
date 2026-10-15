(** Original construction of actual inverse graphs by ordinal induction.
    Each reverse entry is separately built and adjoined; no set image,
    Replacement, or chosen inverse function is assumed. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import
  Compact238 PAinCompact238 OrdinalSuccessor238 OrdinalTrace238
  PairGraph238 GraphTransport238 IsoGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 OrdinalTrace238.OrdinalTrace238
  PairGraph238.PairGraph238 GraphTransport238.GraphTransport238 IsoGraph238.IsoGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module InverseGraph238.

Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

(** In each entry the original index x is $1 and image y is $0; the actual
    Kuratowski object encodes the reversed ordered pair (y,x). *)
Definition inverse_entry (g n p : set_term) : set_form :=
  ∃ ∃ (R n`[↑]`[↑] $1 ∧
    (graph_edge g`[↑]`[↑] $1 $0 ∧ raw_kuratowski p`[↑]`[↑] $0 $1)).
Definition inverse_entries (g n h : set_term) : set_form :=
  ∀ (R h`[↑] $0 → inverse_entry g`[↑] n`[↑] $0).
Definition inverse_correct (g n h : set_term) : set_form :=
  ∀ ∀ (graph_edge h`[↑]`[↑] $1 $0 →
    (R n`[↑]`[↑] $0 ∧ graph_edge g`[↑]`[↑] $0 $1)).
Definition inverse_coverage (g n h : set_term) : set_form :=
  ∀ (R n`[↑] $0 →
    ∃ (graph_edge h`[↑]`[↑] $0 $1 ∧ graph_edge g`[↑]`[↑] $1 $0)).
Definition inverse_prefix (g n h : set_term) : set_form :=
  inverse_entries g n h ∧ (inverse_correct g n h ∧ inverse_coverage g n h).
Definition inverse_exists (g n : set_term) : set_form :=
  ∃ inverse_prefix g`[↑] n`[↑] $0.
Definition inverse_property (g a : set_term) : set_form :=
  subset $0 a`[↑] → inverse_exists g`[↑] $0.

Lemma inverse_entry_intro G g n p x y :
  G ⊢238 R n x -> G ⊢238 graph_edge g x y ->
  G ⊢238 raw_kuratowski p y x -> G ⊢238 inverse_entry g n p.
Proof.
  destruct g as [ig|[]], n as [in_|[]], p as [ip|[]], x as [ix|[]], y as [iy|[]].
  intros Hx HE HP. unfold inverse_entry. apply (ExI $ix).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iy).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply CI; [exact Hx|]. apply CI; assumption.
Qed.

Lemma inverse_entries_instance G g n h p :
  G ⊢238 inverse_entries g n h -> G ⊢238 R h p -> G ⊢238 inverse_entry g n p.
Proof.
  destruct g as [ig|[]], n as [in_|[]], h as [ih|[]], p as [ip|[]].
  intros HI HP. unfold inverse_entries in HI. pose proof (AllE $ip HI) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HP).
Qed.

Lemma inverse_correct_instance G g n h y x :
  G ⊢238 inverse_correct g n h -> G ⊢238 graph_edge h y x ->
  G ⊢238 (R n x ∧ graph_edge g x y).
Proof.
  destruct g as [ig|[]], n as [in_|[]], h as [ih|[]], y as [iy|[]], x as [ix|[]].
  intros HC HE. unfold inverse_correct in HC. pose proof (AllE $ix (AllE $iy HC)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HE).
Qed.

Lemma inverse_coverage_instance G g n h x :
  G ⊢238 inverse_coverage g n h -> G ⊢238 R n x ->
  G ⊢238 ∃ (graph_edge h`[↑] $0 x`[↑] ∧ graph_edge g`[↑] x`[↑] $0).
Proof.
  destruct g as [ig|[]], n as [in_|[]], h as [ih|[]], x as [ix|[]].
  intros HC Hx. unfold inverse_coverage in HC. pose proof (AllE $ix HC) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H Hx).
Qed.

Lemma graph_left_total_instance G g a x :
  G ⊢238 graph_left_total g a -> G ⊢238 R a x ->
  G ⊢238 ∃ graph_edge g`[↑] x`[↑] $0.
Proof.
  destruct g as [ig|[]], a as [ia|[]], x as [ix|[]]. intros HT Hx.
  unfold graph_left_total in HT. pose proof (AllE $ix HT) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H Hx).
Qed.

Lemma empty_inverse_prefix G g n :
  G ⊢238 raw_zero n -> G ⊢238 inverse_prefix g n n.
Proof.
  destruct g as [ig|[]], n as [in_|[]]. intro HZ. unfold inverse_prefix. apply CI.
  - unfold inverse_entries. apply AllI_named. intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, Exp.
    eapply IE; [inherit (zero_excludes_member G $in_ $ip HZ)|apply Ctx; now left].
  - apply CI.
    + unfold inverse_correct. apply AllI_named. intro y. destruct y as [iy|[]].
      apply AllI_named. intro x. destruct x as [ix|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, Exp.
      apply (graph_edge_empty_false _ $in_ $iy $ix); [inherit HZ|apply Ctx; now left].
    + unfold inverse_coverage. apply AllI_named. intro x. destruct x as [ix|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, Exp.
      eapply IE; [inherit (zero_excludes_member G $in_ $ix HZ)|apply Ctx; now left].
Qed.

Lemma inverse_range_fresh G g n h y :
  G ⊢238 member_ir n -> G ⊢238 inverse_prefix g n h ->
  G ⊢238 (¬ graph_edge h y n).
Proof.
  intros HI HP. apply II. eapply IE; [inherit (member_ir_not_self G n HI)|].
  eapply CE1. apply (inverse_correct_instance _ g n h y n).
  - inherit (CE1 (CE2 HP)).
  - apply Ctx. now left.
Qed.

Lemma successor_inverse_entries G g n m h p k v :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 inverse_entries g n h ->
  G ⊢238 raw_successor n m -> G ⊢238 raw_adjunction h p k ->
  G ⊢238 raw_kuratowski p v n -> G ⊢238 graph_edge g n v ->
  G ⊢238 inverse_entries g m k.
Proof.
  destruct g as [ig|[]], n as [in_|[]], m as [im|[]], h as [ih|[]],
    p as [ip|[]], k as [ik|[]], v as [iv|[]]. intros HE HQ HEq HI HS HA HP HV.
  unfold inverse_entries. apply AllI_named. intro q. destruct q as [iq|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_adjunction_member _ $ih $ip $ik $iq); [inherit HA|apply Ctx; now left].
  - eapply ExE_named.
    + apply (inverse_entries_instance _ $ig $in_ $ih $iq); [inherit HI|apply Ctx; now left].
    + intro x. destruct x as [ix|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      eapply ExE_named; [apply Ctx; now left|]. intro y. destruct y as [iy|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (inverse_entry_intro _ $ig $im $iq $ix $iy).
      * apply (raw_successor_old_member _ $in_ $im $ix); [inherit HS|].
        eapply CE1, Ctx. now left.
      * eapply CE1, CE2, Ctx. now left.
      * eapply CE2, CE2, Ctx. now left.
  - apply (inverse_entry_intro _ $ig $im $iq $in_ $iv).
    + apply (raw_successor_point_member _ $in_ $im); [inherit HE|inherit HS].
    + inherit HV.
    + apply (raw_kuratowski_container_transport _ $ip $iq $iv $in_).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
      * inherit HP.
Qed.

Lemma successor_inverse_correct G g n m h p k v :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 inverse_correct g n h -> G ⊢238 raw_successor n m ->
  G ⊢238 raw_adjunction h p k -> G ⊢238 raw_kuratowski p v n ->
  G ⊢238 graph_edge g n v -> G ⊢238 inverse_correct g m k.
Proof.
  destruct g as [ig|[]], n as [in_|[]], m as [im|[]], h as [ih|[]],
    p as [ip|[]], k as [ik|[]], v as [iv|[]]. intros HE HQ HEq HEtr HC HS HA HP HV.
  unfold inverse_correct. apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_adjunction_graph_edge_cases _ $ih $ip $ik $iv $in_ $iy $ix).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit HA.
    + inherit HP.
    + apply Ctx. now left.
  - apply CI.
    + apply (raw_successor_old_member _ $in_ $im $ix); [inherit HS|].
      eapply CE1. apply (inverse_correct_instance _ $ig $in_ $ih $iy $ix);
        [inherit HC|apply Ctx; now left].
    + eapply CE2. apply (inverse_correct_instance _ $ig $in_ $ih $iy $ix);
        [inherit HC|apply Ctx; now left].
  - apply CI.
    + apply (equality_member_transport _ $im $in_ $ix).
      * inherit HE.
      * inherit HQ.
      * apply equality_symmetry_instance; [inherit HEq|]. eapply CE2, Ctx. now left.
      * apply (raw_successor_point_member _ $in_ $im); [inherit HE|inherit HS].
    + apply (graph_edge_coordinate_transport _ $ig $in_ $iv $ix $iy).
      * inherit HEq.
      * inherit HEtr.
      * apply equality_symmetry_instance; [inherit HEq|]. eapply CE2, Ctx. now left.
      * apply equality_symmetry_instance; [inherit HEq|]. eapply CE1, Ctx. now left.
      * inherit HV.
Qed.

Lemma successor_inverse_coverage G g n m h p k v :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 inverse_coverage g n h ->
  G ⊢238 raw_successor n m -> G ⊢238 raw_adjunction h p k ->
  G ⊢238 raw_kuratowski p v n -> G ⊢238 graph_edge g n v ->
  G ⊢238 inverse_coverage g m k.
Proof.
  destruct g as [ig|[]], n as [in_|[]], m as [im|[]], h as [ih|[]],
    p as [ip|[]], k as [ik|[]], v as [iv|[]]. intros HE HEq HEtr HC HS HA HP HV.
  assert (Hnew : G ⊢238 graph_edge $ik $iv $in_).
  { apply (graph_edge_from_entry _ $ik $iv $in_ $ip); [|exact HP].
    apply (raw_adjunction_intro _ $ih $ip $ik $ip); [exact HA|].
    apply DI2. exact (AllE $ip HE). }
  unfold inverse_coverage. apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_successor_member_cases _ $in_ $im $ix); [inherit HS|apply Ctx; now left].
  - eapply ExE_named.
    + apply (inverse_coverage_instance _ $ig $in_ $ih $ix); [inherit HC|apply Ctx; now left].
    + intro y. destruct y as [iy|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iy).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * apply (graph_inclusion_instance _ $ih $ik $iy $ix).
        -- apply (raw_adjunction_graph_inclusion _ $ih $ip $ik). inherit HA.
        -- eapply CE1, Ctx. now left.
      * eapply CE2, Ctx. now left.
  - apply (ExI $iv).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
    + apply (graph_edge_coordinate_transport _ $ik $iv $in_ $iv $ix).
      * inherit HEq.
      * inherit HEtr.
      * inherit (AllE $iv HE).
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
      * inherit Hnew.
    + apply (graph_edge_coordinate_transport _ $ig $in_ $iv $ix $iv).
      * inherit HEq.
      * inherit HEtr.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
      * inherit (AllE $iv HE).
      * inherit HV.
Qed.

Lemma successor_inverse_prefix G g n m h p k v :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 inverse_prefix g n h -> G ⊢238 raw_successor n m ->
  G ⊢238 raw_adjunction h p k -> G ⊢238 raw_kuratowski p v n ->
  G ⊢238 graph_edge g n v -> G ⊢238 inverse_prefix g m k.
Proof.
  intros HE HQ HEq HEtr HI HS HA HP HV. unfold inverse_prefix. apply CI.
  - apply (successor_inverse_entries _ g n m h p k v);
      [exact HE|exact HQ|exact HEq|exact (CE1 HI)|exact HS|exact HA|exact HP|exact HV].
  - apply CI.
    + apply (successor_inverse_correct _ g n m h p k v);
        [exact HE|exact HQ|exact HEq|exact HEtr|exact (CE1 (CE2 HI))|
         exact HS|exact HA|exact HP|exact HV].
    + apply (successor_inverse_coverage _ g n m h p k v);
        [exact HE|exact HEq|exact HEtr|exact (CE2 (CE2 HI))|
         exact HS|exact HA|exact HP|exact HV].
Qed.

Definition fresh_inverse_index (h n : set_term) : set_form :=
  ∀ ¬ graph_edge h`[↑] $0 n`[↑].

Lemma inverse_fresh_index G g n h :
  G ⊢238 member_ir n -> G ⊢238 inverse_prefix g n h ->
  G ⊢238 fresh_inverse_index h n.
Proof.
  destruct g as [ig|[]], n as [in_|[]], h as [ih|[]]. intros HI HP.
  unfold fresh_inverse_index. apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (inverse_range_fresh _ $ig $in_ $ih $iy); assumption.
Qed.

Theorem inverse_prefix_extension G g n m h v :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 ordinal_representative n ->
  G ⊢238 inverse_prefix g n h -> G ⊢238 raw_successor n m ->
  G ⊢238 graph_edge g n v ->
  G ⊢238 ∃ (inverse_prefix g`[↑] m`[↑] $0 ∧
    (graph_inclusion h`[↑] $0 ∧ fresh_inverse_index h`[↑] n`[↑])).
Proof.
  destruct g as [ig|[]], n as [in_|[]], m as [im|[]], h as [ih|[]], v as [iv|[]].
  intros HE HQ HEq HEtr Hempty HA HR HI HS HV.
  assert (HF : G ⊢238 fresh_inverse_index $ih $in_).
  { apply (inverse_fresh_index _ $ig $in_ $ih); [exact (CE2 HR)|exact HI]. }
  eapply ExE_named; [exact Hempty|]. intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. eapply ExE_named.
  - apply (raw_kuratowski_exists _ $ie $iv $in_); [apply Ctx; now left|inherit HA].
  - intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. eapply ExE_named.
    + apply (raw_adjunction_exists _ $ih $ip). inherit HA.
    + intro k. destruct k as [ik|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $ik).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * apply (successor_inverse_prefix _ $ig $in_ $im $ih $ip $ik $iv).
        -- inherit HE.
        -- inherit HQ.
        -- inherit HEq.
        -- inherit HEtr.
        -- inherit HI.
        -- inherit HS.
        -- apply Ctx. now left.
        -- apply Ctx. right. now left.
        -- inherit HV.
      * apply CI.
        -- apply (raw_adjunction_graph_inclusion _ $ih $ip $ik), Ctx. now left.
        -- inherit HF.
Qed.

Lemma inverse_prefix_subst g n h sigma :
  (inverse_prefix g n h)[sigma] = inverse_prefix g`[sigma] n`[sigma] h`[sigma].
Proof.
  unfold inverse_prefix, inverse_entries, inverse_entry, inverse_correct,
    inverse_coverage, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma inverse_exists_subst g n sigma :
  (inverse_exists g n)[sigma] = inverse_exists g`[sigma] n`[sigma].
Proof.
  unfold inverse_exists. cbn [subst_form]. rewrite inverse_prefix_subst.
  rewrite !up_term. reflexivity.
Qed.

Lemma inverse_property_at g a n :
  (inverse_property g a)[n..] = (subset n a → inverse_exists g n).
Proof.
  destruct g as [ig|[]], a as [ia|[]], n as [in_|[]].
  unfold inverse_property, inverse_exists, inverse_prefix, inverse_entries,
    inverse_entry, inverse_correct, inverse_coverage, subset, graph_edge,
    raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn [terms2 Vector.map subst_form subst_term up scons funcomp]. reflexivity.
Qed.

Lemma inverse_induction_base G g a :
  G ⊢238 ordinal_base (inverse_property g a).
Proof.
  destruct g as [ig|[]], a as [ia|[]]. unfold ordinal_base.
  apply AllI_named. intro n. destruct n as [in_|[]].
  change (G ⊢238 ((ordinal_representative $in_ ∧ raw_zero $in_) →
    (inverse_property $ig $ia)[$in_..])).
  rewrite inverse_property_at. apply II, II. unfold inverse_exists. apply (ExI $in_).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply empty_inverse_prefix. eapply CE2, Ctx. right. now left.
Qed.

Lemma inverse_induction_step G g a :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 graph_left_total g a ->
  G ⊢238 ordinal_step (inverse_property g a).
Proof.
  destruct g as [ig|[]], a as [ia|[]]. intros HE HQ HEq HEtr Hempty HA HT.
  apply ordinal_step_intro. intros n m. destruct n as [in_|[]], m as [im|[]].
  rewrite !inverse_property_at. apply II.
  eapply ExE_named.
  - eapply IE; [apply Ctx; right; now left|].
    apply (subset_transitive _ $in_ $im $ia).
    + apply raw_successor_old_subset. eapply CE2, CE2, Ctx. right. right. now left.
    + apply Ctx. now left.
  - intro h. destruct h as [ih|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply ExE_named.
    + apply (graph_left_total_instance _ $ig $ia $in_); [inherit HT|].
      apply (subset_member _ $im $ia $in_); [apply Ctx; right; now left|].
      apply raw_successor_point_member; [inherit HE|].
      eapply CE2, CE2, Ctx. right. right. right. now left.
    + intro v. destruct v as [iv|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      eapply ExE_named.
      * apply (inverse_prefix_extension _ $ig $in_ $im $ih $iv).
        -- inherit HE.
        -- inherit HQ.
        -- inherit HEq.
        -- inherit HEtr.
        -- inherit Hempty.
        -- inherit HA.
        -- eapply CE1, Ctx. right. right. right. right. now left.
        -- apply Ctx. right. now left.
        -- eapply CE2, CE2, Ctx. right. right. right. right. now left.
        -- apply Ctx. now left.
      * intro k. destruct k as [ik|[]].
        cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
        unfold inverse_exists. apply (ExI $ik).
        cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
        eapply CE1, Ctx. now left.
Qed.

(** Totality over an arbitrary actual graph's ordinal domain constructs
    the reverse graph.  The displayed graph-totality assumption is
    discharged; for Iso it is supplied by its concrete left-total clause. *)
Theorem S0_inverse_graph_exists g a :
  derivable finite_set_S0
    (ordinal_representative a → (graph_left_total g a → inverse_exists g a)).
Proof.
  destruct g as [ig|[]], a as [ia|[]].
  assert (HB : bounded (1 + S (ig + ia)) (inverse_property $ig $ia)).
  { unfold inverse_property, inverse_exists, inverse_prefix, inverse_entries,
      inverse_entry, inverse_correct, inverse_coverage, subset, graph_edge,
      raw_kuratowski, raw_pair, raw_singleton, R, E. cbn. fixed_bounds. }
  pose proof (S0_ordinal_induction (S (ig + ia)) (inverse_property $ig $ia) HB) as HI.
  assert (Hbase : derivable finite_set_S0 (ordinal_base (inverse_property $ig $ia))).
  { exists []. split; [intros psi []|apply inverse_induction_base]. }
  destruct (derivable_mp finite_set_S0 _ _ HI Hbase) as [Gind [HGind Hind]].
  destruct S0_empty as [Gempty [HGempty Hempty]].
  set (G := equality_base ++ (adjunction_ax :: (Gempty ++ Gind))).
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
  assert (HA : G ⊢238 adjunction_ax).
  { apply Ctx. unfold G, equality_base. cbn. right. right. right. right. now left. }
  assert (Hempty' : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. right. apply in_or_app. now left. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|[<-|Hpsi]].
    + apply S0_base. apply in_or_app. now left.
    + apply S0_base. apply in_or_app. right. now left.
    + apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGempty|now apply HGind].
  - apply II, II.
    assert (HS : (graph_left_total $ig $ia :: ordinal_representative $ia :: G)
       ⊢238 ordinal_step (inverse_property $ig $ia)).
    { apply inverse_induction_step.
      - apply weaken_one, weaken_one. exact HE.
      - apply weaken_one, weaken_one. exact HQ.
      - apply weaken_one, weaken_one. exact HEq.
      - apply weaken_one, weaken_one. exact HEtr.
      - apply weaken_one, weaken_one. exact Hempty'.
      - apply weaken_one, weaken_one. exact HA.
      - apply Ctx. now left. }
    assert (Hall : (graph_left_total $ig $ia :: ordinal_representative $ia :: G)
       ⊢238 ∀ (ordinal_representative $0 → inverse_property $ig $ia)).
    { eapply IE; [|exact HS]. eapply Weak; [exact Hind|]. intros psi Hpsi.
      right. right. unfold G. apply in_or_app. right. right. apply in_or_app. now right. }
    pose proof (AllE $ia Hall) as Hat.
    change ((graph_left_total $ig $ia :: ordinal_representative $ia :: G) ⊢238
      (ordinal_representative $ia → (inverse_property $ig $ia)[$ia..])) in Hat.
    rewrite inverse_property_at in Hat. eapply IE; [|apply subset_reflexivity].
    eapply IE; [exact Hat|apply Ctx; right; now left].
Qed.

Lemma graph_typed_instance G g a b x y :
  G ⊢238 graph_typed g a b -> G ⊢238 graph_edge g x y -> G ⊢238 (R a x ∧ R b y).
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]], x as [ix|[]], y as [iy|[]].
  intros HT HE. unfold graph_typed in HT. pose proof (AllE $iy (AllE $ix HT)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HE).
Qed.

Lemma graph_right_total_instance G g b y :
  G ⊢238 graph_right_total g b -> G ⊢238 R b y ->
  G ⊢238 ∃ graph_edge g`[↑] $0 y`[↑].
Proof.
  destruct g as [ig|[]], b as [ib|[]], y as [iy|[]]. intros HT Hy.
  unfold graph_right_total in HT. pose proof (AllE $iy HT) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H Hy).
Qed.

Lemma graph_functional_instance G g x y z :
  G ⊢238 graph_functional g -> G ⊢238 graph_edge g x y ->
  G ⊢238 graph_edge g x z -> G ⊢238 E y z.
Proof.
  destruct g as [ig|[]], x as [ix|[]], y as [iy|[]], z as [iz|[]]. intros HF Hy Hz.
  unfold graph_functional in HF. pose proof (AllE $iz (AllE $iy (AllE $ix HF))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma graph_injective_instance G g x y z :
  G ⊢238 graph_injective g -> G ⊢238 graph_edge g x z ->
  G ⊢238 graph_edge g y z -> G ⊢238 E x y.
Proof.
  destruct g as [ig|[]], x as [ix|[]], y as [iy|[]], z as [iz|[]]. intros HF Hx Hy.
  unfold graph_injective in HF. pose proof (AllE $iz (AllE $iy (AllE $ix HF))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma graph_order_instance G g x y u v :
  G ⊢238 graph_order g -> G ⊢238 graph_edge g x u ->
  G ⊢238 graph_edge g y v -> G ⊢238 (R x y ↔ R u v).
Proof.
  destruct g as [ig|[]], x as [ix|[]], y as [iy|[]], u as [iu|[]], v as [iv|[]].
  intros HO Hx Hy. unfold graph_order in HO.
  pose proof (AllE $iv (AllE $iu (AllE $iy (AllE $ix HO)))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma inverse_order_entries G g a b h :
  G ⊢238 graph_typed g a b -> G ⊢238 inverse_entries g a h ->
  G ⊢238 graph_entries h b a.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]], h as [ih|[]]. intros HT HI.
  unfold graph_entries. apply AllI_named. intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply ExE_named.
  - apply (inverse_entries_instance _ $ig $ia $ih $ip); [inherit HI|apply Ctx; now left].
  - intro x. destruct x as [ix|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply ExE_named; [apply Ctx; now left|]. intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (entry_witness_from_components _ $ib $ia $ip $iy $ix).
    + eapply CE2. apply (graph_typed_instance _ $ig $ia $ib $ix $iy);
        [inherit HT|]. eapply CE1, CE2, Ctx. now left.
    + eapply CE1, Ctx. now left.
    + eapply CE2, CE2, Ctx. now left.
Qed.

Lemma inverse_order_typed G g a b h :
  G ⊢238 graph_typed g a b -> G ⊢238 inverse_correct g a h ->
  G ⊢238 graph_typed h b a.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]], h as [ih|[]]. intros HT HC.
  unfold graph_typed. apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, CI.
  - eapply CE2. apply (graph_typed_instance _ $ig $ia $ib $ix $iy); [inherit HT|].
    eapply CE2. apply (inverse_correct_instance _ $ig $ia $ih $iy $ix);
      [inherit HC|apply Ctx; now left].
  - eapply CE1. apply (inverse_correct_instance _ $ig $ia $ih $iy $ix);
      [inherit HC|apply Ctx; now left].
Qed.

Lemma inverse_order_right_total G g a h :
  G ⊢238 inverse_coverage g a h -> G ⊢238 graph_right_total h a.
Proof.
  destruct g as [ig|[]], a as [ia|[]], h as [ih|[]]. intro HC.
  unfold graph_right_total. apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply ExE_named.
  - apply (inverse_coverage_instance _ $ig $ia $ih $ix); [inherit HC|apply Ctx; now left].
  - intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iy).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply CE1, Ctx. now left.
Qed.

Lemma inverse_order_left_total G g a b h :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 graph_typed g a b ->
  G ⊢238 graph_right_total g b -> G ⊢238 graph_functional g ->
  G ⊢238 inverse_coverage g a h -> G ⊢238 graph_left_total h b.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]], h as [ih|[]].
  intros HE HEq HEtr HT HR HF HC. unfold graph_left_total.
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply ExE_named.
  - apply (graph_right_total_instance _ $ig $ib $iy); [inherit HR|apply Ctx; now left].
  - intro x. destruct x as [ix|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. eapply ExE_named.
    + apply (inverse_coverage_instance _ $ig $ia $ih $ix); [inherit HC|].
      eapply CE1. apply (graph_typed_instance _ $ig $ia $ib $ix $iy);
        [inherit HT|apply Ctx; now left].
    + intro z. destruct z as [iz|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $ix).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (graph_edge_coordinate_transport _ $ih $iz $ix $iy $ix).
      * inherit HEq.
      * inherit HEtr.
      * apply equality_symmetry_instance; [inherit HEq|].
        apply (graph_functional_instance _ $ig $ix $iy $iz).
        -- inherit HF.
        -- apply Ctx. right. now left.
        -- eapply CE2, Ctx. now left.
      * inherit (AllE $ix HE).
      * eapply CE1, Ctx. now left.
Qed.

Lemma inverse_order_functional G g a h :
  G ⊢238 graph_injective g -> G ⊢238 inverse_correct g a h ->
  G ⊢238 graph_functional h.
Proof.
  destruct g as [ig|[]], a as [ia|[]], h as [ih|[]]. intros HI HC. unfold graph_functional.
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (graph_injective_instance _ $ig $ix $iz $iy).
  - inherit HI.
  - eapply CE2. apply (inverse_correct_instance _ $ig $ia $ih $iy $ix);
      [inherit HC|]. eapply CE1, Ctx. now left.
  - eapply CE2. apply (inverse_correct_instance _ $ig $ia $ih $iy $iz);
      [inherit HC|]. eapply CE2, Ctx. now left.
Qed.

Lemma inverse_order_injective G g a h :
  G ⊢238 graph_functional g -> G ⊢238 inverse_correct g a h ->
  G ⊢238 graph_injective h.
Proof.
  destruct g as [ig|[]], a as [ia|[]], h as [ih|[]]. intros HF HC. unfold graph_injective.
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (graph_functional_instance _ $ig $ix $iy $iz).
  - inherit HF.
  - eapply CE2. apply (inverse_correct_instance _ $ig $ia $ih $iy $ix);
      [inherit HC|]. eapply CE1, Ctx. now left.
  - eapply CE2. apply (inverse_correct_instance _ $ig $ia $ih $iz $ix);
      [inherit HC|]. eapply CE2, Ctx. now left.
Qed.

Lemma inverse_order_preserves G g a h :
  G ⊢238 graph_order g -> G ⊢238 inverse_correct g a h -> G ⊢238 graph_order h.
Proof.
  destruct g as [ig|[]], a as [ia|[]], h as [ih|[]]. intros HO HC. unfold graph_order.
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro w. destruct w as [iw|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, CI.
  - eapply CE2. apply (graph_order_instance _ $ig $ix $iw $iy $iz).
    + inherit HO.
    + eapply CE2. apply (inverse_correct_instance _ $ig $ia $ih $iy $ix);
        [inherit HC|]. eapply CE1, Ctx. now left.
    + eapply CE2. apply (inverse_correct_instance _ $ig $ia $ih $iz $iw);
        [inherit HC|]. eapply CE2, Ctx. now left.
  - eapply CE1. apply (graph_order_instance _ $ig $ix $iw $iy $iz).
    + inherit HO.
    + eapply CE2. apply (inverse_correct_instance _ $ig $ia $ih $iy $ix);
        [inherit HC|]. eapply CE1, Ctx. now left.
    + eapply CE2. apply (inverse_correct_instance _ $ig $ia $ih $iz $iw);
        [inherit HC|]. eapply CE2, Ctx. now left.
Qed.

Theorem inverse_order_bijection G g a b h :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 order_bijection g a b ->
  G ⊢238 inverse_prefix g a h -> G ⊢238 order_bijection h b a.
Proof.
  intros HE HEq HEtr HG HP. unfold order_bijection. apply CI.
  - apply (inverse_order_entries _ g a b h);
      [exact (CE1 (CE2 HG))|exact (CE1 HP)].
  - apply CI.
    + apply (inverse_order_typed _ g a b h);
        [exact (CE1 (CE2 HG))|exact (CE1 (CE2 HP))].
    + apply CI.
      * apply (inverse_order_left_total _ g a b h).
        -- exact HE.
        -- exact HEq.
        -- exact HEtr.
        -- exact (CE1 (CE2 HG)).
        -- exact (CE1 (CE2 (CE2 (CE2 HG)))).
        -- exact (CE1 (CE2 (CE2 (CE2 (CE2 HG))))).
        -- exact (CE2 (CE2 HP)).
      * apply CI.
        -- apply (inverse_order_right_total _ g a h). exact (CE2 (CE2 HP)).
        -- apply CI.
           ++ apply (inverse_order_functional _ g a h).
              ** exact (CE1 (CE2 (CE2 (CE2 (CE2 (CE2 HG)))))).
              ** exact (CE1 (CE2 HP)).
           ++ apply CI.
              ** apply (inverse_order_injective _ g a h).
                 --- exact (CE1 (CE2 (CE2 (CE2 (CE2 HG))))).
                 --- exact (CE1 (CE2 HP)).
              ** apply (inverse_order_preserves _ g a h).
                 --- exact (CE2 (CE2 (CE2 (CE2 (CE2 (CE2 HG)))))).
                 --- exact (CE1 (CE2 HP)).
Qed.

Theorem S0_inverse_graph_all a :
  derivable finite_set_S0
    (∀ (ordinal_representative a`[↑] →
       (graph_left_total $0 a`[↑] → inverse_exists $0 a`[↑]))).
Proof. apply S0_generalize, S0_inverse_graph_exists. Qed.

(** The graph parameter is universally generalized before eliminating the
    given Iso witness.  A single fixed finite S0 context therefore suffices
    for every instantiated source graph. *)
Theorem S0_order_iso_symmetric a b :
  derivable finite_set_S0
    (ordinal_representative a → (order_iso a b → order_iso b a)).
Proof.
  destruct a as [ia|[]], b as [ib|[]].
  destruct (S0_inverse_graph_all $ia) as [Ginv [HGinv Hinv]].
  set (G := equality_base ++ Ginv).
  assert (HE : G ⊢238 (∀ E $0 $0)).
  { apply Ctx. unfold G, equality_base. cbn. now left. }
  assert (HEq : G ⊢238 equality_symmetry_ax).
  { apply Ctx. unfold G, equality_base, equality_symmetry_ax. cbn. right. now left. }
  assert (HEtr : G ⊢238 pair_equality_transitivity_ax).
  { apply Ctx. unfold G, equality_base, pair_equality_transitivity_ax. cbn.
    right. right. now left. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + now apply HGinv.
  - apply II, II. eapply ExE_named; [apply Ctx; now left|].
    intro g. destruct g as [ig|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    pose proof (AllE $ig Hinv) as Hi.
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in Hi.
    eapply ExE_named.
    + eapply IE; [|eapply CE1, CE2, CE2, Ctx; now left].
      eapply IE; [|apply Ctx; right; right; now left].
      eapply Weak; [exact Hi|]. intros psi Hpsi.
      right. right. right. unfold G. apply in_or_app. now right.
    + intro h. destruct h as [ih|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      unfold order_iso. apply (ExI $ih).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (inverse_order_bijection _ $ig $ia $ib $ih).
      * apply weaken_one, weaken_one, weaken_one, weaken_one. exact HE.
      * apply weaken_one, weaken_one, weaken_one, weaken_one. exact HEq.
      * apply weaken_one, weaken_one, weaken_one, weaken_one. exact HEtr.
      * apply Ctx. right. now left.
      * apply Ctx. now left.
Qed.

Print Assumptions inverse_order_bijection.
Print Assumptions S0_order_iso_symmetric.
Print Assumptions S0_inverse_graph_exists.
Print Assumptions inverse_prefix_extension.
Print Assumptions empty_inverse_prefix.
Print Assumptions inverse_range_fresh.
End InverseGraph238.
