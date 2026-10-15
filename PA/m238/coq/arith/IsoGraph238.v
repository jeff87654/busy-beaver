(** Original set-coded order-isomorphism interface and identity graph
    construction.  Every graph entry is an actual Kuratowski object.
    All graph and object witnesses remain existential and noncanonical. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import
  Compact238 PAinCompact238 OrdinalSuccessor238 OrdinalTrace238
  PairGraph238 GraphTransport238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 OrdinalTrace238.OrdinalTrace238
  PairGraph238.PairGraph238 GraphTransport238.GraphTransport238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module IsoGraph238.

Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition entry_witness (a b p : set_term) : set_form :=
  ∃ ∃ (R a`[↑]`[↑] $1 ∧
    (R b`[↑]`[↑] $0 ∧ raw_kuratowski p`[↑]`[↑] $1 $0)).
Definition graph_entries (g a b : set_term) : set_form :=
  ∀ (R g`[↑] $0 → entry_witness a`[↑] b`[↑] $0).
Definition graph_typed (g a b : set_term) : set_form :=
  ∀ ∀ (graph_edge g`[↑]`[↑] $1 $0 →
    (R a`[↑]`[↑] $1 ∧ R b`[↑]`[↑] $0)).
Definition graph_left_total (g a : set_term) : set_form :=
  ∀ (R a`[↑] $0 → ∃ graph_edge g`[↑]`[↑] $1 $0).
Definition graph_right_total (g b : set_term) : set_form :=
  ∀ (R b`[↑] $0 → ∃ graph_edge g`[↑]`[↑] $0 $1).
Definition graph_functional (g : set_term) : set_form :=
  ∀ ∀ ∀ ((graph_edge g`[↑]`[↑]`[↑] $2 $1 ∧
            graph_edge g`[↑]`[↑]`[↑] $2 $0) → E $1 $0).
Definition graph_injective (g : set_term) : set_form :=
  ∀ ∀ ∀ ((graph_edge g`[↑]`[↑]`[↑] $2 $0 ∧
            graph_edge g`[↑]`[↑]`[↑] $1 $0) → E $2 $1).
Definition graph_order (g : set_term) : set_form :=
  ∀ ∀ ∀ ∀ ((graph_edge g`[↑]`[↑]`[↑]`[↑] $3 $1 ∧
              graph_edge g`[↑]`[↑]`[↑]`[↑] $2 $0) →
              (R $3 $2 ↔ R $1 $0)).
Definition order_bijection (g a b : set_term) : set_form :=
  graph_entries g a b ∧
    (graph_typed g a b ∧
      (graph_left_total g a ∧
        (graph_right_total g b ∧
          (graph_functional g ∧ (graph_injective g ∧ graph_order g))))).
Definition order_iso (a b : set_term) : set_form :=
  ∃ order_bijection $0 a`[↑] b`[↑].

Definition identity_diagonal (g a : set_term) : set_form :=
  ∀ ∀ (graph_edge g`[↑]`[↑] $1 $0 → (R a`[↑]`[↑] $1 ∧ E $1 $0)).
Definition identity_total (g a : set_term) : set_form :=
  ∀ (R a`[↑] $0 → graph_edge g`[↑] $0 $0).
Definition identity_graph (g a : set_term) : set_form :=
  graph_entries g a a ∧ (identity_diagonal g a ∧ identity_total g a).
Definition identity_exists (a : set_term) : set_form :=
  ∃ identity_graph $0 a`[↑].

Lemma entry_witness_from_components G a b p x y :
  G ⊢238 R a x -> G ⊢238 R b y -> G ⊢238 raw_kuratowski p x y ->
  G ⊢238 entry_witness a b p.
Proof.
  destruct a as [ia|[]], b as [ib|[]], p as [ip|[]], x as [ix|[]], y as [iy|[]].
  intros HX HY HP. unfold entry_witness. apply (ExI $ix).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (ExI $iy).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply CI; [exact HX|]. apply CI; assumption.
Qed.

Lemma graph_entries_instance G g a b p :
  G ⊢238 graph_entries g a b -> G ⊢238 R g p -> G ⊢238 entry_witness a b p.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]], p as [ip|[]].
  intros HG HP. unfold graph_entries in HG. pose proof (AllE $ip HG) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HP).
Qed.

Lemma identity_diagonal_instance G g a x y :
  G ⊢238 identity_diagonal g a -> G ⊢238 graph_edge g x y ->
  G ⊢238 (R a x ∧ E x y).
Proof.
  destruct g as [ig|[]], a as [ia|[]], x as [ix|[]], y as [iy|[]].
  intros HD HE. unfold identity_diagonal in HD.
  pose proof (AllE $iy (AllE $ix HD)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HE).
Qed.

Lemma identity_total_instance G g a x :
  G ⊢238 identity_total g a -> G ⊢238 R a x -> G ⊢238 graph_edge g x x.
Proof.
  destruct g as [ig|[]], a as [ia|[]], x as [ix|[]]. intros HT HX.
  unfold identity_total in HT. pose proof (AllE $ix HT) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HX).
Qed.

Lemma graph_edge_empty_false G g x y :
  G ⊢238 raw_zero g -> G ⊢238 graph_edge g x y -> G ⊢238 falsity.
Proof.
  destruct g as [ig|[]], x as [ix|[]], y as [iy|[]]. intros HZ HG.
  unfold graph_edge in HG. eapply ExE_named; [exact HG|]. intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply IE; [inherit (zero_excludes_member G $ig $ip HZ)|].
  eapply CE1, Ctx. now left.
Qed.

(** The induction base uses the displayed empty ordinal itself as an
    actual empty identity graph; no global chosen empty object is needed. *)
Lemma empty_identity_graph G a :
  G ⊢238 raw_zero a -> G ⊢238 identity_graph a a.
Proof.
  destruct a as [ia|[]]. intro HZ. unfold identity_graph. apply CI.
  - unfold graph_entries. apply AllI_named. intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, Exp.
    eapply IE; [inherit (zero_excludes_member G $ia $ip HZ)|apply Ctx; now left].
  - apply CI.
    + unfold identity_diagonal. apply AllI_named. intro x. destruct x as [ix|[]].
      apply AllI_named. intro y. destruct y as [iy|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, Exp.
      apply (graph_edge_empty_false _ $ia $ix $iy); [inherit HZ|apply Ctx; now left].
    + unfold identity_total. apply AllI_named. intro x. destruct x as [ix|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, Exp.
      eapply IE; [inherit (zero_excludes_member G $ia $ix HZ)|apply Ctx; now left].
Qed.

Lemma identity_key_fresh G g a y :
  G ⊢238 member_ir a -> G ⊢238 identity_graph g a -> G ⊢238 (¬ graph_edge g a y).
Proof.
  intros HI HG. apply II. eapply IE.
  - inherit (member_ir_not_self G a HI).
  - eapply CE1. apply (identity_diagonal_instance _ g a a y).
    + inherit (CE1 (CE2 HG)).
    + apply Ctx. now left.
Qed.

Lemma identity_graph_subst g a sigma :
  (identity_graph g a)[sigma] = identity_graph g`[sigma] a`[sigma].
Proof.
  unfold identity_graph, graph_entries, entry_witness, identity_diagonal,
    identity_total, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma identity_exists_subst a sigma :
  (identity_exists a)[sigma] = identity_exists a`[sigma].
Proof.
  unfold identity_exists. cbn [subst_form]. rewrite identity_graph_subst.
  rewrite up_term. reflexivity.
Qed.

Lemma identity_exists_at a : (identity_exists $0)[a..] = identity_exists a.
Proof. rewrite identity_exists_subst. reflexivity. Qed.

Lemma graph_inclusion_instance G g h x y :
  G ⊢238 graph_inclusion g h -> G ⊢238 graph_edge g x y -> G ⊢238 graph_edge h x y.
Proof.
  destruct g as [ig|[]], h as [ih|[]], x as [ix|[]], y as [iy|[]].
  intros HI HE. unfold graph_inclusion in HI.
  pose proof (AllE $iy (AllE $ix HI)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HE).
Qed.

Lemma successor_identity_entries G g p h a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 graph_entries g a a ->
  G ⊢238 raw_successor a b -> G ⊢238 raw_adjunction g p h ->
  G ⊢238 raw_kuratowski p a a -> G ⊢238 graph_entries h b b.
Proof.
  destruct g as [ig|[]], p as [ip|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]].
  intros HE HQ HEq HG HS HA HP. unfold graph_entries.
  apply AllI_named. intro q. destruct q as [iq|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_adjunction_member _ $ig $ip $ih $iq); [inherit HA|apply Ctx; now left].
  - eapply ExE_named.
    + apply (graph_entries_instance _ $ig $ia $ia $iq); [inherit HG|apply Ctx; now left].
    + intro x. destruct x as [ix|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      eapply ExE_named; [apply Ctx; now left|]. intro y. destruct y as [iy|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (entry_witness_from_components _ $ib $ib $iq $ix $iy).
      * apply (raw_successor_old_member _ $ia $ib $ix); [inherit HS|].
        eapply CE1, Ctx. now left.
      * apply (raw_successor_old_member _ $ia $ib $iy); [inherit HS|].
        eapply CE1, CE2, Ctx. now left.
      * eapply CE2, CE2, Ctx. now left.
  - apply (entry_witness_from_components _ $ib $ib $iq $ia $ia).
    + apply (raw_successor_point_member _ $ia $ib); [inherit HE|inherit HS].
    + apply (raw_successor_point_member _ $ia $ib); [inherit HE|inherit HS].
    + apply (raw_kuratowski_container_transport _ $ip $iq $ia $ia).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
      * inherit HP.
Qed.

Lemma successor_identity_diagonal G g p h a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 identity_diagonal g a -> G ⊢238 raw_successor a b ->
  G ⊢238 raw_adjunction g p h -> G ⊢238 raw_kuratowski p a a ->
  G ⊢238 identity_diagonal h b.
Proof.
  destruct g as [ig|[]], p as [ip|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]].
  intros HE HQ HEq HEtr HD HS HA HP. unfold identity_diagonal.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_adjunction_graph_edge_cases _ $ig $ip $ih $ia $ia $ix $iy).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit HA.
    + inherit HP.
    + apply Ctx. now left.
  - apply CI.
    + apply (raw_successor_old_member _ $ia $ib $ix); [inherit HS|].
      eapply CE1. apply (identity_diagonal_instance _ $ig $ia $ix $iy);
        [inherit HD|apply Ctx; now left].
    + eapply CE2. apply (identity_diagonal_instance _ $ig $ia $ix $iy);
        [inherit HD|apply Ctx; now left].
  - apply CI.
    + apply (equality_member_transport _ $ib $ia $ix).
      * inherit HE.
      * inherit HQ.
      * apply equality_symmetry_instance; [inherit HEq|]. eapply CE1, Ctx. now left.
      * apply (raw_successor_point_member _ $ia $ib); [inherit HE|inherit HS].
    + apply (pair_equality_transitivity _ $ix $ia $iy).
      * inherit HEtr.
      * eapply CE1, Ctx. now left.
      * apply equality_symmetry_instance; [inherit HEq|]. eapply CE2, Ctx. now left.
Qed.

Lemma successor_identity_total G g p h a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 identity_total g a ->
  G ⊢238 raw_successor a b -> G ⊢238 raw_adjunction g p h ->
  G ⊢238 raw_kuratowski p a a -> G ⊢238 identity_total h b.
Proof.
  destruct g as [ig|[]], p as [ip|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]].
  intros HE HEq HEtr HT HS HA HP.
  assert (Hnew : G ⊢238 graph_edge $ih $ia $ia).
  { apply (graph_edge_from_entry _ $ih $ia $ia $ip); [|exact HP].
    apply (raw_adjunction_intro _ $ig $ip $ih $ip); [exact HA|].
    apply DI2. exact (AllE $ip HE). }
  unfold identity_total. apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_successor_member_cases _ $ia $ib $ix); [inherit HS|apply Ctx; now left].
  - apply (graph_inclusion_instance _ $ig $ih $ix $ix).
    + apply (raw_adjunction_graph_inclusion _ $ig $ip $ih). inherit HA.
    + apply (identity_total_instance _ $ig $ia $ix); [inherit HT|apply Ctx; now left].
  - apply (graph_edge_coordinate_transport _ $ih $ia $ia $ix $ix).
    + inherit HEq.
    + inherit HEtr.
    + apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
    + apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
    + inherit Hnew.
Qed.

Lemma successor_identity_graph G g p h a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 identity_graph g a -> G ⊢238 raw_successor a b ->
  G ⊢238 raw_adjunction g p h -> G ⊢238 raw_kuratowski p a a ->
  G ⊢238 identity_graph h b.
Proof.
  intros HE HQ HEq HEtr HG HS HA HP. unfold identity_graph. apply CI.
  - apply (successor_identity_entries _ g p h a b);
      [exact HE|exact HQ|exact HEq|exact (CE1 HG)|exact HS|exact HA|exact HP].
  - apply CI.
    + apply (successor_identity_diagonal _ g p h a b);
        [exact HE|exact HQ|exact HEq|exact HEtr|exact (CE1 (CE2 HG))|
         exact HS|exact HA|exact HP].
    + apply (successor_identity_total _ g p h a b);
        [exact HE|exact HEq|exact HEtr|exact (CE2 (CE2 HG))|exact HS|exact HA|exact HP].
Qed.

Definition fresh_key (g a : set_term) : set_form :=
  ∀ ¬ graph_edge g`[↑] a`[↑] $0.

Lemma identity_fresh_key G g a :
  G ⊢238 member_ir a -> G ⊢238 identity_graph g a -> G ⊢238 fresh_key g a.
Proof.
  destruct g as [ig|[]], a as [ia|[]]. intros HI HG. unfold fresh_key.
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (identity_key_fresh _ $ig $ia $iy); assumption.
Qed.

(** The successor graph is constructed by an actual finite pair producer
    and Adjunction.  The old ordinal's local strictness proves that its new
    key has no old edge; the result preserves every old edge. *)
Theorem identity_successor_extension G g a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 identity_graph g a ->
  G ⊢238 raw_successor a b ->
  G ⊢238 ∃ (identity_graph $0 b`[↑] ∧
    (graph_inclusion g`[↑] $0 ∧ fresh_key g`[↑] a`[↑])).
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]].
  intros HE HQ HEq HEtr Hempty HA HR HG HS.
  assert (HF : G ⊢238 fresh_key $ig $ia).
  { apply identity_fresh_key; [exact (CE2 HR)|exact HG]. }
  eapply ExE_named; [exact Hempty|]. intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named.
  - apply (raw_kuratowski_exists _ $ie $ia $ia);
      [apply Ctx; now left|inherit HA].
  - intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. eapply ExE_named.
    + apply (raw_adjunction_exists _ $ig $ip). inherit HA.
    + intro h. destruct h as [ih|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $ih).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * apply (successor_identity_graph _ $ig $ip $ih $ia $ib).
        -- inherit HE.
        -- inherit HQ.
        -- inherit HEq.
        -- inherit HEtr.
        -- inherit HG.
        -- inherit HS.
        -- apply Ctx. now left.
        -- apply Ctx. right. now left.
      * apply CI.
        -- apply (raw_adjunction_graph_inclusion _ $ig $ip $ih), Ctx. now left.
        -- inherit HF.
Qed.

Lemma ordinal_step_intro G phi :
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

Lemma identity_induction_base G : G ⊢238 ordinal_base (identity_exists $0).
Proof.
  unfold ordinal_base. apply AllI_named. intro a. destruct a as [ia|[]].
  change (G ⊢238 ((ordinal_representative $ia ∧ raw_zero $ia) →
    (identity_exists $0)[$ia..])).
  rewrite identity_exists_at. apply II. unfold identity_exists. apply (ExI $ia).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply empty_identity_graph. eapply CE2, Ctx. now left.
Qed.

Lemma identity_induction_step G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 ordinal_step (identity_exists $0).
Proof.
  intros HE HQ HEq HEtr Hempty HA. apply ordinal_step_intro.
  intros a b. destruct a as [ia|[]], b as [ib|[]]. rewrite !identity_exists_at.
  eapply ExE_named; [apply Ctx; now left|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named.
  - apply (identity_successor_extension _ $ig $ia $ib).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Hempty.
    + inherit HA.
    + eapply CE1, Ctx. right. right. now left.
    + apply Ctx. now left.
    + eapply CE2, CE2, Ctx. right. right. now left.
  - intro h. destruct h as [ih|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    unfold identity_exists. apply (ExI $ih).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply CE1, Ctx. now left.
Qed.

Lemma S0_identity_induction_base :
  derivable finite_set_S0 (ordinal_base (identity_exists $0)).
Proof.
  exists []. split; [intros psi []|apply identity_induction_base].
Qed.

Lemma S0_identity_induction_step :
  derivable finite_set_S0 (ordinal_step (identity_exists $0)).
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
  assert (HEtr : G ⊢238 pair_equality_transitivity_ax).
  { apply Ctx. unfold G, equality_base, pair_equality_transitivity_ax. cbn.
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
  - apply identity_induction_step; assumption.
Qed.

Lemma identity_exists_bounded : bounded 1 (identity_exists $0).
Proof.
  unfold identity_exists, identity_graph, graph_entries, entry_witness,
    identity_diagonal, identity_total, graph_edge, raw_kuratowski,
    raw_pair, raw_singleton, R, E. cbn. fixed_bounds.
Qed.

(** The full S0 ordinal induction theorem is consumed with the concrete
    existential graph property.  The base and step above are actual finite
    derivations, so this conclusion postulates no graph supplier. *)
Theorem S0_identity_graph_exists a :
  derivable finite_set_S0 (ordinal_representative a → identity_exists a).
Proof.
  pose proof (S0_ordinal_induction 0 (identity_exists $0) identity_exists_bounded) as HI.
  pose proof (derivable_mp finite_set_S0 _ _ HI S0_identity_induction_base) as Hstep.
  destruct (derivable_mp finite_set_S0 _ _ Hstep S0_identity_induction_step)
    as [G [HG Hforall]].
  exists G. split; [exact HG|]. destruct a as [ia|[]].
  pose proof (AllE $ia Hforall) as H.
  change (G ⊢238 (ordinal_representative $ia → (identity_exists $0)[$ia..])) in H.
  rewrite identity_exists_at in H. exact H.
Qed.

Lemma identity_graph_typed G g a :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 identity_graph g a -> G ⊢238 graph_typed g a a.
Proof.
  destruct g as [ig|[]], a as [ia|[]]. intros HE HQ HG. unfold graph_typed.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, CI.
  - eapply CE1. apply (identity_diagonal_instance _ $ig $ia $ix $iy);
      [inherit (CE1 (CE2 HG))|apply Ctx; now left].
  - apply (equality_member_transport _ $ia $ix $iy).
    + inherit HE.
    + inherit HQ.
    + eapply CE2. apply (identity_diagonal_instance _ $ig $ia $ix $iy);
        [inherit (CE1 (CE2 HG))|apply Ctx; now left].
    + eapply CE1. apply (identity_diagonal_instance _ $ig $ia $ix $iy);
        [inherit (CE1 (CE2 HG))|apply Ctx; now left].
Qed.

Lemma identity_graph_left_total G g a :
  G ⊢238 identity_graph g a -> G ⊢238 graph_left_total g a.
Proof.
  destruct g as [ig|[]], a as [ia|[]]. intro HG. unfold graph_left_total.
  apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (ExI $ix).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (identity_total_instance _ $ig $ia $ix);
    [inherit (CE2 (CE2 HG))|apply Ctx; now left].
Qed.

Lemma identity_graph_right_total G g a :
  G ⊢238 identity_graph g a -> G ⊢238 graph_right_total g a.
Proof.
  destruct g as [ig|[]], a as [ia|[]]. intro HG. unfold graph_right_total.
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (ExI $iy).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (identity_total_instance _ $ig $ia $iy);
    [inherit (CE2 (CE2 HG))|apply Ctx; now left].
Qed.

Lemma identity_graph_functional G g a :
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 identity_graph g a -> G ⊢238 graph_functional g.
Proof.
  destruct g as [ig|[]], a as [ia|[]]. intros HEq HEtr HG. unfold graph_functional.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (pair_equality_transitivity _ $iy $ix $iz).
  - inherit HEtr.
  - apply equality_symmetry_instance; [inherit HEq|].
    eapply CE2. apply (identity_diagonal_instance _ $ig $ia $ix $iy).
    + inherit (CE1 (CE2 HG)).
    + eapply CE1, Ctx. now left.
  - eapply CE2. apply (identity_diagonal_instance _ $ig $ia $ix $iz).
    + inherit (CE1 (CE2 HG)).
    + eapply CE2, Ctx. now left.
Qed.

Lemma identity_graph_injective G g a :
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 identity_graph g a -> G ⊢238 graph_injective g.
Proof.
  destruct g as [ig|[]], a as [ia|[]]. intros HEq HEtr HG. unfold graph_injective.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (pair_equality_transitivity _ $ix $iz $iy).
  - inherit HEtr.
  - eapply CE2. apply (identity_diagonal_instance _ $ig $ia $ix $iz).
    + inherit (CE1 (CE2 HG)).
    + eapply CE1, Ctx. now left.
  - apply equality_symmetry_instance; [inherit HEq|].
    eapply CE2. apply (identity_diagonal_instance _ $ig $ia $iy $iz).
    + inherit (CE1 (CE2 HG)).
    + eapply CE2, Ctx. now left.
Qed.

Lemma equality_membership_biconditional G x y u v :
  G ⊢238 equality_membership_ax -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 E x u -> G ⊢238 E y v -> G ⊢238 (R x y ↔ R u v).
Proof.
  intros HQ HEq Hxu Hyv. apply CI.
  - apply II. eapply IE; [|apply Ctx; now left].
    eapply IE; [|inherit Hxu]. eapply IE; [|inherit Hyv].
    apply (equality_membership_instance _ y x v u). inherit HQ.
  - apply II. eapply IE; [|apply Ctx; now left].
    eapply IE; [|apply equality_symmetry_instance; [inherit HEq|inherit Hxu]].
    eapply IE; [|apply equality_symmetry_instance; [inherit HEq|inherit Hyv]].
    apply (equality_membership_instance _ v u y x). inherit HQ.
Qed.

Lemma identity_graph_order G g a :
  G ⊢238 equality_membership_ax -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 identity_graph g a -> G ⊢238 graph_order g.
Proof.
  destruct g as [ig|[]], a as [ia|[]]. intros HQ HEq HG. unfold graph_order.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro u. destruct u as [iu|[]].
  apply AllI_named. intro v. destruct v as [iv|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (equality_membership_biconditional _ $ix $iy $iu $iv).
  - inherit HQ.
  - inherit HEq.
  - eapply CE2. apply (identity_diagonal_instance _ $ig $ia $ix $iu).
    + inherit (CE1 (CE2 HG)).
    + eapply CE1, Ctx. now left.
  - eapply CE2. apply (identity_diagonal_instance _ $ig $ia $iy $iv).
    + inherit (CE1 (CE2 HG)).
    + eapply CE2, Ctx. now left.
Qed.

Theorem identity_graph_order_bijection G g a :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 identity_graph g a -> G ⊢238 order_bijection g a a.
Proof.
  intros HE HQ HEq HEtr HG. unfold order_bijection. apply CI; [exact (CE1 HG)|].
  apply CI; [apply (identity_graph_typed _ g a); assumption|].
  apply CI; [apply (identity_graph_left_total _ g a); exact HG|].
  apply CI; [apply (identity_graph_right_total _ g a); exact HG|].
  apply CI; [apply (identity_graph_functional _ g a); assumption|].
  apply CI; [apply (identity_graph_injective _ g a); assumption|].
  apply (identity_graph_order _ g a); assumption.
Qed.

Lemma identity_graph_order_iso G g a :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 identity_graph g a -> G ⊢238 order_iso a a.
Proof.
  destruct g as [ig|[]], a as [ia|[]]. intros HE HQ HEq HEtr HG.
  unfold order_iso. apply (ExI $ig).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply identity_graph_order_bijection; assumption.
Qed.

(** Numerical reflexivity is witnessed by the actual identity graph
    constructed through full ordinal induction above. *)
Theorem S0_order_iso_reflexive a :
  derivable finite_set_S0 (ordinal_representative a → order_iso a a).
Proof.
  destruct a as [ia|[]].
  destruct (S0_identity_graph_exists $ia) as [Gid [HGid Hidentity]].
  set (G := equality_base ++ Gid).
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
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + now apply HGid.
  - apply II. eapply ExE_named.
    + eapply IE; [|apply Ctx; now left]. eapply Weak; [exact Hidentity|].
      intros psi Hpsi. right. unfold G. apply in_or_app. now right.
    + intro g. destruct g as [ig|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (identity_graph_order_iso _ $ig $ia).
      * apply weaken_one, weaken_one. exact HE.
      * apply weaken_one, weaken_one. exact HQ.
      * apply weaken_one, weaken_one. exact HEq.
      * apply weaken_one, weaken_one. exact HEtr.
      * apply Ctx. now left.
Qed.

Print Assumptions identity_graph_order_bijection.
Print Assumptions S0_order_iso_reflexive.
Print Assumptions S0_identity_graph_exists.
Print Assumptions successor_identity_graph.
Print Assumptions identity_successor_extension.
Print Assumptions empty_identity_graph.
Print Assumptions identity_key_fresh.
End IsoGraph238.
