(** Actual finite graph clauses shared by arithmetic traces.
    The domain is inclusive. Functionality compares raw objects, and the
    range consists of strict ordinal representatives. Exact extensions
    are built by Adjunction of a real Kuratowski entry. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 GraphTransport238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  GraphTransport238.GraphTransport238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module TraceGraph238.

Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition graph_domain (top g : set_term) : set_form :=
  ∀ ((∃ graph_edge g`[↑]`[↑] $1 $0) ↔
     (R top`[↑] $0 ∨ E $0 top`[↑])).
Definition graph_functional (g : set_term) : set_form :=
  ∀ ∀ ∀ ((graph_edge g`[↑]`[↑]`[↑] $2 $1 ∧
            graph_edge g`[↑]`[↑]`[↑] $2 $0) → E $1 $0).
Definition graph_range (g : set_term) : set_form :=
  ∀ ∀ (graph_edge g`[↑]`[↑] $1 $0 → ordinal_representative $0).
Definition graph_edge_extension (g h a b : set_term) : set_form :=
  ∀ ∀ (graph_edge h`[↑]`[↑] $1 $0 ↔
    (graph_edge g`[↑]`[↑] $1 $0 ∨
      (E $1 a`[↑]`[↑] ∧ E $0 b`[↑]`[↑]))).

Lemma equality_member_transitive_transport G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E a b ->
  G ⊢238 member_transitive a -> G ⊢238 member_transitive b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HQ HEq Hab HA.
  unfold member_transitive. apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (member_transitive_member _ $ia $ix); [inherit HA|].
  apply (equality_container_transport _ $ib $ia $ix).
  - inherit HE.
  - inherit HQ.
  - apply equality_symmetry_instance; [inherit HEq|inherit Hab].
  - apply Ctx. now left.
Qed.

Lemma equality_member_linear_transport G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E a b ->
  G ⊢238 member_linear a -> G ⊢238 member_linear b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HQ HEq Hab HA.
  unfold member_linear. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (linear_member_cases _ $ia $ix $iy); [inherit HA| |].
  - apply (equality_container_transport _ $ib $ia $ix).
    + inherit HE.
    + inherit HQ.
    + apply equality_symmetry_instance; [inherit HEq|inherit Hab].
    + eapply CE1, Ctx. now left.
  - apply (equality_container_transport _ $ib $ia $iy).
    + inherit HE.
    + inherit HQ.
    + apply equality_symmetry_instance; [inherit HEq|inherit Hab].
    + eapply CE2, Ctx. now left.
Qed.

Lemma equality_subset_target_transport G s a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 E a b -> G ⊢238 subset s a -> G ⊢238 subset s b.
Proof.
  destruct s as [is|[]], a as [ia|[]], b as [ib|[]]. intros HE HQ Hab HS.
  unfold subset. apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (equality_container_transport _ $ia $ib $ix).
  - inherit HE.
  - inherit HQ.
  - inherit Hab.
  - apply (subset_member _ $is $ia $ix); [inherit HS|apply Ctx; now left].
Qed.

Lemma equality_internal_extrema_transport G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E a b ->
  G ⊢238 internal_extrema a -> G ⊢238 internal_extrema b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HQ HEq Hab HA.
  unfold internal_extrema. apply AllI_named. intro s. destruct s as [is|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (internal_extrema_instance _ $ia $is); [inherit HA| |].
  - apply (equality_subset_target_transport _ $is $ib $ia).
    + inherit HE.
    + inherit HQ.
    + apply equality_symmetry_instance; [inherit HEq|inherit Hab].
    + eapply CE1, Ctx. now left.
  - eapply CE2, Ctx. now left.
Qed.

Lemma equality_member_ir_transport G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E a b ->
  G ⊢238 member_ir a -> G ⊢238 member_ir b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HQ HEq Hab HA.
  unfold member_ir. apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (member_ir_excludes_self _ $ia $ix); [inherit HA|].
  apply (equality_container_transport _ $ib $ia $ix).
  - inherit HE.
  - inherit HQ.
  - apply equality_symmetry_instance; [inherit HEq|inherit Hab].
  - apply Ctx. now left.
Qed.

Theorem equality_ordinal_representative_transport G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E a b ->
  G ⊢238 ordinal_representative a -> G ⊢238 ordinal_representative b.
Proof.
  intros HE HQ HEq Hab HA. apply CI.
  - apply CI.
    + apply (equality_transitive_transport _ a b); try assumption.
      exact (CE1 (CE1 HA)).
    + apply CI.
      * apply (equality_member_transitive_transport _ a b); try assumption.
        exact (CE1 (CE2 (CE1 HA))).
      * apply CI.
        -- apply (equality_member_linear_transport _ a b); try assumption.
           exact (CE1 (CE2 (CE2 (CE1 HA)))).
        -- apply (equality_internal_extrema_transport _ a b); try assumption.
           exact (CE2 (CE2 (CE2 (CE1 HA)))).
  - apply (equality_member_ir_transport _ a b); try assumption. exact (CE2 HA).
Qed.

Lemma graph_extension_cases G g h a b x y :
  G ⊢238 graph_edge_extension g h a b -> G ⊢238 graph_edge h x y ->
  G ⊢238 (graph_edge g x y ∨ (E x a ∧ E y b)).
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]],
    x as [ix|[]], y as [iy|[]]. intros HE HX.
  unfold graph_edge_extension in HE. pose proof (AllE $iy (AllE $ix HE)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (CE1 H) HX).
Qed.

Lemma graph_extension_intro G g h a b x y :
  G ⊢238 graph_edge_extension g h a b ->
  G ⊢238 (graph_edge g x y ∨ (E x a ∧ E y b)) -> G ⊢238 graph_edge h x y.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]],
    x as [ix|[]], y as [iy|[]]. intros HE HX.
  unfold graph_edge_extension in HE. pose proof (AllE $iy (AllE $ix HE)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (CE2 H) HX).
Qed.

Lemma graph_extension_old_edge G g h a b x y :
  G ⊢238 graph_edge_extension g h a b -> G ⊢238 graph_edge g x y ->
  G ⊢238 graph_edge h x y.
Proof.
  intros HE HX. apply (graph_extension_intro _ g h a b x y);
    [exact HE|apply DI1; exact HX].
Qed.

Lemma graph_extension_new_edge G g h a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 graph_edge_extension g h a b ->
  G ⊢238 graph_edge h a b.
Proof.
  intros HE HX. apply (graph_extension_intro _ g h a b a b); [exact HX|].
  apply DI2, CI; [exact (AllE a HE)|exact (AllE b HE)].
Qed.

Theorem raw_adjunction_exact_graph_extension G g p h a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 raw_adjunction g p h -> G ⊢238 raw_kuratowski p a b ->
  G ⊢238 graph_edge_extension g h a b.
Proof.
  destruct g as [ig|[]], p as [ip|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]].
  intros HE HQ HEq HEtr HA HP. unfold graph_edge_extension.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. apply (raw_adjunction_graph_edge_cases _ $ig $ip $ih $ia $ib $ix $iy).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit HA.
    + inherit HP.
    + apply Ctx. now left.
  - apply II. eapply DE; [apply Ctx; now left| |].
    + unfold graph_inclusion in *.
      pose proof (raw_adjunction_graph_inclusion G $ig $ip $ih HA) as HI.
      pose proof (AllE $iy (AllE $ix HI)) as H.
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
      eapply IE; [inherit H|apply Ctx; now left].
    + apply (graph_edge_from_entry _ $ih $ix $iy $ip).
      * apply (raw_adjunction_intro _ $ig $ip $ih $ip); [inherit HA|].
        apply DI2. inherit (AllE $ip HE).
      * apply (raw_kuratowski_coordinate_transport _ $ip $ia $ib $ix $iy).
        -- inherit HEq.
        -- inherit HEtr.
        -- apply equality_symmetry_instance; [inherit HEq|eapply CE1, Ctx; now left].
        -- apply equality_symmetry_instance; [inherit HEq|eapply CE2, Ctx; now left].
        -- inherit HP.
Qed.

Theorem exact_graph_extension_exists G g a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 ∃ graph_edge_extension g`[↑] $0 a`[↑] b`[↑].
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]]. intros HE HQ HEq HEtr Hempty HA.
  eapply ExE_named; [exact Hempty|]. intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named.
  - apply (raw_kuratowski_exists _ $ie $ia $ib); [apply Ctx; now left|inherit HA].
  - intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply ExE_named; [apply (raw_adjunction_exists _ $ig $ip); inherit HA|].
    intro h. destruct h as [ih|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (ExI $ih).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (raw_adjunction_exact_graph_extension _ $ig $ip $ih $ia $ib).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + apply Ctx. now left.
    + apply Ctx. right. now left.
Qed.

Definition singleton_graph (a b g : set_term) : set_form :=
  ∀ ∀ (graph_edge g`[↑]`[↑] $1 $0 ↔
    (E $1 a`[↑]`[↑] ∧ E $0 b`[↑]`[↑])).

Lemma empty_graph_no_edge G g x y :
  G ⊢238 raw_zero g -> G ⊢238 (¬ graph_edge g x y).
Proof.
  destruct g as [ig|[]], x as [ix|[]], y as [iy|[]]. intro HZ. apply II.
  unfold graph_edge. eapply ExE_named; [apply Ctx; now left|].
  intro p. destruct p as [ip|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply IE; [inherit (zero_excludes_member G $ig $ip HZ)|].
  eapply CE1, Ctx. now left.
Qed.

Lemma singleton_graph_cases G a b g x y :
  G ⊢238 singleton_graph a b g -> G ⊢238 graph_edge g x y ->
  G ⊢238 (E x a ∧ E y b).
Proof.
  destruct a as [ia|[]], b as [ib|[]], g as [ig|[]], x as [ix|[]], y as [iy|[]].
  intros HS HX. unfold singleton_graph in HS.
  pose proof (AllE $iy (AllE $ix HS)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (CE1 H) HX).
Qed.

Lemma singleton_graph_intro G a b g x y :
  G ⊢238 singleton_graph a b g -> G ⊢238 (E x a ∧ E y b) ->
  G ⊢238 graph_edge g x y.
Proof.
  destruct a as [ia|[]], b as [ib|[]], g as [ig|[]], x as [ix|[]], y as [iy|[]].
  intros HS HX. unfold singleton_graph in HS.
  pose proof (AllE $iy (AllE $ix HS)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (CE2 H) HX).
Qed.

Lemma empty_extension_singleton_graph G e h a b :
  G ⊢238 raw_zero e -> G ⊢238 graph_edge_extension e h a b ->
  G ⊢238 singleton_graph a b h.
Proof.
  destruct e as [ie|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]]. intros HZ HE.
  unfold singleton_graph. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. eapply DE.
    + apply (graph_extension_cases _ $ie $ih $ia $ib $ix $iy);
        [inherit HE|apply Ctx; now left].
    + apply Exp. eapply IE; [inherit (empty_graph_no_edge G $ie $ix $iy HZ)|].
      apply Ctx. now left.
    + apply Ctx. now left.
  - apply II. apply (graph_extension_intro _ $ie $ih $ia $ib $ix $iy);
      [inherit HE|apply DI2, Ctx; now left].
Qed.

Theorem singleton_graph_exists G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 ∃ singleton_graph a`[↑] b`[↑] $0.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HQ HEq HEtr Hempty HA.
  eapply ExE_named; [exact Hempty|]. intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  eapply ExE_named.
  - apply (exact_graph_extension_exists _ $ie $ia $ib).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Hempty.
    + inherit HA.
  - intro g. destruct g as [ig|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (ExI $ig).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (empty_extension_singleton_graph _ $ie $ig $ia $ib).
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Lemma graph_domain_edge G top g x y :
  G ⊢238 graph_domain top g -> G ⊢238 graph_edge g x y ->
  G ⊢238 (R top x ∨ E x top).
Proof.
  destruct top as [it|[]], g as [ig|[]], x as [ix|[]], y as [iy|[]]. intros HD HX.
  unfold graph_domain in HD. pose proof (AllE $ix HD) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact (CE1 H)|]. apply (ExI $iy).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. exact HX.
Qed.

Lemma graph_domain_value G top g x :
  G ⊢238 graph_domain top g -> G ⊢238 (R top x ∨ E x top) ->
  G ⊢238 ∃ graph_edge g`[↑] x`[↑] $0.
Proof.
  destruct top as [it|[]], g as [ig|[]], x as [ix|[]]. intros HD HX.
  unfold graph_domain in HD. pose proof (AllE $ix HD) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (CE2 H) HX).
Qed.

Lemma graph_domain_coordinate_transport G top top' g :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 E top top' -> G ⊢238 graph_domain top g ->
  G ⊢238 graph_domain top' g.
Proof.
  destruct top as [it|[]], top' as [it'|[]], g as [ig|[]].
  intros HE HQ HEq HEtr Htt HD. unfold graph_domain.
  apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. eapply ExE_named; [apply Ctx; now left|].
    intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply DE.
    + apply (graph_domain_edge _ $it $ig $ix $iy); [inherit HD|apply Ctx; now left].
    + apply DI1. apply (equality_container_transport _ $it $it' $ix).
      * inherit HE.
      * inherit HQ.
      * inherit Htt.
      * apply Ctx. now left.
    + apply DI2. apply (pair_equality_transitivity _ $ix $it $it').
      * inherit HEtr.
      * apply Ctx. now left.
      * inherit Htt.
  - apply II. apply (graph_domain_value _ $it $ig $ix); [inherit HD|].
    eapply DE; [apply Ctx; now left| |].
    + apply DI1. apply (equality_container_transport _ $it' $it $ix).
      * inherit HE.
      * inherit HQ.
      * apply equality_symmetry_instance; [inherit HEq|inherit Htt].
      * apply Ctx. now left.
    + apply DI2. apply (pair_equality_transitivity _ $ix $it' $it).
      * inherit HEtr.
      * apply Ctx. now left.
      * apply equality_symmetry_instance; [inherit HEq|inherit Htt].
Qed.

Lemma graph_functional_at G g x y z :
  G ⊢238 graph_functional g -> G ⊢238 graph_edge g x y ->
  G ⊢238 graph_edge g x z -> G ⊢238 E y z.
Proof.
  destruct g as [ig|[]], x as [ix|[]], y as [iy|[]], z as [iz|[]]. intros HF HY HZ.
  unfold graph_functional in HF.
  pose proof (AllE $iz (AllE $iy (AllE $ix HF))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact H|]. apply CI; assumption.
Qed.

Lemma graph_range_at G g x y :
  G ⊢238 graph_range g -> G ⊢238 graph_edge g x y ->
  G ⊢238 ordinal_representative y.
Proof.
  destruct g as [ig|[]], x as [ix|[]], y as [iy|[]]. intros HR HX.
  unfold graph_range in HR. pose proof (AllE $iy (AllE $ix HR)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HX).
Qed.

Theorem singleton_graph_domain G e b g :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 raw_zero e ->
  G ⊢238 singleton_graph e b g -> G ⊢238 graph_domain e g.
Proof.
  destruct e as [ie|[]], b as [ib|[]], g as [ig|[]]. intros HE HZ HG.
  unfold graph_domain. apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. eapply ExE_named; [apply Ctx; now left|]. intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply DI2. eapply CE1. apply (singleton_graph_cases _ $ie $ib $ig $ix $iy);
      [inherit HG|apply Ctx; now left].
  - apply II. eapply DE; [apply Ctx; now left| |].
    + apply Exp. eapply IE; [inherit (zero_excludes_member G $ie $ix HZ)|].
      apply Ctx. now left.
    + apply (ExI $ib).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (singleton_graph_intro _ $ie $ib $ig $ix $ib); [inherit HG|].
      apply CI; [apply Ctx; now left|inherit (AllE $ib HE)].
Qed.

Theorem singleton_graph_functional G a b g :
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 singleton_graph a b g -> G ⊢238 graph_functional g.
Proof.
  destruct a as [ia|[]], b as [ib|[]], g as [ig|[]]. intros HEq HEtr HG.
  unfold graph_functional. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (pair_equality_transitivity _ $iy $ib $iz).
  - inherit HEtr.
  - eapply CE2. apply (singleton_graph_cases _ $ia $ib $ig $ix $iy);
      [inherit HG|eapply CE1, Ctx; now left].
  - apply equality_symmetry_instance; [inherit HEq|].
    eapply CE2. apply (singleton_graph_cases _ $ia $ib $ig $ix $iz);
      [inherit HG|eapply CE2, Ctx; now left].
Qed.

Theorem singleton_graph_range G a b g :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 ordinal_representative b ->
  G ⊢238 singleton_graph a b g -> G ⊢238 graph_range g.
Proof.
  destruct a as [ia|[]], b as [ib|[]], g as [ig|[]]. intros HE HQ HEq HB HG.
  unfold graph_range. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (equality_ordinal_representative_transport _ $ib $iy).
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - apply equality_symmetry_instance; [inherit HEq|].
    eapply CE2. apply (singleton_graph_cases _ $ia $ib $ig $ix $iy);
      [inherit HG|apply Ctx; now left].
  - inherit HB.
Qed.

Theorem graph_extension_domain G t tp g h w :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 raw_successor t tp ->
  G ⊢238 graph_domain t g -> G ⊢238 graph_edge_extension g h tp w ->
  G ⊢238 graph_domain tp h.
Proof.
  destruct t as [it|[]], tp as [ip|[]], g as [ig|[]], h as [ih|[]], w as [iw|[]].
  intros HE HS HD HX. unfold graph_domain. apply AllI_named.
  intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - apply II. eapply ExE_named; [apply Ctx; now left|].
    intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply DE.
    + apply (graph_extension_cases _ $ig $ih $ip $iw $ix $iy);
        [inherit HX|apply Ctx; now left].
    + apply DI1. apply (raw_successor_member_intro _ $it $ip $ix); [inherit HS|].
      apply (graph_domain_edge _ $it $ig $ix $iy);
        [inherit HD|apply Ctx; now left].
    + eapply DI2, CE1, Ctx. now left.
  - apply II. eapply DE; [apply Ctx; now left| |].
    + eapply DE.
      * apply (raw_successor_member_cases _ $it $ip $ix);
          [inherit HS|apply Ctx; now left].
      * eapply ExE_named.
        -- apply (graph_domain_value _ $it $ig $ix); [inherit HD|].
           apply DI1, Ctx. now left.
        -- intro y. destruct y as [iy|[]].
           cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
           apply (ExI $iy).
           cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
           apply (graph_extension_old_edge _ $ig $ih $ip $iw $ix $iy);
             [inherit HX|apply Ctx; now left].
      * eapply ExE_named.
        -- apply (graph_domain_value _ $it $ig $ix); [inherit HD|].
           apply DI2, Ctx. now left.
        -- intro y. destruct y as [iy|[]].
           cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
           apply (ExI $iy).
           cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
           apply (graph_extension_old_edge _ $ig $ih $ip $iw $ix $iy);
             [inherit HX|apply Ctx; now left].
    + apply (ExI $iw).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (graph_extension_intro _ $ig $ih $ip $iw $ix $iw); [inherit HX|].
      apply DI2, CI; [apply Ctx; now left|inherit (AllE $iw HE)].
Qed.

(** Only the index is fresh. No freshness assumption is placed on the
    output, which may recur when a multiplier is zero. *)
Lemma successor_old_domain_disjoint G t tp x :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 ordinal_representative t -> G ⊢238 raw_successor t tp ->
  G ⊢238 (R t x ∨ E x t) -> G ⊢238 E x tp -> G ⊢238 falsity.
Proof.
  intros HE HQ HEq HEtr HT HS HD Hxp.
  assert (Hpoint : G ⊢238 R tp t).
  { apply (raw_successor_point_member _ t tp); assumption. }
  assert (Hnot : G ⊢238 (¬ R t t)).
  { apply member_ir_not_self. exact (CE2 HT). }
  eapply DE; [exact HD| |].
  - eapply IE; [inherit Hnot|]. apply (transitive_member _ t tp t).
    + inherit (CE1 (CE1 HT)).
    + apply (equality_member_transport _ t x tp).
      * inherit HE.
      * inherit HQ.
      * inherit Hxp.
      * apply Ctx. now left.
    + inherit Hpoint.
  - eapply IE; [inherit Hnot|]. apply (equality_container_transport _ tp t t).
    + inherit HE.
    + inherit HQ.
    + apply (pair_equality_transitivity _ tp x t).
      * inherit HEtr.
      * apply equality_symmetry_instance; [inherit HEq|inherit Hxp].
      * apply Ctx. now left.
    + inherit Hpoint.
Qed.

Lemma graph_old_source_new_equal_false G t tp g x y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 ordinal_representative t -> G ⊢238 raw_successor t tp ->
  G ⊢238 graph_domain t g -> G ⊢238 graph_edge g x y ->
  G ⊢238 E x tp -> G ⊢238 falsity.
Proof.
  intros HE HQ HEq HEtr HT HS HD HY Hxp.
  apply (successor_old_domain_disjoint _ t tp x); try assumption.
  apply (graph_domain_edge _ t g x y); assumption.
Qed.

Theorem graph_extension_functional G t tp g h w :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 ordinal_representative t -> G ⊢238 raw_successor t tp ->
  G ⊢238 graph_domain t g -> G ⊢238 graph_functional g ->
  G ⊢238 graph_edge_extension g h tp w -> G ⊢238 graph_functional h.
Proof.
  destruct t as [it|[]], tp as [ip|[]], g as [ig|[]], h as [ih|[]], w as [iw|[]].
  intros HE HQ HEq HEtr HT HS HD HF HX.
  unfold graph_functional. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  assert (HY : ((graph_edge $ih $ix $iy ∧ graph_edge $ih $ix $iz) :: G)
      ⊢238 (graph_edge $ig $ix $iy ∨ (E $ix $ip ∧ E $iy $iw))).
  { apply (graph_extension_cases _ $ig $ih $ip $iw $ix $iy);
      [inherit HX|eapply CE1, Ctx; now left]. }
  assert (HZ : ((graph_edge $ih $ix $iy ∧ graph_edge $ih $ix $iz) :: G)
      ⊢238 (graph_edge $ig $ix $iz ∨ (E $ix $ip ∧ E $iz $iw))).
  { apply (graph_extension_cases _ $ig $ih $ip $iw $ix $iz);
      [inherit HX|eapply CE2, Ctx; now left]. }
  eapply DE; [exact HY| |].
  - eapply DE; [inherit HZ| |].
    + apply (graph_functional_at _ $ig $ix $iy $iz).
      * inherit HF.
      * apply Ctx. right. now left.
      * apply Ctx. now left.
    + apply Exp. apply (graph_old_source_new_equal_false _ $it $ip $ig $ix $iy).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HEtr.
      * inherit HT.
      * inherit HS.
      * inherit HD.
      * apply Ctx. right. now left.
      * eapply CE1, Ctx. now left.
  - eapply DE; [inherit HZ| |].
    + apply Exp. apply (graph_old_source_new_equal_false _ $it $ip $ig $ix $iz).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HEtr.
      * inherit HT.
      * inherit HS.
      * inherit HD.
      * apply Ctx. now left.
      * eapply CE1, Ctx. right. now left.
    + apply (pair_equality_transitivity _ $iy $iw $iz).
      * inherit HEtr.
      * eapply CE2, Ctx. right. now left.
      * apply equality_symmetry_instance; [inherit HEq|eapply CE2, Ctx; now left].
Qed.

Theorem graph_extension_range G g h a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 graph_range g ->
  G ⊢238 ordinal_representative b -> G ⊢238 graph_edge_extension g h a b ->
  G ⊢238 graph_range h.
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]].
  intros HE HQ HEq HR HB HX. unfold graph_range.
  apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (graph_extension_cases _ $ig $ih $ia $ib $ix $iy);
      [inherit HX|apply Ctx; now left].
  - apply (graph_range_at _ $ig $ix $iy); [inherit HR|apply Ctx; now left].
  - apply (equality_ordinal_representative_transport _ $ib $iy).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + apply equality_symmetry_instance; [inherit HEq|eapply CE2, Ctx; now left].
    + inherit HB.
Qed.

Print Assumptions graph_extension_domain.
Print Assumptions successor_old_domain_disjoint.
Print Assumptions graph_extension_functional.
Print Assumptions graph_extension_range.
Print Assumptions singleton_graph_exists.
Print Assumptions singleton_graph_domain.
Print Assumptions singleton_graph_functional.
Print Assumptions singleton_graph_range.
Print Assumptions equality_ordinal_representative_transport.
Print Assumptions raw_adjunction_exact_graph_extension.
Print Assumptions exact_graph_extension_exists.
End TraceGraph238.
