(** Original finite derivations for the PA-in-S0 ordinal successor.
    The relation R is converse membership.  Equality is ordinary raw
    equality; no extensionality or canonical successor is used. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module OrdinalSuccessor238.

Definition equality_transitivity_ax : set_form :=
  ∀ ∀ ∀ (E $2 $1 → E $1 $0 → E $2 $0).

Lemma equality_transitivity_instance G x y z :
  G ⊢238 equality_transitivity_ax -> G ⊢238 E x y ->
  G ⊢238 E y z -> G ⊢238 E x z.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]]. intros HE Hxy Hyz.
  unfold equality_transitivity_ax in HE.
  pose proof (AllE $iz (AllE $iy (AllE $ix HE))) as H.
  cbn [E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE (IE H Hxy) Hyz).
Qed.

Lemma equality_container_transport G a b z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 E a b -> G ⊢238 R a z -> G ⊢238 R b z.
Proof.
  intros HE HQ Hab Haz. eapply IE; [|exact Haz].
  eapply IE; [|exact Hab]. eapply IE; [|exact (AllE z HE)].
  apply equality_membership_instance. exact HQ.
Qed.

Lemma equality_transitive_transport G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 E a b ->
  G ⊢238 transitive a -> G ⊢238 transitive b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HQ HS Hab HA.
  unfold transitive. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
  apply (equality_container_transport _ $ia $ib $iy).
  - apply weaken_one. exact HE.
  - apply weaken_one. exact HQ.
  - apply weaken_one. exact Hab.
  - apply (transitive_member _ $ia $ix $iy).
    + apply weaken_one. exact HA.
    + apply (equality_container_transport _ $ib $ia $ix).
      * apply weaken_one. exact HE.
      * apply weaken_one. exact HQ.
      * apply equality_symmetry_instance; apply weaken_one; assumption.
      * eapply CE1, Ctx. now left.
    + eapply CE2, Ctx. now left.
Qed.

Lemma raw_successor_member_intro G a b z :
  G ⊢238 raw_successor a b -> G ⊢238 (R a z ∨ E z a) -> G ⊢238 R b z.
Proof.
  destruct a as [ia|[]], b as [ib|[]], z as [iz|[]]. intros HS HZ.
  unfold raw_successor in HS. pose proof (AllE $iz HS) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE (CE2 H) HZ).
Qed.

Lemma raw_successor_old_member G a b z :
  G ⊢238 raw_successor a b -> G ⊢238 R a z -> G ⊢238 R b z.
Proof.
  intros HS HZ. apply (raw_successor_member_intro _ a b z);
    [exact HS|apply DI1; exact HZ].
Qed.

Lemma raw_successor_point_member G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 raw_successor a b -> G ⊢238 R b a.
Proof.
  intros HE HS. apply (raw_successor_member_intro _ a b a);
    [exact HS|apply DI2; exact (AllE a HE)].
Qed.

Lemma raw_successor_old_subset G a b :
  G ⊢238 raw_successor a b -> G ⊢238 subset a b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intro HS.
  unfold subset. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
  apply (raw_successor_old_member _ $ia $ib $iz);
    [apply weaken_one; exact HS|apply Ctx; now left].
Qed.

Lemma raw_successor_transitive G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 transitive a -> G ⊢238 raw_successor a b -> G ⊢238 transitive b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HQ HA HS.
  unfold transitive. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
  apply (raw_successor_old_member _ $ia $ib $iy).
  - apply weaken_one. exact HS.
  - eapply DE.
    + apply (raw_successor_member_cases _ $ia $ib $ix).
      * apply weaken_one. exact HS.
      * eapply CE1, Ctx. now left.
    + apply (transitive_member _ $ia $ix $iy).
      * apply weaken_one, weaken_one. exact HA.
      * apply Ctx. now left.
      * eapply CE2, Ctx. right. now left.
    + apply (equality_container_transport _ $ix $ia $iy).
      * apply weaken_one, weaken_one. exact HE.
      * apply weaken_one, weaken_one. exact HQ.
      * apply Ctx. now left.
      * eapply CE2, Ctx. right. now left.
Qed.

Lemma raw_successor_member_transitive G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 transitive a ->
  G ⊢238 member_transitive a -> G ⊢238 raw_successor a b ->
  G ⊢238 member_transitive b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HQ HEq HA HM HS.
  unfold member_transitive. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_successor_member_cases _ $ia $ib $iz).
    + apply weaken_one. exact HS.
    + apply Ctx. now left.
  - apply (member_transitive_member _ $ia $iz).
    + apply weaken_one, weaken_one. exact HM.
    + apply Ctx. now left.
  - apply (equality_transitive_transport _ $ia $iz).
    + apply weaken_one, weaken_one. exact HE.
    + apply weaken_one, weaken_one. exact HQ.
    + apply weaken_one, weaken_one. exact HEq.
    + apply equality_symmetry_instance.
      * apply weaken_one, weaken_one. exact HEq.
      * apply Ctx. now left.
    + apply weaken_one, weaken_one. exact HA.
Qed.

Lemma raw_successor_member_linear G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 member_linear a -> G ⊢238 raw_successor a b ->
  G ⊢238 member_linear b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HQ HEq HEtr HA HS.
  unfold member_linear. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_successor_member_cases _ $ia $ib $ix).
    + apply weaken_one. exact HS.
    + eapply CE1, Ctx. now left.
  - eapply DE.
    + apply (raw_successor_member_cases _ $ia $ib $iy).
      * apply weaken_one, weaken_one. exact HS.
      * eapply CE2, Ctx. right. now left.
    + apply (linear_member_cases _ $ia $ix $iy).
      * apply weaken_one, weaken_one, weaken_one. exact HA.
      * apply Ctx. right. now left.
      * apply Ctx. now left.
    + apply DI2, DI1. apply (equality_container_transport _ $ia $iy $ix).
      * apply weaken_one, weaken_one, weaken_one. exact HE.
      * apply weaken_one, weaken_one, weaken_one. exact HQ.
      * apply equality_symmetry_instance.
        -- apply weaken_one, weaken_one, weaken_one. exact HEq.
        -- apply Ctx. now left.
      * apply Ctx. right. now left.
  - eapply DE.
    + apply (raw_successor_member_cases _ $ia $ib $iy).
      * apply weaken_one, weaken_one. exact HS.
      * eapply CE2, Ctx. right. now left.
    + apply DI2, DI2. apply (equality_container_transport _ $ia $ix $iy).
      * apply weaken_one, weaken_one, weaken_one. exact HE.
      * apply weaken_one, weaken_one, weaken_one. exact HQ.
      * apply equality_symmetry_instance.
        -- apply weaken_one, weaken_one, weaken_one. exact HEq.
        -- apply Ctx. right. now left.
      * apply Ctx. now left.
    + apply DI1. apply (equality_transitivity_instance _ $ix $ia $iy).
      * apply weaken_one, weaken_one, weaken_one. exact HEtr.
      * apply Ctx. right. now left.
      * apply equality_symmetry_instance.
        -- apply weaken_one, weaken_one, weaken_one. exact HEq.
        -- apply Ctx. now left.
Qed.

(** This is the actual Separation trace used in successor extrema.
    It keeps exactly the old members of s. *)
Definition old_trace (c s a : set_term) : set_form :=
  ∀ (R c`[↑] $0 ↔ (R s`[↑] $0 ∧ R a`[↑] $0)).
Definition intersection_ax : set_form :=
  ∀ ∀ ∃ ∀ (R $1 $0 ↔ (R $2 $0 ∧ R $3 $0)).

Lemma S0_intersection_allowed : finite_set_S0 intersection_ax.
Proof.
  unfold intersection_ax.
  change (finite_set_S0 (forall_times 1 (separation_ax (R $1 $0)))).
  apply (S0_separation (R $1 $0) 1).
  apply separation_instance_closed. unfold R. apply atom2_bounded; lia.
Qed.

Lemma S0_intersection : derivable finite_set_S0 intersection_ax.
Proof. apply derivable_axiom, S0_intersection_allowed. Qed.

Lemma intersection_exists G s a :
  G ⊢238 intersection_ax -> G ⊢238 ∃ old_trace $0 s`[↑] a`[↑].
Proof.
  destruct s as [is|[]], a as [ia|[]]. intro HI.
  unfold intersection_ax in HI. pose proof (AllE $is (AllE $ia HI)) as H.
  cbn [R terms2 subst_form subst_term up scons funcomp] in H.
  exact H.
Qed.

Lemma old_trace_member G c s a z :
  G ⊢238 old_trace c s a -> G ⊢238 R c z -> G ⊢238 (R s z ∧ R a z).
Proof.
  destruct c as [ic|[]], s as [is|[]], a as [ia|[]], z as [iz|[]].
  intros HT HZ. unfold old_trace in HT. pose proof (AllE $iz HT) as H.
  cbn [R terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE (CE1 H) HZ).
Qed.

Lemma old_trace_intro G c s a z :
  G ⊢238 old_trace c s a -> G ⊢238 R s z ->
  G ⊢238 R a z -> G ⊢238 R c z.
Proof.
  destruct c as [ic|[]], s as [is|[]], a as [ia|[]], z as [iz|[]].
  intros HT HS HA. unfold old_trace in HT. pose proof (AllE $iz HT) as H.
  cbn [R terms2 subst_form subst_term up scons funcomp] in H.
  eapply IE; [exact (CE2 H)|]. apply CI; assumption.
Qed.

Lemma old_trace_subset_right G c s a :
  G ⊢238 old_trace c s a -> G ⊢238 subset c a.
Proof.
  destruct c as [ic|[]], s as [is|[]], a as [ia|[]]. intro HT.
  unfold subset. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
  eapply CE2. apply (old_trace_member _ $ic $is $ia $iz).
  - apply weaken_one. exact HT.
  - apply Ctx. now left.
Qed.

Lemma classical_cases G phi : G ⊢238 (phi ∨ ¬ phi).
Proof.
  apply classical_double_negation, II.
  assert (HN : (¬ (phi ∨ ¬ phi) :: G) ⊢238 (¬ phi)).
  { apply II. eapply IE.
    - apply weaken_one, Ctx. now left.
    - apply DI1, Ctx. now left. }
  eapply IE; [apply Ctx; now left|]. apply DI2. exact HN.
Qed.

Lemma not_nonempty_member_false G c z :
  G ⊢238 (¬ nonempty c) -> G ⊢238 R c z -> G ⊢238 falsity.
Proof.
  destruct c as [ic|[]], z as [iz|[]]. intros HN HZ. eapply IE; [exact HN|].
  unfold nonempty. apply (ExI $iz).
  cbn [R terms2 subst_form subst_term up scons funcomp]. exact HZ.
Qed.

Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

(** A least old member remains least after adjoining a.  The newly
    adjoined point is above every old member by converse membership. *)
Lemma successor_trace_least G a b s c m :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 raw_successor a b ->
  G ⊢238 subset s b -> G ⊢238 old_trace c s a ->
  G ⊢238 least c m -> G ⊢238 least s m.
Proof.
  destruct a as [ia|[]], b as [ib|[]], s as [is|[]],
    c as [ic|[]], m as [im|[]]. intros HE HQ HEq HS Hsub HT HM.
  assert (Hsm : G ⊢238 R $is $im).
  { exact (CE1 (old_trace_member _ $ic $is $ia $im HT (CE1 HM))). }
  assert (Ham : G ⊢238 R $ia $im).
  { exact (CE2 (old_trace_member _ $ic $is $ia $im HT (CE1 HM))). }
  unfold least. apply CI; [exact Hsm|].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_successor_member_cases _ $ia $ib $iz).
    + inherit HS.
    + apply (subset_member _ $is $ib $iz); [inherit Hsub|apply Ctx; now left].
  - apply (least_member_cases _ $ic $im $iz); [inherit HM|].
    apply (old_trace_intro _ $ic $is $ia $iz).
    + inherit HT.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
  - apply DI2. apply (equality_container_transport _ $ia $iz $im).
    + inherit HE.
    + inherit HQ.
    + apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
    + inherit Ham.
Qed.

Lemma successor_point_greatest G a b s :
  G ⊢238 raw_successor a b -> G ⊢238 subset s b ->
  G ⊢238 R s a -> G ⊢238 greatest s a.
Proof.
  destruct a as [ia|[]], b as [ib|[]], s as [is|[]]. intros HS Hsub HA.
  unfold greatest. apply CI; [exact HA|].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply II.
  apply disjunction_swap. apply (raw_successor_member_cases _ $ia $ib $iz).
  - inherit HS.
  - apply (subset_member _ $is $ib $iz); [inherit Hsub|apply Ctx; now left].
Qed.

Lemma successor_trace_greatest G a b s c m :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 raw_successor a b -> G ⊢238 subset s b ->
  G ⊢238 old_trace c s a -> G ⊢238 (¬ R s a) ->
  G ⊢238 greatest c m -> G ⊢238 greatest s m.
Proof.
  destruct a as [ia|[]], b as [ib|[]], s as [is|[]],
    c as [ic|[]], m as [im|[]]. intros HE HQ HS Hsub HT Hna HM.
  unfold greatest. apply CI.
  - exact (CE1 (old_trace_member _ $ic $is $ia $im HT (CE1 HM))).
  - apply AllI_named. intro z. destruct z as [iz|[]].
    cbn [R E terms2 subst_form subst_term up scons funcomp]. apply II.
    eapply DE.
    + apply (raw_successor_member_cases _ $ia $ib $iz).
      * inherit HS.
      * apply (subset_member _ $is $ib $iz); [inherit Hsub|apply Ctx; now left].
    + apply (greatest_member_cases _ $ic $im $iz); [inherit HM|].
      apply (old_trace_intro _ $ic $is $ia $iz).
      * inherit HT.
      * apply Ctx. right. now left.
      * apply Ctx. now left.
    + apply Exp. eapply IE; [inherit Hna|].
      apply (equality_member_transport _ $is $iz $ia).
      * inherit HE.
      * inherit HQ.
      * apply Ctx. now left.
      * apply Ctx. right. now left.
Qed.

(** If the actual old trace is empty, a nonempty subset of the successor
    contains the adjoined point; this produces its extrema directly. *)
Lemma empty_successor_trace_point G a b s c :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 raw_successor a b -> G ⊢238 subset s b ->
  G ⊢238 nonempty s -> G ⊢238 old_trace c s a ->
  G ⊢238 (¬ nonempty c) -> G ⊢238 R s a.
Proof.
  destruct a as [ia|[]], b as [ib|[]], s as [is|[]], c as [ic|[]].
  intros HE HQ HS Hsub Hne HT Hnc.
  eapply ExE_named; [exact Hne|]. intro z. destruct z as [iz|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. eapply DE.
  - apply (raw_successor_member_cases _ $ia $ib $iz).
    + inherit HS.
    + apply (subset_member _ $is $ib $iz); [inherit Hsub|apply Ctx; now left].
  - apply Exp. apply (not_nonempty_member_false _ $ic $iz); [inherit Hnc|].
    apply (old_trace_intro _ $ic $is $ia $iz).
    + inherit HT.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
  - apply (equality_member_transport _ $is $iz $ia).
    + inherit HE.
    + inherit HQ.
    + apply Ctx. now left.
    + apply Ctx. right. now left.
Qed.

Lemma empty_successor_trace_least G a b s c :
  G ⊢238 equality_symmetry_ax -> G ⊢238 raw_successor a b ->
  G ⊢238 subset s b -> G ⊢238 R s a ->
  G ⊢238 old_trace c s a -> G ⊢238 (¬ nonempty c) -> G ⊢238 least s a.
Proof.
  destruct a as [ia|[]], b as [ib|[]], s as [is|[]], c as [ic|[]].
  intros HEq HS Hsub HA HT Hnc. unfold least. apply CI; [exact HA|].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_successor_member_cases _ $ia $ib $iz).
    + inherit HS.
    + apply (subset_member _ $is $ib $iz); [inherit Hsub|apply Ctx; now left].
  - apply Exp. apply (not_nonempty_member_false _ $ic $iz); [inherit Hnc|].
    apply (old_trace_intro _ $ic $is $ia $iz).
    + inherit HT.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
  - apply DI1, equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
Qed.

(** Package the actual finite witness construction.  The positive trace
    case uses the old ordinal's internal extrema; the empty trace case uses
    its forced adjoined point. *)
Theorem successor_trace_extrema G a b s c :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 ordinal_representative a ->
  G ⊢238 raw_successor a b -> G ⊢238 subset s b ->
  G ⊢238 nonempty s -> G ⊢238 old_trace c s a ->
  G ⊢238 ((∃ least s`[↑] $0) ∧ (∃ greatest s`[↑] $0)).
Proof.
  destruct a as [ia|[]], b as [ib|[]], s as [is|[]], c as [ic|[]].
  intros HE HQ HEq HR HS Hsub Hne HT.
  eapply DE; [apply (classical_cases G (nonempty $ic))| |].
  - assert (HX : (nonempty $ic :: G) ⊢238
        ((∃ least $ic`[↑] $0) ∧ (∃ greatest $ic`[↑] $0))).
    { apply (ordinal_internal_extrema _ $ia $ic).
      - inherit HR.
      - apply (old_trace_subset_right _ $ic $is $ia). inherit HT.
      - apply Ctx. now left. }
    apply CI.
    + eapply ExE_named; [exact (CE1 HX)|]. intro m. destruct m as [im|[]].
      cbn [R E terms2 subst_form subst_term up scons funcomp].
      apply (ExI $im).
      cbn [R E terms2 subst_form subst_term up scons funcomp].
      apply (successor_trace_least _ $ia $ib $is $ic $im).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HS.
      * inherit Hsub.
      * inherit HT.
      * apply Ctx. now left.
    + eapply DE; [apply (classical_cases _ (R $is $ia))| |].
      * apply (ExI $ia).
        cbn [R E terms2 subst_form subst_term up scons funcomp].
        apply (successor_point_greatest _ $ia $ib $is).
        -- inherit HS.
        -- inherit Hsub.
        -- apply Ctx. now left.
      * eapply ExE_named; [apply weaken_one; exact (CE2 HX)|]. intro m. destruct m as [im|[]].
        cbn [R E terms2 subst_form subst_term up scons funcomp].
        apply (ExI $im).
        cbn [R E terms2 subst_form subst_term up scons funcomp].
        apply (successor_trace_greatest _ $ia $ib $is $ic $im).
        -- inherit HE.
        -- inherit HQ.
        -- inherit HS.
        -- inherit Hsub.
        -- inherit HT.
        -- apply Ctx. right. now left.
        -- apply Ctx. now left.
  - assert (HP : (¬ nonempty $ic :: G) ⊢238 R $is $ia).
    { apply (empty_successor_trace_point _ $ia $ib $is $ic).
      - inherit HE.
      - inherit HQ.
      - inherit HS.
      - inherit Hsub.
      - inherit Hne.
      - inherit HT.
      - apply Ctx. now left. }
    apply CI.
    + apply (ExI $ia).
      cbn [R E terms2 subst_form subst_term up scons funcomp].
      apply (empty_successor_trace_least _ $ia $ib $is $ic).
      * inherit HEq.
      * inherit HS.
      * inherit Hsub.
      * exact HP.
      * inherit HT.
      * apply Ctx. now left.
    + apply (ExI $ia).
      cbn [R E terms2 subst_form subst_term up scons funcomp].
      apply (successor_point_greatest _ $ia $ib $is).
      * inherit HS.
      * inherit Hsub.
      * exact HP.
Qed.

Theorem raw_successor_internal_extrema G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 intersection_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 raw_successor a b ->
  G ⊢238 internal_extrema b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HE HQ HEq HI HR HS.
  unfold internal_extrema. apply AllI_named. intro s. destruct s as [is|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply II.
  eapply ExE_named.
  - apply (intersection_exists _ $is $ia). inherit HI.
  - intro c. destruct c as [ic|[]].
    cbn [R E terms2 subst_form subst_term up scons funcomp].
    apply (successor_trace_extrema _ $ia $ib $is $ic).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HR.
    + inherit HS.
    + eapply CE1, Ctx. right. now left.
    + eapply CE2, Ctx. right. now left.
    + apply Ctx. now left.
Qed.

(** All five domain components are constructed.  The only set-existence
    premise beyond the raw successor is the displayed closed Separation
    instance; S0 itself supplies that premise below. *)
Theorem raw_successor_ordinal_representative G a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 intersection_ax -> G ⊢238 ordinal_representative a ->
  G ⊢238 raw_successor a b -> G ⊢238 ordinal_representative b.
Proof.
  intros HE HQ HEq HEtr HI HR HS. unfold ordinal_representative. apply CI.
  - unfold representative. apply CI.
    + apply (raw_successor_transitive _ a b); [exact HE|exact HQ| |exact HS].
      exact (CE1 (CE1 HR)).
    + apply CI.
      * apply (raw_successor_member_transitive _ a b);
          [exact HE|exact HQ|exact HEq| | |exact HS].
        -- exact (CE1 (CE1 HR)).
        -- exact (CE1 (CE2 (CE1 HR))).
      * apply CI.
        -- apply (raw_successor_member_linear _ a b);
             [exact HE|exact HQ|exact HEq|exact HEtr| |exact HS].
           exact (CE1 (CE2 (CE2 (CE1 HR)))).
        -- apply (raw_successor_internal_extrema _ a b); assumption.
  - apply (raw_successor_member_ir _ a b); [exact HQ|exact (CE2 HR)|exact HS].
Qed.

Lemma ordinal_successor_exists G a :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 intersection_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 ordinal_representative a ->
  G ⊢238 ∃ (ordinal_representative $0 ∧ raw_successor a`[↑] $0).
Proof.
  destruct a as [ia|[]]. intros HE HQ HEq HEtr HI HA HR.
  eapply ExE_named; [exact (adjunction_raw_successor G $ia HA)|].
  intro b. destruct b as [ib|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  apply (ExI $ib).
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply CI.
  - apply (raw_successor_ordinal_representative _ $ia $ib).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit HI.
    + inherit HR.
    + apply Ctx. now left.
  - apply Ctx. now left.
Qed.

Theorem S0_ordinal_successor_exists a :
  derivable finite_set_S0
    (ordinal_representative a →
      ∃ (ordinal_representative $0 ∧ raw_successor a`[↑] $0)).
Proof.
  set (G := equality_base ++ [adjunction_ax; intersection_ax]).
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
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi.
    apply in_app_or in Hpsi as [Hpsi|[<-|[<-|[]]]].
    + apply S0_base. apply in_or_app. now left.
    + apply S0_base. apply in_or_app. right. now left.
    + apply S0_intersection_allowed.
  - apply II, ordinal_successor_exists.
    + apply weaken_one. exact HE.
    + apply weaken_one. exact HQ.
    + apply weaken_one. exact HEq.
    + apply weaken_one. exact HEtr.
    + apply weaken_one. exact HI.
    + apply weaken_one. exact HA.
    + apply Ctx. now left.
Qed.

Print Assumptions raw_successor_ordinal_representative.
Print Assumptions S0_ordinal_successor_exists.
Print Assumptions S0_intersection.
Print Assumptions successor_trace_least.
Print Assumptions successor_trace_greatest.
Print Assumptions empty_successor_trace_point.
Print Assumptions raw_successor_transitive.
Print Assumptions raw_successor_member_transitive.
Print Assumptions raw_successor_member_linear.
End OrdinalSuccessor238.
