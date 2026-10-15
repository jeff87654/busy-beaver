(** Original finite graph-entry constructors for the PA-in-S0 bridge.
    Each witness is built by finite Adjunction from an actual empty set.
    No canonical pair object, Extensionality, or Replacement is used. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PairGraph238.

Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition raw_adjunction (a x b : set_term) : set_form :=
  ∀ (R b`[↑] $0 ↔ (R a`[↑] $0 ∨ E $0 x`[↑])).
Definition raw_singleton (a s : set_term) : set_form :=
  ∀ (R s`[↑] $0 ↔ E $0 a`[↑]).
Definition raw_pair (a b p : set_term) : set_form :=
  ∀ (R p`[↑] $0 ↔ (E $0 a`[↑] ∨ E $0 b`[↑])).
Definition raw_kuratowski (p a b : set_term) : set_form :=
  ∃ ∃ (raw_singleton a`[↑]`[↑] $1 ∧
    (raw_pair a`[↑]`[↑] b`[↑]`[↑] $0 ∧ raw_pair $1 $0 p`[↑]`[↑])).

Lemma raw_adjunction_exists G a x :
  G ⊢238 adjunction_ax -> G ⊢238 ∃ raw_adjunction a`[↑] x`[↑] $0.
Proof.
  destruct a as [ia|[]], x as [ix|[]]. intro HA.
  unfold adjunction_ax in HA. pose proof (AllE $ix (AllE $ia HA)) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H. exact H.
Qed.

Lemma raw_adjunction_member G a x b z :
  G ⊢238 raw_adjunction a x b -> G ⊢238 R b z ->
  G ⊢238 (R a z ∨ E z x).
Proof.
  destruct a as [ia|[]], x as [ix|[]], b as [ib|[]], z as [iz|[]].
  intros HA HZ. unfold raw_adjunction in HA. pose proof (AllE $iz HA) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE (CE1 H) HZ).
Qed.

Lemma raw_adjunction_intro G a x b z :
  G ⊢238 raw_adjunction a x b -> G ⊢238 (R a z ∨ E z x) -> G ⊢238 R b z.
Proof.
  destruct a as [ia|[]], x as [ix|[]], b as [ib|[]], z as [iz|[]].
  intros HA HZ. unfold raw_adjunction in HA. pose proof (AllE $iz HA) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE (CE2 H) HZ).
Qed.

Lemma raw_singleton_member G a s z :
  G ⊢238 raw_singleton a s -> G ⊢238 R s z -> G ⊢238 E z a.
Proof.
  destruct a as [ia|[]], s as [is|[]], z as [iz|[]]. intros HS HZ.
  unfold raw_singleton in HS. pose proof (AllE $iz HS) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE (CE1 H) HZ).
Qed.

Lemma raw_singleton_intro G a s z :
  G ⊢238 raw_singleton a s -> G ⊢238 E z a -> G ⊢238 R s z.
Proof.
  destruct a as [ia|[]], s as [is|[]], z as [iz|[]]. intros HS HZ.
  unfold raw_singleton in HS. pose proof (AllE $iz HS) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE (CE2 H) HZ).
Qed.

Lemma raw_singleton_from_adjunction G e a s :
  G ⊢238 raw_zero e -> G ⊢238 raw_adjunction e a s -> G ⊢238 raw_singleton a s.
Proof.
  destruct e as [ie|[]], a as [ia|[]], s as [is|[]]. intros HE HA.
  unfold raw_singleton. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply CI.
  - apply II. eapply DE.
    + apply (raw_adjunction_member _ $ie $ia $is $iz);
        [inherit HA|apply Ctx; now left].
    + apply Exp. eapply IE.
      * inherit (zero_excludes_member G $ie $iz HE).
      * apply Ctx. now left.
    + apply Ctx. now left.
  - apply II. apply (raw_adjunction_intro _ $ie $ia $is $iz).
    + inherit HA.
    + apply DI2, Ctx. now left.
Qed.

Lemma raw_singleton_exists G e a :
  G ⊢238 raw_zero e -> G ⊢238 adjunction_ax ->
  G ⊢238 ∃ raw_singleton a`[↑] $0.
Proof.
  destruct e as [ie|[]], a as [ia|[]]. intros HE HA.
  eapply ExE_named; [exact (raw_adjunction_exists G $ie $ia HA)|].
  intro s. destruct s as [is|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply (ExI $is).
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  apply (raw_singleton_from_adjunction _ $ie $ia $is);
    [inherit HE|apply Ctx; now left].
Qed.

Lemma raw_pair_from_adjunction G a b s p :
  G ⊢238 raw_singleton a s -> G ⊢238 raw_adjunction s b p -> G ⊢238 raw_pair a b p.
Proof.
  destruct a as [ia|[]], b as [ib|[]], s as [is|[]], p as [ip|[]].
  intros HS HA. unfold raw_pair. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply CI.
  - apply II. eapply DE.
    + apply (raw_adjunction_member _ $is $ib $ip $iz);
        [inherit HA|apply Ctx; now left].
    + apply DI1. apply (raw_singleton_member _ $ia $is $iz);
        [inherit HS|apply Ctx; now left].
    + apply DI2, Ctx. now left.
  - apply II. apply (raw_adjunction_intro _ $is $ib $ip $iz); [inherit HA|].
    eapply DE; [apply Ctx; now left| |].
    + apply DI1. apply (raw_singleton_intro _ $ia $is $iz);
        [inherit HS|apply Ctx; now left].
    + apply DI2, Ctx. now left.
Qed.

Lemma raw_pair_exists G e a b :
  G ⊢238 raw_zero e -> G ⊢238 adjunction_ax ->
  G ⊢238 ∃ raw_pair a`[↑] b`[↑] $0.
Proof.
  destruct e as [ie|[]], a as [ia|[]], b as [ib|[]]. intros HE HA.
  eapply ExE_named; [exact (raw_singleton_exists G $ie $ia HE HA)|].
  intro s. destruct s as [is|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  eapply ExE_named.
  - apply (raw_adjunction_exists _ $is $ib). inherit HA.
  - intro p. destruct p as [ip|[]].
    cbn [R E terms2 subst_form subst_term up scons funcomp]. apply (ExI $ip).
    cbn [R E terms2 subst_form subst_term up scons funcomp].
    apply (raw_pair_from_adjunction _ $ia $ib $is $ip).
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Lemma raw_kuratowski_from_witnesses G p a b s t :
  G ⊢238 raw_singleton a s -> G ⊢238 raw_pair a b t ->
  G ⊢238 raw_pair s t p -> G ⊢238 raw_kuratowski p a b.
Proof.
  destruct p as [ip|[]], a as [ia|[]], b as [ib|[]], s as [is|[]], t as [it|[]].
  intros HS HT HP. unfold raw_kuratowski. apply (ExI $is).
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply (ExI $it).
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  apply CI; [exact HS|]. apply CI; assumption.
Qed.

Lemma raw_kuratowski_exists G e a b :
  G ⊢238 raw_zero e -> G ⊢238 adjunction_ax ->
  G ⊢238 ∃ raw_kuratowski $0 a`[↑] b`[↑].
Proof.
  destruct e as [ie|[]], a as [ia|[]], b as [ib|[]]. intros HE HA.
  eapply ExE_named; [exact (raw_singleton_exists G $ie $ia HE HA)|].
  intro s. destruct s as [is|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  eapply ExE_named.
  - apply (raw_pair_exists _ $ie $ia $ib); [inherit HE|inherit HA].
  - intro t. destruct t as [it|[]].
    cbn [R E terms2 subst_form subst_term up scons funcomp]. eapply ExE_named.
    + apply (raw_pair_exists _ $ie $is $it); [inherit HE|inherit HA].
    + intro p. destruct p as [ip|[]].
      cbn [R E terms2 subst_form subst_term up scons funcomp]. apply (ExI $ip).
      cbn [R E terms2 subst_form subst_term up scons funcomp].
      apply (raw_kuratowski_from_witnesses _ $ip $ia $ib $is $it).
      * apply Ctx. right. right. now left.
      * apply Ctx. right. now left.
      * apply Ctx. now left.
Qed.

Theorem S0_raw_kuratowski_exists a b :
  derivable finite_set_S0 (∃ raw_kuratowski $0 a`[↑] b`[↑]).
Proof.
  destruct S0_empty as [G [HG HE]]. exists (adjunction_ax :: G). split.
  - intros psi [<-|Hpsi].
    + apply S0_base. apply in_or_app. right. now left.
    + now apply HG.
  - eapply ExE_named; [apply weaken_one; exact HE|]. intro e. destruct e as [ie|[]].
    cbn [R terms2 subst_form subst_term up scons funcomp].
    apply (raw_kuratowski_exists _ $ie a b).
    + apply Ctx. now left.
    + apply Ctx. right. now left.
Qed.

Lemma pair_container_transport G a b z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 E a b -> G ⊢238 R a z -> G ⊢238 R b z.
Proof.
  intros HE HQ Hab Haz. eapply IE; [|exact Haz].
  eapply IE; [|exact Hab]. eapply IE; [|exact (AllE z HE)].
  apply equality_membership_instance. exact HQ.
Qed.

Lemma raw_pair_member G a b p z :
  G ⊢238 raw_pair a b p -> G ⊢238 R p z -> G ⊢238 (E z a ∨ E z b).
Proof.
  destruct a as [ia|[]], b as [ib|[]], p as [ip|[]], z as [iz|[]].
  intros HP HZ. unfold raw_pair in HP. pose proof (AllE $iz HP) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE (CE1 H) HZ).
Qed.

Lemma raw_pair_intro G a b p z :
  G ⊢238 raw_pair a b p -> G ⊢238 (E z a ∨ E z b) -> G ⊢238 R p z.
Proof.
  destruct a as [ia|[]], b as [ib|[]], p as [ip|[]], z as [iz|[]].
  intros HP HZ. unfold raw_pair in HP. pose proof (AllE $iz HP) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE (CE2 H) HZ).
Qed.

Lemma raw_pair_first G a b p :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 raw_pair a b p -> G ⊢238 R p a.
Proof.
  intros HE HP. apply (raw_pair_intro _ a b p a);
    [exact HP|apply DI1; exact (AllE a HE)].
Qed.

Lemma raw_pair_second G a b p :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 raw_pair a b p -> G ⊢238 R p b.
Proof.
  intros HE HP. apply (raw_pair_intro _ a b p b);
    [exact HP|apply DI2; exact (AllE b HE)].
Qed.

(** A shared Kuratowski object determines its first coordinate even when
    all singleton and unordered-pair objects are noncanonical. *)
Lemma kuratowski_first_witness_unique G p a a' b' s t s' t' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 raw_singleton a s ->
  G ⊢238 raw_pair s t p -> G ⊢238 raw_singleton a' s' ->
  G ⊢238 raw_pair a' b' t' -> G ⊢238 raw_pair s' t' p -> G ⊢238 E a a'.
Proof.
  intros HE HQ HEq HS HP HS' HT' HP'.
  apply (equality_symmetry_instance _ a' a); [exact HEq|].
  apply (raw_singleton_member _ a s a'); [exact HS|].
  eapply DE.
  - apply (raw_pair_member _ s' t' p s); [exact HP'|].
    apply (raw_pair_first _ s t p); assumption.
  - apply (pair_container_transport _ s' s a').
    + inherit HE.
    + inherit HQ.
    + apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
    + apply (raw_singleton_intro _ a' s' a'); [inherit HS'|].
      inherit (AllE a' HE).
  - apply (pair_container_transport _ t' s a').
    + inherit HE.
    + inherit HQ.
    + apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
    + apply (raw_pair_first _ a' b' t'); [inherit HE|inherit HT'].
Qed.

Definition pair_equality_transitivity_ax : set_form :=
  ∀ ∀ ∀ (E $2 $1 → E $1 $0 → E $2 $0).

Lemma pair_equality_transitivity G x y z :
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 E x y ->
  G ⊢238 E y z -> G ⊢238 E x z.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]]. intros HE Hxy Hyz.
  unfold pair_equality_transitivity_ax in HE.
  pose proof (AllE $iz (AllE $iy (AllE $ix HE))) as H.
  cbn [E terms2 subst_form subst_term up scons funcomp] in H.
  exact (IE (IE H Hxy) Hyz).
Qed.

Lemma raw_pair_singleton_second G a b t c s :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 E t s -> G ⊢238 raw_pair a b t ->
  G ⊢238 raw_singleton c s -> G ⊢238 E b c.
Proof.
  intros HE HQ Hts HT HS. apply (raw_singleton_member _ c s b); [exact HS|].
  apply (pair_container_transport _ t s b); [exact HE|exact HQ|exact Hts|].
  apply (raw_pair_second _ a b t); assumption.
Qed.

(** Cancellation of a common first member is proved by the actual two
    membership cases, including the collapsed singleton case. *)
Lemma raw_pair_cancel G a b t a' b' t' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 E a a' -> G ⊢238 E t t' ->
  G ⊢238 raw_pair a b t -> G ⊢238 raw_pair a' b' t' -> G ⊢238 E b b'.
Proof.
  intros HE HQ HEq HEtr Haa Htt HT HT'.
  eapply DE.
  - apply (raw_pair_member _ a' b' t' b); [exact HT'|].
    apply (pair_container_transport _ t t' b); [exact HE|exact HQ|exact Htt|].
    apply (raw_pair_second _ a b t); assumption.
  - assert (Hba : (E b a' :: G) ⊢238 E b a).
    { apply (pair_equality_transitivity _ b a' a).
      - inherit HEtr.
      - apply Ctx. now left.
      - apply equality_symmetry_instance; [inherit HEq|inherit Haa]. }
    eapply DE.
    + apply (raw_pair_member _ a b t b'); [inherit HT|].
      apply (pair_container_transport _ t' t b').
      * inherit HE.
      * inherit HQ.
      * apply equality_symmetry_instance; [inherit HEq|inherit Htt].
      * apply (raw_pair_second _ a' b' t'); [inherit HE|inherit HT'].
    + apply (pair_equality_transitivity _ b a b').
      * inherit HEtr.
      * apply weaken_one. exact Hba.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
    + apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
  - apply Ctx. now left.
Qed.

Lemma kuratowski_second_witness_unique G p a b a' b' s t s' t' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 E a a' -> G ⊢238 raw_singleton a s ->
  G ⊢238 raw_pair a b t -> G ⊢238 raw_pair s t p ->
  G ⊢238 raw_singleton a' s' -> G ⊢238 raw_pair a' b' t' ->
  G ⊢238 raw_pair s' t' p -> G ⊢238 E b b'.
Proof.
  intros HE HQ HEq HEtr Haa HS HT HP HS' HT' HP'.
  eapply DE.
  - apply (raw_pair_member _ s' t' p t); [exact HP'|].
    apply (raw_pair_second _ s t p); assumption.
  - assert (Hba' : (E t s' :: G) ⊢238 E b a').
    { apply (raw_pair_singleton_second _ a b t a' s').
      - inherit HE.
      - inherit HQ.
      - apply Ctx. now left.
      - inherit HT.
      - inherit HS'. }
    assert (Hab : (E t s' :: G) ⊢238 E a b).
    { apply (pair_equality_transitivity _ a a' b).
      - inherit HEtr.
      - inherit Haa.
      - apply equality_symmetry_instance; [inherit HEq|exact Hba']. }
    eapply DE.
    + apply (raw_pair_member _ s t p t'); [inherit HP|].
      apply (raw_pair_second _ s' t' p); [inherit HE|inherit HP'].
    + apply equality_symmetry_instance; [inherit HEq|].
      apply (pair_equality_transitivity _ b' a b).
      * inherit HEtr.
      * apply (raw_pair_singleton_second _ a' b' t' a s).
        -- inherit HE.
        -- inherit HQ.
        -- apply Ctx. now left.
        -- inherit HT'.
        -- inherit HS.
      * apply weaken_one. exact Hab.
    + eapply DE.
      * apply (raw_pair_member _ a b t b'); [inherit HT|].
        apply (pair_container_transport _ t' t b').
        -- inherit HE.
        -- inherit HQ.
        -- apply Ctx. now left.
        -- apply (raw_pair_second _ a' b' t'); [inherit HE|inherit HT'].
      * apply equality_symmetry_instance; [inherit HEq|].
        apply (pair_equality_transitivity _ b' a b).
        -- inherit HEtr.
        -- apply Ctx. now left.
        -- apply weaken_one, weaken_one. exact Hab.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
  - apply (raw_pair_cancel _ a b t a' b' t').
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Haa.
    + apply Ctx. now left.
    + inherit HT.
    + inherit HT'.
Qed.

Lemma kuratowski_witness_unique G p a b a' b' s t s' t' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 raw_singleton a s -> G ⊢238 raw_pair a b t -> G ⊢238 raw_pair s t p ->
  G ⊢238 raw_singleton a' s' -> G ⊢238 raw_pair a' b' t' ->
  G ⊢238 raw_pair s' t' p -> G ⊢238 (E a a' ∧ E b b').
Proof.
  intros HE HQ HEq HEtr HS HT HP HS' HT' HP'.
  assert (Hfirst : G ⊢238 E a a').
  { apply (kuratowski_first_witness_unique _ p a a' b' s t s' t'); assumption. }
  apply CI; [exact Hfirst|].
  apply (kuratowski_second_witness_unique _ p a b a' b' s t s' t'); assumption.
Qed.

Theorem raw_kuratowski_unique G p a b a' b' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 raw_kuratowski p a b ->
  G ⊢238 raw_kuratowski p a' b' -> G ⊢238 (E a a' ∧ E b b').
Proof.
  destruct p as [ip|[]], a as [ia|[]], b as [ib|[]], a' as [ia'|[]], b' as [ib'|[]].
  intros HE HQ HEq HEtr HP HP'. unfold raw_kuratowski in HP, HP'.
  eapply ExE_named; [exact HP|]. intro s. destruct s as [is|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro t. destruct t as [it|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  assert (HS : (raw_singleton $ia $is ∧
      (raw_pair $ia $ib $it ∧ raw_pair $is $it $ip) ::
      (∃ (raw_singleton $ia`[↑] $is`[↑] ∧
        (raw_pair $ia`[↑] $ib`[↑] $0 ∧ raw_pair $is`[↑] $0 $ip`[↑]))) :: G)
      ⊢238 raw_singleton $ia $is).
  { eapply CE1, Ctx. now left. }
  assert (Houter : (raw_singleton $ia $is ∧
      (raw_pair $ia $ib $it ∧ raw_pair $is $it $ip) ::
      (∃ (raw_singleton $ia`[↑] $is`[↑] ∧
        (raw_pair $ia`[↑] $ib`[↑] $0 ∧ raw_pair $is`[↑] $0 $ip`[↑]))) :: G)
      ⊢238 raw_pair $is $it $ip).
  { eapply CE2, CE2, Ctx. now left. }
  assert (HT : (raw_singleton $ia $is ∧
      (raw_pair $ia $ib $it ∧ raw_pair $is $it $ip) ::
      (∃ (raw_singleton $ia`[↑] $is`[↑] ∧
        (raw_pair $ia`[↑] $ib`[↑] $0 ∧ raw_pair $is`[↑] $0 $ip`[↑]))) :: G)
      ⊢238 raw_pair $ia $ib $it).
  { eapply CE1, CE2, Ctx. now left. }
  eapply ExE_named; [inherit HP'|]. intro s'. destruct s' as [is'|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  eapply ExE_named; [apply Ctx; now left|]. intro t'. destruct t' as [it'|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  apply (kuratowski_witness_unique _ $ip $ia $ib $ia' $ib' $is $it $is' $it').
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HEtr.
  - inherit HS.
  - inherit HT.
  - inherit Houter.
  - eapply CE1, Ctx. now left.
  - eapply CE1, CE2, Ctx. now left.
  - eapply CE2, CE2, Ctx. now left.
Qed.

Theorem raw_kuratowski_first_unique G p a b a' b' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 raw_kuratowski p a b -> G ⊢238 raw_kuratowski p a' b' -> G ⊢238 E a a'.
Proof.
  intros HE HQ HEq HEtr HP HP'.
  exact (CE1 (raw_kuratowski_unique G p a b a' b' HE HQ HEq HEtr HP HP')).
Qed.

(** A graph is an actual source set of Kuratowski entries.  This edge
    relation permits every noncanonical encoding that the set contains. *)
Definition graph_edge (g a b : set_term) : set_form :=
  ∃ (R g`[↑] $0 ∧ raw_kuratowski $0 a`[↑] b`[↑]).
Definition graph_inclusion (g h : set_term) : set_form :=
  ∀ ∀ (graph_edge g`[↑]`[↑] $1 $0 → graph_edge h`[↑]`[↑] $1 $0).

Lemma graph_edge_from_entry G g a b p :
  G ⊢238 R g p -> G ⊢238 raw_kuratowski p a b -> G ⊢238 graph_edge g a b.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]], p as [ip|[]].
  intros HM HP. unfold graph_edge. apply (ExI $ip).
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply CI; assumption.
Qed.

Lemma raw_adjunction_graph_inclusion G g p h :
  G ⊢238 raw_adjunction g p h -> G ⊢238 graph_inclusion g h.
Proof.
  destruct g as [ig|[]], p as [ip|[]], h as [ih|[]]. intro HA.
  unfold graph_inclusion. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp]. apply II.
  eapply ExE_named; [apply Ctx; now left|]. intro q. destruct q as [iq|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  apply (graph_edge_from_entry _ $ih $ix $iy $iq).
  - apply (raw_adjunction_intro _ $ig $ip $ih $iq); [inherit HA|].
    eapply DI1, CE1, Ctx. now left.
  - eapply CE2, Ctx. now left.
Qed.

Lemma graph_extension_exists G g a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 empty_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 ∃ (graph_edge $0 a`[↑] b`[↑] ∧ graph_inclusion g`[↑] $0).
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]]. intros HE Hempty HA.
  eapply ExE_named; [exact Hempty|]. intro e. destruct e as [ie|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  eapply ExE_named.
  - apply (raw_kuratowski_exists _ $ie $ia $ib).
    + apply Ctx. now left.
    + inherit HA.
  - intro p. destruct p as [ip|[]].
    cbn [R E terms2 subst_form subst_term up scons funcomp].
    eapply ExE_named.
    + apply (raw_adjunction_exists _ $ig $ip). inherit HA.
    + intro h. destruct h as [ih|[]].
      cbn [R E terms2 subst_form subst_term up scons funcomp]. apply (ExI $ih).
      cbn [R E terms2 subst_form subst_term up scons funcomp]. apply CI.
      * apply (graph_edge_from_entry _ $ih $ia $ib $ip).
        -- apply (raw_adjunction_intro _ $ig $ip $ih $ip).
           ++ apply Ctx. now left.
           ++ apply DI2. inherit (AllE $ip HE).
        -- apply Ctx. right. now left.
      * apply (raw_adjunction_graph_inclusion _ $ig $ip $ih), Ctx. now left.
Qed.

Theorem S0_graph_extension_exists g a b :
  derivable finite_set_S0
    (∃ (graph_edge $0 a`[↑] b`[↑] ∧ graph_inclusion g`[↑] $0)).
Proof.
  destruct S0_empty as [G [HG Hempty]].
  exists ((∀ E $0 $0) :: adjunction_ax :: G). split.
  - intros psi [<-|[<-|Hpsi]].
    + apply S0_base. apply in_or_app. left. now left.
    + apply S0_base. apply in_or_app. right. now left.
    + now apply HG.
  - apply (graph_extension_exists _ g a b).
    + apply Ctx. now left.
    + apply weaken_one, weaken_one. exact Hempty.
    + apply Ctx. right. now left.
Qed.

Print Assumptions S0_graph_extension_exists.
Print Assumptions raw_kuratowski_unique.
Print Assumptions raw_kuratowski_first_unique.
Print Assumptions raw_kuratowski_exists.
Print Assumptions S0_raw_kuratowski_exists.
End PairGraph238.
