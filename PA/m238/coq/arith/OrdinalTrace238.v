(** Original finite R9 minimum-counterexample derivation for S0.
    An actual raw successor contains the supposed bad number; Separation
    constructs its bad trace; the containing ordinal supplies a least bad
    member.  Every property parameter and nested binder is retained. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module OrdinalTrace238.

Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma bad_trace_property_specialize (phi : set_form) (c : set_term) :
  (phi[up ↑])[up (c..)] = phi.
Proof.
  destruct c as [ic|[]]. rewrite subst_comp.
  transitivity (phi[var]); [|apply subst_var].
  apply subst_ext. intros [|k];
    cbn [up scons funcomp subst_term]; reflexivity.
Qed.

Lemma bad_trace_witness_specialize (phi : set_form) (c s : set_term) :
  (bad_trace $0 s`[↑] (phi[up ↑]))[c..] = bad_trace c s phi.
Proof.
  destruct c as [ic|[]], s as [is|[]].
  change
    ((∀ (R $(S ic) $0 ↔
      (R $(S is) $0 ∧ ¬ ((phi[up ↑])[up ($ic..)])))) =
     (∀ (R $(S ic) $0 ↔ (R $(S is) $0 ∧ ¬ phi)))).
  rewrite bad_trace_property_specialize. reflexivity.
Qed.

Lemma bad_trace_member_inside G c s phi z :
  G ⊢238 bad_trace c s phi -> G ⊢238 R c z -> G ⊢238 R s z.
Proof.
  destruct c as [ic|[]], s as [is|[]], z as [iz|[]]. intros HT HZ.
  unfold bad_trace in HT. pose proof (AllE $iz HT) as H.
  cbn [R terms2 subst_form subst_term up scons funcomp] in H.
  exact (CE1 (IE (CE1 H) HZ)).
Qed.

Lemma bad_trace_subset G c s phi :
  G ⊢238 bad_trace c s phi -> G ⊢238 subset c s.
Proof.
  destruct c as [ic|[]], s as [is|[]]. intro HT.
  unfold subset. apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R terms2 subst_form subst_term up scons funcomp]. apply II.
  apply (bad_trace_member_inside _ $ic $is phi $iz).
  - inherit HT.
  - apply Ctx. now left.
Qed.

Lemma bad_trace_nonempty G c s phi a :
  G ⊢238 bad_trace c s phi -> G ⊢238 R s a ->
  G ⊢238 (¬ phi[a..]) -> G ⊢238 nonempty c.
Proof.
  destruct c as [ic|[]], a as [ia|[]]. intros HT HA Hbad.
  unfold nonempty. apply (ExI $ia).
  cbn [R terms2 subst_form subst_term up scons funcomp].
  apply (trace_bad_member _ $ic s phi $ia); assumption.
Qed.

(** Least selection is supplied by the containing ordinal's actual
    internal-subset clause.  Its least member is itself an ordinal and its
    members remain inside the containing ordinal. *)
Theorem ordinal_containing_bad_contradiction G phi a s c :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 ordinal_base phi ->
  G ⊢238 ordinal_step phi -> G ⊢238 ordinal_representative s ->
  G ⊢238 R s a -> G ⊢238 (¬ phi[a..]) ->
  G ⊢238 bad_trace c s phi -> G ⊢238 falsity.
Proof.
  destruct a as [ia|[]], s as [is|[]], c as [ic|[]].
  intros HE HQ HEq HB HS HR HA Hbad HT.
  assert (Hsub : G ⊢238 subset $ic $is).
  { apply (bad_trace_subset _ $ic $is phi). exact HT. }
  assert (Hne : G ⊢238 nonempty $ic).
  { apply (bad_trace_nonempty _ $ic $is phi $ia); assumption. }
  assert (HL : G ⊢238 ∃ least $ic`[↑] $0).
  { apply (ordinal_internal_least _ $is $ic); assumption. }
  eapply ExE_named; [exact HL|]. intro b. destruct b as [ib|[]].
  cbn [R E terms2 subst_form subst_term up scons funcomp].
  assert (Hb : (least $ic $ib :: G) ⊢238 R $is $ib).
  { apply (subset_member _ $ic $is $ib); [inherit Hsub|].
    eapply CE1, Ctx. now left. }
  apply (ordinal_least_bad_contradiction _ phi $ic $is $ib).
  - inherit HE.
  - inherit HQ.
  - inherit HEq.
  - inherit HB.
  - inherit HS.
  - apply (ordinal_member_closed _ $is $ib); [inherit HR|exact Hb].
  - apply Ctx. now left.
  - inherit HT.
  - apply (member_subset _ $is $ib); [inherit (CE1 (CE1 HR))|exact Hb].
Qed.

(** No counterexample data is supplied externally.  Adjunction constructs
    the containing successor and Separation constructs the bad trace. *)
Theorem ordinal_induction_at G phi a :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 intersection_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 separation_ax (¬ phi) -> G ⊢238 ordinal_base phi ->
  G ⊢238 ordinal_step phi -> G ⊢238 ordinal_representative a ->
  G ⊢238 phi[a..].
Proof.
  destruct a as [ia|[]]. intros HE HQ HEq HEtr HI HA Hsep HB HS HR.
  apply classical_double_negation, II.
  eapply ExE_named.
  - apply (ordinal_successor_exists _ $ia).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit HI.
    + inherit HA.
    + inherit HR.
  - intro s. destruct s as [is|[]].
    cbn [R E terms2 subst_form subst_term up scons funcomp].
    eapply ExE_named.
    + apply (separation_bad_trace _ $is phi). inherit Hsep.
    + intro c. destruct c as [ic|[]].
      rewrite bad_trace_witness_specialize.
      apply (ordinal_containing_bad_contradiction _ phi $ia $is $ic).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HB.
      * inherit HS.
      * eapply CE1, Ctx. right. now left.
      * apply (raw_successor_point_member _ $ia $is).
        -- inherit HE.
        -- eapply CE2, Ctx. right. now left.
      * apply Ctx. right. right. now left.
      * apply Ctx. now left.
Qed.

Definition ordinal_induction (phi : set_form) : set_form :=
  ordinal_base phi → ordinal_step phi → ∀ (ordinal_representative $0 → phi).

Lemma ordinal_induction_bounded n phi :
  bounded (1 + n) phi -> bounded n (ordinal_induction phi).
Proof.
  intro Hphi. unfold ordinal_induction, ordinal_base, ordinal_step,
    ordinal_representative, member_ir, representative, raw_zero, raw_successor,
    transitive, member_transitive, member_linear, internal_extrema, subset,
    nonempty, least, greatest, R, E.
  cbn. fixed_bounds.
  all: first [exact Hphi | eapply subst_bounded_max; [|exact Hphi]].
  all: intros [|k] Hk; cbn [predecessor_slots successor_slots scons];
       constructor; lia.
Qed.

Lemma ordinal_induction_universally_closed n phi :
  bounded (1 + n) phi -> bounded 0 (forall_times n (ordinal_induction phi)).
Proof.
  intro H. apply forall_times_closed, ordinal_induction_bounded, H.
Qed.

Theorem S0_ordinal_induction n phi :
  bounded (1 + n) phi -> derivable finite_set_S0 (ordinal_induction phi).
Proof.
  intro Hphi.
  destruct (S0_separation_instance n (¬ phi)
    ltac:(constructor; [exact Hphi|constructor])) as [Gsep [HGsep Hsep]].
  set (G := equality_base ++ [adjunction_ax; intersection_ax] ++ Gsep).
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
  assert (Hsep' : G ⊢238 separation_ax (¬ phi)).
  { eapply Weak; [exact Hsep|]. intros chi Hchi. unfold G.
    apply in_or_app. right. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + apply in_app_or in Hpsi as [[<-|[<-|[]]]|Hpsi].
      * apply S0_base. apply in_or_app. right. now left.
      * apply S0_intersection_allowed.
      * now apply HGsep.
  - unfold ordinal_induction. apply II, II, AllI_named.
    intro a. destruct a as [ia|[]].
    cbn [R E terms2 subst_form subst_term up scons funcomp]. apply II.
    apply (ordinal_induction_at _ phi $ia).
    + apply weaken_one, weaken_one, weaken_one. exact HE.
    + apply weaken_one, weaken_one, weaken_one. exact HQ.
    + apply weaken_one, weaken_one, weaken_one. exact HEq.
    + apply weaken_one, weaken_one, weaken_one. exact HEtr.
    + apply weaken_one, weaken_one, weaken_one. exact HI.
    + apply weaken_one, weaken_one, weaken_one. exact HA.
    + apply weaken_one, weaken_one, weaken_one. exact Hsep'.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Lemma S0_forall_times n phi :
  derivable finite_set_S0 phi -> derivable finite_set_S0 (forall_times n phi).
Proof.
  intro H. induction n as [|n IH]; [exact H|].
  unfold forall_times in *. cbn [iter]. apply S0_generalize. exact IH.
Qed.

Theorem S0_ordinal_induction_closed n phi :
  bounded (1 + n) phi ->
  derivable finite_set_S0 (forall_times n (ordinal_induction phi)).
Proof. intro H. apply S0_forall_times, (S0_ordinal_induction n phi H). Qed.

Print Assumptions ordinal_induction_at.
Print Assumptions S0_ordinal_induction.
Print Assumptions S0_ordinal_induction_closed.
End OrdinalTrace238.
