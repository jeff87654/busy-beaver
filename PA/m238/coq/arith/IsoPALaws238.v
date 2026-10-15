(** Original successor equality laws for the represented PA domain.
    Matching constructs the actual target predecessor; raw predecessor
    uniqueness identifies it inside the target ordinal. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 IsoGraph238 IsoZero238 IsoEquality238 IsoMatchSupply238 AddGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  IsoGraph238.IsoGraph238 IsoZero238.IsoZero238 IsoEquality238.IsoEquality238
  IsoMatchSupply238.IsoMatchSupply238 AddGraph238.AddGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module IsoPALaws238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma iso_successor_match_instance G a b p :
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

Theorem order_iso_successor_injective G a sa b sb :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 iso_successor_match_ax ->
  G ⊢238 ordinal_representative sa -> G ⊢238 ordinal_representative b ->
  G ⊢238 ordinal_representative sb -> G ⊢238 raw_successor a sa ->
  G ⊢238 raw_successor b sb -> G ⊢238 order_iso sa sb -> G ⊢238 order_iso a b.
Proof.
  destruct a as [ia|[]], sa as [isa|[]], b as [ib|[]], sb as [isb|[]].
  intros HE HQ HEq HM Hsa Hb Hsb Ha HS HI.
  eapply ExE_named.
  - apply (iso_successor_match_instance _ $isa $isb $ia); assumption.
  - intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (order_iso_coordinate_transport _ $ia $ip $ia $ib).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit (AllE $ia HE).
    + apply (ordinal_successor_predecessor_unique _ $ib $isb $ip).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit Hb.
      * inherit HS.
      * eapply CE1, CE2, Ctx. now left.
    + eapply CE2, CE2, Ctx. now left.
Qed.

Theorem order_iso_successor_zero_false G a sa z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 raw_successor a sa ->
  G ⊢238 raw_zero z -> G ⊢238 order_iso sa z -> G ⊢238 falsity.
Proof.
  intros HE HS HZ HI. eapply IE.
  - apply (zero_excludes_member _ sa a).
    apply (order_iso_zero_source _ sa z); assumption.
  - apply (raw_successor_point_member _ a sa); assumption.
Qed.

Theorem S0_order_iso_successor_injective a sa b sb :
  derivable finite_set_S0
    (ordinal_representative a → (ordinal_representative sa →
      (ordinal_representative b → (ordinal_representative sb →
        (raw_successor a sa → (raw_successor b sb →
          (order_iso sa sb → order_iso a b))))))).
Proof.
  destruct S0_order_iso_successor_match_closed as [Gmatch [HGmatch Hmatch]].
  set (G := equality_base ++ Gmatch).
  assert (HE : G ⊢238 (∀ E $0 $0)).
  { apply Ctx. unfold G, equality_base. cbn. now left. }
  assert (HQ : G ⊢238 equality_membership_ax).
  { apply Ctx. unfold G, equality_base, equality_membership_ax. cbn.
    right. right. right. now left. }
  assert (HEq : G ⊢238 equality_symmetry_ax).
  { apply Ctx. unfold G, equality_base, equality_symmetry_ax. cbn. right. now left. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + now apply HGmatch.
  - apply II, II, II, II, II, II, II.
    apply (order_iso_successor_injective _ a sa b sb).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + eapply Weak; [exact Hmatch|]. intros psi Hpsi.
      right. right. right. right. right. right. right.
      unfold G. apply in_or_app. now right.
    + apply Ctx. right. right. right. right. right. now left.
    + apply Ctx. right. right. right. right. now left.
    + apply Ctx. right. right. right. now left.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Theorem S0_order_iso_successor_not_zero a sa z :
  derivable finite_set_S0
    (raw_successor a sa → (raw_zero z → (¬ order_iso sa z))).
Proof.
  exists [∀ E $0 $0]. split.
  - intros psi [<-|[]]. apply S0_base. apply in_or_app. left. now left.
  - apply II, II, II. apply (order_iso_successor_zero_false _ a sa z).
    + apply Ctx. right. right. right. now left.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Definition iso_successor_injectivity_ax : set_form :=
  ∀ ∀ ∀ ∀ (ordinal_representative $3 → (ordinal_representative $2 →
    (ordinal_representative $1 → (ordinal_representative $0 →
      (raw_successor $3 $2 → (raw_successor $1 $0 →
        (order_iso $2 $0 → order_iso $3 $1))))))).
Definition iso_successor_nonzero_ax : set_form :=
  ∀ ∀ ∀ (raw_successor $2 $1 → (raw_zero $0 → (¬ order_iso $1 $0))).

Lemma iso_successor_injectivity_ax_closed : bounded 0 iso_successor_injectivity_ax.
Proof.
  unfold iso_successor_injectivity_ax, ordinal_representative, representative, member_ir,
    transitive, member_transitive, member_linear, internal_extrema, subset,
    nonempty, least, greatest, raw_successor, order_iso, order_bijection,
    graph_entries, entry_witness, graph_typed, graph_left_total, graph_right_total,
    IsoGraph238.IsoGraph238.graph_functional, graph_injective, graph_order,
    graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E. cbn. fixed_bounds.
Qed.

Lemma iso_successor_nonzero_ax_closed : bounded 0 iso_successor_nonzero_ax.
Proof.
  unfold iso_successor_nonzero_ax, raw_successor, raw_zero, order_iso, order_bijection,
    graph_entries, entry_witness, graph_typed, graph_left_total, graph_right_total,
    IsoGraph238.IsoGraph238.graph_functional, graph_injective, graph_order,
    graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E. cbn. fixed_bounds.
Qed.

Theorem S0_order_iso_successor_injective_closed :
  derivable finite_set_S0 iso_successor_injectivity_ax.
Proof.
  unfold iso_successor_injectivity_ax.
  apply S0_generalize, S0_generalize, S0_generalize, S0_generalize.
  exact (S0_order_iso_successor_injective $3 $2 $1 $0).
Qed.

Theorem S0_order_iso_successor_nonzero_closed :
  derivable finite_set_S0 iso_successor_nonzero_ax.
Proof.
  unfold iso_successor_nonzero_ax. apply S0_generalize, S0_generalize, S0_generalize.
  exact (S0_order_iso_successor_not_zero $2 $1 $0).
Qed.

Print Assumptions iso_successor_match_instance.
Print Assumptions order_iso_successor_injective.
Print Assumptions order_iso_successor_zero_false.
Print Assumptions S0_order_iso_successor_injective.
Print Assumptions S0_order_iso_successor_not_zero.
Print Assumptions iso_successor_injectivity_ax_closed.
Print Assumptions iso_successor_nonzero_ax_closed.
Print Assumptions S0_order_iso_successor_injective_closed.
Print Assumptions S0_order_iso_successor_nonzero_closed.
End IsoPALaws238.
