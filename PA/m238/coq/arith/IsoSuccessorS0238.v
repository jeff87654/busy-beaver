(** Original finite S0 supplier for actual Iso successor congruence.
    Empty is derived by Separation, and Adjunction builds the new endpoint
    pair graph. All four ordinary parameters are universally closed. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 IsoGraph238 IsoSuccessor238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  IsoGraph238.IsoGraph238 IsoSuccessor238.IsoSuccessor238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module IsoSuccessorS0238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Theorem S0_order_iso_successor_congruence a sa b sb :
  derivable finite_set_S0
    (ordinal_representative a → (ordinal_representative b →
      (raw_successor a sa → (raw_successor b sb →
        (order_iso a b → order_iso sa sb))))).
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
  assert (HEtr : G ⊢238 equality_transitivity_ax).
  { apply Ctx. unfold G, equality_base, equality_transitivity_ax. cbn.
    right. right. now left. }
  assert (HA : G ⊢238 adjunction_ax).
  { apply Ctx. unfold G, equality_base. cbn. right. right. right. right. now left. }
  assert (HZ : G ⊢238 empty_ax).
  { eapply Weak; [exact Hempty|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|[<-|Hpsi]].
    + apply S0_base. apply in_or_app. now left.
    + apply S0_base. apply in_or_app. right. now left.
    + now apply HGempty.
  - apply II, II, II, II, II. apply (order_iso_successor_congruence _ a sa b sb).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit HZ.
    + inherit HA.
    + apply Ctx. right. right. right. right. now left.
    + apply Ctx. right. right. right. now left.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Definition iso_successor_congruence_ax : set_form :=
  ∀ ∀ ∀ ∀ (ordinal_representative $3 → (ordinal_representative $1 →
    (raw_successor $3 $2 → (raw_successor $1 $0 →
      (order_iso $3 $1 → order_iso $2 $0))))).

Lemma iso_successor_congruence_ax_closed : bounded 0 iso_successor_congruence_ax.
Proof.
  unfold iso_successor_congruence_ax, ordinal_representative, representative, member_ir,
    transitive, member_transitive, member_linear, internal_extrema, subset,
    nonempty, least, greatest, raw_successor, order_iso, order_bijection,
    graph_entries, entry_witness, graph_typed, graph_left_total, graph_right_total,
    graph_functional, graph_injective, graph_order, graph_edge,
    raw_kuratowski, raw_pair, raw_singleton, R, E. cbn. fixed_bounds.
Qed.

Theorem S0_order_iso_successor_congruence_closed :
  derivable finite_set_S0 iso_successor_congruence_ax.
Proof.
  unfold iso_successor_congruence_ax.
  apply S0_generalize, S0_generalize, S0_generalize, S0_generalize.
  exact (S0_order_iso_successor_congruence $3 $2 $1 $0).
Qed.

Lemma iso_successor_congruence_instance G a sa b sb :
  G ⊢238 iso_successor_congruence_ax ->
  G ⊢238 ordinal_representative a -> G ⊢238 ordinal_representative b ->
  G ⊢238 raw_successor a sa -> G ⊢238 raw_successor b sb ->
  G ⊢238 order_iso a b -> G ⊢238 order_iso sa sb.
Proof.
  destruct a as [ia|[]], sa as [isa|[]], b as [ib|[]], sb as [isb|[]].
  intros HC HA HB HS HT HI. unfold iso_successor_congruence_ax in HC.
  pose proof (AllE $isb (AllE $ib (AllE $isa (AllE $ia HC)))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HI]. eapply IE; [|exact HT]. eapply IE; [|exact HS].
  eapply IE; [|exact HB]. eapply IE; [exact H|exact HA].
Qed.

Print Assumptions S0_order_iso_successor_congruence.
Print Assumptions iso_successor_congruence_ax_closed.
Print Assumptions S0_order_iso_successor_congruence_closed.
Print Assumptions iso_successor_congruence_instance.
End IsoSuccessorS0238.
