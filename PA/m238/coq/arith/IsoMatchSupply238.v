(** Original S0 successor matching from an actual shared Separation cut.
    The cut family is generalized in the source graph before the given
    Iso witness is eliminated. This preserves one finite axiom context. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 GraphTransport238 IsoGraph238 InverseGraph238 IsoMatching238
  IsoPredecessor238 TraceRestriction238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  GraphTransport238.GraphTransport238 IsoGraph238.IsoGraph238
  InverseGraph238.InverseGraph238 IsoMatching238.IsoMatching238
  IsoPredecessor238.IsoPredecessor238 TraceRestriction238.TraceRestriction238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module IsoMatchSupply238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Theorem S0_strict_graph_cut_all p :
  derivable finite_set_S0
    (∀ ∃ strict_graph_cut p`[↑]`[↑] $1 $0).
Proof.
  destruct p as [ip|[]]. apply S0_generalize.
  exact (S0_strict_graph_cut_exists $(S ip) $0).
Qed.

Theorem S0_predecessor_cut_family a b p :
  derivable finite_set_S0 (predecessor_cut_family a b p).
Proof.
  destruct a as [ia|[]], b as [ib|[]], p as [ip|[]].
  destruct (S0_strict_graph_cut_all $ip) as [Gcut [HGcut Hcut]].
  set (G := equality_base ++ Gcut).
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
    + now apply HGcut.
  - unfold predecessor_cut_family. apply AllI_named. intro g. destruct g as [ig|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
    pose proof (AllE $ig Hcut) as Hc.
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in Hc.
    eapply ExE_named.
    + eapply Weak; [exact Hc|]. intros psi Hpsi. right. unfold G.
      apply in_or_app. now right.
    + intro h. destruct h as [ih|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      unfold predecessor_cut_exists. apply (ExI $ih).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * apply (strict_cut_entries _ $ip $ig $ih $ia $ib).
        -- apply Ctx. now left.
        -- apply Ctx. right. now left.
      * change ((strict_graph_cut $ip $ig $ih :: graph_typed $ig $ia $ib :: G)
          ⊢238 strict_graph_restriction $ip $ig $ih).
        apply (strict_cut_edges _ $ip $ig $ih).
        -- inherit HE.
        -- inherit HQ.
        -- inherit HEq.
        -- inherit HEtr.
        -- apply Ctx. now left.
Qed.

Theorem S0_order_iso_successor_match a b p :
  derivable finite_set_S0
    (ordinal_representative a → (ordinal_representative b →
      (raw_successor p a → (order_iso a b →
        ∃ (ordinal_representative $0 ∧
          (raw_successor $0 b`[↑] ∧ order_iso p`[↑] $0)))))).
Proof.
  destruct (S0_predecessor_cut_family a b p) as [Gfam [HGfam Hfam]].
  set (G := equality_base ++ Gfam).
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
    + now apply HGfam.
  - apply II, II, II, II. apply (order_iso_successor_match_from_family _ a b p).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + eapply Weak; [exact Hfam|]. intros psi Hpsi. right. right. right. right.
      unfold G. apply in_or_app. now right.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

(** All three ordinary parameters are closed, including the predecessor
    whose matching image is existentially constructed under a fourth binder. *)
Definition iso_successor_match_ax : set_form :=
  ∀ ∀ ∀ (ordinal_representative $2 → (ordinal_representative $1 →
    (raw_successor $0 $2 → (order_iso $2 $1 →
      ∃ (ordinal_representative $0 ∧
        (raw_successor $0 $2 ∧ order_iso $1 $0)))))).

Lemma iso_successor_match_ax_closed : bounded 0 iso_successor_match_ax.
Proof.
  unfold iso_successor_match_ax, ordinal_representative, representative, member_ir,
    transitive, member_transitive, member_linear, internal_extrema, subset,
    nonempty, least, greatest, raw_successor, order_iso, order_bijection,
    graph_entries, entry_witness, graph_typed, graph_left_total, graph_right_total,
    graph_functional, graph_injective, graph_order, graph_edge, raw_kuratowski,
    raw_pair, raw_singleton, R, E. cbn. fixed_bounds.
Qed.

Theorem S0_order_iso_successor_match_closed :
  derivable finite_set_S0 iso_successor_match_ax.
Proof.
  unfold iso_successor_match_ax. apply S0_generalize, S0_generalize, S0_generalize.
  apply S0_order_iso_successor_match.
Qed.

Print Assumptions iso_successor_match_ax_closed.
Print Assumptions S0_order_iso_successor_match_closed.
Print Assumptions S0_strict_graph_cut_all.
Print Assumptions S0_predecessor_cut_family.
Print Assumptions S0_order_iso_successor_match.
End IsoMatchSupply238.
