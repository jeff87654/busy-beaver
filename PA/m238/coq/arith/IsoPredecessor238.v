(** Original graph laws for matching represented successor predecessors.
    This module consumes a decoded strict restriction. It constructs no
    restriction itself: the actual Separation witness is supplied by the
    shared graph restriction module. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 GraphTransport238 IsoGraph238 InverseGraph238 IsoMatching238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  GraphTransport238.GraphTransport238 IsoGraph238.IsoGraph238
  InverseGraph238.InverseGraph238 IsoMatching238.IsoMatching238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module IsoPredecessor238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

(** A proof interface for the strict cut. Decoded entries are required
    separately, so this edge correspondence cannot conceal junk entries. *)
Definition predecessor_edges (g p h : set_term) : set_form :=
  ∀ ∀ (graph_edge h`[↑]`[↑] $1 $0 ↔
    (graph_edge g`[↑]`[↑] $1 $0 ∧ R p`[↑]`[↑] $1)).

Lemma predecessor_edges_instance G g p h x y :
  G ⊢238 predecessor_edges g p h ->
  G ⊢238 (graph_edge h x y ↔ (graph_edge g x y ∧ R p x)).
Proof.
  destruct g as [ig|[]], p as [ip|[]], h as [ih|[]], x as [ix|[]], y as [iy|[]].
  intro HC. unfold predecessor_edges in HC.
  pose proof (AllE $iy (AllE $ix HC)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact H.
Qed.

Lemma predecessor_old_edge G g p h x y :
  G ⊢238 predecessor_edges g p h -> G ⊢238 graph_edge h x y ->
  G ⊢238 graph_edge g x y.
Proof.
  intros HC HE. exact (CE1 (IE (CE1 (predecessor_edges_instance G g p h x y HC)) HE)).
Qed.

Lemma predecessor_edge_member G g p h x y :
  G ⊢238 predecessor_edges g p h -> G ⊢238 graph_edge h x y -> G ⊢238 R p x.
Proof.
  intros HC HE. exact (CE2 (IE (CE1 (predecessor_edges_instance G g p h x y HC)) HE)).
Qed.

Lemma predecessor_edge_intro G g p h x y :
  G ⊢238 predecessor_edges g p h -> G ⊢238 graph_edge g x y ->
  G ⊢238 R p x -> G ⊢238 graph_edge h x y.
Proof.
  intros HC HE HM. eapply IE; [exact (CE2 (predecessor_edges_instance G g p h x y HC))|].
  apply CI; assumption.
Qed.

Lemma predecessor_order_entries G g p q b h :
  G ⊢238 graph_order g -> G ⊢238 graph_edge g p q ->
  G ⊢238 predecessor_edges g p h -> G ⊢238 graph_entries h p b ->
  G ⊢238 graph_entries h p q.
Proof.
  destruct g as [ig|[]], p as [ip|[]], q as [iq|[]], b as [ib|[]], h as [ih|[]].
  intros HO HP HC HE. unfold graph_entries. apply AllI_named.
  intro k. destruct k as [ik|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  assert (Hk : (R $ih $ik :: G) ⊢238 R $ih $ik).
  { apply Ctx. now left. }
  eapply ExE_named.
  - apply (graph_entries_instance _ $ih $ip $ib $ik); [inherit HE|exact Hk].
  - intro x. destruct x as [ix|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    eapply ExE_named; [apply Ctx; now left|]. intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (entry_witness_from_components _ $ip $iq $ik $ix $iy).
    + eapply CE1, Ctx. now left.
    + apply (predecessor_image_member _ $ig $ip $iq $ix $iy).
      * inherit HO.
      * inherit HP.
      * apply (predecessor_old_edge _ $ig $ip $ih $ix $iy); [inherit HC|].
        apply (graph_edge_from_entry _ $ih $ix $iy $ik);
          [inherit Hk|eapply CE2, CE2, Ctx; now left].
      * eapply CE1, Ctx. now left.
    + eapply CE2, CE2, Ctx. now left.
Qed.

Lemma predecessor_order_typed G g p q h :
  G ⊢238 graph_order g -> G ⊢238 graph_edge g p q ->
  G ⊢238 predecessor_edges g p h -> G ⊢238 graph_typed h p q.
Proof.
  destruct g as [ig|[]], p as [ip|[]], q as [iq|[]], h as [ih|[]].
  intros HO HP HC. unfold graph_typed. apply AllI_named.
  intro x. destruct x as [ix|[]]. apply AllI_named. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, CI.
  - apply (predecessor_edge_member _ $ig $ip $ih $ix $iy);
      [inherit HC|apply Ctx; now left].
  - apply (predecessor_image_member _ $ig $ip $iq $ix $iy).
    + inherit HO.
    + inherit HP.
    + apply (predecessor_old_edge _ $ig $ip $ih $ix $iy);
        [inherit HC|apply Ctx; now left].
    + apply (predecessor_edge_member _ $ig $ip $ih $ix $iy);
        [inherit HC|apply Ctx; now left].
Qed.

Lemma predecessor_order_left_total G g a p h :
  G ⊢238 graph_left_total g a -> G ⊢238 raw_successor p a ->
  G ⊢238 predecessor_edges g p h -> G ⊢238 graph_left_total h p.
Proof.
  destruct g as [ig|[]], a as [ia|[]], p as [ip|[]], h as [ih|[]].
  intros HT HS HC. unfold graph_left_total. apply AllI_named.
  intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  assert (HX : (R $ip $ix :: G) ⊢238 R $ip $ix).
  { apply Ctx. now left. }
  eapply ExE_named.
  - apply (graph_left_total_instance _ $ig $ia $ix); [inherit HT|].
    apply (raw_successor_old_member _ $ip $ia $ix); [inherit HS|exact HX].
  - intro y. destruct y as [iy|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iy).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (predecessor_edge_intro _ $ig $ip $ih $ix $iy);
      [inherit HC|apply Ctx; now left|inherit HX].
Qed.

Lemma predecessor_order_right_total G g b p q h :
  G ⊢238 graph_right_total g b -> G ⊢238 graph_order g ->
  G ⊢238 graph_edge g p q -> G ⊢238 raw_successor q b ->
  G ⊢238 predecessor_edges g p h -> G ⊢238 graph_right_total h q.
Proof.
  destruct g as [ig|[]], b as [ib|[]], p as [ip|[]], q as [iq|[]], h as [ih|[]].
  intros HT HO HP HS HC. unfold graph_right_total. apply AllI_named.
  intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  assert (HY : (R $iq $iy :: G) ⊢238 R $iq $iy).
  { apply Ctx. now left. }
  eapply ExE_named.
  - apply (graph_right_total_instance _ $ig $ib $iy); [inherit HT|].
    apply (raw_successor_old_member _ $iq $ib $iy); [inherit HS|exact HY].
  - intro x. destruct x as [ix|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $ix).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (predecessor_edge_intro _ $ig $ip $ih $ix $iy).
    + inherit HC.
    + apply Ctx. now left.
    + apply (predecessor_source_member _ $ig $ip $iq $ix $iy);
        [inherit HO|inherit HP|apply Ctx; now left|inherit HY].
Qed.

Lemma predecessor_order_functional G g p h :
  G ⊢238 graph_functional g -> G ⊢238 predecessor_edges g p h ->
  G ⊢238 graph_functional h.
Proof.
  destruct g as [ig|[]], p as [ip|[]], h as [ih|[]]. intros HF HC.
  unfold graph_functional. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (graph_functional_instance _ $ig $ix $iy $iz); [inherit HF| |].
  - apply (predecessor_old_edge _ $ig $ip $ih $ix $iy); [inherit HC|].
    eapply CE1, Ctx. now left.
  - apply (predecessor_old_edge _ $ig $ip $ih $ix $iz); [inherit HC|].
    eapply CE2, Ctx. now left.
Qed.

Lemma predecessor_order_injective G g p h :
  G ⊢238 graph_injective g -> G ⊢238 predecessor_edges g p h ->
  G ⊢238 graph_injective h.
Proof.
  destruct g as [ig|[]], p as [ip|[]], h as [ih|[]]. intros HI HC.
  unfold graph_injective. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro z. destruct z as [iz|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (graph_injective_instance _ $ig $ix $iy $iz); [inherit HI| |].
  - apply (predecessor_old_edge _ $ig $ip $ih $ix $iz); [inherit HC|].
    eapply CE1, Ctx. now left.
  - apply (predecessor_old_edge _ $ig $ip $ih $iy $iz); [inherit HC|].
    eapply CE2, Ctx. now left.
Qed.

Lemma predecessor_order_preserves G g p h :
  G ⊢238 graph_order g -> G ⊢238 predecessor_edges g p h -> G ⊢238 graph_order h.
Proof.
  destruct g as [ig|[]], p as [ip|[]], h as [ih|[]]. intros HO HC.
  unfold graph_order. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro y. destruct y as [iy|[]].
  apply AllI_named. intro u. destruct u as [iu|[]].
  apply AllI_named. intro v. destruct v as [iv|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  apply (graph_order_instance _ $ig $ix $iy $iu $iv); [inherit HO| |].
  - apply (predecessor_old_edge _ $ig $ip $ih $ix $iu); [inherit HC|].
    eapply CE1, Ctx. now left.
  - apply (predecessor_old_edge _ $ig $ip $ih $iy $iv); [inherit HC|].
    eapply CE2, Ctx. now left.
Qed.

Theorem predecessor_order_bijection G g a b p q h :
  G ⊢238 order_bijection g a b -> G ⊢238 raw_successor p a ->
  G ⊢238 raw_successor q b -> G ⊢238 graph_edge g p q ->
  G ⊢238 graph_entries h p b -> G ⊢238 predecessor_edges g p h ->
  G ⊢238 order_bijection h p q.
Proof.
  intros HG HS HT HP HE HC. unfold order_bijection. apply CI.
  - apply (predecessor_order_entries _ g p q b h);
      [exact (CE2 (CE2 (CE2 (CE2 (CE2 (CE2 HG))))))|exact HP|exact HC|exact HE].
  - apply CI.
    + apply (predecessor_order_typed _ g p q h);
        [exact (CE2 (CE2 (CE2 (CE2 (CE2 (CE2 HG))))))|exact HP|exact HC].
    + apply CI.
      * apply (predecessor_order_left_total _ g a p h);
          [exact (CE1 (CE2 (CE2 HG)))|exact HS|exact HC].
      * apply CI.
        -- apply (predecessor_order_right_total _ g b p q h).
           ++ exact (CE1 (CE2 (CE2 (CE2 HG)))).
           ++ exact (CE2 (CE2 (CE2 (CE2 (CE2 (CE2 HG)))))).
           ++ exact HP.
           ++ exact HT.
           ++ exact HC.
        -- apply CI.
           ++ apply (predecessor_order_functional _ g p h);
                [exact (CE1 (CE2 (CE2 (CE2 (CE2 HG)))))|exact HC].
           ++ apply CI.
              ** apply (predecessor_order_injective _ g p h);
                   [exact (CE1 (CE2 (CE2 (CE2 (CE2 (CE2 HG))))))|exact HC].
              ** apply (predecessor_order_preserves _ g p h);
                   [exact (CE2 (CE2 (CE2 (CE2 (CE2 (CE2 HG))))))|exact HC].
Qed.

(** The family is universally quantified before an Iso graph witness is
    selected. A single finite context therefore supplies all its cuts. *)
Definition predecessor_cut_exists (g p b : set_term) : set_form :=
  ∃ (graph_entries $0 p`[↑] b`[↑] ∧ predecessor_edges g`[↑] p`[↑] $0).
Definition predecessor_cut_family (a b p : set_term) : set_form :=
  ∀ (graph_typed $0 a`[↑] b`[↑] →
    predecessor_cut_exists $0 p`[↑] b`[↑]).

Lemma predecessor_cut_family_instance G a b p g :
  G ⊢238 predecessor_cut_family a b p -> G ⊢238 graph_typed g a b ->
  G ⊢238 predecessor_cut_exists g p b.
Proof.
  destruct a as [ia|[]], b as [ib|[]], p as [ip|[]], g as [ig|[]]. intros HC HG.
  unfold predecessor_cut_family in HC. pose proof (AllE $ig HC) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HG).
Qed.

Theorem predecessor_cut_order_iso G g a b p q :
  G ⊢238 order_bijection g a b -> G ⊢238 raw_successor p a ->
  G ⊢238 raw_successor q b -> G ⊢238 graph_edge g p q ->
  G ⊢238 predecessor_cut_exists g p b -> G ⊢238 order_iso p q.
Proof.
  destruct g as [ig|[]], a as [ia|[]], b as [ib|[]], p as [ip|[]], q as [iq|[]].
  intros HG HS HT HP HC. unfold predecessor_cut_exists in HC.
  eapply ExE_named; [exact HC|]. intro h. destruct h as [ih|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  unfold order_iso. apply (ExI $ih).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (predecessor_order_bijection _ $ig $ia $ib $ip $iq $ih).
  - inherit HG.
  - inherit HS.
  - inherit HT.
  - inherit HP.
  - eapply CE1, Ctx. now left.
  - eapply CE2, Ctx. now left.
Qed.

Theorem order_iso_successor_match_from_family G a b p :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 predecessor_cut_family a b p ->
  G ⊢238 ordinal_representative b -> G ⊢238 raw_successor p a ->
  G ⊢238 order_iso a b ->
  G ⊢238 ∃ (ordinal_representative $0 ∧
    (raw_successor $0 b`[↑] ∧ order_iso p`[↑] $0)).
Proof.
  destruct a as [ia|[]], b as [ib|[]], p as [ip|[]].
  intros HE HQ HEq HEtr HF HB HS HI. unfold order_iso in HI.
  eapply ExE_named; [exact HI|]. intro g. destruct g as [ig|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HG : (order_bijection $ig $ia $ib :: G) ⊢238 order_bijection $ig $ia $ib).
  { apply Ctx. now left. }
  eapply ExE_named.
  - apply (successor_image_exists _ $ig $ia $ib $ip).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit HB.
    + exact HG.
    + inherit HS.
  - intro q. destruct q as [iq|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HQw : (ordinal_representative $iq ∧
       (raw_successor $iq $ib ∧ graph_edge $ig $ip $iq) ::
       order_bijection $ig $ia $ib :: G) ⊢238
       (ordinal_representative $iq ∧
        (raw_successor $iq $ib ∧ graph_edge $ig $ip $iq))).
    { apply Ctx. now left. }
    apply (ExI $iq).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
    + exact (CE1 HQw).
    + apply CI; [exact (CE1 (CE2 HQw))|].
      apply (predecessor_cut_order_iso _ $ig $ia $ib $ip $iq).
      * inherit HG.
      * inherit HS.
      * exact (CE1 (CE2 HQw)).
      * exact (CE2 (CE2 HQw)).
      * apply (predecessor_cut_family_instance _ $ia $ib $ip $ig);
          [inherit HF|inherit (CE1 (CE2 HG))].
Qed.

Print Assumptions predecessor_cut_family_instance.
Print Assumptions predecessor_cut_order_iso.
Print Assumptions order_iso_successor_match_from_family.
Print Assumptions predecessor_edges_instance.
Print Assumptions predecessor_order_entries.
Print Assumptions predecessor_order_typed.
Print Assumptions predecessor_order_left_total.
Print Assumptions predecessor_order_right_total.
Print Assumptions predecessor_order_functional.
Print Assumptions predecessor_order_injective.
Print Assumptions predecessor_order_preserves.
Print Assumptions predecessor_order_bijection.
End IsoPredecessor238.
