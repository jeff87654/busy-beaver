(** Original composition of actual order graphs. The relational clauses
    below are proved from the two source graphs. Actual graph witnesses
    are separately constructed by finite ordinal prefixes and Adjunction. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238 OrdinalTrace238
  PairGraph238 GraphTransport238 IsoGraph238 InverseGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 OrdinalTrace238.OrdinalTrace238
  PairGraph238.PairGraph238
  GraphTransport238.GraphTransport238 IsoGraph238.IsoGraph238
  InverseGraph238.InverseGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module CompositionGraph238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition composition_edge (g h x z : set_term) : set_form :=
  ∃ (graph_edge g`[↑] x`[↑] $0 ∧ graph_edge h`[↑] $0 z`[↑]).

Lemma composition_edge_intro G g h x y z :
  G ⊢238 graph_edge g x y -> G ⊢238 graph_edge h y z ->
  G ⊢238 composition_edge g h x z.
Proof.
  destruct g as [ig|[]], h as [ih|[]], x as [ix|[]], y as [iy|[]], z as [iz|[]].
  intros HG HH. unfold composition_edge. apply (ExI $iy).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI; assumption.
Qed.

Lemma composition_edge_typed G g h a b c x z :
  G ⊢238 graph_typed g a b -> G ⊢238 graph_typed h b c ->
  G ⊢238 composition_edge g h x z -> G ⊢238 (R a x ∧ R c z).
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]], c as [ic|[]],
    x as [ix|[]], z as [iz|[]]. intros HT HU HX. unfold composition_edge in HX.
  eapply ExE_named; [exact HX|]. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
  - eapply CE1. apply (graph_typed_instance _ $ig $ia $ib $ix $iy);
      [inherit HT|]. eapply CE1, Ctx. now left.
  - eapply CE2. apply (graph_typed_instance _ $ih $ib $ic $iy $iz);
      [inherit HU|]. eapply CE2, Ctx. now left.
Qed.

Lemma composition_edge_functional G g h x z w :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 graph_functional g -> G ⊢238 graph_functional h ->
  G ⊢238 composition_edge g h x z -> G ⊢238 composition_edge g h x w ->
  G ⊢238 E z w.
Proof.
  destruct g as [ig|[]], h as [ih|[]], x as [ix|[]], z as [iz|[]], w as [iw|[]].
  intros HE HEq HEtr HF HK HX HW. unfold composition_edge in HX, HW.
  eapply ExE_named; [exact HX|]. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HY : (graph_edge $ig $ix $iy ∧ graph_edge $ih $iy $iz :: G)
    ⊢238 (graph_edge $ig $ix $iy ∧ graph_edge $ih $iy $iz)).
  { apply Ctx. now left. }
  eapply ExE_named; [inherit HW|]. intro v. destruct v as [iv|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (graph_functional_instance _ $ih $iy $iz $iw).
  - inherit HK.
  - inherit (CE2 HY).
  - apply (graph_edge_coordinate_transport _ $ih $iv $iw $iy $iw).
    + inherit HEq.
    + inherit HEtr.
    + apply equality_symmetry_instance; [inherit HEq|].
      apply (graph_functional_instance _ $ig $ix $iy $iv);
        [inherit HF|inherit (CE1 HY)|eapply CE1, Ctx; now left].
    + inherit (AllE $iw HE).
    + eapply CE2, Ctx. now left.
Qed.

Lemma composition_edge_injective G g h x u z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 graph_injective g -> G ⊢238 graph_injective h ->
  G ⊢238 composition_edge g h x z -> G ⊢238 composition_edge g h u z ->
  G ⊢238 E x u.
Proof.
  destruct g as [ig|[]], h as [ih|[]], x as [ix|[]], u as [iu|[]], z as [iz|[]].
  intros HE HEq HEtr HF HK HX HU. unfold composition_edge in HX, HU.
  eapply ExE_named; [exact HX|]. intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HY : (graph_edge $ig $ix $iy ∧ graph_edge $ih $iy $iz :: G)
    ⊢238 (graph_edge $ig $ix $iy ∧ graph_edge $ih $iy $iz)).
  { apply Ctx. now left. }
  eapply ExE_named; [inherit HU|]. intro v. destruct v as [iv|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (graph_injective_instance _ $ig $ix $iu $iy).
  - inherit HF.
  - inherit (CE1 HY).
  - apply (graph_edge_coordinate_transport _ $ig $iu $iv $iu $iy).
    + inherit HEq.
    + inherit HEtr.
    + inherit (AllE $iu HE).
    + apply equality_symmetry_instance; [inherit HEq|].
      apply (graph_injective_instance _ $ih $iy $iv $iz);
        [inherit HK|inherit (CE2 HY)|eapply CE2, Ctx; now left].
    + eapply CE1, Ctx. now left.
Qed.

Lemma composition_edge_order G g h x u z w :
  G ⊢238 graph_order g -> G ⊢238 graph_order h ->
  G ⊢238 composition_edge g h x z -> G ⊢238 composition_edge g h u w ->
  G ⊢238 (R x u ↔ R z w).
Proof.
  destruct g as [ig|[]], h as [ih|[]], x as [ix|[]], u as [iu|[]],
    z as [iz|[]], w as [iw|[]]. intros HG HH HX HU.
  unfold composition_edge in HX, HU. eapply ExE_named; [exact HX|].
  intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HY : (graph_edge $ig $ix $iy ∧ graph_edge $ih $iy $iz :: G)
    ⊢238 (graph_edge $ig $ix $iy ∧ graph_edge $ih $iy $iz)).
  { apply Ctx. now left. }
  eapply ExE_named; [inherit HU|]. intro v. destruct v as [iv|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  assert (HV : (graph_edge $ig $iu $iv ∧ graph_edge $ih $iv $iw ::
    graph_edge $ig $ix $iy ∧ graph_edge $ih $iy $iz :: G)
    ⊢238 (graph_edge $ig $iu $iv ∧ graph_edge $ih $iv $iw)).
  { apply Ctx. now left. }
  assert (Hxy : (graph_edge $ig $iu $iv ∧ graph_edge $ih $iv $iw ::
    graph_edge $ig $ix $iy ∧ graph_edge $ih $iy $iz :: G) ⊢238 (R $ix $iu ↔ R $iy $iv)).
  { apply (graph_order_instance _ $ig $ix $iu $iy $iv);
      [inherit HG|inherit (CE1 HY)|exact (CE1 HV)]. }
  assert (Hzw : (graph_edge $ig $iu $iv ∧ graph_edge $ih $iv $iw ::
    graph_edge $ig $ix $iy ∧ graph_edge $ih $iy $iz :: G) ⊢238 (R $iy $iv ↔ R $iz $iw)).
  { apply (graph_order_instance _ $ih $iy $iv $iz $iw);
      [inherit HH|inherit (CE2 HY)|exact (CE2 HV)]. }
  apply CI.
  - apply II. eapply IE; [inherit (CE1 Hzw)|].
    eapply IE; [inherit (CE1 Hxy)|apply Ctx; now left].
  - apply II. eapply IE; [inherit (CE2 Hxy)|].
    eapply IE; [inherit (CE2 Hzw)|apply Ctx; now left].
Qed.

Definition composition_entry (g h n p : set_term) : set_form :=
  ∃ ∃ ∃ (R n`[↑]`[↑]`[↑] $2 ∧
    (graph_edge g`[↑]`[↑]`[↑] $2 $1 ∧
      (graph_edge h`[↑]`[↑]`[↑] $1 $0 ∧ raw_kuratowski p`[↑]`[↑]`[↑] $2 $0))).
Definition composition_entries (g h n k : set_term) : set_form :=
  ∀ (R k`[↑] $0 → composition_entry g`[↑] h`[↑] n`[↑] $0).
Definition composition_correct (g h n k : set_term) : set_form :=
  ∀ ∀ (graph_edge k`[↑]`[↑] $1 $0 →
    (R n`[↑]`[↑] $1 ∧ composition_edge g`[↑]`[↑] h`[↑]`[↑] $1 $0)).
Definition composition_coverage (g h n k : set_term) : set_form :=
  ∀ (R n`[↑] $0 →
    ∃ (graph_edge k`[↑]`[↑] $1 $0 ∧ composition_edge g`[↑]`[↑] h`[↑]`[↑] $1 $0)).
Definition composition_prefix (g h n k : set_term) : set_form :=
  composition_entries g h n k ∧ (composition_correct g h n k ∧ composition_coverage g h n k).

Lemma empty_composition_prefix G g h n :
  G ⊢238 raw_zero n -> G ⊢238 composition_prefix g h n n.
Proof.
  destruct g as [ig|[]], h as [ih|[]], n as [in_|[]]. intro HZ.
  unfold composition_prefix. apply CI.
  - unfold composition_entries. apply AllI_named. intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, Exp.
    eapply IE; [inherit (zero_excludes_member G $in_ $ip HZ)|apply Ctx; now left].
  - apply CI.
    + unfold composition_correct. apply AllI_named. intro x. destruct x as [ix|[]].
      apply AllI_named. intro z. destruct z as [iz|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, Exp.
      apply (graph_edge_empty_false _ $in_ $ix $iz); [inherit HZ|apply Ctx; now left].
    + unfold composition_coverage. apply AllI_named. intro x. destruct x as [ix|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, Exp.
      eapply IE; [inherit (zero_excludes_member G $in_ $ix HZ)|apply Ctx; now left].
Qed.

Lemma composition_edge_coordinate_transport G g h x z x' z' :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 E x x' -> G ⊢238 E z z' ->
  G ⊢238 composition_edge g h x z -> G ⊢238 composition_edge g h x' z'.
Proof.
  destruct g as [ig|[]], h as [ih|[]], x as [ix|[]], z as [iz|[]],
    x' as [ix'|[]], z' as [iz'|[]]. intros HE HEq HEtr HX HZ HC.
  unfold composition_edge in HC. eapply ExE_named; [exact HC|].
  intro y. destruct y as [iy|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply (composition_edge_intro _ $ig $ih $ix' $iy $iz').
  - apply (graph_edge_coordinate_transport _ $ig $ix $iy $ix' $iy).
    + inherit HEq.
    + inherit HEtr.
    + inherit HX.
    + inherit (AllE $iy HE).
    + eapply CE1, Ctx. now left.
  - apply (graph_edge_coordinate_transport _ $ih $iy $iz $iy $iz').
    + inherit HEq.
    + inherit HEtr.
    + inherit (AllE $iy HE).
    + inherit HZ.
    + eapply CE2, Ctx. now left.
Qed.

Lemma composition_entry_intro G g h n p x y z :
  G ⊢238 R n x -> G ⊢238 graph_edge g x y -> G ⊢238 graph_edge h y z ->
  G ⊢238 raw_kuratowski p x z -> G ⊢238 composition_entry g h n p.
Proof.
  destruct g as [ig|[]], h as [ih|[]], n as [in_|[]], p as [ip|[]],
    x as [ix|[]], y as [iy|[]], z as [iz|[]]. intros Hn Hg Hh Hp.
  unfold composition_entry. apply (ExI $ix).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iy).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iz).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply CI; [exact Hn|]. apply CI; [exact Hg|]. apply CI; assumption.
Qed.

Lemma composition_entries_instance G g h n k p :
  G ⊢238 composition_entries g h n k -> G ⊢238 R k p ->
  G ⊢238 composition_entry g h n p.
Proof.
  destruct g as [ig|[]], h as [ih|[]], n as [in_|[]], k as [ik|[]], p as [ip|[]].
  intros HC Hp. unfold composition_entries in HC. pose proof (AllE $ip HC) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H Hp).
Qed.

Lemma composition_correct_instance G g h n k x z :
  G ⊢238 composition_correct g h n k -> G ⊢238 graph_edge k x z ->
  G ⊢238 (R n x ∧ composition_edge g h x z).
Proof.
  destruct g as [ig|[]], h as [ih|[]], n as [in_|[]], k as [ik|[]],
    x as [ix|[]], z as [iz|[]]. intros HC HE.
  unfold composition_correct in HC. pose proof (AllE $iz (AllE $ix HC)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HE).
Qed.

Lemma composition_coverage_instance G g h n k x :
  G ⊢238 composition_coverage g h n k -> G ⊢238 R n x ->
  G ⊢238 ∃ (graph_edge k`[↑] x`[↑] $0 ∧ composition_edge g`[↑] h`[↑] x`[↑] $0).
Proof.
  destruct g as [ig|[]], h as [ih|[]], n as [in_|[]], k as [ik|[]], x as [ix|[]].
  intros HC Hx. unfold composition_coverage in HC. pose proof (AllE $ix HC) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H Hx).
Qed.

Lemma composition_key_fresh G g h n k z :
  G ⊢238 member_ir n -> G ⊢238 composition_prefix g h n k ->
  G ⊢238 (¬ graph_edge k n z).
Proof.
  intros HI HP. apply II. eapply IE; [inherit (member_ir_not_self G n HI)|].
  eapply CE1. apply (composition_correct_instance _ g h n k n z);
    [inherit (CE1 (CE2 HP))|apply Ctx; now left].
Qed.

Lemma successor_composition_entries G g h n m k p l y z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 composition_entries g h n k ->
  G ⊢238 raw_successor n m -> G ⊢238 raw_adjunction k p l ->
  G ⊢238 raw_kuratowski p n z -> G ⊢238 graph_edge g n y ->
  G ⊢238 graph_edge h y z -> G ⊢238 composition_entries g h m l.
Proof.
  destruct g as [ig|[]], h as [ih|[]], n as [in_|[]], m as [im|[]], k as [ik|[]],
    p as [ip|[]], l as [il|[]], y as [iy|[]], z as [iz|[]].
  intros HE HQ HEq HC HS HA HP Hg Hh.
  unfold composition_entries. apply AllI_named. intro v. destruct v as [iv|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_adjunction_member _ $ik $ip $il $iv); [inherit HA|apply Ctx; now left].
  - eapply ExE_named.
    + apply (composition_entries_instance _ $ig $ih $in_ $ik $iv);
        [inherit HC|apply Ctx; now left].
    + intro x. destruct x as [ix|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      eapply ExE_named; [apply Ctx; now left|]. intro u. destruct u as [iu|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      eapply ExE_named; [apply Ctx; now left|]. intro w. destruct w as [iw|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (composition_entry_intro _ $ig $ih $im $iv $ix $iu $iw).
      * apply (raw_successor_old_member _ $in_ $im $ix); [inherit HS|].
        eapply CE1, Ctx. now left.
      * eapply CE1, CE2, Ctx. now left.
      * eapply CE1, CE2, CE2, Ctx. now left.
      * eapply CE2, CE2, CE2, Ctx. now left.
  - apply (composition_entry_intro _ $ig $ih $im $iv $in_ $iy $iz).
    + apply (raw_successor_point_member _ $in_ $im); [inherit HE|inherit HS].
    + inherit Hg.
    + inherit Hh.
    + apply (raw_kuratowski_container_transport _ $ip $iv $in_ $iz).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
      * inherit HP.
Qed.

Lemma successor_composition_correct G g h n m k p l y z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 composition_correct g h n k -> G ⊢238 raw_successor n m ->
  G ⊢238 raw_adjunction k p l -> G ⊢238 raw_kuratowski p n z ->
  G ⊢238 graph_edge g n y -> G ⊢238 graph_edge h y z ->
  G ⊢238 composition_correct g h m l.
Proof.
  destruct g as [ig|[]], h as [ih|[]], n as [in_|[]], m as [im|[]], k as [ik|[]],
    p as [ip|[]], l as [il|[]], y as [iy|[]], z as [iz|[]].
  intros HE HQ HEq HEtr HC HS HA HP Hg Hh.
  assert (Hnew : G ⊢238 composition_edge $ig $ih $in_ $iz).
  { apply (composition_edge_intro _ $ig $ih $in_ $iy $iz); assumption. }
  unfold composition_correct. apply AllI_named. intro x. destruct x as [ix|[]].
  apply AllI_named. intro w. destruct w as [iw|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_adjunction_graph_edge_cases _ $ik $ip $il $in_ $iz $ix $iw).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit HA.
    + inherit HP.
    + apply Ctx. now left.
  - apply CI.
    + apply (raw_successor_old_member _ $in_ $im $ix); [inherit HS|].
      eapply CE1. apply (composition_correct_instance _ $ig $ih $in_ $ik $ix $iw);
        [inherit HC|apply Ctx; now left].
    + eapply CE2. apply (composition_correct_instance _ $ig $ih $in_ $ik $ix $iw);
        [inherit HC|apply Ctx; now left].
  - apply CI.
    + apply (equality_member_transport _ $im $in_ $ix).
      * inherit HE.
      * inherit HQ.
      * apply equality_symmetry_instance; [inherit HEq|]. eapply CE1, Ctx. now left.
      * apply (raw_successor_point_member _ $in_ $im); [inherit HE|inherit HS].
    + apply (composition_edge_coordinate_transport _ $ig $ih $in_ $iz $ix $iw).
      * inherit HE.
      * inherit HEq.
      * inherit HEtr.
      * apply equality_symmetry_instance; [inherit HEq|]. eapply CE1, Ctx. now left.
      * apply equality_symmetry_instance; [inherit HEq|]. eapply CE2, Ctx. now left.
      * inherit Hnew.
Qed.

Lemma successor_composition_coverage G g h n m k p l y z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 pair_equality_transitivity_ax -> G ⊢238 composition_coverage g h n k ->
  G ⊢238 raw_successor n m -> G ⊢238 raw_adjunction k p l ->
  G ⊢238 raw_kuratowski p n z -> G ⊢238 graph_edge g n y ->
  G ⊢238 graph_edge h y z -> G ⊢238 composition_coverage g h m l.
Proof.
  destruct g as [ig|[]], h as [ih|[]], n as [in_|[]], m as [im|[]], k as [ik|[]],
    p as [ip|[]], l as [il|[]], y as [iy|[]], z as [iz|[]].
  intros HE HEq HEtr HC HS HA HP Hg Hh.
  assert (Hnew : G ⊢238 graph_edge $il $in_ $iz).
  { apply (graph_edge_from_entry _ $il $in_ $iz $ip); [|exact HP].
    apply (raw_adjunction_intro _ $ik $ip $il $ip); [exact HA|].
    apply DI2. exact (AllE $ip HE). }
  assert (Hcomp : G ⊢238 composition_edge $ig $ih $in_ $iz).
  { apply (composition_edge_intro _ $ig $ih $in_ $iy $iz); assumption. }
  unfold composition_coverage. apply AllI_named. intro x. destruct x as [ix|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II.
  eapply DE.
  - apply (raw_successor_member_cases _ $in_ $im $ix); [inherit HS|apply Ctx; now left].
  - eapply ExE_named.
    + apply (composition_coverage_instance _ $ig $ih $in_ $ik $ix);
        [inherit HC|apply Ctx; now left].
    + intro w. destruct w as [iw|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply (ExI $iw).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
      * apply (graph_inclusion_instance _ $ik $il $ix $iw).
        -- apply (raw_adjunction_graph_inclusion _ $ik $ip $il). inherit HA.
        -- eapply CE1, Ctx. now left.
      * eapply CE2, Ctx. now left.
  - apply (ExI $iz).
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply CI.
    + apply (graph_edge_coordinate_transport _ $il $in_ $iz $ix $iz).
      * inherit HEq.
      * inherit HEtr.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
      * inherit (AllE $iz HE).
      * inherit Hnew.
    + apply (composition_edge_coordinate_transport _ $ig $ih $in_ $iz $ix $iz).
      * inherit HE.
      * inherit HEq.
      * inherit HEtr.
      * apply equality_symmetry_instance; [inherit HEq|apply Ctx; now left].
      * inherit (AllE $iz HE).
      * inherit Hcomp.
Qed.

Theorem successor_composition_prefix G g h n m k p l y z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 composition_prefix g h n k -> G ⊢238 raw_successor n m ->
  G ⊢238 raw_adjunction k p l -> G ⊢238 raw_kuratowski p n z ->
  G ⊢238 graph_edge g n y -> G ⊢238 graph_edge h y z ->
  G ⊢238 composition_prefix g h m l.
Proof.
  intros HE HQ HEq HEtr HC HS HA HP Hg Hh. unfold composition_prefix. apply CI.
  - apply (successor_composition_entries _ g h n m k p l y z);
      [exact HE|exact HQ|exact HEq|exact (CE1 HC)|exact HS|exact HA|exact HP|exact Hg|exact Hh].
  - apply CI.
    + apply (successor_composition_correct _ g h n m k p l y z);
        [exact HE|exact HQ|exact HEq|exact HEtr|exact (CE1 (CE2 HC))|
         exact HS|exact HA|exact HP|exact Hg|exact Hh].
    + apply (successor_composition_coverage _ g h n m k p l y z);
        [exact HE|exact HEq|exact HEtr|exact (CE2 (CE2 HC))|
         exact HS|exact HA|exact HP|exact Hg|exact Hh].
Qed.

Definition composition_exists (g h n : set_term) : set_form :=
  ∃ composition_prefix g`[↑] h`[↑] n`[↑] $0.
Definition composition_property (g h a : set_term) : set_form :=
  subset $0 a`[↑] → composition_exists g`[↑] h`[↑] $0.

Theorem composition_prefix_extension G g h n m k y z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax ->
  G ⊢238 composition_prefix g h n k -> G ⊢238 raw_successor n m ->
  G ⊢238 graph_edge g n y -> G ⊢238 graph_edge h y z ->
  G ⊢238 composition_exists g h m.
Proof.
  destruct g as [ig|[]], h as [ih|[]], n as [in_|[]], m as [im|[]], k as [ik|[]],
    y as [iy|[]], z as [iz|[]]. intros HE HQ HEq HEtr Hempty HA HC HS Hg Hh.
  eapply ExE_named; [exact Hempty|]. intro e. destruct e as [ie|[]].
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. eapply ExE_named.
  - apply (raw_kuratowski_exists _ $ie $in_ $iz); [apply Ctx; now left|inherit HA].
  - intro p. destruct p as [ip|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. eapply ExE_named.
    + apply (raw_adjunction_exists _ $ik $ip). inherit HA.
    + intro l. destruct l as [il|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      unfold composition_exists. apply (ExI $il).
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      apply (successor_composition_prefix _ $ig $ih $in_ $im $ik $ip $il $iy $iz).
      * inherit HE.
      * inherit HQ.
      * inherit HEq.
      * inherit HEtr.
      * inherit HC.
      * inherit HS.
      * apply Ctx. now left.
      * apply Ctx. right. now left.
      * inherit Hg.
      * inherit Hh.
Qed.

Lemma composition_property_at g h a n :
  (composition_property g h a)[n..] = (subset n a → composition_exists g h n).
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], n as [in_|[]].
  unfold composition_property, composition_exists, composition_prefix,
    composition_entries, composition_entry, composition_correct, composition_coverage,
    composition_edge, subset, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn [terms2 Vector.map subst_form subst_term up scons funcomp]. reflexivity.
Qed.

Lemma composition_induction_base G g h a :
  G ⊢238 ordinal_base (composition_property g h a).
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]]. unfold ordinal_base.
  apply AllI_named. intro n. destruct n as [in_|[]].
  change (G ⊢238 ((ordinal_representative $in_ ∧ raw_zero $in_) →
    (composition_property $ig $ih $ia)[$in_..])).
  rewrite composition_property_at. apply II, II.
  unfold composition_exists. apply (ExI $in_).
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
  apply empty_composition_prefix. eapply CE2, Ctx. right. now left.
Qed.

Lemma composition_induction_step G g h a b :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pair_equality_transitivity_ax ->
  G ⊢238 empty_ax -> G ⊢238 adjunction_ax -> G ⊢238 graph_typed g a b ->
  G ⊢238 graph_left_total g a -> G ⊢238 graph_left_total h b ->
  G ⊢238 ordinal_step (composition_property g h a).
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]].
  intros HE HQ HEq HEtr Hempty HA HT Hg Hh.
  apply ordinal_step_intro. intros n m. destruct n as [in_|[]], m as [im|[]].
  rewrite !composition_property_at. apply II.
  assert (HS : (subset $im $ia :: (subset $in_ $ia → composition_exists $ig $ih $in_) ::
    (ordinal_representative $in_ ∧ (ordinal_representative $im ∧ raw_successor $in_ $im)) :: G)
      ⊢238 raw_successor $in_ $im).
  { eapply CE2, CE2, Ctx. right. right. now left. }
  assert (Hm : (subset $im $ia :: (subset $in_ $ia → composition_exists $ig $ih $in_) ::
    (ordinal_representative $in_ ∧ (ordinal_representative $im ∧ raw_successor $in_ $im)) :: G)
      ⊢238 subset $im $ia).
  { apply Ctx. now left. }
  assert (Hn : (subset $im $ia :: (subset $in_ $ia → composition_exists $ig $ih $in_) ::
    (ordinal_representative $in_ ∧ (ordinal_representative $im ∧ raw_successor $in_ $im)) :: G)
      ⊢238 R $ia $in_).
  { apply (subset_member _ $im $ia $in_); [exact Hm|].
    apply (raw_successor_point_member _ $in_ $im); [inherit HE|exact HS]. }
  eapply ExE_named.
  - eapply IE; [apply Ctx; right; now left|].
    apply (subset_transitive _ $in_ $im $ia);
      [apply raw_successor_old_subset; exact HS|exact Hm].
  - intro k. destruct k as [ik|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    assert (HK : (composition_prefix $ig $ih $in_ $ik :: subset $im $ia ::
      (subset $in_ $ia → composition_exists $ig $ih $in_) ::
      (ordinal_representative $in_ ∧ (ordinal_representative $im ∧ raw_successor $in_ $im)) :: G)
       ⊢238 composition_prefix $ig $ih $in_ $ik).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (graph_left_total_instance _ $ig $ia $in_); [inherit Hg|inherit Hn].
    + intro y. destruct y as [iy|[]].
      cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
      assert (HY : (graph_edge $ig $in_ $iy :: composition_prefix $ig $ih $in_ $ik ::
        subset $im $ia :: (subset $in_ $ia → composition_exists $ig $ih $in_) ::
        (ordinal_representative $in_ ∧ (ordinal_representative $im ∧ raw_successor $in_ $im)) :: G)
          ⊢238 graph_edge $ig $in_ $iy).
      { apply Ctx. now left. }
      eapply ExE_named.
      * apply (graph_left_total_instance _ $ih $ib $iy); [inherit Hh|].
        eapply CE2. apply (graph_typed_instance _ $ig $ia $ib $in_ $iy);
          [inherit HT|exact HY].
      * intro z. destruct z as [iz|[]].
        cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
        apply (composition_prefix_extension _ $ig $ih $in_ $im $ik $iy $iz).
        -- inherit HE.
        -- inherit HQ.
        -- inherit HEq.
        -- inherit HEtr.
        -- inherit Hempty.
        -- inherit HA.
        -- inherit HK.
        -- inherit HS.
        -- inherit HY.
        -- apply Ctx. now left.
Qed.

Theorem S0_composition_graph_exists g h a b :
  derivable finite_set_S0
    (ordinal_representative a → (graph_typed g a b →
      (graph_left_total g a → (graph_left_total h b → composition_exists g h a)))).
Proof.
  destruct g as [ig|[]], h as [ih|[]], a as [ia|[]], b as [ib|[]].
  assert (HB : bounded (1 + S (ig + ih + ia)) (composition_property $ig $ih $ia)).
  { unfold composition_property, composition_exists, composition_prefix,
      composition_entries, composition_entry, composition_correct, composition_coverage,
      composition_edge, subset, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.
    cbn. fixed_bounds. }
  pose proof (S0_ordinal_induction (S (ig + ih + ia)) (composition_property $ig $ih $ia) HB) as HI.
  assert (Hbase : derivable finite_set_S0 (ordinal_base (composition_property $ig $ih $ia))).
  { exists []. split; [intros psi []|apply composition_induction_base]. }
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
  - apply II, II, II, II.
    assert (Hstep : (graph_left_total $ih $ib :: graph_left_total $ig $ia ::
      graph_typed $ig $ia $ib :: ordinal_representative $ia :: G)
       ⊢238 ordinal_step (composition_property $ig $ih $ia)).
    { apply (composition_induction_step _ $ig $ih $ia $ib).
      - inherit HE.
      - inherit HQ.
      - inherit HEq.
      - inherit HEtr.
      - inherit Hempty'.
      - inherit HA.
      - apply Ctx. right. right. now left.
      - apply Ctx. right. now left.
      - apply Ctx. now left. }
    assert (Hall : (graph_left_total $ih $ib :: graph_left_total $ig $ia ::
      graph_typed $ig $ia $ib :: ordinal_representative $ia :: G)
       ⊢238 ∀ (ordinal_representative $0 → composition_property $ig $ih $ia)).
    { eapply IE; [|exact Hstep]. eapply Weak; [exact Hind|]. intros psi Hpsi.
      right. right. right. right. unfold G. apply in_or_app. right. right.
      apply in_or_app. now right. }
    pose proof (AllE $ia Hall) as Hat.
    change ((graph_left_total $ih $ib :: graph_left_total $ig $ia ::
      graph_typed $ig $ia $ib :: ordinal_representative $ia :: G) ⊢238
      (ordinal_representative $ia → (composition_property $ig $ih $ia)[$ia..])) in Hat.
    rewrite composition_property_at in Hat. eapply IE; [|apply subset_reflexivity].
    eapply IE; [exact Hat|apply Ctx; right; right; right; now left].
Qed.

Print Assumptions composition_prefix_extension.
Print Assumptions composition_property_at.
Print Assumptions composition_induction_base.
Print Assumptions composition_induction_step.
Print Assumptions S0_composition_graph_exists.
Print Assumptions composition_edge_coordinate_transport.
Print Assumptions composition_entry_intro.
Print Assumptions composition_key_fresh.
Print Assumptions successor_composition_entries.
Print Assumptions successor_composition_correct.
Print Assumptions successor_composition_coverage.
Print Assumptions successor_composition_prefix.
Print Assumptions composition_edge_intro.
Print Assumptions composition_edge_typed.
Print Assumptions composition_edge_functional.
Print Assumptions composition_edge_injective.
Print Assumptions composition_edge_order.
Print Assumptions empty_composition_prefix.
End CompositionGraph238.
