(** Original finite S0 certificates for the represented PA addition laws.
    Closed finite contexts are selected before the displayed term binders.
    Independent traces retain their actual zero, pair and graph witnesses;
    the conclusions compare results through actual order isomorphisms. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 OrdinalSuccessor238
  OrdinalTrace238 PairGraph238 GraphTransport238 TraceGraph238 AddGraph238
  IsoGraph238 IsoZero238 IsoEquality238 TraceRestriction238
  AddCoherence238 IsoSuccessorS0238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 OrdinalTrace238.OrdinalTrace238
  PairGraph238.PairGraph238 GraphTransport238.GraphTransport238
  TraceGraph238.TraceGraph238 AddGraph238.AddGraph238
  IsoGraph238.IsoGraph238 IsoZero238.IsoZero238 IsoEquality238.IsoEquality238
  TraceRestriction238.TraceRestriction238 AddCoherence238.AddCoherence238
  IsoSuccessorS0238.IsoSuccessorS0238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module AddPALaws238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition add_fixed_comparison_ax : set_form :=
  ∀ ∀ ∀ ∀ (ordinal_representative $3 → ordinal_representative $2 →
    add_result $3 $2 $1 → add_result $3 $2 $0 → order_iso $1 $0).

Lemma add_fixed_comparison_ax_closed : bounded 0 add_fixed_comparison_ax.
Proof. unfold add_fixed_comparison_ax. unfold_add_iso_syntax. cbn. fixed_bounds. Qed.

Theorem S0_add_fixed_comparison_closed : derivable finite_set_S0 add_fixed_comparison_ax.
Proof.
  unfold add_fixed_comparison_ax.
  apply S0_generalize, S0_generalize, S0_generalize, S0_generalize.
  exact (S0_add_determinacy $3 $2 $1 $0).
Qed.

Lemma add_fixed_comparison_instance G x y z z' :
  G ⊢238 add_fixed_comparison_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative y -> G ⊢238 add_result x y z ->
  G ⊢238 add_result x y z' -> G ⊢238 order_iso z z'.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]], z' as [iz'|[]].
  intros HC HX HY HA HA'. unfold add_fixed_comparison_ax in HC.
  pose proof (AllE $iz' (AllE $iz (AllE $iy (AllE $ix HC)))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (IE (IE (IE H HX) HY) HA) HA').
Qed.

Definition add_left_zero_ax : set_form :=
  ∀ ∀ ∀ (ordinal_representative $2 → raw_zero $2 → ordinal_representative $1 →
    add_result $2 $1 $0 → order_iso $0 $1).

Lemma add_left_zero_ax_closed : bounded 0 add_left_zero_ax.
Proof. unfold add_left_zero_ax. unfold_add_iso_syntax. cbn. fixed_bounds. Qed.

Theorem add_left_zero_at G e y z :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 add_iso_reflexivity_ax -> G ⊢238 ordinal_representative e ->
  G ⊢238 raw_zero e -> G ⊢238 ordinal_representative y ->
  G ⊢238 add_result e y z -> G ⊢238 order_iso z y.
Proof.
  intros HE HQ HEq HEtr Href HEord HZ HY HA.
  apply (order_iso_coordinate_transport _ y y z y).
  - exact HE.
  - exact HQ.
  - exact HEq.
  - apply equality_symmetry_instance; [exact HEq|].
    apply (add_result_zero_value _ e y z); assumption.
  - exact (AllE y HE).
  - apply (add_iso_reflexivity_instance _ y); assumption.
Qed.

Theorem S0_add_left_zero_closed : derivable finite_set_S0 add_left_zero_ax.
Proof.
  destruct S0_add_iso_reflexivity_closed as [Gref [HGref Href]].
  set (G := equality_base ++ Gref).
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
  assert (Href' : G ⊢238 add_iso_reflexivity_ax).
  { eapply Weak; [exact Href|]. intros psi Hpsi. unfold G. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + now apply HGref.
  - unfold add_left_zero_ax. apply AllI_named. intro e. destruct e as [ie|[]].
    apply AllI_named. intro y. destruct y as [iy|[]].
    apply AllI_named. intro z. destruct z as [iz|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp]. apply II, II, II, II.
    apply (add_left_zero_at _ $ie $iy $iz).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Href'.
    + apply Ctx. right. right. right. now left.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Lemma add_left_zero_instance G e y z :
  G ⊢238 add_left_zero_ax -> G ⊢238 ordinal_representative e -> G ⊢238 raw_zero e ->
  G ⊢238 ordinal_representative y -> G ⊢238 add_result e y z -> G ⊢238 order_iso z y.
Proof.
  destruct e as [ie|[]], y as [iy|[]], z as [iz|[]]. intros HC HE HZ HY HA.
  unfold add_left_zero_ax in HC. pose proof (AllE $iz (AllE $iy (AllE $ie HC))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (IE (IE (IE H HE) HZ) HY) HA).
Qed.

Definition add_left_successor_ax : set_form :=
  ∀ ∀ ∀ ∀ ∀ ∀ (ordinal_representative $5 → ordinal_representative $3 →
    raw_successor $5 $4 → add_result $5 $3 $2 → raw_successor $2 $1 →
    add_result $4 $3 $0 → order_iso $0 $1).

Lemma add_left_successor_ax_closed : bounded 0 add_left_successor_ax.
Proof. unfold add_left_successor_ax. unfold_add_iso_syntax. cbn. fixed_bounds. Qed.

(** The successor trace is actually restricted to the old input ordinal.
    Its previous value is compared with the specified old sum through
    fixed-operand determinacy; a constructed successor Iso finishes. *)
Theorem add_left_successor_at G x sx y z sz w :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 equality_transitivity_ax ->
  G ⊢238 graph_restriction_ax -> G ⊢238 add_fixed_comparison_ax ->
  G ⊢238 iso_successor_congruence_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative y -> G ⊢238 raw_successor x sx ->
  G ⊢238 add_result x y z -> G ⊢238 raw_successor z sz ->
  G ⊢238 add_result sx y w -> G ⊢238 order_iso w sz.
Proof.
  destruct x as [ix|[]], sx as [isx|[]], y as [iy|[]], z as [iz|[]],
    sz as [isz|[]], w as [iw|[]].
  intros HE HQ HEq HEtr Hcuts Hfixed Hsucc HX HY HS HA Hzs HA'.
  eapply ExE_named.
  - apply (add_result_predecessor_witness _ $ix $isx $iy $iw); assumption.
  - intro q. destruct q as [iq|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply (iso_successor_congruence_instance _ $iq $iw $iz $isz).
    + inherit Hsucc.
    + apply (add_result_ordinal _ $ix $iy $iq). eapply CE1, Ctx. now left.
    + apply (add_result_ordinal _ $ix $iy $iz). inherit HA.
    + eapply CE2, Ctx. now left.
    + inherit Hzs.
    + apply (add_fixed_comparison_instance _ $ix $iy $iq $iz).
      * inherit Hfixed.
      * inherit HX.
      * inherit HY.
      * eapply CE1, Ctx. now left.
      * inherit HA.
Qed.

Theorem S0_add_left_successor_closed : derivable finite_set_S0 add_left_successor_ax.
Proof.
  destruct S0_graph_restriction_closed as [Gcuts [HGcuts Hcuts]].
  destruct S0_add_fixed_comparison_closed as [Gfixed [HGfixed Hfixed]].
  destruct S0_order_iso_successor_congruence_closed as [Gsucc [HGsucc Hsucc]].
  set (G := equality_base ++ Gcuts ++ Gfixed ++ Gsucc).
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
  assert (Hcuts' : G ⊢238 graph_restriction_ax).
  { eapply Weak; [exact Hcuts|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. now left. }
  assert (Hfixed' : G ⊢238 add_fixed_comparison_ax).
  { eapply Weak; [exact Hfixed|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. now left. }
  assert (Hsucc' : G ⊢238 iso_successor_congruence_ax).
  { eapply Weak; [exact Hsucc|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + apply S0_base. apply in_or_app. now left.
    + apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGcuts|].
      apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGfixed|now apply HGsucc].
  - unfold add_left_successor_ax. apply AllI_named. intro x. destruct x as [ix|[]].
    apply AllI_named. intro sx. destruct sx as [isx|[]].
    apply AllI_named. intro y. destruct y as [iy|[]].
    apply AllI_named. intro z. destruct z as [iz|[]].
    apply AllI_named. intro sz. destruct sz as [isz|[]].
    apply AllI_named. intro w. destruct w as [iw|[]].
    cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
    apply II, II, II, II, II, II. apply (add_left_successor_at _ $ix $isx $iy $iz $isz $iw).
    + inherit HE.
    + inherit HQ.
    + inherit HEq.
    + inherit HEtr.
    + inherit Hcuts'.
    + inherit Hfixed'.
    + inherit Hsucc'.
    + apply Ctx. right. right. right. right. right. now left.
    + apply Ctx. right. right. right. right. now left.
    + apply Ctx. right. right. right. now left.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Lemma add_left_successor_instance G x sx y z sz w :
  G ⊢238 add_left_successor_ax -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative y -> G ⊢238 raw_successor x sx ->
  G ⊢238 add_result x y z -> G ⊢238 raw_successor z sz ->
  G ⊢238 add_result sx y w -> G ⊢238 order_iso w sz.
Proof.
  destruct x as [ix|[]], sx as [isx|[]], y as [iy|[]], z as [iz|[]],
    sz as [isz|[]], w as [iw|[]]. intros HC HX HY HS HA Hzs HA'.
  unfold add_left_successor_ax in HC.
  pose proof (AllE $iw (AllE $isz (AllE $iz (AllE $iy (AllE $isx (AllE $ix HC)))))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE (IE (IE (IE (IE (IE H HX) HY) HS) HA) Hzs) HA').
Qed.

Print Assumptions add_fixed_comparison_ax_closed.
Print Assumptions S0_add_fixed_comparison_closed.
Print Assumptions add_fixed_comparison_instance.
Print Assumptions add_left_zero_ax_closed.
Print Assumptions S0_add_left_zero_closed.
Print Assumptions add_left_zero_instance.
Print Assumptions add_left_successor_ax_closed.
Print Assumptions S0_add_left_successor_closed.
Print Assumptions add_left_successor_instance.
End AddPALaws238.
