(** Original finite proof transport from S0 to normalized pointed R9.
    The restricted supplier theory below has equality and pointed instances
    only: no global IR, collided schema, model, or correspondence premise.
    Faithful raw numeric R9/vacuity/name translation remains a separate leaf. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PointedSchemas238.

Inductive pointed_equality_theory : set_form -> Prop :=
| forward_equality phi : In phi equality_base -> pointed_equality_theory phi
| forward_pointed phi n :
    bounded 0 (forall_times n (pointed_ax phi)) ->
    pointed_equality_theory (forall_times n (pointed_ax phi)).

Lemma pointed_equality_closed phi : pointed_equality_theory phi -> bounded 0 phi.
Proof. intros [chi H | chi n H]; [now apply equality_base_closed | exact H]. Qed.

Lemma pointed_equality_in_compact phi : pointed_equality_theory phi -> compact_theory phi.
Proof. intros [chi H | chi n H]; [now apply compact_equality | now apply compact_pointed]. Qed.

Lemma forward_generalize phi :
  derivable pointed_equality_theory phi -> derivable pointed_equality_theory (∀ phi).
Proof. apply derivable_generalize, pointed_equality_closed. Qed.

Lemma forward_forall_times n phi :
  derivable pointed_equality_theory phi ->
  derivable pointed_equality_theory (forall_times n phi).
Proof.
  intro H. induction n as [|n IH]; [exact H |].
  change (derivable pointed_equality_theory (∀ forall_times n phi)).
  apply forward_generalize. exact IH.
Qed.

(** Every finite property receives enough explicit closing binders. The
    bounded-form witness supplies only syntax bounds, never a truth oracle. *)
Lemma forward_pointed_open phi : derivable pointed_equality_theory (pointed_ax phi).
Proof.
  destruct (find_bounded phi) as [n Hphi].
  assert (Hb : bounded (3 + n) phi).
  { eapply bounded_up; [exact Hphi | lia]. }
  set (G := [forall_times n (pointed_ax phi)]).
  exists G. split.
  - intros psi [<- | []]. apply forward_pointed, pointed_instance_closed. exact Hb.
  - assert (HA : G ⊢238 forall_times n (pointed_ax phi)).
    { apply Ctx. now left. }
    pose proof (@subst_forall_prv sig_empty ZF_pred_sig falsity_on class
      (pointed_ax phi) n G HA (pointed_ax_bounded n phi Hb) var) as H.
    rewrite subst_var in H. exact H.
Qed.

(** Elementary ordinary-equality derivations are local to this independent
    schema leaf. These are proved instances of the displayed equality base. *)
Definition equality_membership_ax : set_form :=
  ∀ ∀ ∀ ∀ (E $3 $1 → E $2 $0 → R $2 $3 → R $0 $1).
Definition equality_symmetry_ax : set_form := ∀ ∀ (E $1 $0 → E $0 $1).

Lemma equality_membership_instance G x a y b :
  G ⊢238 equality_membership_ax ->
  G ⊢238 (E x y → E a b → R a x → R b y).
Proof.
  destruct x as [ix|[]], a as [ia|[]], y as [iy|[]], b as [ib|[]].
  intro H. unfold equality_membership_ax in H.
  pose proof (AllE $ib (AllE $iy (AllE $ia (AllE $ix H)))) as H'.
  cbn [E R terms2 subst_form subst_term up scons funcomp] in H'. exact H'.
Qed.

Lemma equality_symmetry_instance G x y :
  G ⊢238 equality_symmetry_ax -> G ⊢238 E x y -> G ⊢238 E y x.
Proof.
  destruct x as [ix|[]], y as [iy|[]]. intros HE Hxy.
  unfold equality_symmetry_ax in HE. pose proof (AllE $iy (AllE $ix HE)) as H.
  cbn [R E terms2 subst_form subst_term up scons funcomp] in H. exact (IE H Hxy).
Qed.

Lemma equality_member_transport G a x y :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 E x y -> G ⊢238 R a x -> G ⊢238 R a y.
Proof.
  intros HE HQ Hxy HX. eapply IE; [|exact HX].
  eapply IE; [|exact (AllE a HE)]. eapply IE; [|exact Hxy].
  apply equality_membership_instance. exact HQ.
Qed.

Ltac inherit H :=
  eapply Weak; [exact H |]; intros chi Hchi; repeat right; exact Hchi.

Definition adjunction_property : set_form := R $1 $0 ∨ E $0 $2.
Definition adjunction_witness (u x c : set_term) : set_form :=
  ∀ (R c`[↑] $0 ↔ (R u`[↑] $0 ∨ E $0 x`[↑])).
Definition pointed_adjunction_body (u x c : set_term) : set_form :=
  (∀ ((R u`[↑] $0 → ((R u`[↑] $0 ∨ E $0 x`[↑]) → R c`[↑] $0)) ∧
       (R c`[↑] $0 → (R u`[↑] $0 ∨ E $0 x`[↑])))) ∧
  ((R u x ∨ E x x) → R c x).

Lemma adjunction_witness_at u x c :
  (adjunction_witness u`[↑] x`[↑] $0)[c..] = adjunction_witness u x c.
Proof.
  destruct u as [iu | []], x as [ix | []], c as [ic | []].
  unfold adjunction_witness.
  cbn [R E terms2 subst_form subst_term up scons funcomp]. reflexivity.
Qed.

Lemma pointed_adjunction_body_at u x c :
  (pointed_adjunction_body u`[↑] x`[↑] $0)[c..] = pointed_adjunction_body u x c.
Proof.
  destruct u as [iu | []], x as [ix | []], c as [ic | []].
  unfold pointed_adjunction_body.
  cbn [R E terms2 subst_form subst_term up scons funcomp]. reflexivity.
Qed.

Lemma pointed_adjunction_inputs G u x :
  G ⊢238 pointed_ax adjunction_property ->
  G ⊢238 ∃ pointed_adjunction_body u`[↑] x`[↑] $0.
Proof.
  destruct u as [iu | []], x as [ix | []]. intro HP.
  unfold pointed_ax in HP. pose proof (AllE $ix (AllE $iu HP)) as H.
  unfold pointed_body, adjunction_property in H.
  unfold pointed_adjunction_body.
  cbn [R E terms2 subst_form subst_term member_slots point_slots up scons funcomp] in *.
  exact H.
Qed.

Lemma pointed_adjunction_member G u x c y :
  G ⊢238 pointed_adjunction_body u x c ->
  G ⊢238 ((R u y → ((R u y ∨ E y x) → R c y)) ∧
          (R c y → (R u y ∨ E y x))).
Proof.
  intro HB. unfold pointed_adjunction_body in HB.
  pose proof (AllE y (CE1 HB)) as H.
  cbn [subst_form R E terms2 Vector.map] in H.
  rewrite !subst_term_shift in H. exact H.
Qed.

Lemma pointed_adjunction_derives G u x c :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 equality_membership_ax -> G ⊢238 pointed_adjunction_body u x c ->
  G ⊢238 adjunction_witness u x c.
Proof.
  intros HE HS HM HB.
  assert (Hpoint : G ⊢238 R c x).
  { eapply IE; [exact (CE2 HB) |]. apply DI2. exact (AllE x HE). }
  unfold adjunction_witness. apply AllI_named. intro y.
  destruct y as [iy | []].
  cbn [subst_form R E terms2 Vector.map subst_term up scons funcomp].
  rewrite !subst_term_shift.
  pose proof (pointed_adjunction_member G u x c $iy HB) as Hmember.
  apply CI.
  - apply II. eapply IE; [inherit (CE2 Hmember) |]. apply Ctx. now left.
  - apply II. eapply DE; [apply Ctx; now left | |].
    + eapply IE.
      * eapply IE; [inherit (CE1 Hmember) |]. apply Ctx. now left.
      * apply DI1, Ctx. now left.
    + apply (equality_member_transport _ c x $iy).
      * inherit HE.
      * inherit HM.
      * apply (equality_symmetry_instance _ $iy x); [inherit HS |].
        apply Ctx. now left.
      * inherit Hpoint.
Qed.

Lemma pointed_to_adjunction G :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 equality_membership_ax -> G ⊢238 pointed_ax adjunction_property ->
  G ⊢238 adjunction_ax.
Proof.
  intros HE HS HM HP. unfold adjunction_ax.
  apply AllI_named. intro u. destruct u as [iu | []].
  apply AllI_named. intro x. destruct x as [ix | []].
  change (G ⊢238 ∃ adjunction_witness $iu`[↑] $ix`[↑] $0).
  eapply ExE_named; [exact (pointed_adjunction_inputs G $iu $ix HP) |].
  intro c. rewrite pointed_adjunction_body_at.
  apply (ExI c). rewrite adjunction_witness_at.
  apply pointed_adjunction_derives.
  - inherit HE.
  - inherit HS.
  - inherit HM.
  - apply Ctx. now left.
Qed.

Theorem forward_adjunction : derivable pointed_equality_theory adjunction_ax.
Proof.
  destruct (forward_pointed_open adjunction_property) as [G [HG HP]].
  set (H := equality_base ++ G). exists H. split.
  - intros phi Hphi. apply in_app_or in Hphi as [Hphi | Hphi].
    + now apply forward_equality.
    + now apply HG.
  - apply pointed_to_adjunction.
    + apply Ctx. unfold H. apply in_or_app. left. now left.
    + apply Ctx. unfold H, equality_base, equality_symmetry_ax.
      apply in_or_app. left. right. now left.
    + apply Ctx. unfold H, equality_base, equality_membership_ax.
      apply in_or_app. left. right. right. right. now left.
    + eapply Weak; [exact HP |]. intros phi Hphi. unfold H.
      apply in_or_app. now right.
Qed.

Print Assumptions forward_pointed_open.
Print Assumptions forward_adjunction.


Definition separation_lift : nat -> set_term := $0 .: (fun k => $(3 + k)).
Definition separation_property (phi : set_form) : set_form :=
  R $1 $0 ∧ phi[separation_lift].
Definition separation_witness (u c : set_term) (phi : set_form) : set_form :=
  ∀ (R c`[↑] $0 ↔ (R u`[↑] $0 ∧ phi)).
Definition pointed_separation_body (u x c : set_term) (phi : set_form) : set_form :=
  (∀ ((R u`[↑] $0 → ((R u`[↑] $0 ∧ phi) → R c`[↑] $0)) ∧
       (R c`[↑] $0 → (R u`[↑] $0 ∧ phi)))) ∧
  ((R u x ∧ phi[x..]) → R c x).

Lemma separation_member_inputs (phi : set_form) (u x : set_term) :
  (phi[separation_lift][member_slots])[up (up (up (u..)))][up (up (x..))] = phi[up ↑].
Proof.
  rewrite !subst_comp. apply subst_ext. intros [|k];
    cbn [separation_lift member_slots up scons funcomp subst_term]; reflexivity.
Qed.

Lemma separation_point_inputs (phi : set_form) (u x : set_term) :
  (phi[separation_lift][point_slots])[up (up (u..))][up (x..)] =
  (phi[up ↑])[x`[↑]..].
Proof.
  rewrite !subst_comp. apply subst_ext. intros [|k];
    cbn [separation_lift point_slots up scons funcomp subst_term]; reflexivity.
Qed.

Lemma separation_member_drop (phi : set_form) (c : set_term) : (phi[up ↑])[up (c..)] = phi.
Proof.
  rewrite subst_comp. transitivity (phi[var]); [|apply subst_var].
  apply subst_ext. intros [|k]; cbn [up scons funcomp subst_term]; reflexivity.
Qed.

Lemma separation_point_drop (phi : set_form) (x c : set_term) :
  ((phi[up ↑])[x`[↑]..])[c..] = phi[x..].
Proof.
  destruct x as [ix|[]], c as [ic|[]]. rewrite !subst_comp.
  apply subst_ext. intros [|k]; cbn [up scons funcomp subst_term]; reflexivity.
Qed.

Lemma separation_witness_at u c phi :
  (separation_witness u`[↑] $0 (phi[up ↑]))[c..] = separation_witness u c phi.
Proof.
  destruct u as [iu|[]], c as [ic|[]].
  change ((∀ (R $ic`[↑] $0 ↔
      (R $iu`[↑] $0 ∧ (phi[up ↑])[up ($ic..)]))) =
      separation_witness $iu $ic phi).
  pose proof (separation_member_drop phi $ic) as Hdrop.
  pose proof (f_equal (fun property : set_form =>
    ∀ (R $ic`[↑] $0 ↔ (R $iu`[↑] $0 ∧ property))) Hdrop) as Hcandidate.
  exact Hcandidate.
Qed.

Lemma pointed_separation_body_at u x c phi :
  (pointed_separation_body u`[↑] x`[↑] $0 (phi[up ↑]))[c..] =
  pointed_separation_body u x c phi.
Proof.
  destruct u as [iu|[]], x as [ix|[]], c as [ic|[]].
  change (((∀ ((R $iu`[↑] $0 →
      ((R $iu`[↑] $0 ∧ (phi[up ↑])[up ($ic..)]) → R $ic`[↑] $0)) ∧
      (R $ic`[↑] $0 → (R $iu`[↑] $0 ∧ (phi[up ↑])[up ($ic..)])))) ∧
      ((R $iu $ix ∧ ((phi[up ↑])[$ix`[↑]..])[$ic..]) → R $ic $ix)) =
      pointed_separation_body $iu $ix $ic phi).
  pose proof (separation_member_drop phi $ic) as Hmember.
  pose proof (separation_point_drop phi $ix $ic) as Hpoint.
  pose proof (f_equal2 (fun member_property point_property : set_form =>
    (∀ ((R $iu`[↑] $0 → ((R $iu`[↑] $0 ∧ member_property) → R $ic`[↑] $0)) ∧
         (R $ic`[↑] $0 → (R $iu`[↑] $0 ∧ member_property)))) ∧
    ((R $iu $ix ∧ point_property) → R $ic $ix)) Hmember Hpoint) as Hcandidate.
  exact Hcandidate.
Qed.

Lemma pointed_separation_inputs G phi u x :
  G ⊢238 pointed_ax (separation_property phi) ->
  G ⊢238 ∃ pointed_separation_body u`[↑] x`[↑] $0 (phi[up ↑]).
Proof.
  destruct u as [iu|[]], x as [ix|[]]. intro HP.
  unfold pointed_ax in HP. pose proof (AllE $ix (AllE $iu HP)) as H.
  change (G ⊢238 ∃
    ((∀ ((R $iu`[↑]`[↑] $0 →
      ((R $iu`[↑]`[↑] $0 ∧
        (phi[separation_lift][member_slots])[up (up (up ($iu..)))][up (up ($ix..))]) → R $1 $0)) ∧
      (R $1 $0 → (R $iu`[↑]`[↑] $0 ∧
        (phi[separation_lift][member_slots])[up (up (up ($iu..)))][up (up ($ix..))])))) ∧
      ((R $iu`[↑] $ix`[↑] ∧
        (phi[separation_lift][point_slots])[up (up ($iu..))][up ($ix..)]) → R $0 $ix`[↑]))) in H.
  pose proof (f_equal2 (fun member_property point_property : set_form =>
    ∃ ((∀ ((R $iu`[↑]`[↑] $0 →
      ((R $iu`[↑]`[↑] $0 ∧ member_property) → R $1 $0)) ∧
      (R $1 $0 → (R $iu`[↑]`[↑] $0 ∧ member_property)))) ∧
      ((R $iu`[↑] $ix`[↑] ∧ point_property) → R $0 $ix`[↑])))
    (separation_member_inputs phi $iu $ix) (separation_point_inputs phi $iu $ix)) as Hformula.
  exact (eq_rect _ (fun formula : set_form => G ⊢238 formula) H _ Hformula).
Qed.

Lemma pointed_separation_member G u x c phi y :
  G ⊢238 pointed_separation_body u x c phi ->
  G ⊢238 ((R u y → ((R u y ∧ phi[y..]) → R c y)) ∧
          (R c y → (R u y ∧ phi[y..]))).
Proof.
  intro HB. unfold pointed_separation_body in HB.
  pose proof (AllE y (CE1 HB)) as H.
  cbn [subst_form R terms2 Vector.map] in H.
  rewrite !subst_term_shift in H. exact H.
Qed.

Lemma pointed_separation_derives G u x c phi :
  G ⊢238 pointed_separation_body u x c phi -> G ⊢238 separation_witness u c phi.
Proof.
  intro HB. unfold separation_witness. apply AllI_named. intro y.
  destruct y as [iy|[]]. cbn [subst_form R terms2 Vector.map subst_term up scons funcomp].
  rewrite !subst_term_shift.
  pose proof (pointed_separation_member G u x c phi $iy HB) as Hmember.
  apply CI.
  - apply II. eapply IE; [inherit (CE2 Hmember)|]. apply Ctx. now left.
  - apply II. eapply IE.
    + eapply IE; [inherit (CE1 Hmember)|]. eapply CE1. apply Ctx. now left.
    + apply Ctx. now left.
Qed.

Lemma separation_input_property (phi : set_form) (s : set_term) :
  (phi[separation_slots])[up (up (s..))] = phi[up ↑].
Proof.
  rewrite subst_comp. apply subst_ext. intros [|k];
    cbn [separation_slots up scons funcomp subst_term]; reflexivity.
Qed.

Lemma pointed_to_separation G phi :
  G ⊢238 pointed_ax (separation_property phi) -> G ⊢238 separation_ax phi.
Proof.
  intro HP. unfold separation_ax. apply AllI_named. intro u. destruct u as [iu|[]].
  change (G ⊢238 ∃ separation_witness $iu`[↑] $0
    (phi[separation_slots][up (up ($iu..))])).
  pose proof (f_equal (fun property : set_form =>
    ∃ separation_witness $iu`[↑] $0 property) (separation_input_property phi $iu)) as Hformula.
  refine (eq_rect _ (fun formula : set_form => G ⊢238 formula) _ _ (eq_sym Hformula)).
  eapply ExE_named; [exact (pointed_separation_inputs G phi $iu $iu HP)|].
  intro c. rewrite pointed_separation_body_at.
  apply (ExI c). rewrite separation_witness_at.
  apply (pointed_separation_derives _ $iu $iu c phi), Ctx. now left.
Qed.

Theorem forward_separation phi : derivable pointed_equality_theory (separation_ax phi).
Proof.
  destruct (forward_pointed_open (separation_property phi)) as [G [HG HP]].
  exists G. split; [exact HG|]. apply pointed_to_separation. exact HP.
Qed.

(** Finite context substitution is built by induction on the context. Each
    cut uses [derivable_mp], which explicitly retains a finite union of the
    two supplier contexts; no choice or consistency implication is used. *)
Lemma derivable_context_cut U G phi :
  G ⊢238 phi ->
  (forall psi, In psi G -> derivable U psi) -> derivable U phi.
Proof.
  revert phi. induction G as [|a G IH]; intros phi Hproof Hsuppliers.
  - exists []. split; [intros psi Hpsi; inversion Hpsi|exact Hproof].
  - apply (derivable_mp U a phi).
    + apply IH.
      * apply II. exact Hproof.
      * intros psi Hpsi. apply Hsuppliers. now right.
    + apply Hsuppliers. now left.
Qed.

Lemma finite_theory_transport T U :
  (forall phi, T phi -> derivable U phi) ->
  forall phi, derivable T phi -> derivable U phi.
Proof.
  intros Hsupplier phi [G [HG Hproof]].
  apply (derivable_context_cut U G phi Hproof).
  intros psi Hpsi. apply Hsupplier, HG, Hpsi.
Qed.

Print Assumptions forward_separation.

End PointedSchemas238.
