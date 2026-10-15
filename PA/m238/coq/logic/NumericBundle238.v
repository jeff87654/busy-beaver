(** Original gated PA238 bundle transport.
    The decoded predicate's own code is a fresh output name. Pointed and
    collided normalized instances are read through explicit substitutions;
    the two source vacuity conjuncts retain their exact freshness gate. *)
From Coq Require Import Arith Lia Bool List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.logic Require Import Codes238 Compiler238 NumericSyntax238 NumericSound238.
From P238.arith Require Import Compact238.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module NumericBundle238.
Module C := Compact238.Compact238.
Module N := NumericSyntax238.NumericSyntax238.
Module S := NumericSound238.NumericSound238.
Notation "G ⊢N phi" :=
  (@prv sig_empty ZF_pred_sig falsity_on class G phi) (at level 61).

Definition identity_env : N.named_env := fun v => $v.

Lemma closed_context_substitution (G : list C.set_form) (sigma : nat -> C.set_term) :
  (forall phi, In phi G -> bounded 0 phi) -> map (subst_form sigma) G = G.
Proof.
  induction G as [|phi G IH]; intro HG; cbn; [reflexivity|].
  rewrite bounded_0_subst by (apply HG; now left); f_equal.
  apply IH. intros psi Hpsi; apply HG; now right.
Qed.

Lemma compact_substitution phi sigma : C.derivable C.compact_theory phi ->
  C.derivable C.compact_theory (phi[sigma]).
Proof.
  intros [G [HG Hphi]]; exists G; split; [exact HG|].
  pose proof (subst_Weak sigma Hphi) as H.
  rewrite closed_context_substitution in H; [exact H|].
  intros psi Hpsi; apply C.compact_theory_closed, HG, Hpsi.
Qed.

Lemma compact_environment n rho :
  C.derivable C.compact_theory (N.interpret_code n identity_env) ->
  C.derivable C.compact_theory (N.interpret_code n rho).
Proof.
  intro H; assert (Heq : (N.interpret_code n identity_env)[rho] = N.interpret_code n rho).
  { unfold N.interpret_code; rewrite N.interpret_substitution.
    apply N.interpret_env_ext. intro v; reflexivity. }
  rewrite <- Heq; apply compact_substitution; exact H.
Qed.

Lemma compact_pointed_open phi : C.derivable C.compact_theory (C.pointed_ax phi).
Proof.
  destruct (find_bounded phi) as [n Hphi].
  assert (Hb : bounded (3 + n) phi) by (eapply bounded_up; [exact Hphi|lia]).
  destruct (C.compact_pointed_instance n phi Hb) as [G [HG Hax]].
  exists G; split; [exact HG|].
  pose proof (@subst_forall_prv sig_empty ZF_pred_sig falsity_on class
    (C.pointed_ax phi) n G Hax (C.pointed_ax_bounded n phi Hb) var) as H.
  rewrite subst_var in H; exact H.
Qed.

Lemma compact_collided_open phi : C.derivable C.compact_theory (C.collided_ax phi).
Proof.
  destruct (find_bounded phi) as [n Hphi].
  assert (Hb : bounded (1 + n) phi) by (eapply bounded_up; [exact Hphi|lia]).
  exists [forall_times n (C.collided_ax phi)]; split.
  - intros psi [<-|[]]; apply C.compact_collided, C.collided_instance_closed; exact Hb.
  - assert (Hax : [forall_times n (C.collided_ax phi)] ⊢N forall_times n (C.collided_ax phi)).
    { apply Ctx; now left. }
    pose proof (@subst_forall_prv sig_empty ZF_pred_sig falsity_on class
      (C.collided_ax phi) n _ Hax (C.collided_ax_bounded n phi Hb) var) as H.
    rewrite subst_var in H; exact H.
Qed.

Definition pointed_template_env (a b : nat) : N.named_env :=
  fun v => if Nat.eqb v b then $0 else if Nat.eqb v a then $1 else $(3 + v).
Definition pointed_property a b c := N.interpret_code c (pointed_template_env a b).
Definition collided_template_env (a : nat) : N.named_env :=
  fun v => if Nat.eqb v a then $0 else $(1 + v).
Definition collided_property a c := N.interpret_code c (collided_template_env a).

Local Opaque N.decode N.decode_fuel N.decode_node P unP triangle.

Lemma pointed_member_readout a b c t : c <> a -> c <> b ->
  (pointed_property a b c)[C.member_slots]
    [up (up (up ($a..)))][up (up ($b..))][up (t..)] =
  N.interpret_code c (N.bind_env (N.update_env identity_env c t) b).
Proof.
  destruct t as [it|[]]; intros Hca Hcb.
  unfold pointed_property, N.interpret_code; rewrite !N.interpret_substitution.
  apply N.interpret_env_agree; intros v Hv; unfold pointed_template_env.
  destruct (Nat.eqb v b) eqn:Eb.
  - apply Nat.eqb_eq in Eb; subst v.
    unfold N.bind_env; rewrite Nat.eqb_refl.
    cbn [C.member_slots up scons funcomp subst_term]; reflexivity.
  - destruct (Nat.eqb v a) eqn:Ea.
    + apply Nat.eqb_eq in Ea; subst v.
      unfold N.bind_env, N.update_env, identity_env.
      rewrite Eb, (proj2 (Nat.eqb_neq a c) ltac:(congruence)).
      cbn [C.member_slots up scons funcomp subst_term]; reflexivity.
    + unfold N.bind_env, N.update_env, identity_env; rewrite Eb.
      destruct (Nat.eqb v c) eqn:Ec.
      * apply Nat.eqb_eq in Ec; subst v; rewrite N.decode_self_fresh in Hv; discriminate.
      * cbn [C.member_slots up scons funcomp subst_term]; reflexivity.
Qed.

Lemma pointed_point_readout a b c t : c <> a -> c <> b ->
  (pointed_property a b c)[C.point_slots]
    [up (up ($a..))][up ($b..)][t..] =
  N.interpret_code c (N.update_env identity_env c t).
Proof.
  destruct t as [it|[]]; intros Hca Hcb.
  unfold pointed_property, N.interpret_code; rewrite !N.interpret_substitution.
  apply N.interpret_env_agree; intros v Hv; unfold pointed_template_env.
  destruct (Nat.eqb v b) eqn:Eb.
  - apply Nat.eqb_eq in Eb; subst v; unfold N.update_env, identity_env.
    rewrite (proj2 (Nat.eqb_neq b c) ltac:(congruence)).
    cbn [C.point_slots up scons funcomp subst_term]; reflexivity.
  - destruct (Nat.eqb v a) eqn:Ea.
    + apply Nat.eqb_eq in Ea; subst v; unfold N.update_env, identity_env.
      rewrite (proj2 (Nat.eqb_neq a c) ltac:(congruence)).
      cbn [C.point_slots up scons funcomp subst_term]; reflexivity.
    + unfold N.update_env, identity_env; destruct (Nat.eqb v c) eqn:Ec.
      * apply Nat.eqb_eq in Ec; subst v; rewrite N.decode_self_fresh in Hv; discriminate.
      * cbn [C.point_slots up scons funcomp subst_term]; reflexivity.
Qed.

Lemma collided_member_readout a c t : c <> a ->
  (collided_property a c)[C.collision_member_slots][up (up ($a..))][up (t..)] =
  N.interpret_code c (N.bind_env (N.update_env identity_env c t) a).
Proof.
  destruct t as [it|[]]; intro Hca.
  unfold collided_property, N.interpret_code; rewrite !N.interpret_substitution.
  apply N.interpret_env_agree; intros v Hv; unfold collided_template_env.
  destruct (Nat.eqb v a) eqn:Ea.
  - apply Nat.eqb_eq in Ea; subst v; unfold N.bind_env; rewrite Nat.eqb_refl.
    cbn [C.collision_member_slots up scons funcomp subst_term]; reflexivity.
  - unfold N.bind_env, N.update_env, identity_env; rewrite Ea.
    destruct (Nat.eqb v c) eqn:Ec.
    + apply Nat.eqb_eq in Ec; subst v; rewrite N.decode_self_fresh in Hv; discriminate.
    + cbn [C.collision_member_slots up scons funcomp subst_term]; reflexivity.
Qed.

Lemma collided_point_readout a c t : c <> a ->
  (collided_property a c)[C.collision_point_slots][up ($a..)][t..] =
  N.interpret_code c (N.update_env identity_env c t).
Proof.
  destruct t as [it|[]]; intro Hca.
  unfold collided_property, N.interpret_code; rewrite !N.interpret_substitution.
  apply N.interpret_env_agree; intros v Hv; unfold collided_template_env.
  destruct (Nat.eqb v a) eqn:Ea.
  - apply Nat.eqb_eq in Ea; subst v; unfold N.update_env, identity_env.
    rewrite (proj2 (Nat.eqb_neq a c) ltac:(congruence)).
    cbn [C.collision_point_slots up scons funcomp subst_term]; reflexivity.
  - unfold N.update_env, identity_env; destruct (Nat.eqb v c) eqn:Ec.
    + apply Nat.eqb_eq in Ec; subst v; rewrite N.decode_self_fresh in Hv; discriminate.
    + cbn [C.collision_point_slots up scons funcomp subst_term]; reflexivity.
Qed.

Definition pointed_matrix a b c (t : C.set_term) : C.set_form :=
  (∀ ((C.R ($a)`[↑] $0 →
        (N.interpret_code c (N.bind_env (N.update_env identity_env c t) b) → C.R t`[↑] $0)) ∧
       (C.R t`[↑] $0 → N.interpret_code c (N.bind_env (N.update_env identity_env c t) b)))) ∧
  (N.interpret_code c (N.update_env identity_env c t) → C.R t $b).

Definition collided_matrix a c (t : C.set_term) : C.set_form :=
  (∀ ((C.R $0 $0 →
        (N.interpret_code c (N.bind_env (N.update_env identity_env c t) a) → C.R t`[↑] $0)) ∧
       (C.R t`[↑] $0 → N.interpret_code c (N.bind_env (N.update_env identity_env c t) a)))) ∧
  (N.interpret_code c (N.update_env identity_env c t) → C.R t $a).

Lemma pointed_matrix_readout a b c t : c <> a -> c <> b ->
  ((C.pointed_body (pointed_property a b c))[up (up ($a..))][up ($b..)])[t..] =
  pointed_matrix a b c t.
Proof.
  destruct t as [it|[]]; intros Hca Hcb; unfold C.pointed_body, pointed_matrix.
  cbn [subst_form C.R C.terms2 Vector.map subst_term up scons funcomp].
  rewrite (pointed_member_readout a b c $it Hca Hcb),
          (pointed_point_readout a b c $it Hca Hcb); reflexivity.
Qed.

Lemma collided_matrix_readout a c t : c <> a ->
  ((C.collided_body (collided_property a c))[up ($a..)])[t..] = collided_matrix a c t.
Proof.
  destruct t as [it|[]]; intro Hca; unfold C.collided_body, collided_matrix.
  cbn [subst_form C.R C.terms2 Vector.map subst_term up scons funcomp].
  rewrite (collided_member_readout a c $it Hca),
          (collided_point_readout a c $it Hca); reflexivity.
Qed.

Lemma coded_conjunction_intro G a b rho :
  G ⊢N N.interpret_code a rho -> G ⊢N N.interpret_code b rho ->
  G ⊢N N.interpret_code (wa a b) rho.
Proof.
  intros Ha Hb; rewrite N.interpret_conjunction; apply II.
  eapply IE.
  - eapply IE; [apply Ctx; now left|].
    eapply Weak; [exact Ha|]; intros phi Hphi; now right.
  - eapply Weak; [exact Hb|]; intros phi Hphi; now right.
Qed.

Lemma coded_existential_intro G a b rho t :
  G ⊢N N.interpret_code b (N.update_env rho a t) ->
  G ⊢N N.interpret_code (wex a b) rho.
Proof.
  intro Hb; rewrite N.interpret_existential; apply II.
  assert (Hall : (∀ ¬ N.interpret_code b (N.bind_env rho a)) :: G ⊢N
                 (∀ ¬ N.interpret_code b (N.bind_env rho a))).
  { apply Ctx; now left. }
  pose proof (AllE t Hall) as Hnot.
  change ((∀ ¬ N.interpret_code b (N.bind_env rho a)) :: G ⊢N
          ¬ ((N.interpret_code b (N.bind_env rho a))[t..])) in Hnot.
  rewrite S.interpret_code_instance in Hnot; eapply IE; [exact Hnot|].
  eapply Weak; [exact Hb|]; intros phi Hphi; now right.
Qed.

Definition member_code a b c :=
  wa (wim (wel a b) (wim c (wel c b))) (wim (wel c b) c).
Definition witness_body_code a b c := wa (wal b (member_code a b c)) (wim c (wel c b)).
Definition main_bundle_code a b c := wex c (witness_body_code a b c).

Ltac inherit H :=
  eapply Weak; [exact H|]; intros phi Hphi; repeat right; exact Hphi.

Lemma member_code_intro G a b c rho : G ⊢N C.ir ->
  G ⊢N ((N.interpret_code (wel a b) rho →
          (N.interpret_code c rho → N.interpret_code (wel c b) rho)) ∧
        (N.interpret_code (wel c b) rho → N.interpret_code c rho)) ->
  G ⊢N N.interpret_code (member_code a b c) rho.
Proof.
  intros HIR Hclauses; unfold member_code; apply coded_conjunction_intro.
  - apply S.numeric_implication_intro; [exact HIR|]; apply II.
    apply S.numeric_implication_intro; [inherit HIR|]; apply II.
    assert (Hparts :
      (N.interpret_code c rho) :: (N.interpret_code (wel a b) rho) :: G ⊢N
      ((N.interpret_code (wel a b) rho →
          (N.interpret_code c rho → N.interpret_code (wel c b) rho)) ∧
       (N.interpret_code (wel c b) rho → N.interpret_code c rho))).
    { inherit Hclauses. }
    eapply IE; [eapply IE; [exact (CE1 Hparts)|apply Ctx; right; now left]|].
    apply Ctx; now left.
  - apply S.numeric_implication_intro; [exact HIR|]; apply II.
    assert (Hparts : (N.interpret_code (wel c b) rho) :: G ⊢N
      ((N.interpret_code (wel a b) rho →
          (N.interpret_code c rho → N.interpret_code (wel c b) rho)) ∧
       (N.interpret_code (wel c b) rho → N.interpret_code c rho))).
    { inherit Hclauses. }
    eapply IE; [exact (CE2 Hparts)|apply Ctx; now left].
Qed.

Definition witness_env c (t : C.set_term) b (m : C.set_term) :=
  N.update_env (N.update_env identity_env c t) b m.
Lemma witness_input a b c t m : a <> b -> c <> a -> witness_env c t b m a = $a.
Proof.
  intros Hab Hca; unfold witness_env, N.update_env, identity_env.
  rewrite (proj2 (Nat.eqb_neq a b) Hab), (proj2 (Nat.eqb_neq a c) ltac:(congruence)).
  reflexivity.
Qed.
Lemma witness_member b c t m : witness_env c t b m b = m.
Proof. unfold witness_env, N.update_env; now rewrite Nat.eqb_refl. Qed.
Lemma witness_output b c t m : c <> b -> witness_env c t b m c = t.
Proof.
  intro Hcb; unfold witness_env, N.update_env.
  now rewrite (proj2 (Nat.eqb_neq c b) Hcb), Nat.eqb_refl.
Qed.
Lemma outer_output c t : N.update_env identity_env c t c = t.
Proof. unfold N.update_env; now rewrite Nat.eqb_refl. Qed.
Lemma outer_point b c t : c <> b -> N.update_env identity_env c t b = $b.
Proof.
  intro Hcb; unfold N.update_env, identity_env.
  now rewrite (proj2 (Nat.eqb_neq b c) ltac:(congruence)).
Qed.

Lemma pointed_matrix_member G a b c t m : G ⊢N pointed_matrix a b c t ->
  G ⊢N ((C.R $a m → (N.interpret_code c (witness_env c t b m) → C.R t m)) ∧
        (C.R t m → N.interpret_code c (witness_env c t b m))).
Proof.
  intro HM; unfold pointed_matrix in HM; pose proof (AllE m (CE1 HM)) as H.
  cbn [subst_form C.R C.terms2 Vector.map] in H.
  rewrite !subst_term_shift, S.interpret_code_instance in H; exact H.
Qed.

Lemma collided_matrix_member G a c t m : G ⊢N collided_matrix a c t ->
  G ⊢N ((C.R m m → (N.interpret_code c (witness_env c t a m) → C.R t m)) ∧
        (C.R t m → N.interpret_code c (witness_env c t a m))).
Proof.
  intro HM; unfold collided_matrix in HM; pose proof (AllE m (CE1 HM)) as H.
  cbn [subst_form C.R C.terms2 Vector.map] in H.
  rewrite !subst_term_shift, S.interpret_code_instance in H; exact H.
Qed.

Lemma pointed_matrix_codes G a b c t : a <> b -> c <> a -> c <> b ->
  G ⊢N C.ir -> G ⊢N pointed_matrix a b c t ->
  G ⊢N N.interpret_code (witness_body_code a b c) (N.update_env identity_env c t).
Proof.
  intros Hab Hca Hcb HIR HM; unfold witness_body_code; apply coded_conjunction_intro.
  - rewrite N.interpret_universal; apply AllI_named; intro m; rewrite S.interpret_code_instance.
    apply member_code_intro; [exact HIR|].
    pose proof (pointed_matrix_member G a b c t m HM) as Hparts.
    assert (Hin : N.interpret_code (wel a b) (witness_env c t b m) = C.R $a m).
    { rewrite N.interpret_membership, witness_input by assumption; rewrite witness_member; reflexivity. }
    assert (Hout : N.interpret_code (wel c b) (witness_env c t b m) = C.R t m).
    { rewrite N.interpret_membership, witness_output by assumption; rewrite witness_member; reflexivity. }
    change (G ⊢N
      ((N.interpret_code (wel a b) (witness_env c t b m) →
         (N.interpret_code c (witness_env c t b m) →
          N.interpret_code (wel c b) (witness_env c t b m))) ∧
       (N.interpret_code (wel c b) (witness_env c t b m) →
        N.interpret_code c (witness_env c t b m)))).
    rewrite Hin, Hout; exact Hparts.
  - apply S.numeric_implication_intro; [exact HIR|].
    rewrite (N.interpret_membership c b (N.update_env identity_env c t)), outer_output,
            outer_point by exact Hcb.
    exact (CE2 HM).
Qed.

Lemma collided_matrix_codes G a c t : c <> a ->
  G ⊢N C.ir -> G ⊢N collided_matrix a c t ->
  G ⊢N N.interpret_code (witness_body_code a a c) (N.update_env identity_env c t).
Proof.
  intros Hca HIR HM; unfold witness_body_code; apply coded_conjunction_intro.
  - rewrite N.interpret_universal; apply AllI_named; intro m; rewrite S.interpret_code_instance.
    apply member_code_intro; [exact HIR|].
    pose proof (collided_matrix_member G a c t m HM) as Hparts.
    assert (Hin : N.interpret_code (wel a a) (witness_env c t a m) = C.R m m).
    { rewrite N.interpret_membership, !witness_member; reflexivity. }
    assert (Hout : N.interpret_code (wel c a) (witness_env c t a m) = C.R t m).
    { rewrite N.interpret_membership, witness_output by exact Hca; rewrite witness_member; reflexivity. }
    change (G ⊢N
      ((N.interpret_code (wel a a) (witness_env c t a m) →
         (N.interpret_code c (witness_env c t a m) →
          N.interpret_code (wel c a) (witness_env c t a m))) ∧
       (N.interpret_code (wel c a) (witness_env c t a m) →
        N.interpret_code c (witness_env c t a m)))).
    rewrite Hin, Hout; exact Hparts.
  - apply S.numeric_implication_intro; [exact HIR|].
    rewrite (N.interpret_membership c a (N.update_env identity_env c t)), outer_output,
            outer_point by exact Hca.
    exact (CE2 HM).
Qed.

Lemma pointed_main_bundle a b c : a <> b -> c <> a -> c <> b ->
  C.derivable C.compact_theory (N.interpret_code (main_bundle_code a b c) identity_env).
Proof.
  intros Hab Hca Hcb.
  destruct (compact_pointed_open (pointed_property a b c)) as [G [HG Hax]].
  exists (C.ir :: G); split.
  - intros phi [<-|Hphi]; [apply C.compact_ir|now apply HG].
  - assert (HP : C.ir :: G ⊢N C.pointed_ax (pointed_property a b c)).
    { eapply Weak; [exact Hax|]; intros phi Hphi; now right. }
    unfold C.pointed_ax in HP.
    pose proof (AllE $b (AllE $a HP)) as Hex.
    change (C.ir :: G ⊢N ∃
      ((C.pointed_body (pointed_property a b c))[up (up ($a..))][up ($b..)])) in Hex.
    eapply ExE_named; [exact Hex|].
    intro t; rewrite (pointed_matrix_readout a b c t Hca Hcb).
    unfold main_bundle_code; eapply coded_existential_intro with (t := t).
    apply pointed_matrix_codes; [exact Hab|exact Hca|exact Hcb| |].
    + apply Ctx; right; now left.
    + apply Ctx; now left.
Qed.

Lemma collided_main_bundle a c : c <> a ->
  C.derivable C.compact_theory (N.interpret_code (main_bundle_code a a c) identity_env).
Proof.
  intro Hca.
  destruct (compact_collided_open (collided_property a c)) as [G [HG Hax]].
  exists (C.ir :: G); split.
  - intros phi [<-|Hphi]; [apply C.compact_ir|now apply HG].
  - assert (HP : C.ir :: G ⊢N C.collided_ax (collided_property a c)).
    { eapply Weak; [exact Hax|]; intros phi Hphi; now right. }
    unfold C.collided_ax in HP.
    pose proof (AllE $a HP) as Hex.
    change (C.ir :: G ⊢N ∃ ((C.collided_body (collided_property a c))[up ($a..)])) in Hex.
    eapply ExE_named; [exact Hex|].
    intro t; rewrite (collided_matrix_readout a c t Hca).
    unfold main_bundle_code; eapply coded_existential_intro with (t := t).
    apply collided_matrix_codes; [exact Hca| |].
    + apply Ctx; right; now left.
    + apply Ctx; now left.
Qed.

Theorem numeric_main_bundle_transport a b c rho : c <> a -> c <> b ->
  C.derivable C.compact_theory (N.interpret_code (main_bundle_code a b c) rho).
Proof.
  intros Hca Hcb; apply compact_environment.
  destruct (Nat.eq_dec a b) as [->|Hab].
  - apply collided_main_bundle; exact Hcb.
  - apply pointed_main_bundle; assumption.
Qed.

Lemma compact_coded_conjunction a b rho :
  C.derivable C.compact_theory (N.interpret_code a rho) ->
  C.derivable C.compact_theory (N.interpret_code b rho) ->
  C.derivable C.compact_theory (N.interpret_code (wa a b) rho).
Proof.
  intros [G [HG Ha]] [H [HH Hb]]; exists (G ++ H); split.
  - intros phi Hphi; apply in_app_or in Hphi as [Hphi|Hphi];
      [now apply HG|now apply HH].
  - apply coded_conjunction_intro.
    + eapply Weak; [exact Ha|]; intros phi Hphi; apply in_or_app; now left.
    + eapply Weak; [exact Hb|]; intros phi Hphi; apply in_or_app; now right.
Qed.

Theorem numeric_bundle_transport a b c rho : c <> a -> c <> b ->
  C.derivable C.compact_theory (N.interpret_code (bundle a b c) rho).
Proof.
  intros Hca Hcb; unfold bundle.
  change (C.derivable C.compact_theory
    (N.interpret_code (wa (main_bundle_code a b c)
      (wa (wim (weq a b) (wal c (weq a b)))
          (wim (wel a b) (wal c (wel a b))))) rho)).
  apply compact_coded_conjunction.
  - apply numeric_main_bundle_transport; assumption.
  - apply compact_coded_conjunction.
    + apply S.numeric_equality_vacuity; assumption.
    + apply S.numeric_membership_vacuity; assumption.
Qed.

(** This direction consumes actual numeric derivation constructors. Every
    output retains a finite list of actual closed normalized axioms. *)
Theorem numeric_derivation_transport n : Compiler238.derivable n ->
  forall rho, C.derivable C.compact_theory (N.interpret_code n rho).
Proof.
  intro H; induction H; intro rho.
  - apply N.compact_truth.
  - apply N.numeric_mp_transport with (a := a); [apply IHderivable1|apply IHderivable2].
  - apply N.numeric_generalize_transport; exact IHderivable.
  - apply N.numeric_r1_transport.
  - apply S.numeric_r2_transport.
  - apply S.numeric_r3_transport.
  - apply S.numeric_r4_transport.
  - apply S.numeric_r5_transport.
  - apply S.numeric_r6_transport.
  - apply S.numeric_r7_transport.
  - apply S.numeric_r8_transport.
  - apply numeric_bundle_transport; assumption.
Qed.

Theorem numeric_refutation_to_compact : Compiler238.derivable 1 ->
  exists G : list C.set_form,
    (forall phi, In phi G -> C.compact_theory phi) /\ G ⊢N ⊥.
Proof.
  intro H; apply (C.derivable_mp C.compact_theory
    (N.interpret_code 1 identity_env) ⊥).
  - apply N.compact_not_one.
  - apply numeric_derivation_transport; exact H.
Qed.

Print Assumptions pointed_member_readout.
Print Assumptions collided_member_readout.
Print Assumptions numeric_bundle_transport.
Print Assumptions numeric_derivation_transport.
Print Assumptions numeric_refutation_to_compact.
End NumericBundle238.
