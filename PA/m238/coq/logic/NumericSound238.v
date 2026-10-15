(** Original finite derivation transports for the PA238 numeric rows.
    NumericSyntax238 supplies the total named interpretation and exact
    freshness bounds. These proofs use actual library natural deduction
    from finite contexts; no adequacy theorem is assumed. *)
From Coq Require Import Arith Lia Bool List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.logic Require Import Codes238 Compiler238 NumericSyntax238.
From P238.arith Require Import Compact238.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module NumericSound238.
Module C := Compact238.Compact238.
Module N := NumericSyntax238.NumericSyntax238.
Notation "G ⊢N phi" :=
  (@prv sig_empty ZF_pred_sig falsity_on class G phi) (at level 61).

Lemma interpret_code_instance n rho a t :
  (N.interpret_code n (N.bind_env rho a))[t..] =
  N.interpret_code n (N.update_env rho a t).
Proof. unfold N.interpret_code; apply N.interpret_binder_instance. Qed.

Lemma implication_zero : wim 0 0 = 0.
Proof. reflexivity. Qed.

Local Opaque N.decode N.decode_fuel N.decode_node P unP triangle.

Lemma numeric_mp_nd G a b rho :
  G ⊢N N.interpret_code a rho ->
  G ⊢N N.interpret_code (wim a b) rho ->
  G ⊢N N.interpret_code b rho.
Proof.
  intros Ha Hab; destruct (Nat.eq_dec b 1) as [-> | Hneq].
  - change (G ⊢N N.interpret_code (wn a) rho) in Hab.
    rewrite N.interpret_negation in Hab. apply Exp. exact (IE Hab Ha).
  - destruct (Nat.eq_dec (a + b) 0) as [Hzero | Hpos].
    + assert (b = 0) by lia; subst b; rewrite N.interpret_truth.
      apply II, Ctx; now left.
    + rewrite N.interpret_implication in Hab by lia; exact (IE Hab Ha).
Qed.

(** Introducing an implication whose consequent is code 1 requires IR:
    the numeric decoder uses native negation at that exact code. *)
Lemma numeric_implication_intro G a b rho :
  G ⊢N C.ir ->
  G ⊢N (N.interpret_code a rho → N.interpret_code b rho) ->
  G ⊢N N.interpret_code (wim a b) rho.
Proof.
  intros HIR Himp; destruct (Nat.eq_dec b 1) as [-> | Hneq].
  - change (G ⊢N N.interpret_code (wn a) rho).
    rewrite N.interpret_negation, N.interpret_one in *; apply II.
    eapply IE.
    + apply C.ir_guard. eapply Weak; [exact HIR|]. intros phi Hphi; now right.
    + eapply IE.
      * eapply Weak; [exact Himp|]. intros phi Hphi; now right.
      * apply Ctx; now left.
  - destruct (Nat.eq_dec (a + b) 0) as [Hzero | Hpos].
    + assert (a = 0) by lia; assert (b = 0) by lia; subst a; subst b.
      rewrite implication_zero, N.interpret_truth.
      apply II, Ctx; now left.
    + rewrite N.interpret_implication by lia; exact Himp.
Qed.

Lemma universal_positive a b : 0 < wal a b.
Proof. unfold wal; lia. Qed.

Lemma numeric_r2_nd G a b c rho : G ⊢N N.interpret_code (rho2 a b c) rho.
Proof.
  pose proof (universal_positive a (wim b c)) as HposBC.
  pose proof (universal_positive a b) as HposB.
  unfold rho2.
  rewrite N.interpret_implication by (first [apply wim_not_one|lia]).
  rewrite N.interpret_implication by (first [apply wal_not_one|lia]).
  rewrite !N.interpret_universal; apply II, II, AllI_named; intro t.
  rewrite interpret_code_instance.
  assert (HallB :
    (∀ N.interpret_code b (N.bind_env rho a)) ::
    (∀ N.interpret_code (wim b c) (N.bind_env rho a)) :: G ⊢N
    (∀ N.interpret_code b (N.bind_env rho a))).
  { apply Ctx; now left. }
  assert (HallBC :
    (∀ N.interpret_code b (N.bind_env rho a)) ::
    (∀ N.interpret_code (wim b c) (N.bind_env rho a)) :: G ⊢N
    (∀ N.interpret_code (wim b c) (N.bind_env rho a))).
  { apply Ctx; right; now left. }
  pose proof (AllE t HallB) as HB; rewrite interpret_code_instance in HB.
  pose proof (AllE t HallBC) as HBC; rewrite interpret_code_instance in HBC.
  exact (numeric_mp_nd _ b c (N.update_env rho a t) HB HBC).
Qed.

Theorem numeric_r2_transport a b c rho :
  C.derivable C.compact_theory (N.interpret_code (rho2 a b c) rho).
Proof.
  exists []; split; [intros phi Hphi; inversion Hphi|apply numeric_r2_nd].
Qed.

Lemma updates_commute rho a b ta tb : a <> b -> forall v,
  N.update_env (N.update_env rho a ta) b tb v =
  N.update_env (N.update_env rho b tb) a ta v.
Proof.
  intros Hneq v; unfold N.update_env.
  destruct (Nat.eqb v a) eqn:Ea; destruct (Nat.eqb v b) eqn:Eb;
    try reflexivity.
  apply Nat.eqb_eq in Ea; apply Nat.eqb_eq in Eb; congruence.
Qed.

Lemma numeric_r4_nd G a b c rho : G ⊢N N.interpret_code (rho4 a b c) rho.
Proof.
  pose proof (universal_positive a (wal b c)) as Hpos.
  unfold rho4; rewrite N.interpret_implication by (first [apply wal_not_one|lia]).
  destruct (Nat.eq_dec a b) as [-> | Hneq]; [apply II, Ctx; now left|].
  apply II.
  rewrite (N.interpret_universal b (wal a c) rho).
  apply AllI_named; intro tb; rewrite interpret_code_instance.
  rewrite (N.interpret_universal a c (N.update_env rho b tb)).
  apply AllI_named; intro ta; rewrite interpret_code_instance.
  assert (Hall : (N.interpret_code (wal a (wal b c)) rho) :: G ⊢N
                 (∀ N.interpret_code (wal b c) (N.bind_env rho a))).
  { rewrite <- (N.interpret_universal a (wal b c) rho). apply Ctx; now left. }
  pose proof (AllE ta Hall) as HB; rewrite interpret_code_instance in HB.
  assert (HallB : (N.interpret_code (wal a (wal b c)) rho) :: G ⊢N
                 (∀ N.interpret_code c (N.bind_env (N.update_env rho a ta) b))).
  { rewrite <- (N.interpret_universal b c (N.update_env rho a ta)); exact HB. }
  pose proof (AllE tb HallB) as HC; rewrite interpret_code_instance in HC.
  assert (Henv :
    N.interpret_code c (N.update_env (N.update_env rho a ta) b tb) =
    N.interpret_code c (N.update_env (N.update_env rho b tb) a ta)).
  { unfold N.interpret_code; apply N.interpret_env_ext.
    apply updates_commute; exact Hneq. }
  rewrite <- Henv; exact HC.
Qed.

Theorem numeric_r4_transport a b c rho :
  C.derivable C.compact_theory (N.interpret_code (rho4 a b c) rho).
Proof.
  exists []; split; [intros phi Hphi; inversion Hphi|apply numeric_r4_nd].
Qed.

Lemma update_restore rho a t : forall v,
  N.update_env (N.update_env rho a t) a (rho a) v = rho v.
Proof.
  intro v; unfold N.update_env; destruct (Nat.eqb v a) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E; now subst v.
Qed.

Lemma numeric_r6_nd G a b rho : G ⊢N C.ir ->
  G ⊢N N.interpret_code (rho6 a b) rho.
Proof.
  intro HIR; unfold rho6; apply numeric_implication_intro; [exact HIR|].
  apply II, DN, II.
  assert (Hexists :
    (¬ N.interpret_code b rho) :: (N.interpret_code (wex a (wal a b)) rho) :: G ⊢N
    (¬ ∀ ¬ N.interpret_code (wal a b) (N.bind_env rho a))).
  { rewrite <- (N.interpret_existential a (wal a b) rho).
    apply Ctx; right; now left. }
  eapply IE; [exact Hexists|].
  apply AllI_named; intro t.
  change ((¬ N.interpret_code b rho) :: (N.interpret_code (wex a (wal a b)) rho) :: G ⊢N
          ¬ ((N.interpret_code (wal a b) (N.bind_env rho a))[t..])).
  rewrite interpret_code_instance; apply II.
  assert (Hall :
    (N.interpret_code (wal a b) (N.update_env rho a t)) ::
    (¬ N.interpret_code b rho) :: (N.interpret_code (wex a (wal a b)) rho) :: G ⊢N
    (∀ N.interpret_code b (N.bind_env (N.update_env rho a t) a))).
  { rewrite <- (N.interpret_universal a b (N.update_env rho a t)).
    apply Ctx; now left. }
  pose proof (AllE (rho a) Hall) as HB; rewrite interpret_code_instance in HB.
  assert (Hrestore :
    N.interpret_code b (N.update_env (N.update_env rho a t) a (rho a)) =
    N.interpret_code b rho).
  { unfold N.interpret_code; apply N.interpret_env_ext, update_restore. }
  rewrite Hrestore in HB.
  eapply IE; [apply Ctx; right; now left|exact HB].
Qed.

Theorem numeric_r6_transport a b rho :
  C.derivable C.compact_theory (N.interpret_code (rho6 a b) rho).
Proof.
  exists [C.ir]; split.
  - intros phi [<-|[]]; apply C.compact_ir.
  - apply numeric_r6_nd, Ctx; now left.
Qed.

Ltac inherit_ir H :=
  eapply Weak; [exact H|]; intros phi Hphi; repeat right; exact Hphi.

Lemma numeric_r8_nd G a b c u rho : G ⊢N C.ir ->
  G ⊢N N.interpret_code (rho8 a b c u) rho.
Proof.
  intro HIR; unfold rho8.
  apply numeric_implication_intro; [exact HIR|]; apply II.
  apply numeric_implication_intro; [inherit_ir HIR|]; apply II.
  apply numeric_implication_intro; [inherit_ir HIR|]; apply II.
  eapply IE with (phi :=
    ((N.interpret_code c rho → N.interpret_code u rho) → N.interpret_code c rho));
    [apply Pc|]; apply II.
  assert (HIR4 :
    (N.interpret_code c rho → N.interpret_code u rho) ::
    (N.interpret_code b rho) :: (N.interpret_code (wim a c) rho) ::
    (N.interpret_code (wim (wim c u) a) rho) :: G ⊢N C.ir).
  { inherit_ir HIR. }
  assert (HCU :
    (N.interpret_code c rho → N.interpret_code u rho) ::
    (N.interpret_code b rho) :: (N.interpret_code (wim a c) rho) ::
    (N.interpret_code (wim (wim c u) a) rho) :: G ⊢N
    N.interpret_code (wim c u) rho).
  { apply numeric_implication_intro; [exact HIR4|apply Ctx; now left]. }
  assert (HCUA :
    (N.interpret_code c rho → N.interpret_code u rho) ::
    (N.interpret_code b rho) :: (N.interpret_code (wim a c) rho) ::
    (N.interpret_code (wim (wim c u) a) rho) :: G ⊢N
    N.interpret_code (wim (wim c u) a) rho).
  { apply Ctx; right; right; right; now left. }
  pose proof (numeric_mp_nd _ (wim c u) a rho HCU HCUA) as HA.
  assert (HAC :
    (N.interpret_code c rho → N.interpret_code u rho) ::
    (N.interpret_code b rho) :: (N.interpret_code (wim a c) rho) ::
    (N.interpret_code (wim (wim c u) a) rho) :: G ⊢N
    N.interpret_code (wim a c) rho).
  { apply Ctx; right; right; now left. }
  exact (numeric_mp_nd _ a c rho HA HAC).
Qed.

Theorem numeric_r8_transport a b c u rho :
  C.derivable C.compact_theory (N.interpret_code (rho8 a b c u) rho).
Proof.
  exists [C.ir]; split.
  - intros phi [<-|[]]; apply C.compact_ir.
  - apply numeric_r8_nd, Ctx; now left.
Qed.

Definition equality_membership_ax : C.set_form :=
  ∀ ∀ ∀ ∀ (C.E $3 $1 → C.E $2 $0 → C.R $2 $3 → C.R $0 $1).
Definition equality_symmetry_ax : C.set_form := ∀ ∀ (C.E $1 $0 → C.E $0 $1).
Definition equality_transitivity_ax : C.set_form :=
  ∀ ∀ ∀ (C.E $2 $1 → C.E $1 $0 → C.E $2 $0).

Lemma equality_membership_at G x a y b :
  G ⊢N equality_membership_ax ->
  G ⊢N (C.E x y → C.E a b → C.R a x → C.R b y).
Proof.
  destruct x as [ix|[]], a as [ia|[]], y as [iy|[]], b as [ib|[]].
  intro H; unfold equality_membership_ax in H.
  pose proof (AllE $ib (AllE $iy (AllE $ia (AllE $ix H)))) as Hinstance.
  cbn [C.E C.R C.terms2 subst_form subst_term up scons funcomp Vector.map] in Hinstance.
  exact Hinstance.
Qed.

Lemma equality_symmetry_at G x y :
  G ⊢N equality_symmetry_ax -> G ⊢N C.E x y -> G ⊢N C.E y x.
Proof.
  destruct x as [ix|[]], y as [iy|[]]. intros HE Hxy; unfold equality_symmetry_ax in HE.
  pose proof (AllE $iy (AllE $ix HE)) as Hinstance.
  cbn [C.E C.terms2 subst_form subst_term up scons funcomp Vector.map] in Hinstance.
  exact (IE Hinstance Hxy).
Qed.

Lemma equality_transitivity_at G x y z :
  G ⊢N equality_transitivity_ax -> G ⊢N C.E x y -> G ⊢N C.E y z -> G ⊢N C.E x z.
Proof.
  destruct x as [ix|[]], y as [iy|[]], z as [iz|[]].
  intros HE Hxy Hyz; unfold equality_transitivity_ax in HE.
  pose proof (AllE $iz (AllE $iy (AllE $ix HE))) as Hinstance.
  cbn [C.E C.terms2 subst_form subst_term up scons funcomp Vector.map] in Hinstance.
  exact (IE (IE Hinstance Hxy) Hyz).
Qed.

Lemma numeric_r3_nd G a b c rho :
  G ⊢N C.ir -> G ⊢N (∀ C.E $0 $0) -> G ⊢N equality_membership_ax ->
  G ⊢N N.interpret_code (rho3 a b c) rho.
Proof.
  intros HIR HE HC; unfold rho3.
  apply numeric_implication_intro; [exact HIR|]; apply II.
  apply numeric_implication_intro; [inherit_ir HIR|]; apply II.
  rewrite (N.interpret_membership a c rho).
  assert (Hxy :
    (N.interpret_code (weq b c) rho) :: (N.interpret_code (wel a b) rho) :: G ⊢N
    C.E (rho b) (rho c)).
  { rewrite <- (N.interpret_equality b c rho); apply Ctx; now left. }
  assert (HR :
    (N.interpret_code (weq b c) rho) :: (N.interpret_code (wel a b) rho) :: G ⊢N
    C.R (rho a) (rho b)).
  { rewrite <- (N.interpret_membership a b rho); apply Ctx; right; now left. }
  assert (HC' :
    (N.interpret_code (weq b c) rho) :: (N.interpret_code (wel a b) rho) :: G ⊢N
    equality_membership_ax).
  { inherit_ir HC. }
  assert (HE' :
    (N.interpret_code (weq b c) rho) :: (N.interpret_code (wel a b) rho) :: G ⊢N
    (∀ C.E $0 $0)).
  { inherit_ir HE. }
  pose proof (equality_membership_at _ (rho b) (rho a) (rho c) (rho a) HC') as Hinstance.
  exact (IE (IE (IE Hinstance Hxy) (AllE (rho a) HE')) HR).
Qed.

Lemma numeric_r5_nd G a b c rho :
  G ⊢N C.ir -> G ⊢N (∀ C.E $0 $0) -> G ⊢N equality_membership_ax ->
  G ⊢N N.interpret_code (rho5 a b c) rho.
Proof.
  intros HIR HE HC; unfold rho5.
  apply numeric_implication_intro; [exact HIR|]; apply II.
  apply numeric_implication_intro; [inherit_ir HIR|]; apply II.
  rewrite (N.interpret_membership b c rho).
  assert (Hxy :
    (N.interpret_code (wel a c) rho) :: (N.interpret_code (weq a b) rho) :: G ⊢N
    C.E (rho a) (rho b)).
  { rewrite <- (N.interpret_equality a b rho); apply Ctx; right; now left. }
  assert (HR :
    (N.interpret_code (wel a c) rho) :: (N.interpret_code (weq a b) rho) :: G ⊢N
    C.R (rho a) (rho c)).
  { rewrite <- (N.interpret_membership a c rho); apply Ctx; now left. }
  assert (HC' :
    (N.interpret_code (wel a c) rho) :: (N.interpret_code (weq a b) rho) :: G ⊢N
    equality_membership_ax).
  { inherit_ir HC. }
  assert (HE' :
    (N.interpret_code (wel a c) rho) :: (N.interpret_code (weq a b) rho) :: G ⊢N
    (∀ C.E $0 $0)).
  { inherit_ir HE. }
  pose proof (equality_membership_at _ (rho c) (rho a) (rho c) (rho b) HC') as Hinstance.
  exact (IE (IE (IE Hinstance (AllE (rho c) HE')) Hxy) HR).
Qed.

Lemma numeric_r7_nd G a b c rho :
  G ⊢N C.ir -> G ⊢N equality_symmetry_ax -> G ⊢N equality_transitivity_ax ->
  G ⊢N N.interpret_code (rho7 a b c) rho.
Proof.
  intros HIR HS HT; unfold rho7.
  apply numeric_implication_intro; [exact HIR|]; apply II.
  apply numeric_implication_intro; [inherit_ir HIR|]; apply II.
  rewrite (N.interpret_equality b c rho).
  assert (Hab :
    (N.interpret_code (weq a c) rho) :: (N.interpret_code (weq a b) rho) :: G ⊢N
    C.E (rho a) (rho b)).
  { rewrite <- (N.interpret_equality a b rho); apply Ctx; right; now left. }
  assert (Hac :
    (N.interpret_code (weq a c) rho) :: (N.interpret_code (weq a b) rho) :: G ⊢N
    C.E (rho a) (rho c)).
  { rewrite <- (N.interpret_equality a c rho); apply Ctx; now left. }
  assert (HS' :
    (N.interpret_code (weq a c) rho) :: (N.interpret_code (weq a b) rho) :: G ⊢N
    equality_symmetry_ax).
  { inherit_ir HS. }
  assert (HT' :
    (N.interpret_code (weq a c) rho) :: (N.interpret_code (weq a b) rho) :: G ⊢N
    equality_transitivity_ax).
  { inherit_ir HT. }
  exact (equality_transitivity_at _ (rho b) (rho a) (rho c) HT'
            (equality_symmetry_at _ (rho a) (rho b) HS' Hab) Hac).
Qed.

Definition numeric_axiom_context : list C.set_form := C.equality_base ++ [C.ir].
Lemma numeric_axiom_context_allowed phi :
  In phi numeric_axiom_context -> C.compact_theory phi.
Proof.
  unfold numeric_axiom_context; intro H; apply in_app_or in H as [HE|HIR].
  - apply C.compact_equality; exact HE.
  - destruct HIR as [<-|[]]; apply C.compact_ir.
Qed.
Lemma context_ir : numeric_axiom_context ⊢N C.ir.
Proof. unfold numeric_axiom_context; apply Ctx; apply in_or_app; right; now left. Qed.
Lemma context_reflexivity : numeric_axiom_context ⊢N (∀ C.E $0 $0).
Proof. unfold numeric_axiom_context; apply Ctx; apply in_or_app; left; unfold C.equality_base; now left. Qed.
Lemma context_membership : numeric_axiom_context ⊢N equality_membership_ax.
Proof.
  unfold numeric_axiom_context; apply Ctx; apply in_or_app; left; unfold C.equality_base, equality_membership_ax.
  right; right; right; now left.
Qed.
Lemma context_symmetry : numeric_axiom_context ⊢N equality_symmetry_ax.
Proof.
  unfold numeric_axiom_context; apply Ctx; apply in_or_app; left; unfold C.equality_base, equality_symmetry_ax.
  right; now left.
Qed.
Lemma context_transitivity : numeric_axiom_context ⊢N equality_transitivity_ax.
Proof.
  unfold numeric_axiom_context; apply Ctx; apply in_or_app; left; unfold C.equality_base, equality_transitivity_ax.
  right; right; now left.
Qed.

Theorem numeric_r3_transport a b c rho :
  C.derivable C.compact_theory (N.interpret_code (rho3 a b c) rho).
Proof.
  exists numeric_axiom_context; split; [exact numeric_axiom_context_allowed|].
  apply numeric_r3_nd; [apply context_ir|apply context_reflexivity|apply context_membership].
Qed.
Theorem numeric_r5_transport a b c rho :
  C.derivable C.compact_theory (N.interpret_code (rho5 a b c) rho).
Proof.
  exists numeric_axiom_context; split; [exact numeric_axiom_context_allowed|].
  apply numeric_r5_nd; [apply context_ir|apply context_reflexivity|apply context_membership].
Qed.
Theorem numeric_r7_transport a b c rho :
  C.derivable C.compact_theory (N.interpret_code (rho7 a b c) rho).
Proof.
  exists numeric_axiom_context; split; [exact numeric_axiom_context_allowed|].
  apply numeric_r7_nd; [apply context_ir|apply context_symmetry|apply context_transitivity].
Qed.

Lemma fresh_binder_shift phi rho v : N.free_named v phi = false ->
  N.interpret_named phi (N.bind_env rho v) = (N.interpret_named phi rho)[↑].
Proof.
  intro Hfresh; rewrite N.interpret_substitution; apply N.interpret_env_agree.
  intros u Hu; unfold N.bind_env; destruct (Nat.eqb u v) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E; subst u; rewrite Hfresh in Hu; discriminate.
Qed.

Lemma numeric_vacuity_nd G n v rho : N.free_named v (N.decode n) = false ->
  G ⊢N C.ir -> G ⊢N N.interpret_code (wim n (wal v n)) rho.
Proof.
  intros Hfresh HIR; apply numeric_implication_intro; [exact HIR|].
  rewrite N.interpret_universal.
  assert (Hshift : N.interpret_code n (N.bind_env rho v) = (N.interpret_code n rho)[↑]).
  { unfold N.interpret_code; apply fresh_binder_shift; exact Hfresh. }
  rewrite Hshift; apply C.fresh_vacuity.
Qed.

Lemma equality_name_fresh a b c : c <> a -> c <> b ->
  N.free_named c (N.decode (weq a b)) = false.
Proof.
  intros Hca Hcb; rewrite N.decode_equality; cbn [N.free_named].
  rewrite (proj2 (Nat.eqb_neq c a) Hca), (proj2 (Nat.eqb_neq c b) Hcb); reflexivity.
Qed.
Lemma membership_name_fresh a b c : c <> a -> c <> b ->
  N.free_named c (N.decode (wel a b)) = false.
Proof.
  intros Hca Hcb; rewrite N.decode_membership; cbn [N.free_named].
  rewrite (proj2 (Nat.eqb_neq c a) Hca), (proj2 (Nat.eqb_neq c b) Hcb); reflexivity.
Qed.

Theorem numeric_equality_vacuity a b c rho : c <> a -> c <> b ->
  C.derivable C.compact_theory (N.interpret_code (wim (weq a b) (wal c (weq a b))) rho).
Proof.
  intros Hca Hcb; exists [C.ir]; split.
  - intros phi [<-|[]]; apply C.compact_ir.
  - apply numeric_vacuity_nd; [apply equality_name_fresh; assumption|apply Ctx; now left].
Qed.
Theorem numeric_membership_vacuity a b c rho : c <> a -> c <> b ->
  C.derivable C.compact_theory (N.interpret_code (wim (wel a b) (wal c (wel a b))) rho).
Proof.
  intros Hca Hcb; exists [C.ir]; split.
  - intros phi [<-|[]]; apply C.compact_ir.
  - apply numeric_vacuity_nd; [apply membership_name_fresh; assumption|apply Ctx; now left].
Qed.

Print Assumptions numeric_implication_intro.
Print Assumptions numeric_r2_transport.
Print Assumptions numeric_r4_transport.
Print Assumptions numeric_r6_transport.
Print Assumptions numeric_r8_transport.
Print Assumptions numeric_r3_transport.
Print Assumptions numeric_r5_transport.
Print Assumptions numeric_r7_transport.
Print Assumptions numeric_equality_vacuity.
Print Assumptions numeric_membership_vacuity.
End NumericSound238.
