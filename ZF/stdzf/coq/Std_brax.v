(** * Std_brax: the closures of O'Rear's axioms EXT, UNI, INF and every REP instance are
    derivable from ZFc (bridge_POW is handled elsewhere). *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_tr Std_alpha Std_gen Std_F Std_H Std_iface Std_iface2.
From ZF Require Import Std_setnd Std_setbase Std_setinf Std_breq Std_brnd Std_brrep.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma ZF0base_ZFc psi : In psi ZF0base -> ZFc psi.
Proof. intros H. left. now apply ZF0_base. Qed.

(** ** EXT *)
Theorem bridge_EXT_proof : bridge_EXT.
Proof.
  exists ZF0base. split; [exact ZF0base_ZFc|].
  assert (HG : incl ZF0base ZF0base) by apply incl_refl.
  apply Lib_intro. intros sg. unfold EXT. apply dB_impI. ctx_push H.
  cbn [dB]. apply (ext_rule HG); unfold sub'; fall z; fintro Hz.
  - pose proof (dB_allE _ _ _ z H) as H1. apply dB_andE1 in H1. exact (dB_imp _ _ _ H1 Hz).
  - pose proof (dB_allE _ _ _ z H) as H1. apply dB_andE2 in H1. exact (dB_imp _ _ _ H1 Hz).
Qed.

(** ** UNI *)
Theorem bridge_UNI_proof : bridge_UNI.
Proof.
  exists ZF0base. split; [exact ZF0base_ZFc|].
  assert (HG : incl ZF0base ZF0base) by apply incl_refl.
  apply Lib_intro. intros sg. unfold UNI.
  fobtain (union_ex HG (sg 0)) as u Hu.
  apply (dB_exI _ _ _ u). apply dB_allI. intros z. apply dB_impI. ctx_push H.
  apply (dB_exE _ _ _ _ H). intros w. apply II. ctx_push Hw.
  pose proof (dB_andE1 _ _ _ Hw) as Hw1. apply dB_andE2 in Hw.
  exact (union_in HG (sg 0) u w z Hu Hw Hw1).
Qed.

(** ** INF *)
Theorem bridge_INFo_proof : bridge_INFo.
Proof.
  destruct inf_zf_to_or as [A [HA H]]. exists A. split; [exact HA|].
  apply Lib_intro. intros sg. unfold INF. rewrite INF_lib_eq in H.
  finst H (sg 0). fex H y Hy. fdestr Hy Hy1 Hy2.
  apply (dB_exI _ _ _ y). apply dB_andI; [exact Hy1|].
  apply dB_allI. intros u. apply dB_impI. ctx_push Hu.
  unfold SClos in Hy2. finst Hy2 u. fmp Hy2 Hu. fex Hy2 z Hz. fdestr Hz Hz1 Hz2.
  apply (dB_exI _ _ _ z). apply dB_andI; [exact Hz1|].
  apply dB_allI. intros w. unfold Sing in Hz2. finst Hz2 w. fdestr Hz2 H1 H2.
  apply dB_andI; [exact H1|exact H2].
Qed.

(** ** REP *)
Definition rhoN (v : nat) : term := if Nat.eqb v 3 then $0 else if Nat.eqb v 2 then $1 else $(v + 2).
Definition phiN (ph : wff) : form := dB rhoN (Wal 1 ph).
#[global] Arguments phiN : simpl never.
Definition mN (ph : wff) : nat := S (maxfr (REP ph)).

Lemma fb_phiN ph : fb (S (S (mN ph))) (phiN ph).
Proof.
  unfold phiN. apply fb_dB. intros v Hv. apply fr_maxfr in Hv.
  assert (maxfr (Wal 1 ph) <= maxfr (REP ph)) by (unfold REP, Wex, Wa; cbn [maxfr]; lia).
  unfold rhoN, mN. set (M := maxfr (REP ph)) in *. set (M1 := maxfr (Wal 1 ph)) in *. clearbody M M1.
  destruct (Nat.eqb v 3); [cbn; lia|]. destruct (Nat.eqb v 2); cbn; lia.
Qed.

Lemma phiN_inst ph w z (sg env : nat -> term) : env 3 = w -> env 2 = z ->
  (forall v, v <> 1 -> v <> 2 -> v <> 3 -> env v = sg v) -> (phiN ph)[w .: z .: sg] = dB env (Wal 1 ph).
Proof.
  intros E3 E2 Ev. unfold phiN. rewrite dB_subst. apply dB_ext_fr. intros v Hv. cbn in Hv.
  destruct (Nat.eqb_spec 1 v) as [<-|Hv1]; [discriminate|]. unfold funcomp, rhoN.
  destruct (Nat.eqb_spec v 3) as [->|H3]; [cbn; auto|].
  destruct (Nat.eqb_spec v 2) as [->|H2]; [cbn; auto|].
  cbn. replace (v + 2) with (S (S v)) by lia. cbn. symmetry. apply Ev; lia.
Qed.

Ltac env_eq2 := intros; repeat (rewrite upd_eq || rewrite upd_neq by lia); reflexivity.

Definition A_rep (ph : wff) : list form := forall_times (mN ph) (ax_rep' (phiN ph)) :: ZF0base.

Theorem bridge_REP_proof : bridge_REP.
Proof.
  intros ph n Hn. exists (A_rep ph). split.
  { intros psi [<-|H]; [|now apply ZF0base_ZFc]. left. apply ZF0_rep. apply rep_closed, fb_phiN. }
  assert (HG : incl ZF0base (A_rep ph)) by (intros x Hx; now right).
  assert (HI : In (forall_times (mN ph) (ax_rep' (phiN ph))) (A_rep ph)) by now left.
  apply Lib_intro. intros sg. rewrite REP_eq. apply dB_impI. ctx_push Hh.
  assert (Hfun : forall a b b', Γ ⊢C (phiN ph)[a .: b .: sg] → (phiN ph)[a .: b' .: sg] → b ≡' b').
  { intros a b b'. apply II. ctx_push H1. apply II. ctx_push H2.
    unfold repH in Hh. pose proof (dB_allE _ _ _ a Hh) as T. apply (dB_exE _ _ _ _ T). intros y. apply II.
    ctx_push Hy. pose proof (dB_allE _ _ _ b Hy) as Hb. pose proof (dB_allE _ _ _ b' Hy) as Hb'.
    rewrite (phiN_inst ph a b sg (upd (upd (upd sg 3 a) 1 y) 2 b)) in H1 by env_eq2.
    rewrite (phiN_inst ph a b' sg (upd (upd (upd sg 3 a) 1 y) 2 b')) in H2 by env_eq2.
    pose proof (dB_imp _ _ _ Hb H1) as E1. pose proof (dB_imp _ _ _ Hb' H2) as E2.
    simp_in E1. simp_in E2. feq. }
  pose proof (rep_use _ (mN ph) (phiN ph) sg (sg 0) HI (fb_phiN ph) Hfun) as T. clear Hfun.
  fex T Y HY.
  unfold repC. apply (dB_exI _ _ _ Y). apply dB_allI. intros z.
  pose proof HY as HYz. finst HYz z. rewrite !subst_comp in HYz.
  match type of HYz with context [(phiN ph)[?s]] =>
    assert (EE : (phiN ph)[up (z .: sg)] = (phiN ph)[s]) by (rewrite ?subst_comp; apply subst_ext; intros [|[|[|[|[|[|kk]]]]]]; term_eq);
    rewrite <- EE in HYz; clear EE end.
  apply dB_andI.
  - apply dB_impI. ctx_push Hz. fhave T : (iff_l _ _ _ HYz Hz). fex T w Hw. fdestr Hw Hw1 Hw2.
    unfold repE. apply (dB_exI _ _ _ w). apply dB_andI; [exact Hw1|].
    rewrite (phiN_inst ph w z sg (upd (upd (upd sg 1 Y) 2 z) 3 w)) in Hw2 by env_eq2. exact Hw2.
  - apply dB_impI. ctx_push HE'. unfold repE in HE'. apply (dB_exE _ _ _ _ HE'). intros w. apply II. ctx_push Hw.
    pose proof (dB_andE1 _ _ _ Hw) as Hw1. apply dB_andE2 in Hw.
    rewrite <- (phiN_inst ph w z sg (upd (upd (upd sg 1 Y) 2 z) 3 w)) in Hw by env_eq2.
    apply (iff_r _ _ _ HYz). fexists w. fsplit; assumption.
Qed.
