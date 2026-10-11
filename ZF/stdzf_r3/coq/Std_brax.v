(** * Std_brax: the closures of the axioms EXT, INF and every (bounded-fiber) REP instance are
    derivable from ZFc. *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_tr Std_alpha Std_gen Std_F Std_H Std_iface Std_iface2.
From ZF Require Import Std_setnd Std_setbase Std_setinf Std_breq Std_brnd Ax_rb Std_brrep.
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

(** [psiN ph] (w = $0, F = $1, parameters $2..): F is the fiber of w, i.e. forall z, z in F <-> phiN(w, z).
    Functional by extensionality; its image over x, united, is the set REP asks for. *)
Definition psiN (ph : wff) : form := ∀ ($0 ∈' $2 ↔ (phiN ph)[$1 .: $0 .: (fun k => $(3 + k))]).
(** [sepN ph] (z = $0, w = $1, parameters $2..): separation formula cutting a fiber out of a bound *)
Definition sepN (ph : wff) : form := (phiN ph)[$1 .: $0 .: (fun k => $(2 + k))].
#[global] Arguments psiN : simpl never.
#[global] Arguments sepN : simpl never.

Lemma fb_psiN ph : fb (S (S (mN ph))) (psiN ph).
Proof.
  unfold psiN. cbn.
  repeat first [ split | (eapply fb_subst; [apply fb_phiN|]; intros [|[|i]] Hi; cbn; lia) | (cbn; lia) ].
Qed.

Lemma fb_sepN ph : fb (S (S (mN ph))) (sepN ph).
Proof. unfold sepN. eapply fb_subst; [apply fb_phiN|]. intros [|[|i]] Hi; cbn; lia. Qed.

Lemma psiN_inst ph a b (sg : nat -> term) :
  (psiN ph)[a .: b .: sg] = ∀ ($0 ∈' b`[↑] ↔ (phiN ph)[a`[↑] .: $0 .: (fun k => (sg k)`[↑])]).
Proof.
  unfold psiN. cbn [subst_form]. rewrite !subst_comp.
  assert (E : (phiN ph)[($1 .: $0 .: (fun k => $(3 + k))) >> subst_term (up (a .: b .: sg))]
              = (phiN ph)[a`[↑] .: $0 .: (fun k => (sg k)`[↑])]) by (apply subst_ext; intros [|[|k]]; term_eq).
  rewrite E. reflexivity.
Qed.

Lemma sepN_inst ph w (sg : nat -> term) :
  (sepN ph)[$0 .: (fun k => ((w .: sg) k)`[↑]`[↑])] = (phiN ph)[w`[↑]`[↑] .: $0 .: (fun k => (sg k)`[↑]`[↑])].
Proof. unfold sepN. form_subst_eq. Qed.

(** normalize one instance of [phiN] to [phiN ph][w .: z .: sg] *)
Ltac phin_norm H w z sg :=
  first [ match type of H with context [(phiN ?p)[?s][?t]] =>
            replace ((phiN p)[s][t]) with ((phiN p)[w .: z .: sg]) in H by form_subst_eq end
        | match type of H with context [(phiN ?p)[?s]] =>
            replace ((phiN p)[s]) with ((phiN p)[w .: z .: sg]) in H by form_subst_eq end ].
Ltac phin_norm_goal w z sg :=
  first [ match goal with |- context [(phiN ?p)[?s][?t]] =>
            replace ((phiN p)[s][t]) with ((phiN p)[w .: z .: sg]) by form_subst_eq end
        | match goal with |- context [(phiN ?p)[?s]] =>
            replace ((phiN p)[s]) with ((phiN p)[w .: z .: sg]) by form_subst_eq end ].

Definition A_rep (ph : wff) : list form :=
  forall_times (mN ph) (ax_rep' (psiN ph)) :: forall_times (S (mN ph)) (ax_sep' (sepN ph)) :: ZF0base.

Theorem bridge_REP_proof : bridge_REP.
Proof.
  intros ph n Hn. exists (A_rep ph). split.
  { intros psi [<-|[<-|H]]; [| |now apply ZF0base_ZFc]; left.
    - apply ZF0_rep. apply rep_closed, fb_psiN.
    - apply ZF0_sep. apply sep_closed, fb_sepN. }
  assert (HG : incl ZF0base (A_rep ph)) by (intros x Hx; now right; right).
  assert (HI : In (forall_times (mN ph) (ax_rep' (psiN ph))) (A_rep ph)) by now left.
  assert (HS : In (forall_times (S (mN ph)) (ax_sep' (sepN ph))) (A_rep ph)) by (right; now left).
  apply Lib_intro. intros sg. rewrite REP_eq. apply dB_impI. ctx_push Hh.
  assert (Hfun : forall a b b', Γ ⊢C (psiN ph)[a .: b .: sg] → (psiN ph)[a .: b' .: sg] → b ≡' b').
  { intros a b b'. rewrite !psiN_inst. apply II. ctx_push H1. apply II. ctx_push H2.
    apply (ext_rule HG); unfold sub'; apply AllI_named; intros z; cbn [subst_form]; apply II; ctx_push Hz;
      pose proof (AllE z H1) as E1; pose proof (AllE z H2) as E2; cbn in E1, E2;
      rewrite ?subst_term_shift in E1, E2, Hz; rewrite ?subst_term_shift; rewrite !subst_comp in E1, E2.
    - exact (iff_r _ _ _ E2 (iff_l _ _ _ E1 Hz)).
    - exact (iff_r _ _ _ E1 (iff_l _ _ _ E2 Hz)). }
  pose proof (rep_use _ (mN ph) (psiN ph) sg (sg 0) HI (fb_psiN ph) Hfun) as T. clear Hfun.
  apply (ExE_named T). intros Img. ctx_push HImg. clear T. cbn in HImg.
  fobtain (union_ex HG Img) as U HU.
  unfold repC. apply (dB_exI _ _ _ U). apply dB_allI. intros z. apply dB_andI.
  - apply dB_impI. ctx_push Hz. cbn [dB] in Hz. rewrite upd_eq, upd_neq, upd_eq in Hz by lia.
    fhave T : (union_el HG Img U z HU Hz). fex T Fs HFs. fdestr HFs HF1 HF2.
    pose proof (AllE Fs HImg) as T. simp_in T.
    pose proof (iff_l _ _ _ T HF1) as T2. clear T. apply (ExE_named T2). intros w. ctx_push Hw. clear T2.
    simp_in Hw. fdestr Hw Hw1 Hw2.
    rewrite !subst_comp in Hw2.
    replace ((psiN ph)[_]) with ((psiN ph)[w .: Fs .: sg]) in Hw2 by form_subst_eq.
    rewrite psiN_inst in Hw2. pose proof (AllE z Hw2) as Hw3. cbn in Hw3.
    rewrite ?subst_term_shift in Hw3. rewrite subst_comp in Hw3.
    pose proof (iff_l _ _ _ Hw3 HF2) as Hp. clear Hw3.
    replace ((phiN ph)[_]) with ((phiN ph)[w .: z .: sg]) in Hp by form_subst_eq.
    unfold repE. apply (dB_exI _ _ _ w). apply dB_andI.
    + cbn [dB]. rewrite upd_eq, !upd_neq by lia. exact Hw1.
    + rewrite <- (phiN_inst ph w z sg (upd (upd (upd sg 1 U) 2 z) 3 w)) by env_eq2. exact Hp.
  - apply dB_impI. ctx_push HE'. unfold repE in HE'. apply (dB_exE _ _ _ _ HE'). intros w. apply II. ctx_push Hw.
    pose proof (dB_andE1 _ _ _ Hw) as Hw1. apply dB_andE2 in Hw.
    cbn [dB] in Hw1. rewrite upd_eq, !upd_neq in Hw1 by lia.
    rewrite <- (phiN_inst ph w z sg (upd (upd (upd sg 1 U) 2 z) 3 w)) in Hw by env_eq2.
    unfold repH in Hh. pose proof (dB_allE _ _ _ w Hh) as Hw'.
    apply (dB_exE _ _ _ _ Hw'). intros y. apply II. ctx_push Hy. clear Hw'.
    (* the bound B = y u P(y) *)
    fassert Hpw : ax_power'. { apply Ctx, HG; cbn; tauto. }
    unfold ax_power' in Hpw. apply (AllE y) in Hpw. cbn in Hpw.
    apply (ExE_named Hpw). intros P. ctx_push HP. clear Hpw. simp_in HP.

    fobtain (bun_ex HG y P) as B HB.
    pose proof (sep_use _ (S (mN ph)) (sepN ph) (w .: sg) B HS (fb_sepN ph)) as T.
    rewrite sepN_inst in T. apply (ExE_named T). intros Fw. ctx_push HFw. clear T. cbn in HFw.
    (* Fw is the fiber of w *)
    fassert Hpsi : ((psiN ph)[w .: Fw .: sg]).
    { rewrite psiN_inst. apply AllI_named. intros z'. cbn.
      pose proof (AllE z' HFw) as E. simp_in E. simp.
      phin_norm E w z' sg. phin_norm_goal w z' sg.
      apply CI.
      - apply II. ctx_push Hz'. exact (CE2 (iff_l _ _ _ E Hz')).
      - apply II. ctx_push Hz'. apply (iff_r _ _ _ E). apply CI; [|exact Hz'].
        pose proof (dB_allE _ _ _ z' Hy) as Hy'. 
        rewrite (phiN_inst ph w z' sg (upd (upd (upd sg 3 w) 1 y) 2 z')) in Hz' by env_eq2.
        pose proof (dB_imp _ _ _ Hy' Hz') as H'. rewrite dB_repB in H'. rewrite upd_eq, upd_neq, upd_eq in H' by lia.
        unfold rbC in H'. apply (XM_rule _ (sub' z' y)).
        + apply II. ctx_push Hs. apply (bun_in HG y P B z' HB). apply DI2.
          pose proof (AllE z' HP) as E'. simp_in E'.
          exact (iff_r _ _ _ E' Hs).
        + apply II. ctx_push Hns. apply (bun_in HG y P B z' HB). apply DI1. exact (IE H' Hns). }
    fassert HFI : (Fw ∈' Img).
    { pose proof (AllE Fw HImg) as T. simp_in T.
      apply (iff_r _ _ _ T). apply (ExI w). cbn. rewrite ?subst_term_shift. apply CI; [exact Hw1|].
      rewrite !subst_comp. replace ((psiN ph)[_]) with ((psiN ph)[w .: Fw .: sg]) by form_subst_eq. exact Hpsi. }
    fassert HzF : (z ∈' Fw).
    { rewrite psiN_inst in Hpsi. pose proof (AllE z Hpsi) as E. cbn in E.
      rewrite ?subst_term_shift in E. rewrite subst_comp in E.
      replace ((phiN ph)[_]) with ((phiN ph)[w .: z .: sg]) in E by form_subst_eq.
      exact (iff_r _ _ _ E Hw). }
    cbn [dB]. rewrite upd_eq, upd_neq, upd_eq by lia.
    exact (union_in HG Img U Fw z HU HFI HzF).
Qed.
