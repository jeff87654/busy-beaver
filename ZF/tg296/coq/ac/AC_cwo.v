(** * AC_cwo: the canonical well-order of L_{ξ+1} and canonical witnesses in L (no choice).

    [CWO ξ W]: W is the value at ξ of Z_wo's outer recursion [Sout] (a well-order of Def(L_ξ) = L_{ξ+1}).
    [CanW c x w]: w is the canonical witness of c(·, x) in L (c: $0 = witness, $1 = parameter, read
    through [Std_setrec.Rel2 c v x]): ξ is the least ordinal with a witness in L_{ξ+1} ([HasW]), and w
    is the CWO-least witness in L_{ξ+1}. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZF Require Std_setrec.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_wo.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition CWO (xi W : term) : form :=
  ∃ (∃ (Succ0 xi`[↑]`[↑] $1 ∧ Fun0 $0 ∧ Dom0 $0 $1 ∧ RecOK Sout xi`[↑]`[↑] $0 ∧ App0 $0 xi`[↑]`[↑] W`[↑]`[↑])).
(** some witness of c(·, x) lies in L_{ξ+1} *)
Definition HasW (c : form) (x xi : term) : form := ∃ (InL1 $0 xi`[↑] ∧ Std_setrec.Rel2 c $0 x`[↑]).
Definition CanW (c : form) (x w : term) : form :=
  ∃ (Ord0 $0 ∧ HasW c x`[↑] $0 ∧ (∀ ($0 ∈' $1 → ¬ HasW c x`[↑]`[↑] $0)) ∧ InL1 w`[↑] $0 ∧
     Std_setrec.Rel2 c w`[↑] x`[↑] ∧
     ∀ (CWO $1 $0 → ∀ (InL1 $0 $2 → Std_setrec.Rel2 c $0 x`[↑]`[↑]`[↑] → ¬ ($0 ≡' w`[↑]`[↑]`[↑]) →
                       App0 $1 w`[↑]`[↑]`[↑] $0))).
#[global] Arguments CWO : simpl never.
#[global] Arguments HasW : simpl never.
#[global] Arguments CanW : simpl never.
Lemma CWO_subst xi W sg : (CWO xi W)[sg] = CWO xi`[sg] W`[sg].
Proof. psubst CWO. Qed.
Lemma HasW_subst c x xi sg : (HasW c x xi)[sg] = HasW c x`[sg] xi`[sg].
Proof. psubst HasW. Qed.
#[global] Hint Rewrite CWO_subst HasW_subst : fsub.
Lemma CanW_subst c x w sg : (CanW c x w)[sg] = CanW c x`[sg] w`[sg].
Proof. psubst CanW. Qed.
#[global] Hint Rewrite CanW_subst : fsub.

(** free-index bounds for the concrete predicates at arbitrary indices *)
Lemma fb_InL1 z e N : idx z < N -> idx e < N -> fb N (InL1 z e).
Proof.
  intros Hz He. replace (InL1 z e) with ((InL1 $0 $1)[z .: e .: var]) by (rewrite InL1_subst; reflexivity).
  apply (fb_subst _ 2); [fbcomp|]. intros [|[|i]] Hi; cbn; lia.
Qed.
Lemma fb_Ord0 a N : idx a < N -> fb N (Ord0 a).
Proof.
  intros Ha. replace (Ord0 a) with ((Ord0 $0)[a .: var]) by (rewrite Ord0_subst; reflexivity).
  apply (fb_subst _ 1); [fbcomp|]. intros [|i] Hi; cbn; lia.
Qed.
Lemma fb_App0 f u v N : idx f < N -> idx u < N -> idx v < N -> fb N (App0 f u v).
Proof.
  intros Hf Hu Hv. replace (App0 f u v) with ((App0 $0 $1 $2)[f .: u .: v .: var]) by (rewrite App0_subst; reflexivity).
  apply (fb_subst _ 3); [fbcomp|]. intros [|[|[|i]]] Hi; cbn; lia.
Qed.
Lemma fb_CWO xi W N : idx xi < N -> idx W < N -> fb N (CWO xi W).
Proof.
  intros Hx HW. replace (CWO xi W) with ((CWO $0 $1)[xi .: W .: var]) by (rewrite CWO_subst; reflexivity).
  apply (fb_subst _ 2); [fbcomp|]. intros [|[|i]] Hi; cbn; lia.
Qed.

Lemma fb_HasW0 c : fb 2 (HasW c $1 $0).
Proof.
  unfold HasW. cbn. split.
  - apply fb_InL1; cbn; lia.
  - apply Std_setrec.fb_Rel2; cbn; lia.
Qed.
Lemma fb_HasW_g c x xi N : idx x < N -> idx xi < N -> fb N (HasW c x xi).
Proof.
  intros Hx Hxi. replace (HasW c x xi) with ((HasW c $1 $0)[xi .: x .: var]) by (rewrite HasW_subst; reflexivity).
  eapply fb_subst; [exact (fb_HasW0 c)|]. intros [|[|i]] Hi; cbn; lia.
Qed.
Lemma fb_HasW c : fb 2 c -> fb 2 (HasW c $1 $0).
Proof. intros _. exact (fb_HasW0 c). Qed.

Ltac fbpred := repeat match goal with
  | |- _ /\ _ => split
  | |- True => exact I
  | |- fb _ (Ord0 _) => apply fb_Ord0; cbn; lia
  | |- fb _ (HasW _ _ _) => apply fb_HasW_g; cbn; lia
  | |- fb _ (InL1 _ _) => apply fb_InL1; cbn; lia
  | |- fb _ (Std_setrec.Rel2 _ _ _) => apply Std_setrec.fb_Rel2; cbn; lia
  | |- fb _ (CWO _ _) => apply fb_CWO; cbn; lia
  | |- fb _ (App0 _ _ _) => apply fb_App0; cbn; lia
  | |- _ < _ => lia
  end.
Lemma fb_CanW0 c : fb 2 (CanW c $0 $1).
Proof. unfold CanW. cbn. fbpred. Qed.
Lemma fb_CanW c x w N : fb 2 c -> idx x < N -> idx w < N -> fb N (CanW c x w).
Proof.
  intros _ Hx Hw. replace (CanW c x w) with ((CanW c $0 $1)[x .: w .: var]) by (rewrite CanW_subst; reflexivity).
  eapply fb_subst; [exact (fb_CanW0 c)|]. intros [|[|i]] Hi; cbn; lia.
Qed.

(** the separation formula {v ∈ D | c(v, x)}: $0 = v, $1 = x *)
Definition sep_cw (c : form) : form := Std_setrec.Rel2 c $0 $1.
Lemma fb_sep_cw c : fb 2 (sep_cw c).
Proof. apply Std_setrec.fb_Rel2; cbn; lia. Qed.

Definition Ax_cw (c : form) : list form := [least_inst 1 (HasW c $1 $0); forall_times 1 (ax_sep' (sep_cw c))].
Lemma Ax_cw_ok c a : fb 2 c -> In a (Ax_cw c) -> ZFR a.
Proof.
  intros _ [<-|[<-|[]]].
  - apply ZFR_sep. exact (fb_HasW0 c).
  - apply ZFR_sep. exact (fb_sep_cw c).
Qed.

(** ** Proofs (outside the section, explicit hypotheses) *)
#[local] Ltac weaken_facts a G ::=
  repeat match goal with
  | H : G ⊢C _ |- _ => apply (weak_cons G a) in H
  | H : forall k : nat, @prv _ _ _ class G (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k => weak_cons G a _ (H k)) as H'; clear H; rename H' into H
  | H : incl _ G |- _ => apply (incl_cons_r _ G a) in H
  | H : In _ G |- _ => apply (in_cons_r _ a G) in H
  | H : WOx G |- _ => apply (WOx_cons G a) in H
  end.

Lemma cw_wox {G} : In ax_reg' G -> In ax_om' G -> incl Ax_wo G -> WOx G.
Proof. intros a b d. split; [exact a|split; [exact b|exact d]]. Qed.

Lemma in_psi_ind {G} (HX : WOx G) : In (least_inst 2 (¬ psi_ind)) G.
Proof.
  apply (in_wo HX). unfold wo_list, wo_insts1. rewrite !in_app_iff. right. right. left.
  cbn -[forall_times ax_sep' psi_ind]. repeat (first [left; reflexivity | right]).
Qed.
Lemma in_cw1 {G} c : incl (Ax_cw c) G -> In (least_inst 1 (HasW c $1 $0)) G.
Proof. intros H. apply H. now left. Qed.
Lemma in_cw2 {G} c : incl (Ax_cw c) G -> In (forall_times 1 (ax_sep' (sep_cw c))) G.
Proof. intros H. apply H. right. now left. Qed.

Lemma cwo_ex_g {G} (HG : incl ZF0base G) (HX : WOx G) xi : G ⊢C Ord0 xi -> G ⊢C ∃ CWO xi`[↑] $0.
Proof.
  intros Oxi.
  fobtain (Z_wo.w_succ0_ex HG HX xi) as s Hs.
  pose proof (Z_wo.w_ord_succ HG HX xi s Oxi Hs) as Os.
  pose proof (Z_wo.w_rec_ex HG HX Sout fb_Sout (in_rec_Sout HX) xi s (Sout_loc HG HX xi) (Sout_tot HG HX xi)
                (Sout_fun HG HX xi) Os) as T.
  fex T F HFd. fdestr HFd HFd1 Hr. fdestr HFd1 Hf Hd.
  fobtain (Z_wo.w_dom0_app HG HX F s xi Hd (wo_succ_in xi s Hs)) as W HW.
  fexists W. unfold CWO. fexists s. fexists F.
  fsplit; [fsplit; [fsplit; [fsplit|]|]|]; assumption.
Qed.

Ltac cwo_unpack H s F Hsucc Hf Hd Hr HApp :=
  unfold CWO in H; let Hs := fresh "Hs" in let HF := fresh "HF" in let HF1 := fresh "HF1" in
  let HF2 := fresh "HF2" in let HF3 := fresh "HF3" in
  fex H s Hs; fex Hs F HF; fdestr HF HF1 HApp; fdestr HF1 HF2 Hr; fdestr HF2 HF3 Hd; fdestr HF3 Hsucc Hf.

Lemma cwo_unique_g {G} (HG : incl ZF0base G) (HX : WOx G) xi W W' :
  G ⊢C Ord0 xi -> G ⊢C CWO xi W -> G ⊢C CWO xi W' -> G ⊢C W ≡' W'.
Proof.
  intros Oxi H1 H2.
  cwo_unpack H1 s F Hsucc Hf Hd Hr HApp.
  cwo_unpack H2 s' F' Hsucc' Hf' Hd' Hr' HApp'.
  exact (Z_wo.w_rec_agree HG HX Sout fb_Sout (in_rec_Sout HX) xi s s' F F' xi W W' (Sout_loc HG HX xi) (Sout_fun HG HX xi)
           (Z_wo.w_ord_succ HG HX xi s Oxi Hsucc) Hf Hd Hr
           (Z_wo.w_ord_succ HG HX xi s' Oxi Hsucc') Hf' Hd' Hr'
           (wo_succ_in xi s Hsucc) (wo_succ_in xi s' Hsucc') HApp HApp').
Qed.

Lemma cwo_wo_g {G} (HG : incl ZF0base G) (HX : WOx G) xi W Y D :
  G ⊢C Ord0 xi -> G ⊢C CWO xi W -> G ⊢C LL xi Y -> G ⊢C Def0 Y D -> G ⊢C WO W D.
Proof.
  intros Oxi H HY HD.
  cwo_unpack H s F Hsucc Hf Hd Hr HApp.
  pose proof (Z_wo.w_ord_succ HG HX xi s Oxi Hsucc) as Os.
  pose proof (Z_wo.w_ord_ind HG HX 2 psi_ind (F .: s .: var) xi fb_psi_ind (in_psi_ind HX)) as Ind.
  unfold psi_ind in Ind. simp_in Ind.
  specialize (Ind (outer_step HG HX F s xi Os Hf Hd Hr) Oxi). unfold PsiP in Ind. fmp Ind (wo_succ_in xi s Hsucc).
  finst Ind W. fmp Ind HApp. finst Ind Y. fmp Ind HY. finst Ind D. fmp Ind HD. exact Ind.
Qed.

Ltac canw_unpack H xi Oxi Hhas Hmin Hin Hrel Hcl :=
  unfold CanW in H; let Hx := fresh "Hx" in let A3 := fresh "A" in let A4 := fresh "A" in
  let A5 := fresh "A" in let A6 := fresh "A" in
  fex H xi Hx; fdestr Hx A6 Hcl; fdestr A6 A5 Hrel; fdestr A5 A4 Hin; fdestr A4 A3 Hmin; fdestr A3 Oxi Hhas.

Lemma canw_ex_g {G} (HG : incl ZF0base G) (HX : WOx G) c (HC : incl (Ax_cw c) G) x :
  G ⊢C ∃ (Lform ∧ Std_setrec.Rel2 c $0 x`[↑]) -> G ⊢C ∃ CanW c x`[↑] $0.
Proof.
  intros H. apply (ExE_named H); intros v; ctx_push Hv; try clear H.
  fassert HvL : (InL v). { exact (CE1 Hv). }
  fassert HvR : (Std_setrec.Rel2 c v x).
  { assert (E : (Std_setrec.Rel2 c $0 x`[↑])[v..] = Std_setrec.Rel2 c v x)
      by (rewrite Std_setrec.Rel2_subst; simp; reflexivity).
    rewrite <- E. exact (CE2 Hv). }
  clear Hv. rewrite InL_eq in HvL.
  fex HvL a Ha. fex Ha Y HY. fdestr HY HY1 Hvy. fdestr HY1 Oa HYa.
  pose proof (inl1_ex HG HX a Y v Oa HYa Hvy) as T. fex T e He. fdestr He Hea Hev.
  pose proof (Z_wo.w_ord_el HG HX a e Oa Hea) as Oe.
  fassert Hhas : (HasW c x e). { unfold HasW. fexists v. fsplit; [exact Hev|exact HvR]. }
  pose proof (Z_wo.w_least_ord HG HX 1 (HasW c $1 $0) (x .: var) e (fb_HasW0 c) (in_cw1 c HC) Oe) as L.
  simp_in L. specialize (L Hhas).
  fex L xi Hxi. fdestr Hxi Hxi1 Hmin. fdestr Hxi1 Oxi Hhasxi.
  pose proof Hhasxi as Hh. unfold HasW in Hh. fex Hh u Hu. fdestr Hu Hu1 Hu2.
  fobtain (Z_wo.w_LL_ex HG HX xi Oxi) as Y0 HY0.
  fobtain (Z_wo.w_def_ex HG HX Y0) as D HD.
  fobtain (cwo_ex_g HG HX xi Oxi) as W HWc.
  pose proof (cwo_wo_g HG HX xi W Y0 D Oxi HWc HY0 HD) as HWO.
  fobtain (Z_wo.w_succ0_ex HG HX xi) as s Hs. pose proof (Z_wo.w_ord_succ HG HX xi s Oxi Hs) as Os.
  fobtain (Z_wo.w_LL_ex HG HX s Os) as Ys HYs.
  pose proof (Z_wo.w_def_unique HG HX Y0 D Ys HD (Z_wo.w_LL_succ HG HX xi s Y0 Ys Oxi Hs HY0 HYs)) as EDs.
  pose proof (sep_use _ 1 (sep_cw c) (x .: var) D (in_cw2 c HC) (fb_sep_cw c)) as T. unfold sep_cw in T. simp_in T.
  fex T y Hy.
  fassert HyD : (Sub0 y D).
  { unfold Sub0. fall z. fintro Hz. pose proof Hy as H'. finst H' z. exact (CE1 (iff_l _ _ _ H' Hz)). }
  fassert HuD : (u ∈' D). { pose proof (inl1_lev HG HX u xi s Ys Oxi Hs HYs Hu1) as H'. fmem. }
  fassert Huy : (u ∈' y). { pose proof Hy as H'. finst H' u. apply (iff_r _ _ _ H'). fsplit; assumption. }
  pose proof (wo_least W D y u HWO HyD Huy) as L'. fex L' m Hm.
  pose proof (lst_in _ _ _ Hm) as Hmy.
  pose proof Hy as H'. finst H' m. pose proof (iff_l _ _ _ H' Hmy) as Hm2. clear H'. fdestr Hm2 HmD HmR.
  fexists m. unfold CanW. fexists xi.
  fsplit; [fsplit; [fsplit; [fsplit; [fsplit|]|]|]|].
  - exact Oxi.
  - exact Hhasxi.
  - exact Hmin.
  - unfold InL1. fexists s. fsplit; [exact Hs|]. fexists Ys. fsplit; [exact HYs|]. fmem.
  - exact HmR.
  - fall W'. fintro HW'. fall z. fintro Hz1. fintro Hz2. fintro Hz3.
    pose proof (cwo_unique_g HG HX xi W W' Oxi HWc HW') as EW.
    fassert HzD : (z ∈' D). { pose proof (inl1_lev HG HX z xi s Ys Oxi Hs HYs Hz1) as H'. fmem. }
    fassert Hzy : (z ∈' y). { pose proof Hy as H'. finst H' z. apply (iff_r _ _ _ H'). fsplit; assumption. }
    pose proof (lst_lt W y m z Hm Hzy Hz3) as A. frew_in EW (App0 $0 m`[↑] z`[↑]) A. exact A.
Qed.

Lemma canw_unique_g {G} (HG : incl ZF0base G) (HX : WOx G) c x w w' :
  G ⊢C CanW c x w -> G ⊢C CanW c x w' -> G ⊢C w ≡' w'.
Proof.
  intros H1 H2.
  canw_unpack H1 xi Oxi Hhas Hmin Hin Hrel Hcl.
  canw_unpack H2 xi' Oxi' Hhas' Hmin' Hin' Hrel' Hcl'.
  fassert E : (xi ≡' xi').
  { pose proof (Z_wo.w_ord_tri HG HX xi xi' Oxi Oxi') as Tr. fcases Tr Tr1 Tr2; [fcases Tr1 Tr3 Tr4|].
    - fabsurd. finst Hmin' xi. fmp Hmin' Tr3. exact (IE Hmin' Hhas).
    - exact Tr4.
    - fabsurd. finst Hmin xi'. fmp Hmin Tr2. exact (IE Hmin Hhas'). }
  frew_in E (InL1 w'`[↑] $0) Hin'.
  fobtain (cwo_ex_g HG HX xi Oxi) as W HWc.
  pose proof HWc as HWc'. frew_in E (CWO $0 W`[↑]) HWc'.
  pose proof Hin as HinX. frew_in E (InL1 w`[↑] $0) HinX.
  fobtain (Z_wo.w_LL_ex HG HX xi Oxi) as Y0 HY0.
  fobtain (Z_wo.w_def_ex HG HX Y0) as D HD.
  pose proof (cwo_wo_g HG HX xi W Y0 D Oxi HWc HY0 HD) as HWO.
  fobtain (Z_wo.w_succ0_ex HG HX xi) as s Hs. pose proof (Z_wo.w_ord_succ HG HX xi s Oxi Hs) as Os.
  fobtain (Z_wo.w_LL_ex HG HX s Os) as Ys HYs.
  pose proof (Z_wo.w_def_unique HG HX Y0 D Ys HD (Z_wo.w_LL_succ HG HX xi s Y0 Ys Oxi Hs HY0 HYs)) as EDs.
  fassert HwD : (w ∈' D). { pose proof (inl1_lev HG HX w xi s Ys Oxi Hs HYs Hin) as H'. fmem. }
  fassert Hw'D : (w' ∈' D). { pose proof (inl1_lev HG HX w' xi s Ys Oxi Hs HYs Hin') as H'. fmem. }
  apply (XM_rule _ (w ≡' w')); [apply imp_refl|]. fintro NE. fabsurd.
  fassert NE' : (¬ (w' ≡' w)). { fintro E'. apply (IE NE). feq. }
  pose proof Hcl as C1. finst C1 W. fmp C1 HWc. finst C1 w'. fmp C1 Hin'. fmp C1 Hrel'. fmp C1 NE'.
  pose proof Hcl' as C2. finst C2 W. fmp C2 HWc'. finst C2 w. fmp C2 HinX. fmp C2 Hrel. fmp C2 NE.
  exact (wo_asym W D w w' HWO HwD Hw'D C1 C2).
Qed.

Lemma canw_L_g {G} (HG : incl ZF0base G) (HX : WOx G) c x w : G ⊢C CanW c x w -> G ⊢C InL w.
Proof.
  intros H. canw_unpack H xi Oxi Hhas Hmin Hin Hrel Hcl.
  unfold InL1 in Hin. fex Hin s Hs. fdestr Hs Hs1 Hs2. fex Hs2 Ys HYs. fdestr HYs HYs1 HYs2.
  exact (InL_intro s Ys w (Z_wo.w_ord_succ HG HX xi s Oxi Hs1) HYs1 HYs2).
Qed.

Lemma canw_sat_g {G} (HG : incl ZF0base G) c x w : G ⊢C CanW c x w -> G ⊢C Std_setrec.Rel2 c w x.
Proof. intros H. canw_unpack H xi Oxi Hhas Hmin Hin Hrel Hcl. exact Hrel. Qed.

Section CW.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G).
#[local] Set Default Proof Using "All".

Lemma cwo_ex xi : G ⊢C Ord0 xi -> G ⊢C ∃ CWO xi`[↑] $0.
Proof. exact (cwo_ex_g HG (cw_wox HR HOm HW) xi). Qed.

Lemma cwo_unique xi W W' : G ⊢C Ord0 xi -> G ⊢C CWO xi W -> G ⊢C CWO xi W' -> G ⊢C W ≡' W'.
Proof. exact (cwo_unique_g HG (cw_wox HR HOm HW) xi W W'). Qed.

Lemma cwo_wo xi W Y D : G ⊢C Ord0 xi -> G ⊢C CWO xi W -> G ⊢C LL xi Y -> G ⊢C Def0 Y D -> G ⊢C WO W D.
Proof. exact (cwo_wo_g HG (cw_wox HR HOm HW) xi W Y D). Qed.

Context (c : form) (Hc : fb 2 c) (HC : incl (Ax_cw c) G).

Lemma canw_ex x : G ⊢C ∃ (Lform ∧ Std_setrec.Rel2 c $0 x`[↑]) -> G ⊢C ∃ CanW c x`[↑] $0.
Proof. exact (canw_ex_g HG (cw_wox HR HOm HW) c HC x). Qed.

Lemma canw_unique x w w' : G ⊢C CanW c x w -> G ⊢C CanW c x w' -> G ⊢C w ≡' w'.
Proof. exact (canw_unique_g HG (cw_wox HR HOm HW) c x w w'). Qed.

Lemma canw_L x w : G ⊢C CanW c x w -> G ⊢C InL w.
Proof. exact (canw_L_g HG (cw_wox HR HOm HW) c x w). Qed.

Lemma canw_sat x w : G ⊢C CanW c x w -> G ⊢C Std_setrec.Rel2 c w x.
Proof. exact (canw_sat_g HG c x w). Qed.

End CW.
