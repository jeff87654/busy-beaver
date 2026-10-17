(** * AC_gu: GU holds in L (inside ZF + Reg + GU).

    For x ∈ L at stage a, GU gives a universe U ∋ {a, ω}; κ = U ∩ On; u := L_κ ∈ L, x ∈ u.
    (Gru u)^L, clause by clause (the pattern of SU_reg.GU_WF): the L-witness W comes from the ZF
    theorems [T_pow], [T_pair], [T_un] relativized to L (their relativized bodies are literally the
    relativized clauses of Gru); W ⊆ L_κ ([cond] for the elements), W ∈ U (V-Gru), so W ⊆ L_c for some
    c ∈ κ ([bnd]) and W ∈ L_κ ([cond]). *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZF Require Std_setrec.
From RegCon Require Import Rel.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_sg Z_refl Z_axL Z_wo Z_ac.
From M254TG Require Import SU_gu SU_fn SU_univ.
From M254TG Require SU_V.
From M254TGA Require Import AC_rec AC_univ AC_cwo AC_tup AC_hull AC_iso AC_coll AC_cond.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

#[local] Arguments Lform : simpl never.
#[local] Arguments InL : simpl never.
#[local] Hint Rewrite Z_axL.Lform_up Z_axL.Lform_inst Z_axL.InL_subst Z_axL.relL_subst : fsub.

(** the three ZF theorems transferred to L *)
Definition T_pow : form := ∀ (∃ (∀ ($0 ∈' $1 ↔ Sub0 $0 $2))).
Definition T_pair : form := ∀ (∀ (∃ Pair0 $2 $1 $0)).
Definition T_un : form := ∀ (∃ (∀ ($0 ∈' $1 ↔ ∃ ((∃ App0 $4 $0 $1) ∧ $1 ∈' $0)))).

Lemma T_pow_closed : closedf T_pow.
Proof. unfold closedf. fbcomp. Qed.
Lemma T_pair_closed : closedf T_pair.
Proof. unfold closedf. fbcomp. Qed.
Lemma T_un_closed : closedf T_un.
Proof. unfold closedf. fbcomp. Qed.

(** ∪ran f by separation from ⋃⋃⋃f: $0 = z, $1 = f (as SU_gru.psi_ur) *)
Definition psi_unT : form := ∃ ((∃ App0 $3 $0 $1) ∧ $1 ∈' $0).
Lemma fb_unT : fb 2 psi_unT.
Proof. unfold psi_unT. fbcomp. Qed.

(** the ZF derivations (instances filled by the prover of this file) *)
Definition Ax_T : list form := [forall_times 1 (ax_sep' psi_unT)].
Lemma Ax_T_ok a : In a Ax_T -> ZFR a.
Proof. intros [<-|[]]. apply ZFR_sep. exact fb_unT. Qed.
Definition A_T : list form := ax_reg' :: ax_om' :: ZF0base ++ Ax_wo ++ Ax_T.

Lemma T_pair_g {G} (HG : incl ZF0base G) : G ⊢C T_pair.
Proof.
  assert (HP : incl Ax_prim G) by (intros a []).
  unfold T_pair. fall x. fall y. eapply pair0_ex; eassumption.
Qed.

Lemma T_pow_g {G} (HG : incl ZF0base G) : G ⊢C T_pow.
Proof.
  unfold T_pow. fall x. pose proof (SU_V.pow_ex HG x) as A. fex A P HP. fexists P.
  unfold is_power in HP. exact HP.
Qed.

Lemma T_un_g {G} (HG : incl ZF0base G) (HA : In (forall_times 1 (ax_sep' psi_unT)) G) : G ⊢C T_un.
Proof.
  assert (HP : incl Ax_prim G) by (intros a []).
  unfold T_un. fall F.
  fassert A1 : (∃ Union0 F`[↑] $0). { eapply union0_ex; eassumption. } fex A1 U1 HU1.
  fassert A2 : (∃ Union0 U1`[↑] $0). { eapply union0_ex; eassumption. } fex A2 U2 HU2.
  fassert A3 : (∃ Union0 U2`[↑] $0). { eapply union0_ex; eassumption. } fex A3 U3 HU3.
  pose proof (sep_use _ 1 psi_unT (F .: var) U3 HA fb_unT) as A.
  unfold psi_unT in A. simp_in A. fex A X HX. fexists X. fall z. fsplit.
  - fintro Hz. finst HX z. exact (CE2 (iff_l _ _ _ HX Hz)).
  - fintro Hz. finst HX z. apply (iff_r _ _ _ HX). fsplit; [|exact Hz].
    fex Hz v Hv. fdestr Hv Hv1 Hzv. fex Hv1 a Ha. pose proof Ha as Ha'. unfold App0 in Ha'.
    fex Ha' q Hq. fdestr Hq Hq1 Hq2. pose proof (op0_val a v q Hq2) as B. fex B r Hr. fdestr Hr Hr1 Hr2.
    apply (union_in0 U2 U3 v z HU3); [|exact Hzv].
    apply (union_in0 U1 U2 r v HU2); [|exact Hr2]. exact (union_in0 F U1 q r HU1 Hq1 Hr1).
Qed.

Lemma A_T_base : incl ZF0base A_T.
Proof. intros b Hb. right. right. apply in_app_iff. now left. Qed.
Lemma A_T_un : In (forall_times 1 (ax_sep' psi_unT)) A_T.
Proof. right. right. apply in_app_iff. right. apply in_app_iff. right. now left. Qed.

Lemma T_pow_prv : A_T ⊢C T_pow.
Proof. exact (T_pow_g A_T_base). Qed.
Lemma T_pair_prv : A_T ⊢C T_pair.
Proof. exact (T_pair_g A_T_base). Qed.
Lemma T_un_prv : A_T ⊢C T_un.
Proof. exact (T_un_g A_T_base A_T_un). Qed.

(** instances used in V (extended by the prover of this file) *)
Definition Ax_gu : list form := Ax_cond.
Lemma Ax_gu_ok a : In a Ax_gu -> ZFR a.
Proof. exact (Ax_cond_ok a). Qed.

Lemma gu_cond G : incl Ax_gu G -> incl Ax_cond G.
Proof. intros H. exact H. Qed.
Lemma cond_univ G : incl Ax_cond G -> incl Ax_univ G.
Proof. intros H a Ha. apply H. unfold Ax_cond. apply in_app_iff. now left. Qed.

(** ** L-side helpers *)
Lemma inLe {G} (HT : G ⊢C TransC Lform) x z : G ⊢C InL x -> G ⊢C z ∈' x -> G ⊢C InL z.
Proof. exact (trans_use Lform bounded_Lform G x z HT). Qed.

Lemma d0L {G} (HT : G ⊢C TransC Lform) (phi : form) sg : D0 phi -> (forall k, G ⊢C InL (sg k)) ->
  G ⊢C rel Lform (phi[sg]) ↔ phi[sg].
Proof. intros Hd Hs. rewrite <- relsub. exact (D0_abs Lform bounded_Lform phi Hd G sg HT Hs). Qed.

Section D0L.
Context {G : list form} (HT : G ⊢C TransC Lform).

Lemma relL_Sub0 z x : G ⊢C InL z -> G ⊢C InL x -> G ⊢C rel Lform (Sub0 z x) ↔ Sub0 z x.
Proof.
  intros Hz Hx. pose proof (d0L HT (Sub0 $0 $1) (z .: x .: (fun _ => z))) as H.
  rewrite Sub0_subst in H. apply H; [d0comp | intros [|[|k]]; assumption].
Qed.

Lemma relL_Pair0 x y q : G ⊢C InL x -> G ⊢C InL y -> G ⊢C InL q ->
  G ⊢C rel Lform (Pair0 x y q) ↔ Pair0 x y q.
Proof.
  intros Hx Hy Hq. pose proof (d0L HT (Pair0 $0 $1 $2) (x .: y .: q .: (fun _ => x))) as H.
  rewrite Pair0_subst in H. apply H; [d0comp | intros [|[|[|k]]]; assumption].
Qed.

Lemma relL_Trans0 w : G ⊢C InL w -> G ⊢C rel Lform (Trans0 w) ↔ Trans0 w.
Proof.
  intros Hw. pose proof (d0L HT (Trans0 $0) (w .: (fun _ => w))) as H.
  rewrite Trans0_subst in H. apply H; [d0comp | intros [|k]; assumption].
Qed.

Lemma relL_Fun0 f : G ⊢C InL f -> G ⊢C rel Lform (Fun0 f) ↔ Fun0 f.
Proof.
  intros Hf. pose proof (d0L HT (Fun0 $0) (f .: (fun _ => f))) as H.
  rewrite Fun0_subst in H. apply H; [d0comp | intros [|k]; assumption].
Qed.

Lemma relL_Dom0 f x : G ⊢C InL f -> G ⊢C InL x -> G ⊢C rel Lform (Dom0 f x) ↔ Dom0 f x.
Proof.
  intros Hf Hx. pose proof (d0L HT (Dom0 $0 $1) (f .: x .: (fun _ => f))) as H.
  rewrite Dom0_subst in H. apply H; [d0comp | intros [|[|k]]; assumption].
Qed.

Lemma relL_App0 f a v : G ⊢C InL f -> G ⊢C InL a -> G ⊢C InL v ->
  G ⊢C rel Lform (App0 f a v) ↔ App0 f a v.
Proof.
  intros Hf Ha Hv. pose proof (d0L HT (App0 $0 $1 $2) (f .: a .: v .: (fun _ => f))) as H.
  rewrite App0_subst in H. apply H; [d0comp | intros [|[|[|k]]]; assumption].
Qed.

End D0L.

(** both components of a pair (a, v) ∈ f ∈ L are in L *)
Lemma app_L {G} (HT : G ⊢C TransC Lform) f a v : G ⊢C InL f -> G ⊢C App0 f a v -> G ⊢C InL a ∧ InL v.
Proof.
  intros Hf H. unfold App0 in H. fex H p Hp. fdestr Hp Hpf Hop.
  pose proof (inLe HT _ _ Hf Hpf) as Hpw.
  unfold OP0 in Hop. simp_in Hop. fdestr Hop Hop12 Hop3. fdestr Hop12 Hs Hq.
  fsplit.
  - fex Hs s Hs'. fdestr Hs' Hsp Hsing. unfold Sing0 in Hsing. fdestr Hsing Has Hs2.
    exact (inLe HT _ _ (inLe HT _ _ Hpw Hsp) Has).
  - fex Hq q Hq'. fdestr Hq' Hqp Hpair. unfold Pair0 in Hpair. fdestr Hpair Hpair1 Hpair2.
    fdestr Hpair1 Haq Hvq. exact (inLe HT _ _ (inLe HT _ _ Hpw Hqp) Hvq).
Qed.

(** ** Universe-side helpers *)
(** [cond] with explicit arguments (robust against the final section-variable list of AC_cond) *)
Lemma cond_w {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HC : incl Ax_cond G) (HT1 : G ⊢C rel Lform T1) U k y c Y :
  G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Lim0 k -> G ⊢C ∃ (Om0 $0 ∧ $0 ∈' k`[↑]) ->
  G ⊢C InL y -> G ⊢C c ∈' k -> G ⊢C LL c Y -> G ⊢C Sub0 y Y -> G ⊢C InLk k y.
Proof. intros H1 H2 H3 H4 H5 H6 H7 H8. eapply cond; eassumption. Qed.

(** L_κ ⊆ U *)
Lemma gu_uU {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HU : incl Ax_univ G) U k u z :
  G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Lim0 k -> G ⊢C LL k u -> G ⊢C z ∈' u -> G ⊢C z ∈' U.
Proof.
  intros HGru HK Hl Hu Hz. pose proof (LL_InLk HG HR HOm HW HU k u z Hl Hu Hz) as H.
  unfold InLk in H. fex H e He. fdestr He He1 He2. fex He2 Y HY. fdestr HY HY1 HY2.
  exact (gru_tr U Y z HGru (LL_inU HG HR HOm HW HU U k e Y HGru HK He1 HY1) HY2).
Qed.

(** a constructible subset of a member of L_κ is in L_κ (condensation) *)
Lemma gu_cond_el {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HC : incl Ax_cond G) (HT1 : G ⊢C rel Lform T1) U k w u x z :
  G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Lim0 k -> G ⊢C Om0 w -> G ⊢C w ∈' k -> G ⊢C LL k u ->
  G ⊢C x ∈' u -> G ⊢C InL z -> G ⊢C Sub0 z x -> G ⊢C InLk k z.
Proof.
  intros HGru HK Hl Hw Hwk Hu Hx Hz Hzx.
  pose proof (cond_univ _ HC) as HU. pose proof (Ax_wo_L _ HW) as HL.
  fassert Hom : (∃ (Om0 $0 ∧ $0 ∈' k`[↑])). { fexists w. fsplit; assumption. }
  pose proof (LL_InLk HG HR HOm HW HU k u x Hl Hu Hx) as H.
  unfold InLk in H. fex H e He. fdestr He He1 He2. fex He2 Y HY. fdestr HY HY1 HY2.
  pose proof (ord_el_g k e (lim_ord0 k Hl) He1) as Heo.
  pose proof (LL_trans HG HR HOm HL e Y Heo HY1) as HYt.
  fassert HxY : (Sub0 x Y). { unfold Sub0. fall t. fintro Ht. exact (trans0_use Y x t HYt HY2 Ht). }
  exact (cond_w HG HR HOm HW HC HT1 U k z e Y HGru HK Hl Hom Hz He1 HY1 (sub0_trans z x Y Hzx HxY)).
Qed.

(** W ∈ L, W ∈ U, W ⊆ L_κ  ⟹  W ∈ L_κ  (BND + COND) *)
Lemma gu_into {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HC : incl Ax_cond G) (HT1 : G ⊢C rel Lform T1) U k w u W :
  G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Lim0 k -> G ⊢C Om0 w -> G ⊢C w ∈' k -> G ⊢C LL k u ->
  G ⊢C InL W -> G ⊢C W ∈' U -> G ⊢C ∀ ($0 ∈' W`[↑] → InLk k`[↑] $0) -> G ⊢C W ∈' u.
Proof.
  intros HGru HK Hl Hw Hwk Hu HWL HWU Hel.
  pose proof (cond_univ _ HC) as HU.
  fassert Hom : (∃ (Om0 $0 ∧ $0 ∈' k`[↑])). { fexists w. fsplit; assumption. }
  pose proof (bnd HG HR HOm HW HU U k W HGru HK Hl HWU Hel) as B.
  fex B c Hc. fdestr Hc Hck HcY. fex HcY Y HY. fdestr HY HYc HWY.
  pose proof (cond_w HG HR HOm HW HC HT1 U k W c Y HGru HK Hl Hom HWL Hck HYc HWY) as HWk.
  exact (InLk_LL HG HR HOm HW HU k u W Hl Hu HWk).
Qed.

(** ** (Gru L_κ)^L *)
Lemma gru_L {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HC : incl Ax_cond G) (HT1 : G ⊢C rel Lform T1) (Hpow : G ⊢C rel Lform T_pow)
  (Hpair : G ⊢C rel Lform T_pair) (Hun : G ⊢C rel Lform T_un) U k w u :
  G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Lim0 k -> G ⊢C Om0 w -> G ⊢C w ∈' k -> G ⊢C LL k u ->
  G ⊢C InL u -> G ⊢C rel Lform (Gru u).
Proof.
  intros HGru HK Hl Hw Hwk Hu HuL.
  pose proof (cond_univ _ HC) as HU. pose proof (Ax_wo_L _ HW) as HL.
  pose proof (L_transC HG HR HOm HL) as HTL.
  pose proof (lim_ord0 k Hl) as Hko.
  pose proof (LL_trans HG HR HOm HL k u Hko Hu) as HuT.
  unfold T_pow in Hpow. unfold T_pair in Hpair. unfold T_un in Hun. cbn [rel] in Hpow, Hpair, Hun.
  pose proof HGru as HGru'. unfold Gru in HGru'. fdestr HGru' HGT HGcl.
  unfold Gru. simp. fsplit.
  { apply (iff_r _ _ _ (relL_Trans0 HTL u HuL)). exact HuT. }
  fall x. fintro HxL. fintro Hxu.
  pose proof (gu_uU HG HR HOm HW HU U k u x HGru HK Hl Hu Hxu) as HxU.
  finst HGcl x. fmp HGcl HxU. fdestr HGcl HGa12 HGa3. fdestr HGa12 HGa1 HGa2.
  fsplit; [fsplit|].
  - (* power set *)
    pose proof Hpow as Hp. finst Hp x. fmp Hp HxL. fex Hp W HW0. fdestr HW0 HWL HWdef.
    fexists W. fsplit; [exact HWL|]. fsplit; [|exact HWdef].
    fassert Hsub : (∀ ($0 ∈' W`[↑] → InL $0 ∧ Sub0 $0 x`[↑])).
    { fall z. fintro Hz. fassert HzL : (InL z). { exact (inLe HTL W z HWL Hz). }
      fsplit; [exact HzL|]. finst HWdef z. fmp HWdef HzL.
      exact (iff_l _ _ _ (relL_Sub0 HTL z x HzL HxL) (iff_l _ _ _ HWdef Hz)). }
    apply (gu_into HG HR HOm HW HC HT1 U k w u W HGru HK Hl Hw Hwk Hu HWL).
    + fex HGa1 P HP. fdestr HP HPU HPdef. apply (gru_sub HG U P W HGru HPU).
      unfold Sub0. fall z. fintro Hz. finst Hsub z. fmp Hsub Hz. finst HPdef z.
      exact (iff_r _ _ _ HPdef (CE2 Hsub)).
    + fall z. fintro Hz. finst Hsub z. fmp Hsub Hz. fdestr Hsub HzL Hzx.
      exact (gu_cond_el HG HR HOm HW HC HT1 U k w u x z HGru HK Hl Hw Hwk Hu Hxu HzL Hzx).
  - (* pairs *)
    fall y. fintro HyL. fintro Hyu.
    pose proof Hpair as Hp. finst Hp x. fmp Hp HxL. finst Hp y. fmp Hp HyL. fex Hp W HW0. fdestr HW0 HWL HWr.
    fexists W. fsplit; [exact HWL|]. fsplit; [|exact HWr].
    pose proof (iff_l _ _ _ (relL_Pair0 HTL x y W HxL HyL HWL) HWr) as HWp.
    pose proof HWp as HWp'. unfold Pair0 in HWp'. fdestr HWp' HWp1 HWp2.
    apply (gu_into HG HR HOm HW HC HT1 U k w u W HGru HK Hl Hw Hwk Hu HWL).
    + pose proof (gu_uU HG HR HOm HW HU U k u y HGru HK Hl Hu Hyu) as HyU.
      finst HGa2 y. fmp HGa2 HyU. fex HGa2 q Hq. fdestr Hq HqU Hpq.
      apply (gru_sub HG U q W HGru HqU). unfold Sub0. fall z. fintro Hz.
      finst HWp2 z. fmp HWp2 Hz.
      unfold Pair0 in Hpq. fdestr Hpq Hpq1 Hpq2. fdestr Hpq1 Hxq Hyq.
      fcases HWp2 E E.
      * exact (elem_l HG x z q (eq_sym' HG _ _ E) Hxq).
      * exact (elem_l HG y z q (eq_sym' HG _ _ E) Hyq).
    + fall z. fintro Hz. finst HWp2 z. fmp HWp2 Hz. apply (LL_InLk HG HR HOm HW HU k u z Hl Hu).
      fcases HWp2 E E.
      * exact (elem_l HG x z u (eq_sym' HG _ _ E) Hxu).
      * exact (elem_l HG y z u (eq_sym' HG _ _ E) Hyu).
  - (* unions of ranges *)
    fall f. fintro HfL. fintro Hf. fdestr Hf Hf12 Hf3. fdestr Hf12 HFr HDr.
    pose proof (iff_l _ _ _ (relL_Fun0 HTL f HfL) HFr) as HF.
    pose proof (iff_l _ _ _ (relL_Dom0 HTL f x HfL HxL) HDr) as HD.
    pose proof Hun as Hp. finst Hp f. fmp Hp HfL. fex Hp W HW0. fdestr HW0 HWL HWdef.
    fexists W. fsplit; [exact HWL|]. fsplit; [|exact HWdef].
    fassert Hval : (∀ (∀ (App0 f`[↑]`[↑] $1 $0 → $0 ∈' u`[↑]`[↑]))).
    { fall b. fall v. fintro Hab. pose proof (app_L HTL f b v HfL Hab) as Hbv. fdestr Hbv HbL HvL.
      finst Hf3 b. fmp Hf3 HbL. finst Hf3 v. fmp Hf3 HvL.
      exact (IE Hf3 (iff_r _ _ _ (relL_App0 HTL f b v HfL HbL HvL) Hab)). }
    fassert Hel : (∀ ($0 ∈' W`[↑] → ∃ ((∃ App0 f`[↑]`[↑]`[↑] $0 $1) ∧ $1 ∈' $0))).
    { fall z. fintro Hz. fassert HzL : (InL z). { exact (inLe HTL W z HWL Hz). }
      finst HWdef z. fmp HWdef HzL. pose proof (iff_l _ _ _ HWdef Hz) as T.
      fex T v Hv. fdestr Hv HvL Hv2. fdestr Hv2 Hva Hzv. fex Hva b Hb. fdestr Hb HbL Hbr.
      fexists v. fsplit; [|exact Hzv]. fexists b.
      exact (iff_l _ _ _ (relL_App0 HTL f b v HfL HbL HvL) Hbr). }
    apply (gu_into HG HR HOm HW HC HT1 U k w u W HGru HK Hl Hw Hwk Hu HWL).
    + fassert Hran : (∀ (∀ (App0 f`[↑]`[↑] $1 $0 → $0 ∈' U`[↑]`[↑]))).
      { fall b. fall v. fintro Hab. finst Hval b v. fmp Hval Hab.
        exact (gu_uU HG HR HOm HW HU U k u v HGru HK Hl Hu Hval). }
      pose proof (gru_fam U x f HGru HxU HF HD Hran) as T. fex T Sv HS. fdestr HS HSU HSdef.
      apply (gru_sub HG U Sv W HGru HSU). unfold Sub0. fall z. fintro Hz. finst Hel z. fmp Hel Hz.
      finst HSdef z. exact (iff_r _ _ _ HSdef Hel).
    + fall z. fintro Hz. finst Hel z. fmp Hel Hz. fex Hel v Hv. fdestr Hv Hva Hzv. fex Hva b Hb.
      finst Hval b v. fmp Hval Hb.
      exact (LL_InLk HG HR HOm HW HU k u z Hl Hu (trans0_use u v z HuT Hval Hzv)).
Qed.

Section GU.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HC : incl Ax_gu G) (HGU : In GU G)
  (HT1 : G ⊢C rel Lform T1) (Hpow : G ⊢C rel Lform T_pow) (Hpair : G ⊢C rel Lform T_pair)
  (Hun : G ⊢C rel Lform T_un).

Theorem guL : G ⊢C rel Lform GU.
Proof using HG HR HOm HW HC HGU HT1 Hpow Hpair Hun.
  pose proof (gu_cond _ HC) as HCo. pose proof (cond_univ _ HCo) as HU.
  pose proof (Ax_wo_L _ HW) as HL. pose proof (Ax_cl_ord _ (Ax_L_cl _ HL)) as HO.
  assert (HP : incl Ax_prim G) by (intros a []).
  assert (HGUf : G ⊢C GU) by (apply Ctx; exact HGU).
  unfold GU. cbn [rel]. fall x. fintro HxL.
  pose proof HxL as Hx'. rewrite InL_eq in Hx'. fex Hx' a Ha. fex Ha Y HY. fdestr HY HY12 HxY.
  fdestr HY12 Hao HaY.
  pose proof (om_ex_g HG HO HOm) as Tw. fex Tw w Hw.
  fassert Tp : (∃ Pair0 a`[↑] w`[↑] $0). { eapply pair0_ex; eassumption. }
  fex Tp p Hp.
  unfold GU in HGUf. finst HGUf p. fex HGUf U HU0. fdestr HU0 HpU HGru.
  pose proof Hp as Hp'. unfold Pair0 in Hp'. fdestr Hp' Hp12 Hp3. fdestr Hp12 Hap Hwp.
  pose proof (gru_tr U p a HGru HpU Hap) as HaU. pose proof (gru_tr U p w HGru HpU Hwp) as HwU.
  pose proof (kap_ex HG HR HOm HW HU U HGru) as Tk. fex Tk k Hk.
  pose proof (kap_in HG HR HOm HW HU U k a Hk HaU Hao) as Hak.
  pose proof (om_ord_g w Hw) as Hwo.
  pose proof (kap_in HG HR HOm HW HU U k w Hk HwU Hwo) as Hwk.
  pose proof (kap_lim HG HR HOm HW HU U k w HGru Hk Hw HwU) as Hl.
  pose proof (lim_ord0 k Hl) as Hko.
  pose proof (LL_ex HG HR HOm HL k Hko) as Tu. fex Tu u Hu.
  pose proof (L_LL HG HR HOm HL k u Hko Hu) as HuL.
  pose proof (LL_mono HG HR HOm HL k a u Y Hko Hak Hu HaY) as HYu. fdestr HYu HYu1 HYu2.
  fexists u. fsplit; [exact HuL|]. fsplit; [exact (sub0_use Y u x HYu2 HxY)|].
  exact (gru_L HG HR HOm HW HCo HT1 Hpow Hpair Hun U k w u HGru Hk Hl Hw Hwk Hu HuL).
Qed.

End GU.
