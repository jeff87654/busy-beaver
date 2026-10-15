(** * AC_univ: a Grothendieck universe U and the ordinal κ = U ∩ On, facts about L below κ.

    [Kap U k]: k = U ∩ On.  [InLk k x]: x ∈ L_e for some e ∈ k (x ∈ L_k when k is a limit).
    - [kap_lim]: κ is a limit (U ∋ ω); [kap_notin]: κ ∉ U;
    - [LL_inU]: L_c ∈ U for c ∈ κ;
    - [bnd]: a member S ∈ U with S ⊆ L_κ lies inside one L_c, c ∈ κ (least stages + Gru's ∪ran);
    - [surj]: a set function with domain inside a member of U covering an ordinal d forces d ∈ κ;
    - [lim_above]: a limit ordinal ζ with c ∈ ζ ∈ κ (ω-recursion of successor, AC_rec);
    - [LL_op], [LL_num]: L_ζ (ζ limit) is closed under ordered pairs and contains the numerals. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZF Require Std_setrec.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_wo.
From M254TG Require Import SU_gu SU_fn SU_univ.
From ZFC Require Z_axL.
From M254TGA Require Import AC_rec.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.
#[local] Set Default Proof Using "All".

Definition Kap (U k : term) : form := Ord0 k ∧ ∀ ($0 ∈' k`[↑] ↔ $0 ∈' U`[↑] ∧ Ord0 $0).
Definition InLk (k x : term) : form := ∃ ($0 ∈' k`[↑] ∧ ∃ (LL $1 $0 ∧ x`[↑]`[↑] ∈' $0)).
#[global] Arguments Kap : simpl never.
#[global] Arguments InLk : simpl never.
Lemma Kap_subst U k sg : (Kap U k)[sg] = Kap U`[sg] k`[sg].
Proof. psubst Kap. Qed.
Lemma InLk_subst k x sg : (InLk k x)[sg] = InLk k`[sg] x`[sg].
Proof. psubst InLk. Qed.
#[global] Hint Rewrite Kap_subst InLk_subst : fsub.

(** instances (extended by the prover of this file) *)
(** induction formula for L_c ∈ U: $0 = c, $1 = U *)
Definition psi_LU : form := $0 ∈' $1 → ∀ (LL $1 $0 → $0 ∈' $2).
(** a ↦ L_a: $0 = a, $1 = v *)
Definition psi_LL : form := Ord0 $0 ∧ LL $0 $1.
(** s ↦ least stage: $0 = s, $1 = e *)
Definition psi_Rho : form := Ord0 $1 ∧ Rho $0 $1.
(** S' = {i ∈ S | ∃m (F(i) = m ∧ m ∈ k)}: $0 = i, $1 = F, $2 = k *)
Definition phi_Sk : form := ∃ (App0 $2 $1 $0 ∧ $0 ∈' $3).
(** F restricted: $0 = i, $1 = m, $2 = F, $3 = k *)
Definition psi_Fk : form := App0 $2 $0 $1 ∧ $1 ∈' $3.
(** n with all values of g at n in k: $0 = n, $1 = g, $2 = k *)
Definition phi_gk : form := ∀ (App0 $2 $1 $0 → $0 ∈' $3).

Lemma fb_LU : fb 2 psi_LU. Proof. fbcomp. Qed.
Lemma fb_LLf : fb 2 psi_LL. Proof. fbcomp. Qed.
Lemma fb_Rhof : fb 2 psi_Rho. Proof. fbcomp. Qed.
Lemma fb_Sk : fb 3 phi_Sk. Proof. fbcomp. Qed.
Lemma fb_Fk : fb 4 psi_Fk. Proof. fbcomp. Qed.
Lemma fb_gk : fb 3 phi_gk. Proof. fbcomp. Qed.
Lemma fb_succG : fb 2 (Succ0 $0 $1). Proof. fbcomp. Qed.

Definition univ_insts : list form :=
  [least_inst 1 (¬ psi_LU); forall_times 0 (ax_rep' (fnR psi_LL)); forall_times 0 (ax_rep' (fnR psi_Rho));
   forall_times 2 (ax_sep' phi_Sk); forall_times 2 (ax_rep' (fnR psi_Fk)); forall_times 2 (ax_sep' phi_gk)].

Definition Ax_univ : list form := Ax_U ++ Ax_rec (Succ0 $0 $1) ++ univ_insts.
Lemma Ax_univ_ok a : In a Ax_univ -> ZFR a.
Proof.
  unfold Ax_univ. intros H. apply in_app_iff in H as [H|H]; [exact (Ax_U_ok a H)|].
  apply in_app_iff in H as [H|H]; [exact (Ax_rec_ok _ a fb_succG H)|].
  destruct H as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
  - apply ZFR_sep. cbn. split; [exact fb_LU|exact I].
  - apply ZFR_rep. exact (fb_fnR 0 _ fb_LLf).
  - apply ZFR_rep. exact (fb_fnR 0 _ fb_Rhof).
  - apply ZFR_sep. exact fb_Sk.
  - apply ZFR_rep. exact (fb_fnR 2 _ fb_Fk).
  - apply ZFR_sep. exact fb_gk.
Qed.

Lemma univ_U G : incl Ax_univ G -> incl Ax_U G.
Proof. intros H a Ha. apply H. unfold Ax_univ. apply in_app_iff. now left. Qed.
Lemma univ_rec G : incl Ax_univ G -> incl (Ax_rec (Succ0 $0 $1)) G.
Proof. intros H a Ha. apply H. unfold Ax_univ. apply in_app_iff. right. apply in_app_iff. now left. Qed.
Lemma univ_in G a : incl Ax_univ G -> In a univ_insts -> In a G.
Proof. intros H Ha. apply H. unfold Ax_univ. apply in_app_iff. right. apply in_app_iff. now right. Qed.
Ltac uin H := apply (univ_in _ _ H); cbn; tauto.

(** helper: the union of a family of ordinals is an ordinal *)
Lemma fam_ord {G} (HG : incl ZF0base G) f T :
  G ⊢C ∀ (∀ (App0 f`[↑]`[↑] $1 $0 → Ord0 $0)) ->
  G ⊢C ∀ ($0 ∈' T`[↑] ↔ ∃ ((∃ App0 f`[↑]`[↑]`[↑] $0 $1) ∧ $1 ∈' $0)) -> G ⊢C Ord0 T.
Proof.
  intros Hf HT. unfold Ord0 at 1. fsplit.
  - unfold Trans0. fall x. fintro Hx. fall y. fintro Hy. pose proof HT as T1. finst T1 x.
    fhave T2 : (iff_l _ _ _ T1 Hx). fex T2 v Hv. fdestr Hv Hv1 Hv2. fex Hv1 a Ha.
    finst Hf a v. fmp Hf Ha. finst HT y. apply (iff_r _ _ _ HT). fexists v. fsplit; [fexists a; exact Ha|].
    exact (ord_tr_g v y x Hf Hy Hv2).
  - fall x. fintro Hx. finst HT x. fhave T2 : (iff_l _ _ _ HT Hx). fex T2 v Hv. fdestr Hv Hv1 Hv2. fex Hv1 a Ha.
    finst Hf a v. fmp Hf Ha. exact (CE1 (ord_el_g v x Hf Hv2)).
Qed.

Local Ltac pre := match goal with HW0 : incl Ax_wo _ |- _ =>
  let HL := fresh "HL" in let HC := fresh "HC" in let HO := fresh "HO" in let HP := fresh "HP" in
  pose proof (Ax_wo_L _ HW0) as HL; pose proof (Ax_L_cl _ HL) as HC; pose proof (Ax_cl_ord _ HC) as HO;
  pose proof (Ax_ord_prim _ HO) as HP end.
Ltac fex_raw H x Hx := apply (ExE_named H); intros x; ctx_push Hx; try clear H.
Lemma wox {G} : In ax_reg' G -> In ax_om' G -> incl Ax_wo G -> WOx G.
Proof. intros a b c. split; [exact a|split; [exact b|exact c]]. Qed.

Lemma kap_el_g {G} U k a : G ⊢C Kap U k -> G ⊢C a ∈' k -> G ⊢C a ∈' U ∧ Ord0 a.
Proof. intros H Ha. unfold Kap in H. pose proof (CE2 H) as T. finst T a. exact (iff_l _ _ _ T Ha). Qed.
Lemma kap_in_g {G} U k a : G ⊢C Kap U k -> G ⊢C a ∈' U -> G ⊢C Ord0 a -> G ⊢C a ∈' k.
Proof.
  intros H Ha Ho. unfold Kap in H. pose proof (CE2 H) as T. finst T a. apply (iff_r _ _ _ T). fsplit; assumption.
Qed.
Lemma kap_ord_g {G} U k : G ⊢C Kap U k -> G ⊢C Ord0 k.
Proof. intros H. unfold Kap in H. exact (CE1 H). Qed.

Lemma kap_notin_g {G} (HG : incl ZF0base G) (HR : In ax_reg' G) U k : G ⊢C Kap U k -> G ⊢C k ∈' U -> G ⊢C ⊥.
Proof. intros Hk HkU. apply (no_self HG HR k). exact (kap_in_g U k k Hk HkU (kap_ord_g U k Hk)). Qed.

(** {a, b} ∈ Def(A) for a, b ∈ A *)
Lemma pair_def {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HC : incl Ax_cl G) A D a b :
  G ⊢C Def0 A D -> G ⊢C a ∈' A -> G ⊢C b ∈' A -> G ⊢C ∃ ($0 ∈' D`[↑] ∧ Pair0 a`[↑] b`[↑] $0).
Proof.
  intros HD Ha Hb.
  assert (Hsg : forall i, i < 2 -> G ⊢C (a .: b .: var) i ∈' A) by (intros [|[|i]] Hi; cbn; [exact Ha|exact Hb|lia]).
  pose proof (definable_g HG HR HOm HC 2 ($0 ≡' $1 ∨ $0 ≡' $2) (a .: b .: var) A D ltac:(fbcomp) HD Hsg) as HX.
  clear Hsg. fex_raw HX X HX0. fdestr HX0 HXD HXd. simp_in HXD.
  fexists X. fsplit; [exact HXD|]. unfold Pair0. fsplit; [fsplit|].
  - pose proof (Z_axL.def_mem ($0 ≡' $1 ∨ $0 ≡' $2) (a .: b .: var) A X a HXd) as Hm. cbn in Hm.
    apply (iff_r _ _ _ Hm). fsplit; [exact Ha|]. fleft. feq.
  - pose proof (Z_axL.def_mem ($0 ≡' $1 ∨ $0 ≡' $2) (a .: b .: var) A X b HXd) as Hm. cbn in Hm.
    apply (iff_r _ _ _ Hm). fsplit; [exact Hb|]. fright. feq.
  - fall z. fintro Hz. pose proof (Z_axL.def_mem ($0 ≡' $1 ∨ $0 ≡' $2) (a .: b .: var) A X z HXd) as Hm.
    cbn in Hm. exact (CE2 (iff_l _ _ _ Hm Hz)).
Qed.

(** OP(a, b) ∈ L_z when a, b ∈ L_e, e ∈ z, z limit *)
Lemma op_lev {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G) z Y e Ye a b p :
  G ⊢C Lim0 z -> G ⊢C LL z Y -> G ⊢C e ∈' z -> G ⊢C LL e Ye -> G ⊢C a ∈' Ye -> G ⊢C b ∈' Ye -> G ⊢C OP0 a b p ->
  G ⊢C p ∈' Y.
Proof.
  intros Hz HY He HYe Ha Hb Hp. pre.
  pose proof (lim_ord0 z Hz) as Hzo. pose proof (ord_el_g z e Hzo He) as Heo.
  fobtain (succ0_ex HG HP e) as s Hs. fhave Hso : (ord_succ HG e s Heo Hs).
  fhave Hsz : (lim_succ HG HR HO z e s Hz He Hs).
  fobtain (succ0_ex HG HP s) as s2 Hs2. fhave Hs2o : (ord_succ HG s s2 Hso Hs2).
  fhave Hs2z : (lim_succ HG HR HO z s s2 Hz Hsz Hs2).
  fobtain (LL_ex HG HR HOm HL s Hso) as Ys HYs. fobtain (LL_ex HG HR HOm HL s2 Hs2o) as Ys2 HYs2.
  fhave HD1 : (LL_succ HG HR HOm HL e s Ye Ys Heo Hs HYe HYs).
  fhave HD2 : (LL_succ HG HR HOm HL s s2 Ys Ys2 Hso Hs2 HYs HYs2).
  fobtain (pair_def HG HR HOm HC Ye Ys a a HD1 Ha Ha) as Xa HXa. fdestr HXa HXa1 HXa2.
  fobtain (pair_def HG HR HOm HC Ye Ys a b HD1 Ha Hb) as Xb HXb. fdestr HXb HXb1 HXb2.
  fobtain (pair_def HG HR HOm HC Ys Ys2 Xa Xb HD2 HXa1 HXb1) as Xp HXp. fdestr HXp HXp1 HXp2.
  fassert HSa : (Sing0 a Xa).
  { unfold Pair0 in HXa2. fdestr HXa2 H12 H3. fdestr H12 H1 H2. unfold Sing0. fsplit; [exact H1|].
    fall y. fintro Hy. finst H3 y. fmp H3 Hy. fcases H3 C1 C2; [exact C1|exact C2]. }
  fassert Hop : (OP0 a b Xp).
  { pose proof HXp2 as T. unfold Pair0 in T. fdestr T T12 T3. fdestr T12 T1 T2.
    unfold OP0. fsplit; [fsplit|].
    - fexists Xa. fsplit; [exact T1|exact HSa].
    - fexists Xb. fsplit; [exact T2|exact HXb2].
    - fall y. fintro Hy. finst T3 y. fmp T3 Hy. fcases T3 C1 C2.
      + fleft. frew C1 (Sing0 a`[↑] $0). exact HSa.
      + fright. frew C2 (Pair0 a`[↑] b`[↑] $0). exact HXb2. }
  fhave E : (u_op0_unique HG HR HOm HC a b p Xp Hp Hop).
  fhave HXpY : (Z_L.sub_use Ys2 Y Xp (LL_lim_sub HG HR HOm HL z Y s2 Ys2 Hz HY Hs2z HYs2) HXp1).
  exact (elem_l HG Xp p Y (eq_sym' HG _ _ E) HXpY).
Qed.

Lemma num_om n : forall {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HO : incl Ax_ord G) w t,
  G ⊢C Om0 w -> G ⊢C NumF n t -> G ⊢C t ∈' w.
Proof.
  induction n as [|n IH]; intros G HG HR HO w t Hw H.
  - rewrite NumF_0 in H. exact (om_emp HG HR w t Hw H).
  - rewrite NumF_S in H. fex H t' Ht'. fdestr Ht' Ht1 Ht2. rewrite NumF_subst in Ht1.
    exact (om_succ HG HR HO w t' t Hw (IH _ HG HR HO w t' Hw Ht1) Ht2).
Qed.

(** the core of [surj]: k ⊆ d is impossible *)
Lemma surj_aux {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HU : incl Ax_univ G) U k S F d : G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Lim0 k -> G ⊢C S ∈' U -> G ⊢C Fun0 F ->
  G ⊢C ∀ (∀ (App0 F`[↑]`[↑] $1 $0 → $1 ∈' S`[↑]`[↑])) ->
  G ⊢C ∀ ($0 ∈' d`[↑] → ∃ App0 F`[↑]`[↑] $0 $1) -> G ⊢C Sub0 k d -> G ⊢C ⊥.
Proof.
  intros HGU Hk Hl HS HF HFS Hcov Hkd. pre.
  assert (HinS : In (forall_times 2 (ax_sep' phi_Sk)) G) by uin HU.
  assert (HinF : In (forall_times 2 (ax_rep' (fnR psi_Fk))) G) by uin HU.
  pose proof (sep_use _ 2 phi_Sk (F .: k .: var) S HinS fb_Sk) as T. unfold phi_Sk in T. simp_in T.
  fex T S' HS'.
  fassert HS'U : (S' ∈' U).
  { apply (gru_sub HG U S S' HGU HS). unfold Sub0. fall i. fintro Hi. finst HS' i. exact (CE1 (iff_l _ _ _ HS' Hi)). }
  fassert HF' : (∃ ((Fun0 $0 ∧ Dom0 $0 S'`[↑]) ∧ ∀ (∀ (App0 $2 $1 $0 ↔ $1 ∈' S'`[↑]`[↑]`[↑] ∧
                   psi_Fk[$1 .: $0 .: (fun i => ((F .: k .: var) i)`[↑]`[↑]`[↑])])))).
  { apply (fn_build HG HP 2 psi_Fk (F .: k .: var) S' fb_Fk HinF).
    - unfold psi_Fk. simp. fall i. fall m. fall m'. fintro H1. fintro H2.
      exact (u_fun0_app HG HR HOm HC F i m m' HF (CE1 H1) (CE1 H2)).
    - unfold psi_Fk. simp. fall i. fintro Hi. finst HS' i. fhave T : (CE2 (iff_l _ _ _ HS' Hi)).
      fex T m Hm. fexists m. exact Hm. }
  unfold psi_Fk in HF'. simp_in HF'. fex HF' F' HF0. fdestr HF0 HF12 HFg. fdestr HF12 HFf HFd.
  fassert Hran : (∀ (∀ (App0 F'`[↑]`[↑] $1 $0 → $0 ∈' U`[↑]`[↑]))).
  { fall i. fall m. fintro H. finst HFg i m. fhave T : (iff_l _ _ _ HFg H). fdestr T Hi Hp. fdestr Hp Hp1 Hp2.
    exact (CE1 (kap_el_g U k m Hk Hp2)). }
  fobtain (gru_fam U S' F' HGU HS'U HFf HFd Hran) as W HW'. fdestr HW' HWU HWc.
  apply (kap_notin_g HG HR U k Hk). apply (gru_sub HG U W k HGU HWU). unfold Sub0. fall m. fintro Hm.
  unfold Lim0 in Hl. pose proof (CE2 Hl) as Hup. finst Hup m. fmp Hup Hm. fex Hup m' Hm'. fdestr Hm' Hm'1 Hm'2.
  finst Hcov m'. fmp Hcov (Z_L.sub_use k d m' Hkd Hm'1). fex Hcov i Hi.
  finst HWc m. apply (iff_r _ _ _ HWc). fexists m'. fsplit; [|exact Hm'2]. fexists i.
  finst HFg i m'. apply (iff_r _ _ _ HFg). fsplit.
  - finst HS' i. apply (iff_r _ _ _ HS'). fsplit.
    + finst HFS i m'. exact (IE HFS Hi).
    + fexists m'. fsplit; [exact Hi|exact Hm'1].
  - fsplit; [exact Hi|exact Hm'1].
Qed.

Section Univ.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HU : incl Ax_univ G).


Lemma kap_ex U : G ⊢C Gru U -> G ⊢C ∃ Kap U`[↑] $0.
Proof.
  intros H. pose proof (kappa_ex HG (univ_U _ HU) U H) as T. fex T k Hk. fexists k. unfold Kap. exact Hk.
Qed.

Lemma kap_el U k a : G ⊢C Kap U k -> G ⊢C a ∈' k -> G ⊢C a ∈' U ∧ Ord0 a.
Proof. exact (kap_el_g U k a). Qed.

Lemma kap_in U k a : G ⊢C Kap U k -> G ⊢C a ∈' U -> G ⊢C Ord0 a -> G ⊢C a ∈' k.
Proof. exact (kap_in_g U k a). Qed.

Lemma kap_lim U k w : G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Om0 w -> G ⊢C w ∈' U -> G ⊢C Lim0 k.
Proof.
  intros HGU Hk Hw HwU. pre. unfold Lim0 at 1. fsplit; [fsplit|].
  - exact (kap_ord_g U k Hk).
  - fexists w. fsplit; [|feq]. exact (kap_in_g U k w Hk HwU (om_ord_g w Hw)).
  - fall a. fintro Ha. fhave T : (kap_el_g U k a Hk Ha). fdestr T HaU Hao.
    fobtain (succ0_ex HG HP a) as s Hs. fexists s. fsplit; [|exact (succ_self0 a s Hs)].
    apply (kap_in_g U k s Hk). + exact (gru_succ HG U a s HGU Hao HaU Hs). + exact (ord_succ HG a s Hao Hs).
Qed.

Lemma kap_notin U k : G ⊢C Kap U k -> G ⊢C k ∈' U -> G ⊢C ⊥.
Proof.
  intros Hk HkU. pre. apply (no_self HG HR k). exact (kap_in_g U k k Hk HkU (kap_ord_g U k Hk)).
Qed.

Lemma LL_inU U k c Y : G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C c ∈' k -> G ⊢C LL c Y -> G ⊢C Y ∈' U.
Proof.
  intros HGU Hk Hc HY. pre.
  pose proof (kap_el_g U k c Hk Hc) as Hck. pose proof (CE1 Hck) as HcU. pose proof (CE2 Hck) as Hco. clear Hck.
  assert (Hin1 : In (least_inst 1 (¬ psi_LU)) G) by uin HU.
  assert (Hin2 : In (forall_times 0 (ax_rep' (fnR psi_LL))) G) by uin HU.
  assert (Hstep : G ⊢C ∀ (Ord0 $0 → (∀ ($0 ∈' $1 → psi_LU[up ((U .: var) >> subst_term ↑)])) → psi_LU[up (U .: var)])).
  { unfold psi_LU. simp. fall b. fintro Hb. fintro IH. fintro HbU. fall Y'. fintro HY'.
    fhave Cs : (ord_cases HG HR HO b Hb). fcases Cs C0 C3; [fcases C0 C1 C2|].
    - fhave E : (LL_zero HG HR HOm HL b Y' C1 HY'). apply (gru_sub HG U b Y' HGU HbU).
      unfold Sub0. fall x. fintro Hx. fabsurd. exact (emp_use Y' x E Hx).
    - fex C2 a Ha. fdestr Ha Hao Has.
      fhave HaU : (gru_tr U b a HGU HbU (succ_self0 a b Has)).
      fobtain (LL_ex HG HR HOm HL a Hao) as Ya HYa.
      pose proof IH as IHa. finst IHa a. fmp IHa (succ_self0 a b Has). fmp IHa HaU. finst IHa Ya. fmp IHa HYa.
      fhave HD : (LL_succ HG HR HOm HL a b Ya Y' Hao Has HYa HY').
      fobtain (gru_pow U Ya HGU IHa) as P HPP. fdestr HPP HPU HPc.
      apply (gru_sub HG U P Y' HGU HPU). unfold Sub0. fall x. fintro Hx. finst HPc x. apply (iff_r _ _ _ HPc).
      exact (def_sub HG HR HOm HC Ya Y' x HD Hx).
    - fassert HF : (∃ ((Fun0 $0 ∧ Dom0 $0 b`[↑]) ∧ ∀ (∀ (App0 $2 $1 $0 ↔ $1 ∈' b`[↑]`[↑]`[↑] ∧
                      psi_LL[$1 .: $0 .: (fun i => (var i)`[↑]`[↑]`[↑])])))).
      { apply (fn_build HG HP 0 psi_LL var b fb_LLf Hin2).
        - unfold psi_LL. simp. fall a. fall v. fall v'. fintro H1. fintro H2. fdestr H1 H1o H1L. fdestr H2 H2o H2L.
          exact (LL_unique HG HR HOm HL a v v' H1o H1L H2L).
        - unfold psi_LL. simp. fall a. fintro Ha. fhave Hao : (ord_el_g b a Hb Ha).
          fobtain (LL_ex HG HR HOm HL a Hao) as Ya HYa. fexists Ya. fsplit; assumption. }
      unfold psi_LL in HF. simp_in HF. fex HF F HF0. fdestr HF0 HF12 HFg. fdestr HF12 HFf HFd.
      fassert Hran : (∀ (∀ (App0 F`[↑]`[↑] $1 $0 → $0 ∈' U`[↑]`[↑]))).
      { fall a. fall v. fintro H. finst HFg a v. fhave T : (iff_l _ _ _ HFg H). fdestr T Ha Hp. fdestr Hp Hao HLv.
        pose proof IH as IHa. finst IHa a. fmp IHa Ha. fmp IHa (gru_tr U b a HGU HbU Ha). finst IHa v.
        exact (IE IHa HLv). }
      fobtain (gru_fam U b F HGU HbU HFf HFd Hran) as W HW'. fdestr HW' HWU HWc.
      apply (gru_sub HG U W Y' HGU HWU). unfold Sub0. fall x. fintro Hx.
      pose proof (LL_lim HG HR HOm HL b Y' C3 HY') as T. finst T x. fmp T Hx. fex T e He. fdestr He He1 He2.
      fex He2 Ye HYe. fdestr HYe HYe1 HYe2.
      finst HWc x. apply (iff_r _ _ _ HWc). fexists Ye. fsplit; [|exact HYe2]. fexists e. finst HFg e Ye.
      apply (iff_r _ _ _ HFg). fsplit; [exact He1|]. fsplit; [exact (ord_el_g b e Hb He1)|exact HYe1]. }
  pose proof (ord_ind HG HR 1 psi_LU (U .: var) c fb_LU Hin1 Hstep Hco) as T. unfold psi_LU in T. simp_in T.
  fmp T HcU. finst T Y. exact (IE T HY).
Qed.

Lemma InLk_InL k x : G ⊢C Ord0 k -> G ⊢C InLk k x -> G ⊢C InL x.
Proof.
  intros Hk H. unfold InLk in H. fex H e He. fdestr He He1 He2. fex He2 Y HY. fdestr HY HY1 HY2.
  exact (InL_intro e Y x (ord_el_g k e Hk He1) HY1 HY2).
Qed.

(** L_k = ⋃_{e ∈ k} L_e for a limit k *)
Lemma LL_InLk k u x : G ⊢C Lim0 k -> G ⊢C LL k u -> G ⊢C x ∈' u -> G ⊢C InLk k x.
Proof.
  intros Hl Hu Hx. pre. pose proof (LL_lim HG HR HOm HL k u Hl Hu) as T. finst T x. fmp T Hx. unfold InLk. exact T.
Qed.

Lemma InLk_LL k u x : G ⊢C Lim0 k -> G ⊢C LL k u -> G ⊢C InLk k x -> G ⊢C x ∈' u.
Proof.
  intros Hl Hu H. pre. unfold InLk in H. fex H e He. fdestr He He1 He2. fex He2 Y HY. fdestr HY HY1 HY2.
  exact (Z_L.sub_use Y u x (LL_lim_sub HG HR HOm HL k u e Y Hl Hu He1 HY1) HY2).
Qed.

Lemma bnd U k S : G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Lim0 k -> G ⊢C S ∈' U ->
  G ⊢C ∀ ($0 ∈' S`[↑] → InLk k`[↑] $0) -> G ⊢C ∃ ($0 ∈' k`[↑] ∧ ∃ (LL $1 $0 ∧ Sub0 S`[↑]`[↑] $0)).
Proof.
  intros HGU Hk Hl HS Hall. pre. pose proof (kap_ord_g U k Hk) as Hko.
  assert (Hin : In (forall_times 0 (ax_rep' (fnR psi_Rho))) G) by uin HU.
  fassert HF : (∃ ((Fun0 $0 ∧ Dom0 $0 S`[↑]) ∧ ∀ (∀ (App0 $2 $1 $0 ↔ $1 ∈' S`[↑]`[↑]`[↑] ∧
                  psi_Rho[$1 .: $0 .: (fun i => (var i)`[↑]`[↑]`[↑])])))).
  { apply (fn_build HG HP 0 psi_Rho var S fb_Rhof Hin).
    - unfold psi_Rho. simp. fall s. fall e. fall e'. fintro H1. fintro H2. fdestr H1 H1o H1r. fdestr H2 H2o H2r.
      exact (rho_unique HG (wox HR HOm HW) s e e' H1o H2o H1r H2r).
    - unfold psi_Rho. simp. fall s. fintro Hs. finst Hall s. fmp Hall Hs. unfold InLk in Hall.
      fex Hall e He. fdestr He He1 He2. fex He2 Ye HYe. fdestr HYe HYe1 HYe2.
      fhave Heo : (ord_el_g k e Hko He1).
      fhave T : (rho_ex HG (wox HR HOm HW) e Ye s Heo HYe1 HYe2). fex T r Hr. fdestr Hr Hr1 Hr2. fdestr Hr2 Hr4 Hr3.
      fexists r. fsplit; assumption. }
  unfold psi_Rho in HF. simp_in HF. fex HF F HF0. fdestr HF0 HF12 HFg. fdestr HF12 HFf HFd.
  fassert Hvk : (∀ (∀ (App0 F`[↑]`[↑] $1 $0 → $0 ∈' k`[↑]`[↑]))).
  { fall s. fall r. fintro H. finst HFg s r. fhave T : (iff_l _ _ _ HFg H). fdestr T Hs Hp. fdestr Hp Hro Hrr.
    finst Hall s. fmp Hall Hs. unfold InLk in Hall.
    fex Hall e He. fdestr He He1 He2. fex He2 Ye HYe. fdestr HYe HYe1 HYe2.
    fhave Heo : (ord_el_g k e Hko He1).
    fhave T : (rho_ex HG (wox HR HOm HW) e Ye s Heo HYe1 HYe2). fex T r' Hr'. fdestr Hr' Hr'1 Hr'2.
    fdestr Hr'2 Hr'e Hr'r.
    fhave E : (rho_unique HG (wox HR HOm HW) s r r' Hro Hr'1 Hrr Hr'r).
    apply (elem_l HG r' r k (eq_sym' HG _ _ E)). exact (ord_tr_g k r' e Hko Hr'e He1). }
  fassert Hran : (∀ (∀ (App0 F`[↑]`[↑] $1 $0 → $0 ∈' U`[↑]`[↑]))).
  { fall s. fall r. fintro H. finst Hvk s r. fmp Hvk H. exact (CE1 (kap_el_g U k r Hk Hvk)). }
  fobtain (gru_fam U S F HGU HS HFf HFd Hran) as Tu HT. fdestr HT HTU HTc.
  fassert HTo : (Ord0 Tu).
  { apply (fam_ord HG F Tu); [|exact HTc]. fall s. fall r. fintro H. finst Hvk s r. fmp Hvk H.
    exact (CE2 (kap_el_g U k r Hk Hvk)). }
  fhave HTk : (kap_in_g U k Tu Hk HTU HTo).
  fobtain (succ0_ex HG HP Tu) as c Hc.
  fhave Hck : (lim_succ HG HR HO k Tu c Hl HTk Hc).
  fhave Hco : (ord_succ HG Tu c HTo Hc).
  fobtain (LL_ex HG HR HOm HL c Hco) as Yc HYc.
  fexists c. fsplit; [exact Hck|]. fexists Yc. fsplit; [exact HYc|].
  unfold Sub0. fall s. fintro Hs.
  fobtain (dom0_app_g HG F S s HFd Hs) as r Hr.
  pose proof HFg as T1. finst T1 s r. fhave T2 : (iff_l _ _ _ T1 Hr). fdestr T2 Hs' Hp. fdestr Hp Hro Hrr.
  fobtain (succ0_ex HG HP r) as sr Hsr.
  fhave Hsro : (ord_succ HG r sr Hro Hsr).
  fobtain (LL_ex HG HR HOm HL sr Hsro) as Ysr HYsr.
  unfold Rho in Hrr. fdestr Hrr Hrr1 Hrr2.
  fhave Hs1 : (inl1_lev HG (wox HR HOm HW) s r sr Ysr Hro Hsr HYsr Hrr1).
  fassert Hrt : (Sub0 r Tu).
  { unfold Sub0. fall x. fintro Hx. finst HTc x. apply (iff_r _ _ _ HTc). fexists r.
    fsplit; [fexists s; exact Hr|exact Hx]. }
  fassert Hsub : (Sub0 sr c).
  { unfold Sub0. fall y. fintro Hy. fhave C : (succ_el0 r sr y Hsr Hy).
    fhave C2 : (ord_sub HG HR HO r Tu Hro HTo Hrt).
    fcases C Cy1 Cy2.
    - apply (Z_L.sub_use Tu c y (succ_sub0 Tu c Hc)). exact (Z_L.sub_use r Tu y Hrt Cy1).
    - fcases C2 D1 D2.
      + apply (Z_L.sub_use Tu c y (succ_sub0 Tu c Hc)). frew Cy2 ($0 ∈' Tu`[↑]). exact D1.
      + frew Cy2 ($0 ∈' c`[↑]). frew D2 ($0 ∈' c`[↑]). exact (succ_self0 Tu c Hc). }
  exact (Z_L.sub_use Ysr Yc s (LL_sub HG HR HOm HL c sr Yc Ysr Hco Hsro Hsub HYc HYsr) Hs1).
Qed.

Lemma surj U k S F d : G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Lim0 k -> G ⊢C S ∈' U -> G ⊢C Fun0 F ->
  G ⊢C ∀ (∀ (App0 F`[↑]`[↑] $1 $0 → $1 ∈' S`[↑]`[↑])) -> G ⊢C Ord0 d ->
  G ⊢C ∀ ($0 ∈' d`[↑] → ∃ App0 F`[↑]`[↑] $0 $1) -> G ⊢C d ∈' k.
Proof.
  intros HGU Hk Hl HS HF HFS Hd Hcov. pre.
  fhave Tri : (ord_tri HG HR HO d k Hd (kap_ord_g U k Hk)). fcases Tri T1 T3; [fcases T1 T1a T2|].
  - exact T1a.
  - fabsurd. apply (surj_aux HG HR HOm HW HU U k S F d HGU Hk Hl HS HF HFS Hcov).
    frew T2 (Sub0 k`[↑] $0). exact (sub_refl0 k).
  - fabsurd. apply (surj_aux HG HR HOm HW HU U k S F d HGU Hk Hl HS HF HFS Hcov).
    exact (ord_el_sub k d Hd T3).
Qed.

Lemma lim_above U k c w : G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Lim0 k -> G ⊢C Om0 w -> G ⊢C w ∈' k ->
  G ⊢C c ∈' k -> G ⊢C ∃ ($0 ∈' k`[↑] ∧ (Lim0 $0 ∧ c`[↑] ∈' $0)).
Proof.
  intros HGU Hk Hl Hw Hwk Hc. pre.
  pose proof (univ_rec _ HU) as HIr.
  assert (Hin : In (forall_times 2 (ax_sep' phi_gk)) G) by uin HU.
  assert (Ht : G ⊢C Std_setrec.GTot (Succ0 $0 $1)).
  { unfold Std_setrec.GTot, Std_setrec.Rel2. simp. fall x. fobtain (succ0_ex HG HP x) as y Hy. fexists y. exact Hy. }
  assert (Hu : G ⊢C Std_setrec.GFun (Succ0 $0 $1)).
  { unfold Std_setrec.GFun, Std_setrec.Rel2. simp. fall x. fall y. fall y'. fintro H1. fintro H2.
    exact (succ0_unique HG x y y' H1 H2). }
  pose proof (om_ord_g w Hw) as Hwo.
  pose proof (omrec_ex HG HR HOm HL (Succ0 $0 $1) fb_succG HIr c w Ht Hu Hwo) as Hg0.
  clear Ht Hu. fex Hg0 g Hg. fdestr Hg Hg12 Hg3. fdestr Hg12 Hgf Hgd.
  pose proof (sep_use _ 2 phi_gk (g .: k .: var) w Hin fb_gk) as T. unfold phi_gk in T. simp_in T. fex T X HX.
  fassert Hsub : (Sub0 w X).
  { apply (om_ind HG HR HO w X Hw).
    - fall e. fintro He. finst HX e. apply (iff_r _ _ _ HX). fsplit; [exact (om_emp HG HR w e Hw He)|].
      fall v. fintro Hv.
      fhave E : (omrec_zero HG HR HOm HL (Succ0 $0 $1) fb_succG HIr c g e v Hg3 Hv He).
      frew E ($0 ∈' k`[↑]). exact Hc.
    - fall n. fintro Hn. fintro HnX. fall s. fintro Hs.
      pose proof HX as HXn. finst HXn n. fhave T : (iff_l _ _ _ HXn HnX). fdestr T Hnw Hnv.
      fhave Hsw : (om_succ HG HR HO w n s Hw Hnw Hs).
      finst HX s. apply (iff_r _ _ _ HX). fsplit; [exact Hsw|]. fall v'. fintro Hv'.
      fobtain (dom0_app_g HG g w n Hgd Hnw) as u Hun. finst Hnv u. fmp Hnv Hun.
      fhave Hr : (omrec_succ HG HR HOm HL (Succ0 $0 $1) fb_succG HIr c g n s u v' Hgf Hg3 Hun Hs Hv').
      unfold Std_setrec.Rel2 in Hr. simp_in Hr.
      exact (lim_succ HG HR HO k u v' Hl Hnv Hr). }
  fassert Hvk : (∀ (∀ (App0 g`[↑]`[↑] $1 $0 → $0 ∈' k`[↑]`[↑]))).
  { fall n. fall v. fintro H. fhave Hn : (u_dom0_in HG HR HOm HC g w n v Hgd H).
    fhave HnX : (Z_L.sub_use w X n Hsub Hn). finst HX n. fhave T : (iff_l _ _ _ HX HnX). fdestr T T1 Hall.
    finst Hall v. exact (IE Hall H). }
  fassert Hran : (∀ (∀ (App0 g`[↑]`[↑] $1 $0 → $0 ∈' U`[↑]`[↑]))).
  { fall n. fall v. fintro H. finst Hvk n v. fmp Hvk H. exact (CE1 (kap_el_g U k v Hk Hvk)). }
  fhave HwU : (CE1 (kap_el_g U k w Hk Hwk)).
  fobtain (gru_fam U w g HGU HwU Hgf Hgd Hran) as z Hz'. fdestr Hz' HzU Hzc.
  fassert Hzo : (Ord0 z).
  { apply (fam_ord HG g z); [|exact Hzc]. fall n. fall v. fintro H. finst Hvk n v. fmp Hvk H.
    exact (CE2 (kap_el_g U k v Hk Hvk)). }
  fassert Hinz : (∀ (∀ (App0 g`[↑]`[↑] $1 $0 → $0 ∈' z`[↑]`[↑]))).
  { fall n. fall v. fintro H. fhave Hn : (u_dom0_in HG HR HOm HC g w n v Hgd H).
    fobtain (succ0_ex HG HP n) as s Hs. fhave Hsw : (om_succ HG HR HO w n s Hw Hn Hs).
    fobtain (dom0_app_g HG g w s Hgd Hsw) as v' Hv'.
    fhave Hr : (omrec_succ HG HR HOm HL (Succ0 $0 $1) fb_succG HIr c g n s v v' Hgf Hg3 H Hs Hv').
    unfold Std_setrec.Rel2 in Hr. simp_in Hr.
    finst Hzc v. apply (iff_r _ _ _ Hzc). fexists v'. fsplit; [fexists s; exact Hv'|exact (succ_self0 v v' Hr)]. }
  fobtain (u_emp0_ex HG HR HOm HC) as e He.
  fhave Hew : (om_emp HG HR w e Hw He). fobtain (dom0_app_g HG g w e Hgd Hew) as v0 Hv0.
  fhave E0 : (omrec_zero HG HR HOm HL (Succ0 $0 $1) fb_succG HIr c g e v0 Hg3 Hv0 He).
  pose proof Hinz as T0. finst T0 e v0. fmp T0 Hv0.
  fhave Hcz : (elem_l HG v0 c z E0 T0).
  fexists z. fsplit; [exact (kap_in_g U k z Hk HzU Hzo)|]. fsplit; [|exact Hcz].
  unfold Lim0. fsplit; [fsplit|].
  - exact Hzo.
  - fexists c. fsplit; [exact Hcz|feq].
  - fall x. fintro Hx. finst Hzc x. fhave T : (iff_l _ _ _ Hzc Hx). fex T v Hv. fdestr Hv Hv1 Hv2. fex Hv1 n Hn.
    fexists v. fsplit; [|exact Hv2]. finst Hinz n v. exact (IE Hinz Hn).
Qed.

Lemma LL_op z Y a b p : G ⊢C Lim0 z -> G ⊢C LL z Y -> G ⊢C a ∈' Y -> G ⊢C b ∈' Y -> G ⊢C OP0 a b p ->
  G ⊢C p ∈' Y.
Proof.
  intros Hz HY Ha Hb Hp. pre. pose proof (lim_ord0 z Hz) as Hzo.
  pose proof (LL_lim HG HR HOm HL z Y Hz HY) as T.
  pose proof T as Ta. finst Ta a. fmp Ta Ha. fex Ta e1 He1. fdestr He1 He1z He1b. fex He1b Y1 HY1. fdestr HY1 HY1L HaY1.
  finst T b. fmp T Hb. fex T e2 He2. fdestr He2 He2z He2b. fex He2b Y2 HY2. fdestr HY2 HY2L HbY2.
  fhave He1o : (ord_el_g z e1 Hzo He1z). fhave He2o : (ord_el_g z e2 Hzo He2z).
  fhave Tri : (ord_tri HG HR HO e1 e2 He1o He2o). fcases Tri T1 T3; [fcases T1 T1a T2|].
  - fhave M : (LL_mono HG HR HOm HL e2 e1 Y2 Y1 He2o T1a HY2L HY1L). fdestr M M1 M2.
    exact (op_lev HG HR HOm HW z Y e2 Y2 a b p Hz HY He2z HY2L (Z_L.sub_use Y1 Y2 a M2 HaY1) HbY2 Hp).
  - frew_in T2 (LL $0 Y2`[↑]) HY2L.
    fhave E : (LL_unique HG HR HOm HL e1 Y1 Y2 He1o HY1L HY2L).
    exact (op_lev HG HR HOm HW z Y e1 Y2 a b p Hz HY He1z HY2L (elem_r HG a Y1 Y2 E HaY1) HbY2 Hp).
  - fhave M : (LL_mono HG HR HOm HL e1 e2 Y1 Y2 He1o T3 HY1L HY2L). fdestr M M1 M2.
    exact (op_lev HG HR HOm HW z Y e1 Y1 a b p Hz HY He1z HY1L HaY1 (Z_L.sub_use Y2 Y1 b M2 HbY2) Hp).
Qed.

Lemma LL_num z Y w n t : G ⊢C Ord0 z -> G ⊢C LL z Y -> G ⊢C Om0 w -> G ⊢C Sub0 w z -> G ⊢C NumF n t ->
  G ⊢C t ∈' Y.
Proof.
  intros Hz HY Hw Hwz Hn. pre. pose proof (num_om n HG HR HO w t Hw Hn) as Htw.
  apply (Z_L.sub_use z Y t (CE1 (LL_ord HG HR HOm HL z Y Hz HY))). exact (Z_L.sub_use w z t Hwz Htw).
Qed.

End Univ.
