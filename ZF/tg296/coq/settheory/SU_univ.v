(** * SU_univ: Grothendieck universes and the cumulative hierarchy (inside ZF + Reg).

    For a universe U (Gru U):
    - [gru_tr], [gru_pow], [gru_sub] (subsets of members are members), [gru_fam] (∪ran f);
    - [gru_succ]: ordinals in U are closed under successor;
    - [kappa_ex]: κ := U ∩ On is an ordinal;
    - [VV_U]: V_β ∈ U for every ordinal β ∈ U (ordinal induction; V_β = ∪ran (γ ↦ 𝒫 V_γ));
    - [VVk_U]: if every element of the ordinal k lies in U, then V_k ⊆ U. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec.
From M254S Require Import S_gic.
From M254TG Require Import SU_gu SU_V SU_fn.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** ** Fixed instances *)
(** P = 𝒫(V_γ): $0 = γ, $1 = P *)
Definition psi_PV : form := Ord0 $0 ∧ ∃ (VV $1 $0 ∧ is_power $0 $2).
(** induction formula: $0 = β, $1 = U *)
Definition psi_VU : form := $0 ∈' $1 → ∀ (VV $1 $0 → $0 ∈' $2).

Lemma fb_PV : fb 2 psi_PV.
Proof. unfold psi_PV, is_power, sub'. fbcomp. Qed.
Lemma fb_VU : fb 2 psi_VU.
Proof. fbcomp. Qed.
Lemma fb_ord : fb 1 (Ord0 $0).
Proof. fbcomp. Qed.

Definition Ax_U : list form :=
  [forall_times 0 (ax_rep' (fnR psi_PV)); least_inst 1 (¬ psi_VU); forall_times 0 (ax_sep' (Ord0 $0))].
Lemma Ax_U_ok a : In a Ax_U -> ZFR a.
Proof.
  intros [<-|[<-|[<-|[]]]].
  - apply ZFR_rep. exact (fb_fnR 0 _ fb_PV).
  - apply ZFR_sep. cbn. split; [exact fb_VU|exact I].
  - apply ZFR_sep. exact fb_ord.
Qed.
Lemma in_PV G : incl Ax_U G -> In (forall_times 0 (ax_rep' (fnR psi_PV))) G.
Proof. intros H. apply H. now left. Qed.
Lemma in_VU G : incl Ax_U G -> In (least_inst 1 (¬ psi_VU)) G.
Proof. intros H. apply H. right. now left. Qed.
Lemma in_ordsep G : incl Ax_U G -> In (forall_times 0 (ax_sep' (Ord0 $0))) G.
Proof. intros H. apply H. right. right. now left. Qed.

(** ** Using Gru *)
Lemma gru_tr {G} U a b : G ⊢C Gru U -> G ⊢C a ∈' U -> G ⊢C b ∈' a -> G ⊢C b ∈' U.
Proof.
  intros H Ha Hb. unfold Gru in H. pose proof (CE1 H) as T. unfold Trans0 in T. finst T a. fmp T Ha.
  finst T b. exact (IE T Hb).
Qed.

Lemma gru_pow {G} U x : G ⊢C Gru U -> G ⊢C x ∈' U ->
  G ⊢C ∃ ($0 ∈' U`[↑] ∧ ∀ ($0 ∈' $1 ↔ Sub0 $0 x`[↑]`[↑])).
Proof.
  intros H Hx. unfold Gru in H. pose proof (CE2 H) as T. finst T x. fmp T Hx. exact (CE1 (CE1 T)).
Qed.

Lemma gru_fam {G} U x f : G ⊢C Gru U -> G ⊢C x ∈' U -> G ⊢C Fun0 f -> G ⊢C Dom0 f x ->
  G ⊢C ∀ (∀ (App0 f`[↑]`[↑] $1 $0 → $0 ∈' U`[↑]`[↑])) ->
  G ⊢C ∃ ($0 ∈' U`[↑] ∧ ∀ ($0 ∈' $1 ↔ ∃ ((∃ App0 f`[↑]`[↑]`[↑]`[↑] $0 $1) ∧ $1 ∈' $0))).
Proof.
  intros H Hx Hf Hd Hr. unfold Gru in H. pose proof (CE2 H) as T. finst T x. fmp T Hx.
  pose proof (CE2 T) as T'. finst T' f.
  fassert A : ((Fun0 f ∧ Dom0 f x) ∧ ∀ (∀ (App0 f`[↑]`[↑] $1 $0 → $0 ∈' U`[↑]`[↑]))).
  { fsplit; [fsplit|]; assumption. }
  fmp T' A. exact T'.
Qed.

Lemma gru_sub {G} (HG : incl ZF0base G) U x s : G ⊢C Gru U -> G ⊢C x ∈' U -> G ⊢C Sub0 s x -> G ⊢C s ∈' U.
Proof.
  intros H Hx Hs. fobtain (gru_pow U x H Hx) as P HP. fdestr HP HPU HPc.
  fassert HsP : (s ∈' P). { finst HPc s. exact (iff_r _ _ _ HPc Hs). }
  exact (gru_tr U P s H HPU HsP).
Qed.

(** P ∈ U whenever P = 𝒫(x), x ∈ U *)
Lemma gru_pow_in {G} (HG : incl ZF0base G) U x P : G ⊢C Gru U -> G ⊢C x ∈' U -> G ⊢C is_power x P ->
  G ⊢C P ∈' U.
Proof.
  intros H Hx HP. fobtain (gru_pow U x H Hx) as P' HP'. fdestr HP' HP'U HP'c.
  fassert E : (P' ≡' P).
  { apply (ext_rule HG); unfold sub'; fall z; fintro Hz.
    - unfold is_power in HP. finst HP z. apply (iff_r _ _ _ HP). finst HP'c z.
      pose proof (iff_l _ _ _ HP'c Hz) as T. exact T.
    - unfold is_power in HP. finst HP z. finst HP'c z. apply (iff_r _ _ _ HP'c).
      exact (iff_l _ _ _ HP Hz). }
  exact (elem_l HG P' P U E HP'U).
Qed.

(** ordinals in U are closed under successor: s = a ∪ {a} ⊆ 𝒫 a *)
Lemma gru_succ {G} (HG : incl ZF0base G) U a s : G ⊢C Gru U -> G ⊢C Ord0 a -> G ⊢C a ∈' U ->
  G ⊢C Succ0 a s -> G ⊢C s ∈' U.
Proof.
  intros H Ha HaU Hs. fobtain (gru_pow U a H HaU) as P HP. fdestr HP HPU HPc.
  apply (gru_sub HG U P s H HPU). unfold Sub0. fall z. fintro Hz. finst HPc z. apply (iff_r _ _ _ HPc).
  unfold Succ0 in Hs. fdestr Hs Hs12 Hs3. finst Hs3 z. fmp Hs3 Hz. fcases Hs3 C1 C2.
  - eapply ord_el_sub; [exact Ha|exact C1].
  - frew C2 (Sub0 $0 a`[↑]). unfold Sub0. fall y. fintro Hy. exact Hy.
Qed.

(** κ = U ∩ On is an ordinal *)
Lemma kappa_ex {G} (HG : incl ZF0base G) (HU : incl Ax_U G) U : G ⊢C Gru U ->
  G ⊢C ∃ (Ord0 $0 ∧ ∀ ($0 ∈' $1 ↔ $0 ∈' U`[↑]`[↑] ∧ Ord0 $0)).
Proof.
  intros H. pose proof (sep_use _ 0 (Ord0 $0) var U (in_ordsep _ HU) fb_ord) as T. simp_in T.
  fex T k Hk. fexists k. fsplit; [|exact Hk].
  unfold Ord0 at 1. fsplit.
  - unfold Trans0. fall a. fintro Ha. fall b. fintro Hb. pose proof Hk as Hka. finst Hka a.
    fhave T : (iff_l _ _ _ Hka Ha). fdestr T HaU Hao. finst Hk b. apply (iff_r _ _ _ Hk). fsplit.
    + exact (gru_tr U a b H HaU Hb).
    + eapply ord_el; [exact Hao|exact Hb].
  - fall a. fintro Ha. finst Hk a. fhave T : (iff_l _ _ _ Hk Ha). fdestr T HaU Hao.
    unfold Ord0 in Hao. exact (CE1 Hao).
Qed.

(** ** V_β ∈ U for ordinals β ∈ U *)
Lemma VV_U_step {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) (HU : incl Ax_U G) U :
  G ⊢C Gru U ->
  G ⊢C ∀ (Ord0 $0 → (∀ ($0 ∈' $1 → psi_VU[up ((U .: var) >> subst_term ↑)])) → psi_VU[up (U .: var)]).
Proof.
  intros HGU. pose proof (Ax_ord_prim _ (Ax_V_ord _ HV)) as HPr.
  unfold psi_VU. simp. fall b. fintro Hb. fintro IH. fintro HbU. fall Y. fintro HY.
  (* F : γ ↦ 𝒫(V_γ) on b *)
  fassert HF : (∃ ((Fun0 $0 ∧ Dom0 $0 b`[↑]) ∧
       ∀ (∀ (App0 $2 $1 $0 ↔ $1 ∈' b`[↑]`[↑]`[↑] ∧ psi_PV[$1 .: $0 .: (fun k => (var k)`[↑]`[↑]`[↑])])))).
  { apply (fn_build HG HPr 0 psi_PV var b fb_PV (in_PV _ HU)).
    - unfold psi_PV. simp. fall c. fall P. fall P'. fintro H1. fintro H2.
      fdestr H1 H1o H1e. fdestr H2 H2o H2e. fex H1e Y1 HY1. fdestr HY1 HY1v HY1p.
      fex H2e Y2 HY2. fdestr HY2 HY2v HY2p.
      fhave E : (VV_unique HG HR HV c Y1 Y2 H1o HY1v HY2v).
      apply (ext_rule HG); unfold sub'; fall z; fintro Hz.
      + unfold is_power in HY1p, HY2p. finst HY1p z. finst HY2p z. apply (iff_r _ _ _ HY2p).
        fhave S1 : (iff_l _ _ _ HY1p Hz). unfold sub' in S1 |- *. fall y. fintro Hy. finst S1 y.
        fmp S1 Hy. exact (elem_r HG y Y1 Y2 E S1).
      + unfold is_power in HY1p, HY2p. finst HY1p z. finst HY2p z. apply (iff_r _ _ _ HY1p).
        fhave S1 : (iff_l _ _ _ HY2p Hz). unfold sub' in S1 |- *. fall y. fintro Hy. finst S1 y.
        fmp S1 Hy. exact (elem_r HG y Y2 Y1 (eq_sym' HG _ _ E) S1).
    - unfold psi_PV. simp. fall c. fintro Hc.
      fhave Hco : (ord_el b c Hb Hc).
      fobtain (VV_ex HG HR HV c Hco) as Yc HYc. fobtain (pow_ex HG Yc) as P HPc.
      fexists P. fsplit; [exact Hco|]. fexists Yc. fsplit; [exact HYc|exact HPc]. }
  unfold psi_PV in HF. simp_in HF. fex HF F HF0. fdestr HF0 HF12 HFg. fdestr HF12 HFf HFd.
  (* values of F are in U *)
  fassert Hran : (∀ (∀ (App0 F`[↑]`[↑] $1 $0 → $0 ∈' U`[↑]`[↑]))).
  { fall c. fall P. fintro H. finst HFg c P. fhave T : (iff_l _ _ _ HFg H). fdestr T Hc Hp.
    fdestr Hp Hco He. fex He Yc HYc. fdestr HYc HYcv HYcp.
    pose proof IH as IHc. finst IHc c. fmp IHc Hc. fmp IHc (gru_tr U b c HGU HbU Hc). finst IHc Yc.
    fmp IHc HYcv. exact (gru_pow_in HG U Yc P HGU IHc HYcp). }
  fobtain (gru_fam U b F HGU HbU HFf HFd Hran) as W HW. fdestr HW HWU HWc.
  fassert E : (Y ≡' W).
  { apply (ext_rule HG); unfold sub'; fall z; fintro Hz.
    - fhave T : (VV_el HG HR HV b Y z Hb HY Hz). fex T c Hc. fdestr Hc Hc1 Hc2. fex Hc2 Yc HYc.
      fdestr HYc HYcv HYcz.
      fobtain (dom0_app_g HG F b c HFd Hc1) as P HPa.
      pose proof HFg as T. finst T c P. fhave T' : (iff_l _ _ _ T HPa). fdestr T' _Hc Hp.
      fdestr Hp Hco He. fex He Y' HY'. fdestr HY' HY'v HY'p.
      fhave E : (VV_unique HG HR HV c Yc Y' Hco HYcv HY'v).
      finst HWc z. apply (iff_r _ _ _ HWc). fexists P. fsplit.
      + fexists c. exact HPa.
      + unfold is_power in HY'p. finst HY'p z. apply (iff_r _ _ _ HY'p). unfold sub'. fall y. fintro Hy.
        unfold Sub0 in HYcz. finst HYcz y. fmp HYcz Hy. exact (elem_r HG y Yc Y' E HYcz).
    - finst HWc z. fhave T : (iff_l _ _ _ HWc Hz). fex T P HP. fdestr HP HP1 HP2. fex HP1 c Hc.
      pose proof HFg as T. finst T c P. fhave T' : (iff_l _ _ _ T Hc). fdestr T' Hcb Hp.
      fdestr Hp Hco He. fex He Yc HYc. fdestr HYc HYcv HYcp.
      unfold is_power in HYcp. finst HYcp z. fhave Hs : (iff_l _ _ _ HYcp HP2).
      exact (VV_intro_el HG HR HV b Y c Yc z Hb HY Hcb HYcv Hs). }
  exact (elem_l HG W Y U (eq_sym' HG _ _ E) HWU).
Qed.

Lemma VV_U {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) (HU : incl Ax_U G) U b Y :
  G ⊢C Gru U -> G ⊢C Ord0 b -> G ⊢C b ∈' U -> G ⊢C VV b Y -> G ⊢C Y ∈' U.
Proof.
  intros HGU Hb HbU HY.
  pose proof (ord_ind HG HR 1 psi_VU (U .: var) b fb_VU (in_VU _ HU) (VV_U_step HG HR HV HU U HGU) Hb) as T.
  unfold psi_VU in T. simp_in T. fmp T HbU. finst T Y. exact (IE T HY).
Qed.

(** V_k ⊆ U when every element of k is in U *)
Lemma VVk_U {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) (HU : incl Ax_U G) U k Y z :
  G ⊢C Gru U -> G ⊢C Ord0 k -> G ⊢C Sub0 k U -> G ⊢C VV k Y -> G ⊢C z ∈' Y -> G ⊢C z ∈' U.
Proof.
  intros HGU Hk HkU HY Hz.
  fhave T : (VV_el HG HR HV k Y z Hk HY Hz). fex T c Hc. fdestr Hc Hc1 Hc2. fex Hc2 Yc HYc.
  fdestr HYc HYcv HYcz.
  fhave Hco : (ord_el k c Hk Hc1).
  fhave HYcU : (VV_U HG HR HV HU U c Yc HGU Hco (sub_use' k U c HkU Hc1) HYcv).
  exact (gru_sub HG U Yc z HGU HYcU HYcz).
Qed.
