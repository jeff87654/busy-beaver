(** * AC_cond: condensation below a universe ordinal.

      [cond]: U a universe, κ = U ∩ On (a limit > ω), y ∈ L, y ⊆ L_c with c ∈ κ  ⟹  y ∈ L_e, e ∈ κ.

    Proof.  c' ≥ c, ω; a limit ζ ∈ κ above c' ([lim_above]); I := L_ζ ∈ U.  Base H0 maps (0, a) ↦ a for
    a ∈ L_{c'} and (0, L_{c'}) ↦ y.  [hull_ex] with c := [c_cond] (the tagged pieces of [Lform] and of
    [psi_ext]) gives X = ran H ⊆ L, and [ps_PH] + Z_refl.TV give rel Lform φ ↔ relS X φ for φ = Lform[y],
    psi_ext.  Hence X is extensional; [coll_ex] collapses it to a transitive M with P(y) = y.  y ∈ L
    holds in L ([relL_InL], from rel Lform T1), so relS X (InL y), so relS M (InL y) ([iso_relS]): there
    are a, Y' ∈ M with LL a Y', y ∈ Y' ([Sg_upS]).  succ(a) ⊆ M is covered by i ↦ P(H(i)) with
    i ∈ I ∈ U, so a ∈ κ ([surj]). *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZF Require Std_setrec.
From RegCon Require Import Rel.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L Z_sg Z_refl Z_axL Z_wo Z_ac.
From M254TG Require Import SU_gu SU_fn SU_univ.
From M254TGA Require Import AC_rec AC_univ AC_cwo AC_tup AC_hull AC_iso AC_coll.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition psi_ext : form := ∃ (¬ ($0 ∈' $1 ↔ $0 ∈' $2)).
Definition ps_cond : list (nat * form) := pcs 1 Lform ++ pcs 2 psi_ext.
Definition c_cond : form := cps ps_cond.
#[local] Set Default Proof Using "All".

Lemma fb_psi_ext : fb 2 psi_ext.
Proof. fbcomp. Qed.

Lemma ps_cond_fb K b : In (K, b) ps_cond -> fb (S K) b.
Proof.
  unfold ps_cond. intros H. apply in_app_iff in H as [H|H].
  - exact (pcs_fb Lform 1 fb_Lform K b H).
  - exact (pcs_fb psi_ext 2 fb_psi_ext K b H).
Qed.

Lemma fb_c_cond : fb 2 c_cond.
Proof. exact (fb_cps ps_cond ps_cond_fb). Qed.

(** the instances of this file *)
(** D = {(e, a) | a ∈ B}: $0 = a, $1 = q, $2 = e *)
Definition phi_D : form := OP0 $2 $0 $1.
(** base function: $0 = i, $1 = v, $2 = e, $3 = A0, $4 = y *)
Definition psi_H0 : form := ∃ (OP0 $3 $0 $1 ∧ (($0 ∈' $4 ∧ $2 ≡' $0) ∨ ((¬ ($0 ∈' $4)) ∧ $2 ≡' $5))).
(** S = {i ∈ I | ∃x (H(i) = x ∧ ∃m (P(x) = m ∧ m ∈ s))}: $0 = i, $1 = H, $2 = P, $3 = s *)
Definition phi_S : form := ∃ (App0 $2 $1 $0 ∧ ∃ (App0 $4 $1 $0 ∧ $0 ∈' $5)).
(** i ↦ P(H(i)): $0 = i, $1 = m, $2 = H, $3 = P *)
Definition psi_F : form := ∃ (App0 $3 $1 $0 ∧ App0 $4 $0 $2).

Lemma fb_D : fb 3 phi_D. Proof. fbcomp. Qed.
Lemma fb_H0 : fb 5 psi_H0. Proof. fbcomp. Qed.
Lemma fb_S : fb 4 phi_S. Proof. fbcomp. Qed.
Lemma fb_F : fb 4 psi_F. Proof. fbcomp. Qed.

Definition cond_insts : list form :=
  [forall_times 1 (ax_rep' phi_D); forall_times 3 (ax_rep' (fnR psi_H0));
   forall_times 3 (ax_sep' phi_S); forall_times 2 (ax_rep' (fnR psi_F))].

Definition Ax_cond : list form := Ax_univ ++ Ax_hull c_cond ++ Ax_coll ++ cond_insts.
Lemma Ax_cond_ok a : In a Ax_cond -> ZFR a.
Proof.
  unfold Ax_cond. intros H. apply in_app_iff in H as [H|H]; [exact (Ax_univ_ok a H)|].
  apply in_app_iff in H as [H|H]; [exact (Ax_hull_ok c_cond a fb_c_cond H)|].
  apply in_app_iff in H as [H|H]; [exact (Ax_coll_ok a H)|].
  destruct H as [<-|[<-|[<-|[<-|[]]]]].
  - apply ZFR_rep. exact fb_D.
  - apply ZFR_rep. exact (fb_fnR 3 _ fb_H0).
  - apply ZFR_sep. exact fb_S.
  - apply ZFR_rep. exact (fb_fnR 2 _ fb_F).
Qed.

Lemma cond_univ G : incl Ax_cond G -> incl Ax_univ G.
Proof. intros H a Ha. apply H. unfold Ax_cond. apply in_app_iff. now left. Qed.
Lemma cond_hull G : incl Ax_cond G -> incl (Ax_hull c_cond) G.
Proof. intros H a Ha. apply H. unfold Ax_cond. apply in_app_iff. right. apply in_app_iff. now left. Qed.
Lemma cond_coll G : incl Ax_cond G -> incl Ax_coll G.
Proof.
  intros H a Ha. apply H. unfold Ax_cond. apply in_app_iff. right. apply in_app_iff. right.
  apply in_app_iff. now left.
Qed.
Lemma cond_in G a : incl Ax_cond G -> In a cond_insts -> In a G.
Proof.
  intros H Ha. apply H. unfold Ax_cond. apply in_app_iff. right. apply in_app_iff. right.
  apply in_app_iff. now right.
Qed.
Local Ltac cin H := apply (cond_in _ _ H); cbn; tauto.

(** ** relativization helpers *)
Lemma rel_exI G (phi : form) t : G ⊢C InL t -> G ⊢C rel Lform (phi[t..]) -> G ⊢C rel Lform (∃ phi).
Proof.
  intros H1 H2. change (G ⊢C ∃ (Lform ∧ rel Lform phi)). apply (ExI t).
  change (G ⊢C Lform[t..] ∧ (rel Lform phi)[t..]). rewrite relsub. exact (CI H1 H2).
Qed.

Lemma relS_exE G Y (phi psi : form) : G ⊢C relS Y (∃ phi) ->
  (forall t, ((t ∈' Y ∧ relS Y (phi[t..])) :: G) ⊢C psi) -> G ⊢C psi.
Proof.
  intros H H'. change (G ⊢C ∃ ($0 ∈' Y`[↑] ∧ relS Y`[↑] phi)) in H. apply (ExE_named H). intros t.
  replace (($0 ∈' Y`[↑] ∧ relS Y`[↑] phi)[t..]) with (t ∈' Y ∧ relS Y (phi[t..])); [apply H'|].
  symmetry. change ((t ∈' Y`[↑]`[t..]) ∧ (relS Y`[↑] phi)[t..] = t ∈' Y ∧ relS Y phi[t..]).
  rewrite relS_subst, subst_term_shift. reflexivity.
Qed.

(** y ∈ L holds relativized to L, from (∀α ∃Y LL α Y)^L *)
Lemma relL_InL {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G) y :
  G ⊢C rel Lform Z_ac.T1 -> G ⊢C InL y -> G ⊢C rel Lform (InL y).
Proof.
  intros H1 HyL. pose proof HyL as Hy. rewrite InL_eq in Hy.
  fex Hy a Ha. fex Ha Y HY. fdestr HY HY1 HY3. fdestr HY1 HOa HLY.
  fassert HT : (TransC Lform). { eapply L_transC; eassumption. }
  fassert HaL : (InL a). { eapply L_ord; eassumption. }
  fassert HOaL : (rel Lform (Ord0 a)). { now apply Ord0_L. }
  pose proof (rel_allE _ _ a H1 HaL) as H1a. unfold Z_ac.T1 in H1a.
  replace ((Ord0 $0 → ∃ LL $1 $0)[a..]) with (Ord0 a → ∃ LL a`[↑] $0) in H1a by (simp; reflexivity).
  pose proof (rel_impE _ _ _ H1a HOaL) as H1b. clear H1a.
  rex H1b Y' HY0. fdestr HY0 HY'L HY'.
  replace ((LL a`[↑] $0)[Y'..]) with (LL a Y') in HY' by (simp; reflexivity).
  fassert HLY' : (LL a Y'). { now apply LL_up. }
  fassert HE : (Y ≡' Y'). { eapply LL_unique; eassumption. }
  fassert HxY' : (y ∈' Y'). { eapply elem_cong; [eassumption | apply eq_refl'; eassumption | exact HE | exact HY3]. }
  rewrite InL_eq. apply (rel_exI _ _ a HaL).
  replace ((∃ (Ord0 $1 ∧ LL $1 $0 ∧ y`[↑]`[↑] ∈' $0))[a..]) with (∃ (Ord0 a`[↑] ∧ LL a`[↑] $0 ∧ y`[↑] ∈' $0))
    by (simp; reflexivity).
  apply (rel_exI _ _ Y' HY'L).
  replace ((Ord0 a`[↑] ∧ LL a`[↑] $0 ∧ y`[↑] ∈' $0)[Y'..]) with (Ord0 a ∧ LL a Y' ∧ y ∈' Y')
    by (simp; reflexivity).
  match goal with |- ?G' ⊢C _ => change (G' ⊢C (rel Lform (Ord0 a) ∧ rel Lform (LL a Y')) ∧ y ∈' Y') end.
  fsplit; [fsplit|]; assumption.
Qed.

#[local] Hint Rewrite NumF_subst : fsub.

Lemma Lform_const y : Lform[fun _ => y] = Lform[y..].
Proof. apply (bounded_subst bounded_Lform). intros [|k] Hk; [reflexivity|lia]. Qed.


Lemma ps_PH_cond {G0 : list form} X :
  incl ZF0base G0 -> In ax_reg' G0 -> In ax_om' G0 -> incl Ax_L G0 ->
  G0 ⊢C OPClos X -> G0 ⊢C ∀ (Emp0 $0 → $0 ∈' X`[↑]) ->
  (forall i, G0 ⊢C ∀ (NumF i $0 → $0 ∈' X`[↑])) ->
  G0 ⊢C WClos c_cond X ->
  forall K b, In (K, b) ps_cond -> PH G0 X K b.
Proof.
  intros HG HR HOm HL Hop He Hn Hw. apply (ps_PH ps_cond X ps_cond_fb HG HR HOm HL Hop He).
  - intros i _. apply Hn.
  - exact Hw.
Qed.

Lemma Sg_mat : Sg (Ord0 $0 ∧ LL $0 $1 ∧ $2 ∈' $1).
Proof. sgcomp. Qed.

#[local] Opaque c_cond.

Lemma extX_of {G0 : list form} X : incl ZF0base G0 -> In ax_reg' G0 -> In ax_om' G0 -> incl Ax_L G0 ->
  (forall G' t, incl G0 G' -> G' ⊢C t ∈' X -> G' ⊢C InL t) ->
  (forall K b, In (K, b) (pcs 2 psi_ext) -> PH G0 X K b) -> G0 ⊢C ExtX X.
Proof.
  intros HG HR HOm HL HLsub HPE. pose proof (L_transC HG HR HOm HL) as HTL. pose proof (incl_refl G0) as HG0.
  unfold ExtX. fall a. fintro Ha. fall b. fintro Hb. fintro Hne.
    fassert Hz : (∃ (¬ ($0 ∈' a`[↑] ↔ $0 ∈' b`[↑]))).
    { fcontra Hn. fapply Hne. apply ext_rule; try assumption; unfold sub'; fall t; fintro Ht; fcontra Ht';
        fapply Hn; fexists t; fintro Hiff.
      - exact (IE Ht' (IE (CE1 Hiff) Ht)).
      - exact (IE Ht' (IE (CE2 Hiff) Ht)). }
    fex Hz t Ht.
    pose proof (HLsub _ a HG0 Ha) as HaL. pose proof (HLsub _ b HG0 Hb) as HbL.
    fassert HtL : (InL t).
    { apply (XM_rule _ (t ∈' a)).
      - fintro Hta. exact (trans_use Lform bounded_Lform _ a t HTL HaL Hta).
      - fintro Hta. apply (XM_rule _ (t ∈' b)).
        + fintro Htb. exact (trans_use Lform bounded_Lform _ b t HTL HbL Htb).
        + fintro Htb. fabsurd. fapply Ht. fsplit; fintro H'; fabsurd; [exact (IE Hta H')|exact (IE Htb H')]. }
    match goal with |- ?G' ⊢C _ => assert (Hsg : forall j, j < 2 -> G' ⊢C (a .: b .: var) j ∈' X)
      by (intros [|[|j]] Hj; cbn; [exact Ha|exact Hb|lia]) end.
    pose proof (TV X HLsub psi_ext 2 HPE _ (a .: b .: var) HG0 Hsg) as T.
    assert (E1 : rel Lform (psi_ext[a .: b .: var]) = ∃ (Lform ∧ ¬ ($0 ∈' a`[↑] ↔ $0 ∈' b`[↑]))) by reflexivity.
    assert (E2 : relS X (psi_ext[a .: b .: var]) = ∃ ($0 ∈' X`[↑] ∧ ¬ ($0 ∈' a`[↑] ↔ $0 ∈' b`[↑]))) by reflexivity.
    rewrite E1, E2 in T. apply (iff_l _ _ _ T). fexists t. fsplit; [rewrite <- InL_eq; exact HtL|exact Ht].
Qed.

(** steps 9-10: from relS M (InL y) to y ∈ L_a with a ∈ κ *)
Lemma cond_tail {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HU : incl Ax_univ G) (HinS : In (forall_times 3 (ax_sep' phi_S)) G)
  (HinF : In (forall_times 2 (ax_rep' (fnR psi_F))) G) U k I Fh X P M y :
  G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Lim0 k -> G ⊢C I ∈' U -> G ⊢C Fun0 Fh ->
  G ⊢C ∀ (∀ (App0 Fh`[↑]`[↑] $1 $0 → $1 ∈' I`[↑]`[↑])) ->
  G ⊢C ∀ ($0 ∈' X`[↑] ↔ ∃ App0 Fh`[↑]`[↑] $0 $1) ->
  G ⊢C Coll X P M -> G ⊢C Trans0 M -> G ⊢C relS M (InL y) -> G ⊢C InLk k y.
Proof.
  intros HGU Hk Hl HIU HFhf HFhI HXr HM HMt HrM.
  pose proof (Ax_wo_L _ HW) as HL. pose proof (Ax_L_cl _ HL) as HCl. pose proof (Ax_cl_ord _ HCl) as HO.
  pose proof (Ax_ord_prim _ HO) as HP.
  pose proof (kap_ord_g U k Hk) as Hko.
  rewrite InL_eq in HrM.
  apply (relS_exE _ _ _ _ HrM). intros a. ctx_push Ha. fdestr Ha HaM Ha2.
  replace ((∃ (Ord0 $1 ∧ LL $1 $0 ∧ y`[↑]`[↑] ∈' $0))[a..]) with (∃ (Ord0 a`[↑] ∧ LL a`[↑] $0 ∧ y`[↑] ∈' $0)) in Ha2
    by (simp; reflexivity).
  apply (relS_exE _ _ _ _ Ha2). intros Y'. ctx_push HY'. fdestr HY' HY'M HY'2.
  replace ((Ord0 a`[↑] ∧ LL a`[↑] $0 ∧ y`[↑] ∈' $0)[Y'..]) with (Ord0 a ∧ LL a Y' ∧ y ∈' Y') in HY'2
    by (simp; reflexivity).
  fassert HyY' : (y ∈' Y'). { exact (CE2 HY'2). }
  fhave HyM : (trans_el M Y' y HMt HY'M HyY').
  fassert Hmat : (Ord0 a ∧ LL a Y' ∧ y ∈' Y').
  { pose proof (Sg_upS (Ord0 $0 ∧ LL $0 $1 ∧ $2 ∈' $1) Sg_mat _ M (a .: Y' .: (fun _ => y)) HG HMt) as T3.
    assert (E : (Ord0 $0 ∧ LL $0 $1 ∧ $2 ∈' $1)[a .: Y' .: (fun _ => y)] = (Ord0 a ∧ LL a Y' ∧ y ∈' Y'))
      by (simp; reflexivity).
    rewrite E in T3. apply T3; [intros [|[|j]]; cbn; assumption | exact HY'2]. }
  fdestr Hmat Hmat1 Hmat2. fdestr Hmat1 Hao HLY'.
  fobtain (succ0_ex HG HP a) as s Hs. fhave Hso : (ord_succ HG a s Hao Hs).
  fassert HsM : (Sub0 s M).
  { unfold Sub0. fall m. fintro Hm. fhave C : (succ_el0 a s m Hs Hm). fcases C C1 C2.
    - exact (trans_el M a m HMt HaM C1).
    - exact (elem_l HG a m M (eq_sym' HG _ _ C2) HaM). }
  pose proof HM as HM'. unfold Coll in HM'. fdestr HM' HM3 HMv. fdestr HM3 HM2 HMr. fdestr HM2 HPf HPd.
  pose proof (sep_use _ 3 phi_S (Fh .: P .: s .: var) I HinS fb_S) as T. unfold phi_S in T. simp_in T. fex T Sx HS.
  fassert HSI : (Sub0 Sx I).
  { unfold Sub0. fall i. fintro Hi. pose proof HS as T. finst T i. exact (CE1 (iff_l _ _ _ T Hi)). }
  fhave HSU : (gru_sub HG U I Sx HGU HIU HSI).
  fassert HF : (∃ ((Fun0 $0 ∧ Dom0 $0 Sx`[↑]) ∧ ∀ (∀ (App0 $2 $1 $0 ↔ $1 ∈' Sx`[↑]`[↑]`[↑] ∧
                  psi_F[$1 .: $0 .: (fun i => ((Fh .: P .: var) i)`[↑]`[↑]`[↑])])))).
  { apply (fn_build HG HP 2 psi_F (Fh .: P .: var) Sx fb_F HinF).
    - unfold psi_F. simp. fall i. fall m. fall m'. fintro H1. fintro H2. fex H1 x Hx. fex H2 x' Hx'.
      fdestr Hx Hx1 Hx2. fdestr Hx' Hx'1 Hx'2.
      fhave E : (fun0_app_g HG Fh i x x' HFhf Hx1 Hx'1).
      frew_in E (App0 P`[↑] $0 m'`[↑]) Hx'2.
      exact (fun0_app_g HG P x m m' HPf Hx2 Hx'2).
    - unfold psi_F. simp. fall i. fintro Hi. pose proof HS as T. finst T i. fhave T2 : (iff_l _ _ _ T Hi).
      fdestr T2 T2a T2b. fex T2b x Hx. fdestr Hx Hx1 Hx2. fex Hx2 m Hm. fdestr Hm Hm1 Hm2.
      fexists m. fexists x. fsplit; assumption. }
  unfold psi_F in HF. simp_in HF. fex HF F HFx. fdestr HFx HFa HFg. fdestr HFa HFf HFd.
  fassert HFS : (∀ (∀ (App0 F`[↑]`[↑] $1 $0 → $1 ∈' Sx`[↑]`[↑]))).
  { fall i. fall m. fintro H1. exact (dom0_in_g HG F Sx i m HFd H1). }
  fassert Hcov : (∀ ($0 ∈' s`[↑] → ∃ App0 F`[↑]`[↑] $0 $1)).
  { fall m. fintro Hm. fhave HmM : (Z_L.sub_use s M m HsM Hm). pose proof HMr as T. finst T m.
    fhave T2 : (iff_l _ _ _ T HmM). fex T2 x Hx.
    fhave HxX : (dom0_in_g HG P X x m HPd Hx). pose proof HXr as T3. finst T3 x. fhave T4 : (iff_l _ _ _ T3 HxX).
    fex T4 i Hi. pose proof HFhI as T5. finst T5 i x. fmp T5 Hi.
    fassert HiS : (i ∈' Sx).
    { pose proof HS as T6. finst T6 i. apply (iff_r _ _ _ T6). fsplit; [exact T5|]. fexists x.
      fsplit; [exact Hi|]. fexists m. fsplit; [exact Hx|exact Hm]. }
    fexists i. pose proof HFg as T7. finst T7 i m. apply (iff_r _ _ _ T7). fsplit; [exact HiS|].
    fexists x. fsplit; [exact Hi|exact Hx]. }
  fhave Hsk : (surj HG HR HOm HW HU U k Sx F s HGU Hk Hl HSU HFf HFS Hso Hcov).
  fhave Hak : (ord_tr_g k a s Hko (succ_self0 a s Hs) Hsk).
  unfold InLk. fexists a. fsplit; [exact Hak|]. fexists Y'. fsplit; [exact HLY'|exact HyY'].
Qed.

Section Cond.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HW : incl Ax_wo G)
  (HC : incl Ax_cond G) (HT1 : G ⊢C rel Lform Z_ac.T1).

Theorem cond U k y c Y : G ⊢C Gru U -> G ⊢C Kap U k -> G ⊢C Lim0 k -> G ⊢C ∃ (Om0 $0 ∧ $0 ∈' k`[↑]) ->
  G ⊢C InL y -> G ⊢C c ∈' k -> G ⊢C LL c Y -> G ⊢C Sub0 y Y -> G ⊢C InLk k y.
Proof.
  intros HGU Hk Hl Hom HyL Hck HcY HyY.
  pose proof (Ax_wo_L _ HW) as HL. pose proof (Ax_L_cl _ HL) as HCl. pose proof (Ax_cl_ord _ HCl) as HO.
  pose proof (Ax_ord_prim _ HO) as HP.
  pose proof (cond_univ _ HC) as HU. pose proof (cond_hull _ HC) as HH. pose proof (cond_coll _ HC) as HCo.
  assert (HinD : In (forall_times 1 (ax_rep' phi_D)) G) by cin HC.
  assert (HinH0 : In (forall_times 3 (ax_rep' (fnR psi_H0))) G) by cin HC.
  assert (HinS : In (forall_times 3 (ax_sep' phi_S)) G) by cin HC.
  assert (HinF : In (forall_times 2 (ax_rep' (fnR psi_F))) G) by cin HC.
  clear HC.
  pose proof (kap_ord_g U k Hk) as Hko.
  fex Hom w Hw. fdestr Hw Hw1 Hw2.
  fhave Hco : (ord_el_g k c Hko Hck). fhave Hwo : (om_ord_g w Hw1).
  (* 1. c1 ⊇ c, ω in k; A0 = L_c1 *)
  fassert Hc1 : (∃ ($0 ∈' k`[↑] ∧ (Sub0 c`[↑] $0 ∧ Sub0 w`[↑] $0))).
  { fhave Tri : (ord_tri HG HR HO c w Hco Hwo). fcases Tri Ta Tc; [fcases Ta T1a Teq|].
    - fexists w. fsplit; [exact Hw2|fsplit; [exact (ord_el_sub c w Hwo T1a)|exact (sub_refl0 w)]].
    - fexists w. fsplit; [exact Hw2|fsplit; [|exact (sub_refl0 w)]]. frew Teq (Sub0 $0 w`[↑]). exact (sub_refl0 w).
    - fexists c. fsplit; [exact Hck|fsplit; [exact (sub_refl0 c)|exact (ord_el_sub w c Hco Tc)]]. }
  fex Hc1 c1 Hc1x. fdestr Hc1x Hc1k Hc1s. fdestr Hc1s Hcc1 Hwc1.
  fhave Hc1o : (ord_el_g k c1 Hko Hc1k).
  fobtain (LL_ex HG HR HOm HL c1 Hc1o) as A0 HA0.
  fhave HA0U : (LL_inU HG HR HOm HW HU U k c1 A0 HGU Hk Hc1k HA0).
  fhave HA0t : (LL_trans HG HR HOm HL c1 A0 Hc1o HA0).
  fhave HyA0 : (sub_tr0 y Y A0 HyY (LL_sub HG HR HOm HL c1 c A0 Y Hc1o Hco Hcc1 HA0 HcY)).
  assert (HnumA0 : forall n, Γ ⊢C ∀ (NumF n $0 → $0 ∈' A0`[↑])).
  { intros n. fall t. fintro Hn. exact (LL_num HG HR HOm HW HU c1 A0 w n t Hc1o HA0 Hw1 Hwc1 Hn). }
  pose proof (L_LL HG HR HOm HL c1 A0 Hc1o HA0) as HA0L.
  fhave HTL : (L_transC HG HR HOm HL).
  (* 2. zeta, I = L_zeta *)
  fobtain (lim_above HG HR HOm HW HU U k c1 w HGU Hk Hl Hw1 Hw2 Hc1k) as z Hz.
  fdestr Hz Hzk Hz2. fdestr Hz2 Hzl Hc1z.
  fhave Hzo : (lim_ord0 z Hzl).
  fobtain (LL_ex HG HR HOm HL z Hzo) as I HI.
  fhave HIU : (LL_inU HG HR HOm HW HU U k z I HGU Hk Hzk HI).
  fhave Hwz : (sub_tr0 w c1 z Hwc1 (ord_el_sub c1 z Hzo Hc1z)).
  assert (HnumI : forall n, Γ ⊢C ∀ (NumF n $0 → $0 ∈' I`[↑])).
  { intros n. fall t. fintro Hn. exact (LL_num HG HR HOm HW HU z I w n t Hzo HI Hw1 Hwz Hn). }
  fhave HAI : (LL_mono HG HR HOm HL z c1 I A0 Hzo Hc1z HI HA0). fdestr HAI HA0I HA0sI.
  fassert HIop : (∀ ($0 ∈' I`[↑] → ∀ ($0 ∈' I`[↑]`[↑] → ∀ (OP0 $2 $1 $0 → $0 ∈' I`[↑]`[↑]`[↑])))).
  { fall a. fintro Ha. fall b. fintro Hb. fall p. fintro Hp. exact (LL_op HG HR HOm HW HU z I a b p Hzl HI Ha Hb Hp). }
  (* 3. the base function H0: (e, a) ↦ a for a ∈ A0, (e, A0) ↦ y *)
  fobtain (u_emp0_ex HG HR HOm HCl) as e He.
  fassert HeA0 : (e ∈' A0). { pose proof (HnumA0 0) as T. finst T e. rewrite NumF_0 in T. exact (IE T He). }
  fobtain (succ0_ex HG HP A0) as B0 HB0.
  pose proof (rep_use _ 1 phi_D (e .: var) B0 HinD fb_D) as T.
  assert (Hmf : forall a q q', Γ ⊢C phi_D[a .: q .: (e .: var)] → phi_D[a .: q' .: (e .: var)] → q ≡' q').
  { intros a q q'. unfold phi_D. simp. fintro H1. fintro H2. exact (op0_unique_g HG e a q q' H1 H2). }
  specialize (T Hmf). clear Hmf. unfold phi_D in T. simp_in T. fex T D HD.
  fassert HH0 : (∃ ((Fun0 $0 ∧ Dom0 $0 D`[↑]) ∧ ∀ (∀ (App0 $2 $1 $0 ↔ $1 ∈' D`[↑]`[↑]`[↑] ∧
                  psi_H0[$1 .: $0 .: (fun i => ((e .: A0 .: y .: var) i)`[↑]`[↑]`[↑])])))).
  { apply (fn_build HG HP 3 psi_H0 (e .: A0 .: y .: var) D fb_H0 HinH0).
    - unfold psi_H0. simp. fall i. fall v. fall v'. fintro H1. fintro H2.
      fex H1 a Ha. fex H2 a' Ha'. fdestr Ha Ha1 Ha2. fdestr Ha' Ha'1 Ha'2.
      fhave E : (CE2 (op0_inj_g HG e a e a' i Ha1 Ha'1)).
      fcases Ha2 Hx1 Hx2; fcases Ha'2 Hy1 Hy2.
      + fdestr Hx1 Hx1a Hx1b. fdestr Hy1 Hy1a Hy1b.
        exact (eq_trans' HG _ _ _ Hx1b (eq_trans' HG _ _ _ E (eq_sym' HG _ _ Hy1b))).
      + fdestr Hx1 Hx1a Hx1b. fdestr Hy2 Hy2a Hy2b. fabsurd. exact (IE Hy2a (elem_l HG a a' A0 E Hx1a)).
      + fdestr Hx2 Hx2a Hx2b. fdestr Hy1 Hy1a Hy1b. fabsurd. exact (IE Hx2a (elem_l HG a' a A0 (eq_sym' HG _ _ E) Hy1a)).
      + fdestr Hx2 Hx2a Hx2b. fdestr Hy2 Hy2a Hy2b. exact (eq_trans' HG _ _ _ Hx2b (eq_sym' HG _ _ Hy2b)).
    - unfold psi_H0. simp. fall i. fintro Hi. pose proof HD as T. finst T i. fhave T2 : (iff_l _ _ _ T Hi).
      fex T2 a Ha. fdestr Ha Ha1 Ha2.
      apply (XM_rule _ (a ∈' A0)).
      + fintro HaA. fexists a. fexists a. fsplit; [exact Ha2|]. fleft. fsplit; [exact HaA|exact (eq_refl' HG a)].
      + fintro HaA. fexists y. fexists a. fsplit; [exact Ha2|]. fright. fsplit; [exact HaA|exact (eq_refl' HG y)]. }
  unfold psi_H0 in HH0. simp_in HH0. fex HH0 H0 HH0x. fdestr HH0x HH0a HH0g. fdestr HH0a HH0f HH0d.
  (* 4. the hull *)
  fassert Hh2 : (∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → $1 ∈' I`[↑]`[↑] ∧ Lform))).
  { fall i. fall v. fintro Hiv. pose proof HH0g as T. finst T i v. fhave T2 : (iff_l _ _ _ T Hiv). fdestr T2 HiD Hex.
    fex Hex a Ha. fdestr Ha Ha1 Ha2. fsplit.
    - pose proof HD as T3. finst T3 i. fhave T4 : (iff_l _ _ _ T3 HiD). fex T4 a' Ha'. fdestr Ha' Ha'1 Ha'2.
      fassert Ha'I : (a' ∈' I).
      { fhave C : (succ_el0 A0 B0 a' HB0 Ha'1). fcases C C1 C2.
        - exact (Z_L.sub_use A0 I a' HA0sI C1).
        - exact (elem_l HG A0 a' I (eq_sym' HG _ _ C2) HA0I). }
      pose proof HIop as T5. finst T5 e. fmp T5 (Z_L.sub_use A0 I e HA0sI HeA0). finst T5 a'. fmp T5 Ha'I.
      finst T5 i. exact (IE T5 Ha'2).
    - rewrite <- InL_eq. fcases Ha2 C1 C2.
      + fdestr C1 C1a C1b. apply (leib _ Lform _ _ HG (eq_sym' HG _ _ C1b)).
        exact (trans_use Lform bounded_Lform _ A0 a HTL HA0L C1a).
      + fdestr C2 C2a C2b. apply (leib _ Lform _ _ HG (eq_sym' HG _ _ C2b)). exact HyL. }
  fassert Hh3 : (∀ (∀ (App0 H0`[↑]`[↑] $1 $0 → ∃ (∃ (NumF 0 $1 ∧ OP0 $1 $0 $3))))).
  { fall i. fall v. fintro Hiv. pose proof HH0g as T. finst T i v. fhave T2 : (iff_l _ _ _ T Hiv). fdestr T2 HiD Hex.
    fex Hex a Ha. fdestr Ha Ha1 Ha2. fexists e. fexists a. fsplit; [try rewrite NumF_0; exact He|exact Ha1]. }
  fobtain (hull_ex HG HR HOm HW c_cond fb_c_cond HH H0 I HH0f Hh2 Hh3 HIop (HnumI 1) (HnumI 2)) as Fh HHx.
  fex HHx X HX.
  unfold HullP in HX. fdestr HX HX6 HWc. fdestr HX6 HX5 HOPc. fdestr HX5 HX4 HXL. fdestr HX4 HX3 HH0H.
  fdestr HX3 HX2 HXr. fdestr HX2 HFhf HFhI.
  (* 5. facts about X *)
  fassert HA0X : (Sub0 A0 X).
  { unfold Sub0. fall a. fintro Ha. fobtain (op0_ex HG HP e a) as i Hi.
    fassert HiD : (i ∈' D).
    { pose proof HD as T. finst T i. apply (iff_r _ _ _ T). fexists a.
      fsplit; [exact (Z_L.sub_use A0 B0 a (succ_sub0 A0 B0 HB0) Ha)|exact Hi]. }
    fassert Hia : (App0 H0 i a).
    { pose proof HH0g as T. finst T i a. apply (iff_r _ _ _ T). fsplit; [exact HiD|]. fexists a.
      fsplit; [exact Hi|]. fleft. fsplit; [exact Ha|exact (eq_refl' HG a)]. }
    pose proof HH0H as T. finst T i a. fmp T Hia. pose proof HXr as T2. finst T2 a. apply (iff_r _ _ _ T2).
    fexists i. exact T. }
  fassert HyX : (y ∈' X).
  { fobtain (op0_ex HG HP e A0) as i Hi.
    fassert HiD : (i ∈' D).
    { pose proof HD as T. finst T i. apply (iff_r _ _ _ T). fexists A0. fsplit; [exact (succ_self0 A0 B0 HB0)|exact Hi]. }
    fassert Hiy : (App0 H0 i y).
    { pose proof HH0g as T. finst T i y. apply (iff_r _ _ _ T). fsplit; [exact HiD|]. fexists A0.
      fsplit; [exact Hi|]. fright. fsplit; [fintro Hc; exact (no_self HG HR A0 Hc)|exact (eq_refl' HG y)]. }
    pose proof HH0H as T. finst T i y. fmp T Hiy. pose proof HXr as T2. finst T2 y. apply (iff_r _ _ _ T2).
    fexists i. exact T. }
  fassert HemX : (∀ (Emp0 $0 → $0 ∈' X`[↑])).
  { fall t. fintro Ht. pose proof (HnumA0 0) as T. finst T t. rewrite NumF_0 in T.
    exact (Z_L.sub_use A0 X t HA0X (IE T Ht)). }
  assert (HnumX : forall n, Γ ⊢C ∀ (NumF n $0 → $0 ∈' X`[↑])).
  { intros n. fall t. fintro Ht. pose proof (HnumA0 n) as T. finst T t. exact (Z_L.sub_use A0 X t HA0X (IE T Ht)). }
  pose proof (ps_PH_cond X HG HR HOm HL HOPc HemX HnumX HWc) as HPH.
  assert (HPL : forall K b, In (K, b) (pcs 1 Lform) -> PH Γ X K b)
    by (intros K b Hin; apply HPH; unfold ps_cond; apply in_or_app; now left).
  assert (HPE : forall K b, In (K, b) (pcs 2 psi_ext) -> PH Γ X K b)
    by (intros K b Hin; apply HPH; unfold ps_cond; apply in_or_app; now right).
  clear HPH.
  assert (HLsub : forall G' t, incl Γ G' -> G' ⊢C t ∈' X -> G' ⊢C InL t).
  { intros G' t HG' Ht. pose proof (AllE t (Weak HXL HG')) as T.
    assert (E : (($0 ∈' X`[↑] → Lform)[t..]) = (t ∈' X → InL t)) by (cbn; rewrite subst_term_shift; reflexivity).
    rewrite E in T. exact (IE T Ht). }
  pose proof (incl_refl Γ) as HG0.
  (* 6. X is extensional *)
  fhave HExt : (extX_of X HG HR HOm HL HLsub HPE).
  clear HPE.
  (* 7. collapse *)
  fobtain (coll_ex HG HR HOm HW HCo X HXL) as P HPx. fex HPx M HM.
  fhave HIso : (coll_iso HG HR HOm HW HCo X P M HM HExt).
  fhave HMt : (coll_trans HG HR HOm HW HCo X P M HM).
  fhave HPy : (coll_fix_sub HG HR HOm HW HCo X P M A0 y HM HA0t HA0X HyA0 HyX).
  (* 8. transfer y ∈ L: L -> X -> M *)
  pose proof (relL_InL HG HR HOm HL y HT1 HyL) as HrL.
  match goal with |- ?G' ⊢C _ => assert (Hsg1 : forall j, j < 1 -> G' ⊢C (y..) j ∈' X)
    by (intros [|j] Hj; cbn; [exact HyX|lia]) end.
  pose proof (TV X HLsub Lform 1 HPL _ (y..) HG0 Hsg1) as T.
  fassert HrX : (relS X (InL y)). { exact (iff_l _ _ _ T HrL). }
  clear T.
  pose proof (iso_relS Lform _ X P M (fun _ => y) (fun _ => y) HG HIso (fun _ => HyX) (fun _ => HPy)) as T.
  rewrite Lform_const in T.
  fassert HrM : (relS M (InL y)). { exact (iff_l _ _ _ T HrX). }
  clear T.
  (* 9-10. *)
  exact (cond_tail HG HR HOm HW HU HinS HinF U k I Fh X P M y HGU Hk Hl HIU HFhf HFhI HXr HM HMt HrM).
Qed.

End Cond.
