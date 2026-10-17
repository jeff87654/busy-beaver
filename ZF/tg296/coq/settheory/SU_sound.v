(** * SU_sound: SUIR is consistent relative to ZF + Reg + GU (soundness).

    Every SUIR derivation is relativized to the cumulative hierarchy [Vform] (x ∈ V_α for some α), and
    every SUIR axiom is proved relativized to V inside ZF + Reg + GU:
    - equality axioms: directly;  IR: regularity;
    - UG'_φ at p ∈ V_α: GU gives a universe U ∋ α; κ := U ∩ On; w := V_κ ∋ p.
      CP clause: x ∈ V_κ ⊆ V_β (β < κ), W := V_{β+1} ∈ V_κ.
      Family clause (f, B ∈ V_κ): δ_a := the least δ such that a has a V-witness in V_δ if it has one
      (0 otherwise); σ := ∪_{a∈B} δ_a; C := {y ∈ V_σ | ∃a∈B φ^V(a, y, f)}.  If every a ∈ B has a
      witness in V_κ, then all δ_a < κ, B ∈ U, and Gru's family clause gives σ ∈ U, i.e. σ < κ, so the
      bound U := V_σ ∈ V_κ. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From RegCon Require Import Rel.
From RegCon Require MinZF.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec.
From ZFC Require Z_axL.
From M254S Require Import S_def S_qt S_gic.
From M254TG Require Import SU_def SU_gu SU_V SU_fn SU_univ SU_gru.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

#[local] Arguments Vform : simpl never.
#[local] Arguments InV : simpl never.

Lemma Vform_up sg : Vform[up sg] = Vform.
Proof. exact (M_up' Vform bounded_Vform sg). Qed.
Lemma Vform_inst t : Vform[t..] = InV t.
Proof. reflexivity. Qed.
Lemma InV_subst t sg : (InV t)[sg] = InV t`[sg].
Proof. unfold InV. apply (M_subst bounded_Vform). Qed.
Lemma relV_subst (phi : form) sg : (rel Vform phi)[sg] = rel Vform (phi[sg]).
Proof. apply (rel_subst bounded_Vform). Qed.
#[local] Hint Rewrite Vform_up Vform_inst InV_subst relV_subst : fsub.

Ltac lift HGG' :=
  match type of HGG' with incl ?G ?G' =>
  repeat match goal with
  | H : G ⊢C _ |- _ => apply (Z_axL.wk HGG') in H
  | H : forall k : nat, k < ?m -> @prv _ _ _ class G (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k hk => Z_axL.wk HGG' (H k hk)) as H'; clear H; rename H' into H
  | H : incl ?L G |- _ => apply (fun h => incl_tran h HGG') in H
  | H : In _ G |- _ => apply HGG' in H
  end end; clear HGG'.


(** ** The class V *)
Lemma V_trans {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) z y :
  G ⊢C InV z -> G ⊢C y ∈' z -> G ⊢C InV y.
Proof.
  intros Hz Hy. rewrite InV_eq in Hz. fex Hz a Ha. fex Ha Y HY. fdestr HY HY12 HzY. fdestr HY12 Hao HYv.
  fhave T : (VV_el HG HR HV a Y z Hao HYv HzY). fex T b Hb. fdestr Hb Hb1 Hb2. fex Hb2 Yb HYb.
  fdestr HYb HYbv HzYb.
  exact (InV_intro b Yb y (ord_el a b Hao Hb1) HYbv (sub_use' z Yb y HzYb Hy)).
Qed.

(** ** Equality axioms and IR in V *)
Lemma V_eqax {G} (HG : incl ZF0base G) a : In a SUbase -> G ⊢C rel Vform a.
Proof.
  intros H. repeat (destruct H as [<-|H]; [|]); [..|destruct H]; cbn [rel ax_refl' ax_sym' ax_trans' ax_eq_elem'].
  - fall x. fintro Hx. exact (eq_refl' HG x).
  - fall x. fintro Hx. fall y. fintro Hy. fintro E. exact (eq_sym' HG _ _ E).
  - fall x. fintro Hx. fall y. fintro Hy. fall z. fintro Hz. fintro E1. fintro E2. exact (eq_trans' HG _ _ _ E1 E2).
  - fall x. fintro Hx. fall y. fintro Hy. fall x'. fintro Hx'. fall y'. fintro Hy'. fintro E1. fintro E2. fintro H.
    exact (elem_cong HG _ _ _ _ E1 E2 H).
Qed.

Lemma V_ir {G} (HG : incl ZF0base G) (HR : In ax_reg' G) : G ⊢C rel Vform ax_ir.
Proof. unfold ax_ir. cbn. fall x. fintro Hx. fintro H. exact (no_self_g HG HR x H). Qed.

(** ** UG' in V *)
(** Q(δ, a): "if a has a V-witness y with φ^V(a, y, f), one lies in V_δ"
    ($0 = δ, $1 = a, $2 = f, $(k+3) = parameter k) *)
Definition qQ (phi : form) : form :=
  (∃ (Vform ∧ rel Vform (phi[$2 .: $0 .: $3 .: (fun k => $(4 + k))]))) →
  ∃ (VV $1 $0 ∧ ∃ ($0 ∈' $1 ∧ rel Vform (phi[$3 .: $0 .: $4 .: (fun k => $(5 + k))]))).
(** δ is the least ordinal with Q(δ, a)  ($0 = a, $1 = δ, $2 = f, $(k+3) = parameter k) *)
Definition psi_lst (phi : form) : form :=
  (Ord0 $1 ∧ (qQ phi)[$1 .: $0 .: $2 .: (fun k => $(3 + k))]) ∧
  ∀ ($0 ∈' $2 → ¬ (qQ phi)[$0 .: $1 .: $3 .: (fun k => $(4 + k))]).
(** C = {y ∈ V_σ | ∃a∈B φ^V(a, y, f)}  ($0 = y, $1 = B, $2 = f, $(k+3) = parameter k) *)
Definition psi_C (phi : form) : form := ∃ ($0 ∈' $2 ∧ rel Vform (phi[$0 .: $1 .: $3 .: (fun k => $(4 + k))])).
#[global] Arguments qQ : simpl never.

Lemma fb_relV {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : forall N,
  fb N phi -> fb N (rel Vform phi).
Proof.
  induction phi as [|ff P v|ff op a IHa c IHc|ff q a IHa]; intros N H; cbn in *.
  - exact I.
  - destruct P; exact H.
  - split; [apply IHa|apply IHc]; tauto.
  - destruct q; cbn; (split; [eapply fb_mono; [exact fb_Vform|lia] | apply IHa; exact H]).
Qed.

Lemma fb_VV a Y N : idx a < N -> idx Y < N -> fb N (VV a Y).
Proof.
  intros Ha HY. replace (VV a Y) with ((VV $0 $1)[a .: Y .: var]) by (rewrite VV_subst; reflexivity).
  apply (fb_subst _ 2); [fbcomp|]. intros [|[|i]] Hi; cbn; [exact Ha|exact HY|lia].
Qed.

Ltac fbV H :=
  repeat match goal with
  | |- _ /\ _ => split
  | |- True => exact I
  | |- fb _ Vform => eapply fb_mono; [exact fb_Vform|lia]
  | |- fb _ (rel Vform _) => apply fb_relV
  | |- fb _ (VV _ _) => apply fb_VV; cbn; lia
  | |- fb _ (Ord0 _) => unfold Ord0, Trans0; cbn
  | |- fb _ (_[_]) => eapply fb_subst; [exact H|]; let i := fresh in let Hi := fresh in
                       intros [|[|[|i]]] Hi; cbn; lia
  | |- _ < _ => cbn; lia
  | |- fb _ _ => progress cbn [fb]
  end.

Lemma fb_qQ n phi : fb (S (S (S n))) phi -> fb (S (S (S n))) (qQ phi).
Proof. intros H. unfold qQ. fbV H. Qed.

Lemma fb_lst n phi : fb (S (S (S n))) phi -> fb (S (S (S n))) (psi_lst phi).
Proof. intros H. pose proof (fb_qQ n phi H) as HQ. unfold psi_lst. fbV HQ. Qed.

Lemma fb_C n phi : fb (S (S (S n))) phi -> fb (S (S (S n))) (psi_C phi).
Proof. intros H. unfold psi_C. fbV H. Qed.

Definition ug_insts (n : nat) (phi : form) : list form :=
  [least_inst (S (S n)) (qQ phi); forall_times (S n) (ax_rep' (SU_fn.fnR (psi_lst phi)));
   forall_times (S (S n)) (ax_sep' (psi_C phi))].
Lemma ug_insts_ok n phi a : fb (S (S (S n))) phi -> In a (ug_insts n phi) -> ZFR a.
Proof.
  intros H [<-|[<-|[<-|[]]]].
  - apply ZFR_sep. exact (fb_qQ n phi H).
  - apply ZFR_rep. exact (fb_fnR (S n) _ (fb_lst n phi H)).
  - apply ZFR_sep. exact (fb_C n phi H).
Qed.

Lemma in_lstQ G n phi : incl (ug_insts n phi) G -> In (least_inst (S (S n)) (qQ phi)) G.
Proof. intros H. apply H. now left. Qed.
Lemma in_lstF G n phi : incl (ug_insts n phi) G -> In (forall_times (S n) (ax_rep' (SU_fn.fnR (psi_lst phi)))) G.
Proof. intros H. apply H. right. now left. Qed.
Lemma in_lstC G n phi : incl (ug_insts n phi) G -> In (forall_times (S (S n)) (ax_sep' (psi_C phi))) G.
Proof. intros H. apply H. right. right. now left. Qed.

(** existence of the least stage *)
Lemma lst_ex {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) n phi tau f a :
  fb (S (S (S n))) phi -> incl (ug_insts n phi) G ->
  G ⊢C ∃ (psi_lst phi)[a`[↑] .: $0 .: f`[↑] .: (fun k => (tau k)`[↑])].
Proof.
  intros Hfb HI.
  fassert Hex : (∃ (Ord0 $0 ∧ (qQ phi)[$0 .: a`[↑] .: f`[↑] .: (fun k => (tau k)`[↑])])).
  { apply (XM_rule _ (∃ (Vform ∧ rel Vform (phi[a`[↑] .: $0 .: f`[↑] .: (fun k => (tau k)`[↑])])))).
    - fintro Hy. pose proof Hy as Hy'. fex Hy' y Hy0. fdestr Hy0 HyV Hphi.
      rewrite InV_eq in HyV. fex HyV b Hb. fex Hb Yb HYb. fdestr HYb HYb12 HyYb. fdestr HYb12 Hbo HYbv.
      fexists b. fsplit; [exact Hbo|]. unfold qQ. simp. fintro _H. fexists Yb. fsplit; [exact HYbv|].
      fexists y. fsplit; [exact HyYb|fconv_h Hphi].
    - fintro Hn. fobtain (emp0_ex HG) as e He. fexists e. fsplit; [exact (ord_emp_g e He)|].
      unfold qQ. simp. fintro Hy. fabsurd. apply (IE Hn). fconv_h Hy. }
  fex Hex d Hd. fdestr Hd Hdo HQ.
  fassert HQ' : ((qQ phi)[d .: (a .: f .: tau)]); [fconv_h HQ|].
  pose proof (least_ord_g HG HR (S (S n)) (qQ phi) (a .: f .: tau) d (fb_qQ n phi Hfb) (in_lstQ _ _ _ HI) Hdo HQ') as T.
  fex T dl Hdl. fexists dl. unfold psi_lst. simp. fconv_h Hdl.
Qed.

Lemma lst_unique {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) phi tau f a d d' :
  G ⊢C (psi_lst phi)[a .: d .: f .: tau] -> G ⊢C (psi_lst phi)[a .: d' .: f .: tau] -> G ⊢C d ≡' d'.
Proof.
  intros H1 H2. pose proof (Ax_V_ord _ HV) as HO. unfold psi_lst in H1, H2. simp_in H1. simp_in H2.
  fdestr H1 H1a H1c. fdestr H1a H1o H1q. fdestr H2 H2a H2c. fdestr H2a H2o H2q.
  fhave T : (ord_tri_g HG HR (in_tri1 _ HO) (in_tri2 _ HO) d d' H1o H2o). unfold Tri in T.
  fcases T Hl' H3; [fcases Hl' E1 E2|].
  - fabsurd. finst H2c d. fmp H2c E1. apply (IE H2c). fconv_h H1q.
  - exact E2.
  - fabsurd. finst H1c d'. fmp H1c H3. apply (IE H1c). fconv_h H2q.
Qed.

Lemma lst_fn {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) n phi tau f B :
  fb (S (S (S n))) phi -> incl (ug_insts n phi) G ->
  G ⊢C ∃ ((Fun0 $0 ∧ Dom0 $0 B`[↑]) ∧
          ∀ (∀ (App0 $2 $1 $0 ↔ $1 ∈' B`[↑]`[↑]`[↑] ∧
                (psi_lst phi)[$1 .: $0 .: (fun k => ((f .: tau) k)`[↑]`[↑]`[↑])]))).
Proof.
  intros Hfb HI. apply (fn_build HG HP0 (S n) (psi_lst phi) (f .: tau) B (fb_lst n phi Hfb) (in_lstF _ _ _ HI)).
  - fall a. fall d. fall d'. fintro H1. fintro H2.
    fassert H1' : ((psi_lst phi)[a .: d .: f .: tau]). { unfold psi_lst in H1 |- *. simp_in H1. simp. fconv_h H1. }
    fassert H2' : ((psi_lst phi)[a .: d' .: f .: tau]). { unfold psi_lst in H2 |- *. simp_in H2. simp. fconv_h H2. }
    exact (lst_unique HG HR HV phi tau f a d d' H1' H2').
  - fall a. fintro Ha. pose proof (lst_ex HG HR HV n phi tau f a Hfb HI) as T. fex T d Hd.
    fexists d. fconv_h Hd.
Qed.

(** using / building instances of psi_lst and qQ *)
Lemma lst_use {G} phi tau f a d : G ⊢C (psi_lst phi)[a .: d .: f .: tau] ->
  G ⊢C (Ord0 d ∧ (qQ phi)[d .: a .: f .: tau]) ∧
       ∀ ($0 ∈' d`[↑] → ¬ (qQ phi)[$0 .: a`[↑] .: f`[↑] .: (fun k => (tau k)`[↑])]).
Proof. intros H. unfold psi_lst in H. simp_in H. fconv_h H. Qed.

Lemma qQ_use {G} phi tau f a d y : G ⊢C (qQ phi)[d .: a .: f .: tau] -> G ⊢C InV y ->
  G ⊢C rel Vform (phi[a .: y .: f .: tau]) ->
  G ⊢C ∃ (VV d`[↑] $0 ∧ ∃ ($0 ∈' $1 ∧ rel Vform (phi[a`[↑]`[↑] .: $0 .: f`[↑]`[↑] .: (fun k => (tau k)`[↑]`[↑])]))).
Proof.
  intros H Hy Hp. unfold qQ in H. simp_in H.
  fassert A : (∃ (Vform ∧ rel Vform (phi[$2 .: $0 .: $3 .: (fun k => $(4 + k))][up (d .: a .: f .: tau)]))).
  { fexists y. fsplit; [exact Hy|fconv_h Hp]. }
  fmp H A. fconv_h H.
Qed.

Lemma qQ_intro {G} phi tau f a d Y y : G ⊢C VV d Y -> G ⊢C y ∈' Y -> G ⊢C rel Vform (phi[a .: y .: f .: tau]) ->
  G ⊢C (qQ phi)[d .: a .: f .: tau].
Proof.
  intros HY Hy Hp. unfold qQ. simp. fintro _H. fexists Y. fsplit; [exact HY|]. fexists y. fsplit; [exact Hy|fconv_h Hp].
Qed.

(** ∪ ran F *)
Lemma ran_union {G} (HG : incl ZF0base G) (HA : incl Ax_gru G) F :
  G ⊢C ∃ ∀ ($0 ∈' $1 ↔ ∃ ((∃ App0 F`[↑]`[↑]`[↑]`[↑] $0 $1) ∧ $1 ∈' $0)).
Proof.
  fobtain (union0_ex HG HP0 F) as U1 HU1. fobtain (union0_ex HG HP0 U1) as U2 HU2.
  fobtain (union0_ex HG HP0 U2) as U3 HU3.
  pose proof (sep_use _ 1 psi_ur (F .: var) U3 (HA _ (or_introl eq_refl)) fb_ur) as T.
  unfold psi_ur in T. simp_in T. fex T X HX. fexists X. fall z. fsplit.
  - fintro Hz. finst HX z. exact (CE2 (iff_l _ _ _ HX Hz)).
  - fintro Hz. finst HX z. apply (iff_r _ _ _ HX). fsplit; [|exact Hz].
    fex Hz v Hv. fdestr Hv Hv1 Hzv. fex Hv1 a Ha. pose proof Ha as Ha'. unfold App0 in Ha'.
    fex Ha' q Hq. fdestr Hq Hq1 Hq2. pose proof (op0_val' a v q Hq2) as T. fex T r Hr. fdestr Hr Hr1 Hr2.
    apply (union_in' U2 U3 v z HU3); [|exact Hzv].
    apply (union_in' U1 U2 r v HU2); [|exact Hr2]. exact (union_in' F U1 q r HU1 Hq1 Hr1).
Qed.

Lemma sigma_ord {G} (HG : incl ZF0base G) F sg :
  G ⊢C ∀ (∀ (App0 F`[↑]`[↑] $1 $0 → Ord0 $0)) ->
  G ⊢C ∀ ($0 ∈' sg`[↑] ↔ ∃ ((∃ App0 F`[↑]`[↑]`[↑] $0 $1) ∧ $1 ∈' $0)) -> G ⊢C Ord0 sg.
Proof.
  intros Ho Hs. unfold Ord0 at 1. fsplit.
  - unfold Trans0. fall z. fintro Hz. fall y. fintro Hy. pose proof Hs as T. finst T z.
    fhave T' : (iff_l _ _ _ T Hz). fex T' v Hv. fdestr Hv Hv1 Hzv. fex Hv1 a Ha.
    pose proof Ho as T2. finst T2 a v. fmp T2 Ha.
    finst Hs y. apply (iff_r _ _ _ Hs). fexists v. fsplit; [fexists a; exact Ha|].
    exact (ord_tr_g v y z T2 Hy Hzv).
  - fall z. fintro Hz. finst Hs z. fhave T' : (iff_l _ _ _ Hs Hz). fex T' v Hv. fdestr Hv Hv1 Hzv.
    fex Hv1 a Ha. pose proof Ho as T2. finst T2 a v. fmp T2 Ha.
    fhave Hzo : (ord_el_g v z T2 Hzv). unfold Ord0 in Hzo. exact (CE1 Hzo).
Qed.

Lemma ug_core {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HGU : In GU G) (HV : incl Ax_V G)
  (HU : incl Ax_U G) (HA : incl Ax_gru G) n phi tau :
  fb (S (S (S n))) phi -> incl (ug_insts n phi) G -> G ⊢C rel Vform ((ug phi)[tau]).
Proof.
  intros Hfb HI. unfold ug. cbn [subst_form rel].
  fall p. fintro Hp. rewrite InV_eq in Hp. fex Hp al Hal. fex Hal Yal HYal. fdestr HYal HYal12 HpY.
  fdestr HYal12 Halo HYalv.
  fassert Hgu : GU. { apply Ctx. exact HGU. }
  unfold GU in Hgu. finst Hgu al. fex Hgu U HU0. fdestr HU0 HalU HGru.
  fobtain (kappa_ex HG HU U HGru) as k Hk. fdestr Hk Hko Hkc.
  fassert Hkin : (∀ ($0 ∈' U`[↑] → Ord0 $0 → $0 ∈' k`[↑])).
  { fall a. fintro Ha. fintro Hao. pose proof Hkc as T. finst T a. apply (iff_r _ _ _ T). fsplit; assumption. }
  fassert Hkout : (Sub0 k U).
  { unfold Sub0. fall a. fintro Ha. pose proof Hkc as T. finst T a. exact (CE1 (iff_l _ _ _ T Ha)). }
  fassert Halk : (al ∈' k). { pose proof Hkin as K. finst K al. fmp K HalU. exact (IE K Halo). }
  fobtain (VV_ex HG HR HV k Hko) as w Hw.
  fexists w. fsplit; [exact (InV_VV HG HR HV k w Hko Hw)|].
  fsplit; [fsplit|].
  - (* p ∈ w *)
    exact (sub_use' Yal w p (VV_sub HG HR HV k al w Yal Hko Halo (ord_el_sub_g al k Hko Halk) Hw HYalv) HpY).
  - (* CP clause *)
    fall x. fintro HxV. fintro Hxw.
    fhave T : (VV_el HG HR HV k w x Hko Hw Hxw). fex T b Hb. fdestr Hb Hbk Hb2. fex Hb2 Yb HYb.
    fdestr HYb HYbv HxYb.
    fhave Hbo : (ord_el_g k b Hko Hbk).
    fsplit.
    + fall z. fintro HzV. fintro Hzx.
      exact (sub_use' Yb w z (VV_sub HG HR HV k b w Yb Hko Hbo (ord_el_sub_g b k Hko Hbk) Hw HYbv)
               (sub_use' x Yb z HxYb Hzx)).
    + fobtain (v_succ0_ex HG HR HV b) as s Hs. fhave Hso : (v_ord_succ HG HR HV b s Hbo Hs).
      fhave HsU : (gru_succ HG U b s HGru Hbo (sub_use' k U b Hkout Hbk) Hs).
      fassert Hsk : (s ∈' k). { pose proof Hkin as K. finst K s. fmp K HsU. exact (IE K Hso). }
      fobtain (VV_ex HG HR HV s Hso) as Ws HWs.
      fexists Ws. fsplit; [exact (InV_VV HG HR HV s Ws Hso HWs)|].
      fsplit; [exact (VV_in HG HR HV k s w Ws Hko Hsk Hw HWs)|].
      fall z. fintro HzV. fintro Hzx.
      apply (VV_succ HG HR HV b s Yb Ws z Hbo Hs HYbv HWs). unfold Sub0. fall y. fintro Hy.
      finst Hzx y. fmp Hzx (V_trans HG HR HV z y HzV Hy). fmp Hzx Hy. exact (sub_use' x Yb y HxYb Hzx).
  - (* family clause *)
    fall f. fintro HfV. fall B. fintro HBV. fintro HBw.
    fobtain (lst_fn HG HR HV n phi tau f B Hfb HI) as F HF. fdestr HF HF12 HFg. fdestr HF12 HFf HFd.
    fassert Happ : (∀ (∀ (App0 F`[↑]`[↑] $1 $0 →
        ($1 ∈' B`[↑]`[↑] ∧ Ord0 $0) ∧ (qQ phi)[$0 .: $1 .: f`[↑]`[↑] .: (fun k => (tau k)`[↑]`[↑])]))).
    { fall a. fall d. fintro Had. pose proof HFg as T. finst T a d. fhave T' : (iff_l _ _ _ T Had).
      fdestr T' Ta Tl.
      fassert Tl' : ((psi_lst phi)[a .: d .: f .: tau]). { unfold psi_lst in Tl |- *. simp_in Tl. simp. fconv_h Tl. }
      fhave L : (lst_use phi tau f a d Tl'). fdestr L L1 _L2. fdestr L1 Ldo LQ.
      fsplit; [fsplit; assumption|fconv_h LQ]. }
    fassert Hmin : (∀ (∀ (App0 F`[↑]`[↑] $1 $0 →
        ∀ ($0 ∈' $1 → ¬ (qQ phi)[$0 .: $2 .: f`[↑]`[↑]`[↑] .: (fun k => (tau k)`[↑]`[↑]`[↑])])))).
    { fall a. fall d. fintro Had. pose proof HFg as T. finst T a d. fhave T' : (iff_l _ _ _ T Had).
      fdestr T' Ta Tl.
      fassert Tl' : ((psi_lst phi)[a .: d .: f .: tau]). { unfold psi_lst in Tl |- *. simp_in Tl. simp. fconv_h Tl. }
      fhave L : (lst_use phi tau f a d Tl'). fdestr L _L1 L2. fconv_h L2. }
    fobtain (ran_union HG HA F) as sg Hsg.
    fassert Hdo : (∀ (∀ (App0 F`[↑]`[↑] $1 $0 → Ord0 $0))).
    { fall a. fall d. fintro Had. pose proof Happ as T. finst T a d. fmp T Had. exact (CE2 (CE1 T)). }
    fhave Hsgo : (sigma_ord HG F sg Hdo Hsg).
    fassert Hdsg : (∀ (∀ (App0 F`[↑]`[↑] $1 $0 → Sub0 $0 sg`[↑]`[↑]))).
    { fall a. fall d. fintro Had. unfold Sub0. fall z. fintro Hz. pose proof Hsg as S1. finst S1 z.
      apply (iff_r _ _ _ S1). fexists d. fsplit; [fexists a; exact Had|exact Hz]. }
    fobtain (VV_ex HG HR HV sg Hsgo) as Ysg HYsg.
    pose proof (sep_use _ (S (S n)) (psi_C phi) (B .: f .: tau) Ysg (in_lstC _ _ _ HI) (fb_C n phi Hfb)) as T.
    unfold psi_C in T. simp_in T. fex T C HCc.
    fexists C. fsplit.
    { fobtain (v_succ0_ex HG HR HV sg) as s Hs. fhave Hso : (v_ord_succ HG HR HV sg s Hsgo Hs).
      fobtain (VV_ex HG HR HV s Hso) as Ys HYs.
      apply (InV_intro s Ys C Hso HYs). apply (VV_succ HG HR HV sg s Ysg Ys C Hsgo Hs HYsg HYs).
      unfold Sub0. fall y. fintro Hy. pose proof HCc as T. finst T y. exact (CE1 (iff_l _ _ _ T Hy)). }
    fsplit; [fsplit|].
    + (* cov *)
      fall a. fintro HaV. fintro HaB. fall y. fintro HyV. fintro Hphi.
      fobtain (dom0_app_g HG F B a HFd HaB) as d Had.
      pose proof Happ as T. finst T a d. fmp T Had. fdestr T T1 TQ. fdestr T1 _Ta Tdo.
      fassert TQ' : ((qQ phi)[d .: a .: f .: tau]); [fconv_h TQ|].
      fassert Hphi' : (rel Vform (phi[a .: y .: f .: tau])); [fconv_h Hphi|].
      fobtain (qQ_use phi tau f a d y TQ' HyV Hphi') as Y HY. fdestr HY HYv HY2. fex HY2 y' Hy'.
      fdestr Hy' Hy'Y Hphi''.
      fassert HYsub : (Sub0 Y Ysg).
      { apply (VV_sub HG HR HV sg d Ysg Y Hsgo Tdo); [|exact HYsg|exact HYv].
        pose proof Hdsg as T. finst T a d. exact (IE T Had). }
      fexists y'. fsplit; [exact (InV_intro d Y y' Tdo HYv Hy'Y)|]. fsplit; [fconv_h Hphi''|].
      pose proof HCc as T. finst T y'. apply (iff_r _ _ _ T). fsplit; [exact (sub_use' Y Ysg y' HYsub Hy'Y)|].
      fexists a. fsplit; [exact HaB|fconv_h Hphi''].
    + (* nx *)
      fall y. fintro HyV. fintro HyC. pose proof HCc as T. finst T y. fhave T' : (iff_l _ _ _ T HyC).
      fdestr T' _T1 T2. fex T2 a Ha. fdestr Ha HaB Hphi.
      fexists a. fsplit; [exact (V_trans HG HR HV B a HBV HaB)|fconv_h Hphi].
    + (* the bound, when all witnesses can be found in w *)
      fintro Htot.
      fassert HBU : (B ∈' U). { exact (VVk_U HG HR HV HU U k w B HGru Hko Hkout Hw HBw). }
      fassert Hran : (∀ (∀ (App0 F`[↑]`[↑] $1 $0 → $0 ∈' U`[↑]`[↑]))).
      { fall a. fall d. fintro Had.
        pose proof Happ as T. finst T a d. fmp T Had. fdestr T T1 TQ. fdestr T1 HaB Hdo'.
        pose proof Htot as T. finst T a. fmp T (V_trans HG HR HV B a HBV HaB). fmp T HaB.
        fex T y Hy. fdestr Hy HyV Hy2. fdestr Hy2 Hyw Hphi.
        fhave T2 : (VV_el HG HR HV k w y Hko Hw Hyw). fex T2 b Hb. fdestr Hb Hbk Hb2. fex Hb2 Yb HYb.
        fdestr HYb HYbv HyYb.
        fhave Hbo : (ord_el_g k b Hko Hbk).
        fobtain (v_succ0_ex HG HR HV b) as s Hs. fhave Hso : (v_ord_succ HG HR HV b s Hbo Hs).
        fhave HsU : (gru_succ HG U b s HGru Hbo (sub_use' k U b Hkout Hbk) Hs).
        fassert Hsk : (s ∈' k). { pose proof Hkin as K. finst K s. fmp K HsU. exact (IE K Hso). }
        fobtain (VV_ex HG HR HV s Hso) as Ys HYs.
        fassert HQs : ((qQ phi)[s .: a .: f .: tau]).
        { apply (qQ_intro phi tau f a s Ys y HYs (VV_succ HG HR HV b s Yb Ys y Hbo Hs HYbv HYs HyYb)).
          fconv_h Hphi. }
        fhave T3 : (ord_tri_g HG HR (in_tri1 _ (Ax_V_ord _ HV)) (in_tri2 _ (Ax_V_ord _ HV)) d s Hdo' Hso).
        unfold Tri in T3. fassert Hdk : (d ∈' k).
        { fcases T3 T4 T5; [fcases T4 E1 E2|].
          - exact (ord_tr_g k d s Hko E1 Hsk).
          - frew E2 ($0 ∈' k`[↑]). exact Hsk.
          - fabsurd. pose proof Hmin as M. finst M a d. fmp M Had. finst M s. fmp M T5. apply (IE M).
            fconv_h HQs. }
        exact (sub_use' k U d Hkout Hdk). }
      fobtain (gru_fam U B F HGru HBU HFf HFd Hran) as W HW. fdestr HW HWU HWc.
      fassert E : (sg ≡' W).
      { apply (ext_rule HG); unfold sub'; fall z; fintro Hz.
        - pose proof Hsg as T. finst T z. pose proof HWc as T'. finst T' z. apply (iff_r _ _ _ T').
          exact (iff_l _ _ _ T Hz).
        - pose proof Hsg as T. finst T z. pose proof HWc as T'. finst T' z. apply (iff_r _ _ _ T).
          exact (iff_l _ _ _ T' Hz). }
      fassert Hsgk : (sg ∈' k).
      { pose proof Hkin as K. finst K sg. fmp K (elem_l HG W sg U (eq_sym' HG _ _ E) HWU). exact (IE K Hsgo). }
      fexists Ysg. fsplit; [exact (InV_VV HG HR HV sg Ysg Hsgo HYsg)|].
      fsplit; [exact (VV_in HG HR HV k sg w Ysg Hko Hsgk Hw HYsg)|].
      fall y. fintro HyV. fintro HyC. fall z. fintro HzV. fintro Hzy.
      pose proof HCc as T. finst T y. fhave T' : (iff_l _ _ _ T HyC). fdestr T' HyY _T2.
      fhave T2 : (VV_el HG HR HV sg Ysg y Hsgo HYsg HyY). fex T2 c Hc. fdestr Hc Hcs Hc2. fex Hc2 Yc HYc.
      fdestr HYc HYcv HyYc.
      fhave Hco : (ord_el_g sg c Hsgo Hcs).
      exact (sub_use' Yc Ysg z (VV_sub HG HR HV sg c Ysg Yc Hsgo Hco (ord_el_sub_g c sg Hsgo Hcs) HYsg HYcv)
               (sub_use' y Yc z HyYc Hzy)).
Qed.

(** ** Assembly *)
Definition holdsV (a : form) : Prop := exists A, (forall b, In b A -> T_GUR b) /\
  forall G, incl ZF0base G -> In ax_reg' G -> In GU G -> incl Ax_V G -> incl Ax_U G -> incl Ax_gru G ->
    incl A G -> G ⊢C rel Vform a.

Lemma ZFR_TGUR b : ZFR b -> T_GUR b.
Proof. intros H. now left. Qed.

Lemma V_ug n phi : closedf (forall_times n (ug phi)) -> holdsV (forall_times n (ug phi)).
Proof.
  intros Hc. pose proof (fb_ug_inv n phi Hc) as Hfb.
  exists (ug_insts n phi). split; [intros b Hb; apply ZFR_TGUR; exact (ug_insts_ok n phi b Hfb Hb)|].
  intros G HG HR HGU HV HU HA HI.
  enough (H : G ⊢C (rel Vform (forall_times n (ug phi)))[var]) by (rewrite subst_var in H; exact H).
  apply (rel_ft Vform bounded_Vform). intros G' tau HGG' _ _. rewrite relV_subst.
  apply (ug_core (incl_tran HG HGG') (HGG' _ HR) (HGG' _ HGU) (incl_tran HV HGG') (incl_tran HU HGG')
    (incl_tran HA HGG') n phi tau Hfb (incl_tran HI HGG')).
Qed.

Theorem SUIR_V a : SUIR a -> holdsV a.
Proof.
  intros [[a' Ha | phi n Hc] | ->].
  - exists []. split; [intros b []|]. intros G HG _ _ _ _ _ _. exact (V_eqax HG a' Ha).
  - now apply V_ug.
  - exists []. split; [intros b []|]. intros G HG HR _ _ _ _ _. exact (V_ir HG HR).
Qed.

Theorem SU_to_TGUR : SUIR ⊢TC ⊥ -> T_GUR ⊢TC ⊥.
Proof.
  intros [A [HA H]].
  destruct (MinZF.collect (R := fun L (a : form) => forall G, incl ZF0base G -> In ax_reg' G -> In GU G ->
               incl Ax_V G -> incl Ax_U G -> incl Ax_gru G -> incl L G -> G ⊢C rel Vform a)
             (Q := T_GUR) (A := A)) as [L [HL1 HL2]].
  - intros L L' x Hx HL G H1 H2 H3 H4 H5 H6 H7. apply Hx; trivial. intros b Hb. now apply H7, HL.
  - intros a Ha. now apply SUIR_V, HA.
  - set (G0 := ax_reg' :: GU :: ZF0base ++ Ax_V ++ Ax_U ++ Ax_gru ++ L).
    assert (HG0 : incl ZF0base G0) by (intros b Hb; right; right; apply in_app_iff; now left).
    assert (HR0 : In ax_reg' G0) by now left.
    assert (HU0 : In GU G0) by (right; now left).
    assert (HV0 : incl Ax_V G0)
      by (intros b Hb; right; right; apply in_app_iff; right; apply in_app_iff; now left).
    assert (HUU0 : incl Ax_U G0)
      by (intros b Hb; right; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; now left).
    assert (HA0 : incl Ax_gru G0)
      by (intros b Hb; right; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right;
          apply in_app_iff; now left).
    assert (HL0 : incl L G0)
      by (intros b Hb; right; right; apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right;
          apply in_app_iff; now right).
    exists G0. split.
    + intros b [ <- | [ <- | Hb ] ]; [left; now right | now right |].
      apply in_app_iff in Hb as [Hb|Hb]; [left; left; left; now apply ZF0_base|].
      apply in_app_iff in Hb as [Hb|Hb]; [apply ZFR_TGUR; now apply Ax_V_ok|].
      apply in_app_iff in Hb as [Hb|Hb]; [apply ZFR_TGUR; now apply Ax_U_ok|].
      apply in_app_iff in Hb as [Hb|Hb]; [left; left; left; now apply Ax_gru_ok | now apply HL1].
    + apply (ExE_named (V_ex HG0 HR0 HV0)). intros t.
      change ⊥ with (rel Vform ⊥).
      apply (transfer Vform bounded_Vform A ⊥ _ t H).
      * cbn. exact I.
      * intros a Ha. exact (SUIR_closed a (HA a Ha)).
      * intros a Ha. apply weak_cons. apply HL2; trivial.
      * apply Ctx. now left.
Qed.
