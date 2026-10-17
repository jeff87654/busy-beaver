(** * SU_V: the cumulative hierarchy V_α (α ↦ [VV α Y], "Y = V_α") and the class [Vform].

      V_α = ⋃_{β<α} 𝒫(V_β)       (one uniform step; no case split on zero / successor / limit)

    Built with the recursion theorem of ZF/stdzf_r3/zfc Z_trec, like Z_L builds L.  Only the facts used by
    the soundness proof are developed: existence, uniqueness, the membership equation [VV_el] /
    [VV_intro], monotonicity, and V_β ∈ V_α for β ∈ α.  Transitivity of V_α is NOT needed. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** recursion step: f = $0, ξ = $1, v = $2:  ∀z (z ∈ v ↔ ∃β∈ξ ∃w (f(β) = w ∧ z ⊆ w)) *)
Definition vu_form : form := ∃ ($0 ∈' $3 ∧ ∃ (App0 $3 $1 $0 ∧ Sub0 $2 $0)).
Definition SV : form := ∀ ($0 ∈' $3 ↔ vu_form).

(** Y = V_α *)
Definition VV (a Y : term) : form :=
  ∃ (∃ (Succ0 a`[↑]`[↑] $1 ∧ Fun0 $0 ∧ Dom0 $0 $1 ∧ RecOK SV a`[↑]`[↑] $0 ∧ App0 $0 a`[↑]`[↑] Y`[↑]`[↑])).
#[global] Arguments VV : simpl never.
Lemma VV_subst a Y sg : (VV a Y)[sg] = VV a`[sg] Y`[sg].
Proof. psubst VV. Qed.
#[global] Hint Rewrite VV_subst : fsub.

(** the class V = ⋃_α V_α, a formula in $0 *)
Definition Vform : form := ∃ (∃ (Ord0 $1 ∧ VV $1 $0 ∧ $2 ∈' $0)).
Definition InV (x : term) : form := Vform[x..].

Lemma fb_vu : fb 3 vu_form.
Proof. fbcomp. Qed.
Lemma fb_SV : fb 4 SV.
Proof. fbcomp. Qed.
Lemma fb_Vform : fb 1 Vform.
Proof. fbcomp. Qed.
Lemma bounded_Vform : bounded 1 Vform.
Proof. apply fb_bounded, fb_Vform. Qed.
Lemma InV_eq x : InV x = ∃ (∃ (Ord0 $1 ∧ VV $1 $0 ∧ x`[↑]`[↑] ∈' $0)).
Proof. unfold InV, Vform. cbn. autorewrite with fsub. cbn. fix_up. reflexivity. Qed.

(** fixed instances *)
Definition V_insts : list form := [forall_times 2 (ax_sep' vu_form)].
Definition Ax_V : list form := Ax_ord ++ rec_insts SV ++ V_insts.
Lemma Ax_V_ok a : In a Ax_V -> ZFR a.
Proof.
  intros [H|[H|H]%in_app_iff]%in_app_iff.
  - now apply Ax_ord_ok.
  - exact (rec_insts_ok SV a fb_SV H).
  - destruct H as [<-|[]]. exact (ZFR_sep 2 _ fb_vu).
Qed.
Lemma Ax_V_ord G : incl Ax_V G -> incl Ax_ord G.
Proof. intros H a Ha. apply H, in_app_iff. now left. Qed.
Lemma Ax_V_rec G : incl Ax_V G -> incl (rec_insts SV) G.
Proof. intros H a Ha. apply H, in_app_iff. right. apply in_app_iff. now left. Qed.
Lemma in_vu G : incl Ax_V G -> In (forall_times 2 (ax_sep' vu_form)) G.
Proof. intros H. apply H, in_app_iff. right. apply in_app_iff. right. now left. Qed.

(** ** The step formula, instantiated *)
Definition SVf (f xi v : term) : form :=
  ∀ ($0 ∈' v`[↑] ↔ ∃ ($0 ∈' xi`[↑]`[↑] ∧ ∃ (App0 f`[↑]`[↑]`[↑] $1 $0 ∧ Sub0 $2 $0))).
#[global] Arguments SVf : simpl never.
Lemma SVf_subst f xi v sg : (SVf f xi v)[sg] = SVf f`[sg] xi`[sg] v`[sg].
Proof. psubst SVf. Qed.
#[global] Hint Rewrite SVf_subst : fsub.
Lemma SR_SV f xi v p : SR SV f xi v p = SVf f xi v.
Proof. unfold SR, SV, SVf, vu_form. simp. reflexivity. Qed.
Lemma RecOK_SV p q f : RecOK SV p f = RecOK SV q f.
Proof. unfold RecOK. now rewrite !SR_SV. Qed.

Lemma svf_el {G} f xi v z : G ⊢C SVf f xi v -> G ⊢C z ∈' v ->
  G ⊢C ∃ ($0 ∈' xi`[↑] ∧ ∃ (App0 f`[↑]`[↑] $1 $0 ∧ Sub0 z`[↑]`[↑] $0)).
Proof. intros H Hz. unfold SVf in H. finst H z. exact (iff_l _ _ _ H Hz). Qed.
Lemma svf_intro {G} f xi v z b w : G ⊢C SVf f xi v -> G ⊢C b ∈' xi -> G ⊢C App0 f b w -> G ⊢C Sub0 z w ->
  G ⊢C z ∈' v.
Proof.
  intros H Hb Hw Hz. unfold SVf in H. finst H z. apply (iff_r _ _ _ H).
  fexists b. fsplit; [exact Hb|]. fexists w. fsplit; [exact Hw|exact Hz].
Qed.

(** ** Basic helpers *)
Lemma sub_use' {G} x y z : G ⊢C Sub0 x y -> G ⊢C z ∈' x -> G ⊢C z ∈' y.
Proof. intros H Hz. unfold Sub0 in H. finst H z. exact (IE H Hz). Qed.
Lemma sub_refl' {G} x : G ⊢C Sub0 x x.
Proof. unfold Sub0. fall z. fintro Hz. exact Hz. Qed.
Lemma succ_self' {G} x s : G ⊢C Succ0 x s -> G ⊢C x ∈' s.
Proof. intros H. unfold Succ0 in H. exact (CE1 (CE1 H)). Qed.
Lemma succ_sub' {G} x s : G ⊢C Succ0 x s -> G ⊢C Sub0 x s.
Proof. intros H. unfold Succ0 in H. exact (CE2 (CE1 H)). Qed.
Lemma union_in' {G} x u y z : G ⊢C Union0 x u -> G ⊢C y ∈' x -> G ⊢C z ∈' y -> G ⊢C z ∈' u.
Proof.
  intros H Hy Hz. unfold Union0 in H. pose proof (CE2 H) as H2. finst H2 y. fmp H2 Hy. finst H2 z.
  exact (IE H2 Hz).
Qed.
Lemma op0_val' {G} u w q : G ⊢C OP0 u w q -> G ⊢C ∃ ($0 ∈' q`[↑] ∧ w`[↑] ∈' $0).
Proof.
  intros H. unfold OP0 in H. pose proof (CE2 (CE1 H)) as T. fex T r Hr. fdestr Hr Hr1 Hr2.
  fexists r. fsplit; [exact Hr1|]. unfold Pair0 in Hr2. exact (CE2 (CE1 Hr2)).
Qed.
Lemma agree_use' {G} f g xi e w : G ⊢C Agree f g xi -> G ⊢C e ∈' xi -> G ⊢C App0 f e w -> G ⊢C App0 g e w.
Proof. intros H He Hw. unfold Agree in H. finst H e. fmp H He. finst H w. exact (iff_l _ _ _ H Hw). Qed.

Lemma pow_ex {G} (HG : incl ZF0base G) x : G ⊢C ∃ is_power x`[↑] $0.
Proof.
  assert (H : G ⊢C ax_power') by (apply Ctx, HG; cbn; tauto). unfold ax_power' in H.
  apply (AllE x) in H. cbn in H. rewrite is_power_subst in H. cbn in H. exact H.
Qed.

(** ** Wrappers (uniform signature HG HR HV) *)
Section Wr.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G).
Lemma v_pairsall_use f B u v : G ⊢C PairsAll f B -> G ⊢C App0 f u v -> G ⊢C B[v .: u .: var].
Proof using HG HR HV. intros. eapply pairsall_use; eassumption. Qed.
Lemma v_dom0_in f d u v : G ⊢C Dom0 f d -> G ⊢C App0 f u v -> G ⊢C u ∈' d.
Proof using HG HR HV. intros. eapply dom0_in; eassumption. Qed.
Lemma v_dom0_app f d u : G ⊢C Dom0 f d -> G ⊢C u ∈' d -> G ⊢C ∃ App0 f`[↑] u`[↑] $0.
Proof using HG HR HV. intros. eapply dom0_app; eassumption. Qed.
Lemma v_ord_el a x : G ⊢C Ord0 a -> G ⊢C x ∈' a -> G ⊢C Ord0 x.
Proof using HG HR HV. intros. eapply ord_el; eassumption. Qed.
Lemma v_ord_tr a x y : G ⊢C Ord0 a -> G ⊢C x ∈' y -> G ⊢C y ∈' a -> G ⊢C x ∈' a.
Proof using HG HR HV. intros. eapply ord_tr; eassumption. Qed.
Lemma v_ord_succ a s : G ⊢C Ord0 a -> G ⊢C Succ0 a s -> G ⊢C Ord0 s.
Proof using HG HR HV. intros. eapply ord_succ; eassumption. Qed.
Lemma v_ord_emp e : G ⊢C Emp0 e -> G ⊢C Ord0 e.
Proof using HG HR HV. intros. eapply ord_emp; eassumption. Qed.
Lemma v_succ0_ex x : G ⊢C ∃ Succ0 x`[↑] $0.
Proof using HG HR HV. eapply succ0_ex; [eassumption|apply Ax_ord_prim, Ax_V_ord; eassumption]. Qed.
Lemma v_emp0_ex : G ⊢C ∃ Emp0 $0.
Proof using HG HR HV. eapply emp0_ex; eassumption. Qed.
Lemma v_union0_ex x : G ⊢C ∃ Union0 x`[↑] $0.
Proof using HG HR HV. eapply union0_ex; [eassumption|apply Ax_ord_prim, Ax_V_ord; eassumption]. Qed.
Lemma v_rec_ex p d : G ⊢C SLoc SV p -> G ⊢C STot SV p -> G ⊢C SFun SV p -> G ⊢C Ord0 d ->
  G ⊢C ∃ (Fun0 $0 ∧ Dom0 $0 d`[↑] ∧ RecOK SV p`[↑] $0).
Proof using HG HR HV. intros. exact (rec_ex HG HR (Ax_V_ord _ HV) SV fb_SV (Ax_V_rec _ HV) p d H H0 H1 H2). Qed.
Lemma v_rec_agree p d d' f f' xi u u' : G ⊢C SLoc SV p -> G ⊢C SFun SV p ->
  G ⊢C Ord0 d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK SV p f ->
  G ⊢C Ord0 d' -> G ⊢C Fun0 f' -> G ⊢C Dom0 f' d' -> G ⊢C RecOK SV p f' ->
  G ⊢C xi ∈' d -> G ⊢C xi ∈' d' -> G ⊢C App0 f xi u -> G ⊢C App0 f' xi u' -> G ⊢C u ≡' u'.
Proof using HG HR HV.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
  exact (rec_agree HG HR (Ax_V_ord _ HV) SV fb_SV (Ax_V_rec _ HV) p d d' f f' xi u u' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14).
Qed.
End Wr.

(** ** Locality, totality, functionality of the step *)

Lemma SV_loc {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) p : G ⊢C SLoc SV p.
Proof.
  unfold SLoc. fall f. fall g. fall xi. fall v. rewrite !SR_SV.
  fintro Hf. fintro Hg. fintro Hxi. fintro HA. fintro H.
  unfold SVf. fall z. fsplit.
  - fintro Hz. fhave T : (svf_el f xi v z H Hz). fex T b Hb. fdestr Hb Hb1 Hb2. fex Hb2 w Hw.
    fdestr Hw Hw1 Hw2. fexists b. fsplit; [exact Hb1|]. fexists w. fsplit; [|exact Hw2].
    exact (agree_use' f g xi b w HA Hb1 Hw1).
  - fintro Hz. fex Hz b Hb. fdestr Hb Hb1 Hb2. fex Hb2 w Hw. fdestr Hw Hw1 Hw2.
    apply (svf_intro f xi v z b w H Hb1); [|exact Hw2].
    unfold Agree in HA. finst HA b. fmp HA Hb1. finst HA w. exact (iff_r _ _ _ HA Hw1).
Qed.

Lemma SV_tot {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) p : G ⊢C STot SV p.
Proof.
  unfold STot. fall f. fall xi. rewrite SR_SV. fintro Hf. fintro Hxi. fintro Htot.
  fobtain (v_union0_ex HG HR HV f) as U1 HU1.
  fobtain (v_union0_ex HG HR HV U1) as U2 HU2.
  fobtain (v_union0_ex HG HR HV U2) as U3 HU3.
  fobtain (pow_ex HG U3) as P HP.
  pose proof (sep_use _ 2 vu_form (f .: xi .: var) P (in_vu _ HV) fb_vu) as HX.
  unfold vu_form in HX. simp_in HX. fex HX X HXc.
  fexists X. unfold SVf. fall z. fsplit.
  - fintro Hz. pose proof HXc as H. finst H z. exact (CE2 (iff_l _ _ _ H Hz)).
  - fintro Hz. pose proof HXc as H. finst H z. apply (iff_r _ _ _ H). fsplit; [|exact Hz].
    fex Hz b Hb. fdestr Hb Hb1 Hb2. fex Hb2 w Hw. fdestr Hw Hw1 Hw2.
    unfold is_power in HP. finst HP z. apply (iff_r _ _ _ HP). unfold sub'. fall y. fintro Hy.
    pose proof Hw1 as Hw'. unfold App0 in Hw'. fex Hw' q Hq. fdestr Hq Hq1 Hq2.
    pose proof (op0_val' b w q Hq2) as T. fex T r Hr. fdestr Hr Hr1 Hr2.
    apply (union_in' U2 U3 w y HU3); [|exact (sub_use' z w y Hw2 Hy)].
    apply (union_in' U1 U2 r w HU2); [|exact Hr2]. exact (union_in' f U1 q r HU1 Hq1 Hr1).
Qed.

Lemma SV_fun {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) p : G ⊢C SFun SV p.
Proof.
  unfold SFun. fall f. fall xi. fall v. fall v'. rewrite !SR_SV. fintro Hf. fintro Hxi. fintro H. fintro H'.
  apply (ext_rule HG); unfold sub'; fall z; fintro Hz.
  - fhave T : (svf_el f xi v z H Hz). fex T b Hb. fdestr Hb Hb1 Hb2. fex Hb2 w Hw. fdestr Hw Hw1 Hw2.
    exact (svf_intro f xi v' z b w H' Hb1 Hw1 Hw2).
  - fhave T : (svf_el f xi v' z H' Hz). fex T b Hb. fdestr Hb Hb1 Hb2. fex Hb2 w Hw. fdestr Hw Hw1 Hw2.
    exact (svf_intro f xi v z b w H Hb1 Hw1 Hw2).
Qed.

(** ** The hierarchy: existence, uniqueness, the membership equation *)
Local Ltac vvdestr H d f Hs Hfun Hdom Hrec Happ :=
  let T := fresh "T" in let T1 := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in
  unfold VV in H; fex H d T; fex T f T1; fdestr T1 T2 Happ; fdestr T2 T3 Hrec; fdestr T3 T1 Hdom;
  fdestr T1 Hs Hfun.

Lemma VV_intro {G} a Y d f : G ⊢C Succ0 a d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK SV a f ->
  G ⊢C App0 f a Y -> G ⊢C VV a Y.
Proof.
  intros H1 H2 H3 H4 H5. unfold VV. fexists d. fexists f.
  fsplit; [|exact H5]. fsplit; [|exact H4]. fsplit; [|exact H3]. fsplit; [exact H1|exact H2].
Qed.


Lemma recok_sv {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) p f u v : G ⊢C RecOK SV p f -> G ⊢C App0 f u v -> G ⊢C SVf f u v.
Proof.
  intros H Hv. unfold RecOK in H. pose proof (v_pairsall_use HG HR HV _ _ u v H Hv) as T.
  simp_in T. rewrite SR_SV in T. exact T.
Qed.

Lemma VV_fun_eq {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) p d f e w Y : G ⊢C Ord0 d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK SV p f ->
  G ⊢C App0 f e w -> G ⊢C VV e Y -> G ⊢C w ≡' Y.
Proof.
  intros Hd Hf Hdom Hrec Hw HY.
  pose proof (v_dom0_in HG HR HV f d e w Hdom Hw) as He.
  pose proof (v_ord_el HG HR HV d e Hd He) as Heo.
  vvdestr HY d' g Hs Hg Hgdom Hgrec Hgapp.
  rewrite (RecOK_SV e p) in Hgrec.
  exact (v_rec_agree HG HR HV p d d' f g e w Y (SV_loc HG HR HV p) (SV_fun HG HR HV p)
    Hd Hf Hdom Hrec (v_ord_succ HG HR HV e d' Heo Hs) Hg Hgdom Hgrec He (succ_self' e d' Hs) Hw Hgapp).
Qed.

Lemma VV_ex {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) a : G ⊢C Ord0 a -> G ⊢C ∃ VV a`[↑] $0.
Proof.
  intros Ha. fobtain (v_succ0_ex HG HR HV a) as d Hd.
  pose proof (v_ord_succ HG HR HV a d Ha Hd) as Hdo.
  pose proof (v_rec_ex HG HR HV a d (SV_loc HG HR HV a) (SV_tot HG HR HV a)
    (SV_fun HG HR HV a) Hdo) as T.
  fex T f Hf. fdestr Hf Hf12 Hf3. fdestr Hf12 Hf1 Hf2.
  pose proof (v_dom0_app HG HR HV f d a Hf2 (succ_self' a d Hd)) as T. fex T Y HY.
  fexists Y. exact (VV_intro a Y d f Hd Hf1 Hf2 Hf3 HY).
Qed.

Lemma VV_unique {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) a Y Y' : G ⊢C Ord0 a -> G ⊢C VV a Y -> G ⊢C VV a Y' -> G ⊢C Y ≡' Y'.
Proof.
  intros Ha H1 H2. vvdestr H1 d f Hs Hf Hdom Hrec Happ.
  exact (VV_fun_eq HG HR HV a d f a Y Y' (v_ord_succ HG HR HV a d Ha Hs) Hf Hdom Hrec Happ H2).
Qed.

Lemma VV_of_fun {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) p d f e w : G ⊢C Ord0 d -> G ⊢C Fun0 f -> G ⊢C Dom0 f d -> G ⊢C RecOK SV p f ->
  G ⊢C App0 f e w -> G ⊢C VV e w.
Proof.
  intros Hd Hf Hdom Hrec Hw.
  pose proof (v_dom0_in HG HR HV f d e w Hdom Hw) as He.
  pose proof (v_ord_el HG HR HV d e Hd He) as Heo.
  pose proof (VV_ex HG HR HV e Heo) as T. fex T Y HY.
  pose proof (VV_fun_eq HG HR HV p d f e w Y Hd Hf Hdom Hrec Hw HY) as E.
  frew_in E (VV e`[↑] $0) HY. exact HY.
Qed.

(** z ∈ V_a ↔ z ⊆ V_b for some b ∈ a *)
Lemma VV_el {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) a Y z : G ⊢C Ord0 a -> G ⊢C VV a Y -> G ⊢C z ∈' Y ->
  G ⊢C ∃ ($0 ∈' a`[↑] ∧ ∃ (VV $1 $0 ∧ Sub0 z`[↑]`[↑] $0)).
Proof.
  intros Ha HY Hz. vvdestr HY d f Hs Hf Hdom Hrec Happ.
  pose proof (v_ord_succ HG HR HV a d Ha Hs) as Hdo.
  pose proof (svf_el f a Y z (recok_sv HG HR HV a f a Y Hrec Happ) Hz) as T. fex T b Hb. fdestr Hb Hb1 Hb2.
  fex Hb2 w Hw. fdestr Hw Hw1 Hw2.
  fexists b. fsplit; [exact Hb1|]. fexists w. fsplit; [|exact Hw2].
  exact (VV_of_fun HG HR HV a d f b w Hdo Hf Hdom Hrec Hw1).
Qed.

Lemma VV_intro_el {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) a Y b Yb z : G ⊢C Ord0 a -> G ⊢C VV a Y -> G ⊢C b ∈' a -> G ⊢C VV b Yb ->
  G ⊢C Sub0 z Yb -> G ⊢C z ∈' Y.
Proof.
  intros Ha HY Hb HYb Hz. vvdestr HY d f Hs Hf Hdom Hrec Happ.
  pose proof (v_ord_succ HG HR HV a d Ha Hs) as Hdo.
  pose proof (v_dom0_app HG HR HV f d b Hdom (v_ord_tr HG HR HV d b a Hdo Hb (succ_self' a d Hs))) as T.
  fex T w Hw.
  pose proof (VV_fun_eq HG HR HV a d f b w Yb Hdo Hf Hdom Hrec Hw HYb) as E.
  apply (svf_intro f a Y z b w (recok_sv HG HR HV a f a Y Hrec Happ) Hb Hw).
  frew E (Sub0 z`[↑] $0). exact Hz.
Qed.

(** b ∈ a → V_b ∈ V_a *)
Lemma VV_in {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) a b Ya Yb : G ⊢C Ord0 a -> G ⊢C b ∈' a -> G ⊢C VV a Ya -> G ⊢C VV b Yb -> G ⊢C Yb ∈' Ya.
Proof.
  intros Ha Hb HYa HYb. exact (VV_intro_el HG HR HV a Ya b Yb Yb Ha HYa Hb HYb (sub_refl' Yb)).
Qed.

(** b ⊆ a → V_b ⊆ V_a *)
Lemma VV_sub {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) a b Ya Yb : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C Sub0 b a -> G ⊢C VV a Ya -> G ⊢C VV b Yb ->
  G ⊢C Sub0 Yb Ya.
Proof.
  intros Ha Hb Hs HYa HYb. unfold Sub0. fall z. fintro Hz.
  pose proof (VV_el HG HR HV b Yb z Hb HYb Hz) as T. fex T c Hc. fdestr Hc Hc1 Hc2. fex Hc2 Yc HYc.
  fdestr HYc HYc1 HYc2.
  exact (VV_intro_el HG HR HV a Ya c Yc z Ha HYa (sub_use' b a c Hs Hc1) HYc1 HYc2).
Qed.

(** subsets of V_a lie in V_{a+1} *)
Lemma VV_succ {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) a s Ya Ys z : G ⊢C Ord0 a -> G ⊢C Succ0 a s -> G ⊢C VV a Ya -> G ⊢C VV s Ys ->
  G ⊢C Sub0 z Ya -> G ⊢C z ∈' Ys.
Proof.
  intros Ha Hs HYa HYs Hz.
  exact (VV_intro_el HG HR HV s Ys a Ya z (v_ord_succ HG HR HV a s Ha Hs) HYs (succ_self' a s Hs) HYa Hz).
Qed.

(** ** The class *)
Lemma InV_intro {G} a Y x : G ⊢C Ord0 a -> G ⊢C VV a Y -> G ⊢C x ∈' Y -> G ⊢C InV x.
Proof. intros H1 H2 H3. rewrite InV_eq. fexists a. fexists Y. fsplit; [fsplit|]; assumption. Qed.

(** V_a itself is in the class (it lies in V_{a+1}) *)
Lemma InV_VV {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) a Y : G ⊢C Ord0 a -> G ⊢C VV a Y -> G ⊢C InV Y.
Proof.
  intros Ha HY. fobtain (v_succ0_ex HG HR HV a) as s Hs.
  pose proof (v_ord_succ HG HR HV a s Ha Hs) as Hso.
  pose proof (VV_ex HG HR HV s Hso) as T. fex T Ys HYs.
  exact (InV_intro s Ys Y Hso HYs (VV_succ HG HR HV a s Y Ys Y Ha Hs HY HYs (sub_refl' Y))).
Qed.

Lemma V_ex {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HV : incl Ax_V G) : G ⊢C ∃ Vform.
Proof.
  fobtain (v_emp0_ex HG HR HV) as e He.
  pose proof (v_ord_emp HG HR HV e He) as Heo.
  pose proof (VV_ex HG HR HV e Heo) as T. fex T Y HY.
  apply (ExI Y). exact (InV_VV HG HR HV e Y Heo HY).
Qed.

