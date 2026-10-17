(** * SU_quot: the raw w of one UG' instance is a weak universe of the bisimulation quotient.

    phiU := qtS (App0 $2 $0 $1): "(a, y) ∈ f" in the quotient (input a = $0, output y = $1, f = $2).
    [SU_GU0]: SU0 ⊢TC qtS GU0.  The raw w given by [ug phiU] at p := x satisfies, in the quotient:
    - Tr: raw transitivity + [mem_r];
    - power containers: an interpreted subset z of x ≈ x' ∈ w is ≈ its raw trace {u ∈ x' | Mem u z},
      a raw subset of x', hence in the raw container W;
    - the family clause: the interpreted B is ≈ a raw B' ∈ w, interpreted images in u are ≈ raw ones
      in w, phiU is ≈-invariant ([qt_inv]); the raw bound ∪C ⊆ U gives the interpreted one. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq Std_setinf.
From ZFC Require Import Z_rel Z_base.
From M254S Require Import S_def S_qt S_gic S_raw S_quot S_ax.
From M254TG Require Import SU_def SU_s0 SU_gu SU_gru.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition phiU : form := qtS (App0 $2 $0 $1).
Definition AppQ (f a y : term) : form := qtS (App0 f a y).

Lemma fb_phiU : fb 3 phiU.
Proof. unfold phiU, qtS, App0, OP0, Sing0, Pair0, Eqv, Mem, Bisim. fbcomp. Qed.

Lemma phiU_eq sg : phiU[sg] = AppQ (sg 2) (sg 0) (sg 1).
Proof. unfold phiU, AppQ. rewrite qtS_subst. now rewrite App0_subst. Qed.

Lemma AppQ_subst f a y sg : (AppQ f a y)[sg] = AppQ f`[sg] a`[sg] y`[sg].
Proof. unfold AppQ. rewrite qtS_subst. now rewrite App0_subst. Qed.
#[global] Hint Rewrite AppQ_subst : fsub.

(** normalize φU-instances in a hypothesis / the goal *)
Ltac nphi_in H := unfold phiU in H; rewrite ?qtS_subst in H; rewrite ?App0_subst in H; simp_in H.
Ltac nphi := rewrite ?subst_comp, ?phiU_eq; cbn.
Ltac nq := rewrite ?(qt_subst Eqv Mem Eqv_subst Mem_subst); rewrite ?App0_subst; simp.
Ltac nq_in H := rewrite ?(qt_subst Eqv Mem Eqv_subst Mem_subst) in H;
  rewrite ?App0_subst in H; simp_in H.

Lemma AppQ_inv {G} (HB : incl Sbase G) (HQ : incl Sq G) f a y f' a' y' :
  G ⊢C Eqv f f' -> G ⊢C Eqv a a' -> G ⊢C Eqv y y' -> G ⊢C AppQ f a y -> G ⊢C AppQ f' a' y'.
Proof.
  intros Hf Ha Hy H.
  pose proof (qt_inv (App0 $2 $0 $1) G (a .: y .: f .: var) (a' .: y' .: f' .: var) HB HQ) as T.
  rewrite !qtS_subst, !App0_subst in T. cbn in T. apply T; [|exact H].
  intros [|[|[|n]]]; cbn; [exact Ha|exact Hy|exact Hf|apply (eqv_refl HB HQ)].
Qed.

Lemma ug_phiU_ok : SU0 (forall_times 0 (ug phiU)).
Proof. apply SU0_ug, ug_closed, fb_phiU. Qed.

(** the core, in an abstract context *)
Lemma GU0_core G : incl Sbase G -> incl Sq G -> incl Sq_ax G -> In (ug phiU) G -> G ⊢C qtS GU0.
Proof.
  intros HB HQ HA Hug. pose proof (HE HB) as HE.
  assert (H : G ⊢C ug phiU) by (apply Ctx, Hug). clear Hug.
  unfold qtS, GU0. cbn. fall x. unfold ug in H. finst H x. fex H w Hw.
  fdestr Hw Hw1 HFam. fdestr Hw1 HxW HCP. fexists w. fsplit; [exact (mem_raw HB HQ x w HxW)|].
  unfold Gru0. cbn. fsplit; [fsplit|].
  - (* Tr *)
    unfold Trans0. cbn. fall a. fintro Ha. fall b. fintro Hb.
    unfold Mem in Ha. fex Ha a' Ha'. fdestr Ha' Ha'w Haa'.
    fhave Hb' : (mem_r HB HQ b a a' Haa' Hb). unfold Mem in Hb'. fex Hb' b' Hb''. fdestr Hb'' Hb'a' Hbb'.
    unfold Mem. fexists b'. fsplit; [|exact Hbb'].
    pose proof HCP as T. finst T a'. fmp T Ha'w. fdestr T T1 _T2. finst T1 b'. exact (IE T1 Hb'a').
  - (* power containers *)
    fall X. fintro HX. unfold Mem in HX. fex HX x' Hx'. fdestr Hx' Hx'w HXx'.
    pose proof HCP as T. finst T x'. fmp T Hx'w. fdestr T _T1 T2. fex T2 W HW. fdestr HW HWw HWc.
    fexists W. fsplit; [exact (mem_raw HB HQ W w HWw)|].
    unfold Sub0. cbn. fall z. fintro Hsub.
    pose proof (HA (forall_times 2 (gic (sep_th psi_trace))) ltac:(cbn; tauto)) as Hin2.
    pose proof (sepS_use _ 1 psi_trace (z .: var) x' HE Hin2 ltac:(unfold psi_trace, Mem, Eqv, Bisim, App0, OP0, Sing0, Pair0; cbn; lia)) as T.
    fex T r Hr. unfold psi_trace in Hr. simp_in Hr.
    fassert Hrx : (∀ ($0 ∈' r`[↑] → $0 ∈' x'`[↑])).
    { fall u. fintro Hu. finst Hr u. exact (CE1 (iff_l _ _ _ Hr Hu)). }
    fassert HrW : (r ∈' W). { finst HWc r. exact (IE HWc Hrx). }
    fassert Hzr : (Eqv z r).
    { apply (eqv_ext HB HQ).
      - fall t. fintro Ht. pose proof Hsub as T. finst T t. fmp T Ht.
        fhave T' : (mem_r HB HQ t X x' HXx' T). unfold Mem in T'. fex T' u Hu. fdestr Hu Hux Htu.
        unfold Mem. fexists u. fsplit; [|exact Htu].
        finst Hr u. apply (iff_r _ _ _ Hr). fsplit; [exact Hux | exact (mem_l HB HQ t u z Htu Ht)].
      - fall t. fintro Ht. unfold Mem in Ht. fex Ht u Hu. fdestr Hu Hur Htu. finst Hr u.
        fhave T : (iff_l _ _ _ Hr Hur). fdestr T Hux HuZ.
        exact (mem_l HB HQ u t z (eqv_sym HB HQ _ _ Htu) HuZ). }
    unfold Mem. fexists r. fsplit; [exact HrW | exact Hzr].
  - (* family clause *)
    fall f. fall Bi. fintro HBi. fintro Htot.
    unfold Mem in HBi. fex HBi B HB'. fdestr HB' HBw HBiB.
    finst HFam f B. fmp HFam HBw. fex HFam C HC. fdestr HC HC12 Hbound. fdestr HC12 Hcov _Hnx.
    fassert Htot' : (∀ ($0 ∈' B`[↑] → ∃ ($0 ∈' w`[↑]`[↑] ∧ AppQ f`[↑]`[↑] $1 $0))).
    { fall a. fintro Ha.
      fhave Ha' : (mem_r HB HQ a B Bi (eqv_sym HB HQ _ _ HBiB) (mem_raw HB HQ a B Ha)).
      pose proof Htot as T. finst T a. fmp T Ha'. fex T y Hy. fdestr Hy Hyw HAy. nq_in HAy.
      unfold Mem in Hyw. fex Hyw y' Hy'. fdestr Hy' Hy'w Hyy'.
      fexists y'. fsplit; [exact Hy'w|].
      apply (AppQ_inv HB HQ f a y f a y' (eqv_refl HB HQ f) (eqv_refl HB HQ a) Hyy'). exact HAy. }
    nphi_in Hbound. fmp Hbound Htot'. fex Hbound U HU. fdestr HU HUw HUc.
    fexists C. fsplit.
    + fall a. fintro Ha. fall y. fintro Hay. nq_in Hay.
      fhave Ha1 : (mem_r HB HQ a Bi B HBiB Ha). unfold Mem in Ha1. fex Ha1 a' Ha'. fdestr Ha' Ha'B Haa'.
      fassert Hay' : (AppQ f a' y).
      { apply (AppQ_inv HB HQ f a y f a' y (eqv_refl HB HQ f) Haa' (eqv_refl HB HQ y)). exact Hay. }
      pose proof Hcov as T. finst T a'. fmp T Ha'B. finst T y. nphi_in T. fmp_conv T Hay'.
      fex T y' Hy'. fdestr Hy' Hy'1 Hy'C. nphi_in Hy'1.
      fexists y'. fsplit.
      * nq. apply (AppQ_inv HB HQ f a' y' f a y' (eqv_refl HB HQ f) (eqv_sym HB HQ _ _ Haa') (eqv_refl HB HQ y')).
        exact Hy'1.
      * exact (mem_raw HB HQ y' C Hy'C).
    + fexists U. fsplit; [exact (mem_raw HB HQ U w HUw)|].
      fall y. fintro Hy. fall z. fintro Hz. unfold Mem in Hy. fex Hy y' Hy'. fdestr Hy' Hy'C Hyy'.
      fhave Hz' : (mem_r HB HQ z y y' Hyy' Hz). unfold Mem in Hz'. fex Hz' z' Hz''. fdestr Hz'' Hz'y' Hzz'.
      unfold Mem. fexists z'. fsplit; [|exact Hzz'].
      pose proof HUc as T. finst T y'. fmp T Hy'C. finst T z'. exact (IE T Hz'y').
Qed.

Theorem SU_GU0 : SU0 ⊢TC qtS GU0.
Proof.
  apply (tprv_cut (fun a => S0 a \/ a = ug phiU)).
  - intros a [Ha | ->].
    + exact (S0_ax_SU0 a Ha).
    + exists [ug phiU]. split; [intros b [<-|[]]; exact ug_phiU_ok | apply Ctx; now left].
  - exists (ug phiU :: B0). split.
    + intros a [<-|Ha]; [now right | left; now apply B0_ok].
    + apply GU0_core.
      * intros a Ha. right. now apply B0_base.
      * intros a Ha. right. now apply B0_q.
      * intros a Ha. right. now apply B0_ax.
      * now left.
Qed.
