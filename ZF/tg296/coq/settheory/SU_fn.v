(** * SU_fn: set functions from functional formulas (replacement), in ZF.

    [fn_build]: if psi(a, v; params) is functional and total on the set B, there is a set function F
    (Fun0 F, Dom0 F B) whose graph is exactly {(a, v) | a ∈ B ∧ psi(a, v)}.  One replacement instance
    [forall_times n (ax_rep' (fnR psi))] is used; psi: $0 = a, $1 = v, $(k+2) = parameter k. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From ZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec.
From M254S Require Import S_gic.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** the replacement formula: $0 = a, $1 = q (the pair code), $(k+2) = parameter k *)
Definition fnR (psi : form) : form := ∃ (OP0 $1 $0 $2 ∧ psi[$1 .: $0 .: (fun k => $(3 + k))]).

Lemma fb_fnR n psi : fb (S (S n)) psi -> fb (S (S n)) (fnR psi).
Proof.
  intros H. unfold fnR, OP0, Sing0, Pair0. cbn. repeat split; try lia.
  eapply fb_subst; [exact H|]. intros [|[|i]] Hi; cbn; lia.
Qed.

Lemma fn_build {G} (HG : incl ZF0base G) (HP : incl Ax_prim G) n psi sg B :
  fb (S (S n)) psi -> In (forall_times n (ax_rep' (fnR psi))) G ->
  G ⊢C ∀ (∀ (∀ (psi[$2 .: $1 .: (fun k => (sg k)`[↑]`[↑]`[↑])] →
                psi[$2 .: $0 .: (fun k => (sg k)`[↑]`[↑]`[↑])] → $1 ≡' $0))) ->
  G ⊢C ∀ ($0 ∈' B`[↑] → ∃ psi[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑])]) ->
  G ⊢C ∃ ((Fun0 $0 ∧ Dom0 $0 B`[↑]) ∧
          ∀ (∀ (App0 $2 $1 $0 ↔ $1 ∈' B`[↑]`[↑]`[↑] ∧ psi[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑]`[↑])]))).
Proof.
  intros Hfb Hin Hfun Htot.
  assert (Hmf : forall a b b', G ⊢C (fnR psi)[a .: b .: sg] → (fnR psi)[a .: b' .: sg] → b ≡' b').
  { intros a b b'. unfold fnR. simp. fintro H1. fintro H2. fex H1 v Hv. fdestr Hv Hv1 Hv2.
    fex H2 v' Hv'. fdestr Hv' Hv1' Hv2'.
    fassert E : (v ≡' v').
    { pose proof Hfun as T. finst T a v v'. fmp_conv T Hv2. fmp_conv T Hv2'. exact T. }
    frew_in E (OP0 a`[↑] $0 b'`[↑]) Hv1'. exact (op0_unique_g HG a v b b' Hv1 Hv1'). }
  pose proof (rep_use G n (fnR psi) sg B Hin (fb_fnR n psi Hfb) Hmf) as HY. clear Hmf.
  unfold fnR in HY. simp_in HY. fex HY F HFd.
  fassert K1 : (∀ (∀ (App0 F`[↑]`[↑] $1 $0 →
                 $1 ∈' B`[↑]`[↑] ∧ psi[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑])]))).
  { fall a. fall v. fintro H. pose proof H as H'. unfold App0 in H'. fex H' q Hq. fdestr Hq Hq1 Hq2.
    pose proof HFd as HFz. finst HFz q. fhave T : (iff_l _ _ _ HFz Hq1). clear HFz.
    fex T a' Ha'. fdestr Ha' Ha'1 Ha'2. fex Ha'2 v' Hv'. fdestr Hv' Hv'1 Hv'2.
    fhave E : (op0_inj_g HG a v a' v' q Hq2 Hv'1). fdestr E E1 E2.
    fsplit.
    - exact (elem_l HG a' a B (eq_sym' HG _ _ E1) Ha'1).
    - fassert Hp : (psi[a' .: v' .: sg]); [fconv_h Hv'2|].
      fassert Hp' : (psi[a .: v .: sg]).
      { apply (leib_gen psi _ (a' .: v' .: sg) (a .: v .: sg) HG); [|exact Hp].
        intros [|[|k]]; cbn; [exact (eq_sym' HG _ _ E1)|exact (eq_sym' HG _ _ E2)|exact (eq_refl' HG _)]. }
      fconv_h Hp'. }
  fassert K2 : (∀ (∀ ($1 ∈' B`[↑]`[↑] → psi[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑])] → App0 F`[↑]`[↑] $1 $0))).
  { fall a. fall v. fintro Ha. fintro Hp. fobtain (op0_ex HG HP a v) as q Hq.
    apply (app0_intro_g F a v q Hq). pose proof HFd as HFz. finst HFz q. apply (iff_r _ _ _ HFz).
    fexists a. fsplit; [exact Ha|]. fexists v. fsplit; [exact Hq|]. fconv_h Hp. }
  fexists F. fsplit; [fsplit|].
  - apply (fun0_intro HG HP).
    + apply (isrel0_intro HG HP). fall q. fintro Hq. pose proof HFd as HFz. finst HFz q.
      fhave T : (iff_l _ _ _ HFz Hq). fex T a Ha. fdestr Ha Ha1 Ha2.
      fex Ha2 v Hv. fdestr Hv Hv1 Hv2. fexists a. fexists v. exact Hv1.
    + fall a. fall v. fall v'. fintro H1. fintro H2.
      pose proof K1 as K. finst K a v. fmp K H1. pose proof K1 as K'. finst K' a v'. fmp K' H2.
      fdestr K Ka Kp. fdestr K' Ka' Kp'.
      pose proof Hfun as T. finst T a v v'. fmp_conv T Kp. fmp_conv T Kp'. exact T.
  - apply (dom0_intro HG HP).
    + fall a. fintro Ha. pose proof Htot as T. finst T a. fmp T Ha. fex T v Hv. fexists v.
      pose proof K2 as K. finst K a v. fmp K Ha. fmp_conv K Hv. exact K.
    + fall a. fall v. fintro H. pose proof K1 as K. finst K a v. fmp K H. exact (CE1 K).
  - fall a. fall v. fsplit.
    + fintro H. pose proof K1 as K. finst K a v. fmp K H. fconv_h K.
    + fintro H. fdestr H Ha Hp. pose proof K2 as K. finst K a v. fmp K Ha. fmp_conv K Hp. exact K.
Qed.
