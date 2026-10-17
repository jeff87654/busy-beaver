(** * SU_s0: SU0 derives every axiom of S0 (CP and every closed GIC instance).

    CP is the first conjunct of any UG' instance.  GIC for φ is UG' for φ' := φ with the inner
    variable f skipped, instantiated at p := B (so B ∈ w) and f := B.  Hence every S0-derivation
    becomes an SU0-derivation ([S0_to_SU0]), and all of ZF/m254/coq/settheory's raw toolkit applies. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_F Std_breq.
From M254S Require Import S_def S_qt S_gic.
From M254S Require S_sound.
From M254TG Require Import SU_def.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** φ with the inner variable f ($2) skipped *)
Definition skipf (phi : form) : form := phi[$0 .: $1 .: (fun k => $(3 + k))].

Lemma fb_skipf n phi : fb (S (S n)) phi -> fb (S (S (S n))) (skipf phi).
Proof. intros H. unfold skipf. eapply fb_subst; [exact H|]. intros [|[|i]] Hi; cbn; lia. Qed.

Lemma ug_cp G phi : G ⊢C ug phi -> G ⊢C ax_cp.
Proof.
  intros H. unfold ax_cp. fall p. unfold ug in H. finst H p. fex H w Hw. fexists w.
  exact (CE1 Hw).
Qed.

Lemma ug_gic G phi : G ⊢C ug (skipf phi) -> G ⊢C gic phi.
Proof.
  intros H. unfold gic. fall B. unfold ug in H. finst H B. fex H w Hw. fdestr Hw Hw1 Hw2.
  fdestr Hw1 HBw _HCP. finst Hw2 B B. fmp Hw2 HBw. fex Hw2 C HC. fdestr HC HC12 _Htot.
  fdestr HC12 Hcov Hnx. fexists C. fsplit.
  - fall a. fintro Ha. fall y. fintro Hy. finst Hcov a. fmp Hcov Ha. finst Hcov y.
    unfold skipf in Hcov. fmp_conv Hcov Hy. fex Hcov y' Hy'. fdestr Hy' Hy'1 Hy'2.
    fexists y'. fsplit; [fconv_h Hy'1 | exact Hy'2].
  - fall y. fintro Hy. finst Hnx y. fmp Hnx Hy. fex Hnx x Hx. fexists x. unfold skipf in Hx. fconv_h Hx.
Qed.

Lemma ctx_forall_times (A : list form) n phi :
  (forall a, In a A -> closedf a) -> A ⊢C phi -> A ⊢C forall_times n phi.
Proof.
  intros HA D. induction n as [|n IH]; [exact D|].
  change (forall_times (S n) phi) with (∀ forall_times n phi). apply AllI_closed; [exact HA | exact IH].
Qed.

Lemma ug_ax_cp_ok : SU0 (forall_times 0 (ug ⊥)).
Proof. apply SU0_ug, ug_closed. exact I. Qed.

Theorem S0_ax_SU0 a : S0 a -> SU0 ⊢TC a.
Proof.
  intros [a' H | phi n Hc].
  - assert (Hcase : a' = ax_cp \/ In a' SUbase).
    { unfold Sbase in H. repeat (destruct H as [<-|H]; [first [now left | right; cbn; tauto] |]). destruct H. }
    destruct Hcase as [-> | Hb].
    + exists [forall_times 0 (ug ⊥)]. split; [intros b [<-|[]]; exact ug_ax_cp_ok|].
      apply (ug_cp _ ⊥). apply Ctx. now left.
    + exists [a']. split; [|apply Ctx; now left]. intros b [<-|[]]. now apply SU0_base.
  - pose proof (S_sound.fb_gic_inv n phi Hc) as Hfb.
    assert (Hc' : closedf (forall_times n (ug (skipf phi)))) by apply ug_closed, fb_skipf, Hfb.
    exists [forall_times n (ug (skipf phi))]. split; [intros b [<-|[]]; now apply SU0_ug|].
    apply ctx_forall_times; [intros b [<-|[]]; exact Hc'|].
    apply ug_gic. assert (D : [forall_times n (ug (skipf phi))] ⊢C forall_times n (ug (skipf phi)))
      by (apply Ctx; now left).
    pose proof (closed_inst _ n _ var Hc' D) as T. rewrite subst_var in T. exact T.
Qed.

Theorem S0_to_SU0 phi : S0 ⊢TC phi -> SU0 ⊢TC phi.
Proof. apply tprv_cut. exact S0_ax_SU0. Qed.
