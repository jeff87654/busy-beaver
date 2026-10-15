(** * SU_complete: ZF + GU ⊢ ⊥ → SU0 ⊢ ⊥ (the bisimulation quotient interprets ZF + GU in SU0).

    ZFc + GU ⊢ ⊥  →  ZF0 + INF_lib + GU0 ⊢ ⊥     (inf_or_to_zf; GU_of_GU0)
                  →  SU0 ⊢ ⊥                      (qt_tprv: S_ZF0inf + S0_to_SU0; SU_GU0) *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From M254S Require Import S_def S_qt S_quot S_ax.
From M254TG Require Import SU_def SU_s0 SU_gu SU_gru SU_quot.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma tprv_ax (T : form -> Prop) a : T a -> T ⊢TC a.
Proof. intros H. exists [a]. split; [intros b [<-|[]]; exact H | apply Ctx; now left]. Qed.

Definition TZG (a : form) : Prop := (ZF0 a \/ a = INF_lib) \/ a = GU0.

Lemma TGU_to_TZG : T_GU ⊢TC ⊥ -> TZG ⊢TC ⊥.
Proof.
  apply tprv_cut. intros a [[Ha | ->] | ->].
  - apply tprv_ax. left. now left.
  - apply (tprv_cut (fun a => ZF0 a \/ a = INF_lib)); [|exact inf_or_to_zf].
    intros b Hb. apply tprv_ax. now left.
  - exists (GU0 :: ZF0base ++ Ax_gru). split.
    + intros b [<-|Hb]; [now right|]. left. left. apply in_app_or in Hb as [Hb|Hb].
      * now apply ZF0_base.
      * now apply Ax_gru_ok.
    + apply GU_of_GU0.
      * intros b Hb. right. apply in_or_app. now left.
      * intros b Hb. right. apply in_or_app. now right.
      * apply Ctx. now left.
Qed.

Lemma TZG_qt a : TZG a -> SU0 ⊢TC qtS a.
Proof.
  intros [Ha | ->].
  - apply S0_to_SU0. exact (S_ZF0inf a Ha).
  - exact SU_GU0.
Qed.

Theorem GU_to_SU0 : T_GU ⊢TC ⊥ -> SU0 ⊢TC ⊥.
Proof.
  intros H. apply TGU_to_TZG in H.
  exact (qt_tprv Eqv Mem Eqv_subst Mem_subst _ SU0 ⊥ TZG_qt H).
Qed.

Lemma SU0_SUIR phi : SU0 ⊢TC phi -> SUIR ⊢TC phi.
Proof. intros [A [HA D]]. exists A. split; [intros b Hb; left; now apply HA | exact D]. Qed.

Theorem GU_to_SUIR : T_GU ⊢TC ⊥ -> SUIR ⊢TC ⊥.
Proof. intros H. apply SU0_SUIR, GU_to_SU0, H. Qed.
