(** * SU_main: SUIR (the ZF + GU machine's set theory) is equiconsistent with ZF + GU.

      GU_to_SUIR   : T_GU ⊢TC ⊥ -> SUIR ⊢TC ⊥      (SU_complete: bisimulation quotient)
      SU_to_TGUR   : SUIR ⊢TC ⊥ -> T_GUR ⊢TC ⊥     (SU_sound: relativization to ⋃_α V_α)
      GU_reg_relcon: T_GUR ⊢TC ⊥ -> T_GU ⊢TC ⊥     (SU_reg: regcon's WF relativization + GU)

    T_GU = Std_iface.ZFc + GU, T_GUR = T_GU + Reg, GU = ∀x ∃u (x ∈ u ∧ Gru u), Gru = set.mm df-gru. *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_tr Std_gen Std_iface.
From M254S Require Import S_def.
From M254TG Require Import SU_def SU_gu SU_complete SU_sound SU_reg.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Theorem SU_equicons : SUIR ⊢TC ⊥ <-> T_GU ⊢TC ⊥.
Proof. split; [intros H; exact (GU_reg_relcon (SU_to_TGUR H)) | exact GU_to_SUIR]. Qed.

Theorem SU_equicons_R : SUIR ⊢TC ⊥ <-> T_GUR ⊢TC ⊥.
Proof. split; [exact SU_to_TGUR | intros H; exact (GU_to_SUIR (GU_reg_relcon H))]. Qed.

Theorem SU0_equicons : SU0 ⊢TC ⊥ <-> T_GU ⊢TC ⊥.
Proof. split; [intros H; apply SU_equicons, SU0_SUIR, H | exact GU_to_SU0]. Qed.
