(** * Logic_GU_TG: the m254tg enumerator halts iff ZF + GU is inconsistent
    (with m254tg-settheory's SU_equicons: SUIR ⊢TC ⊥ <-> T_GU ⊢TC ⊥, T_GU = Std_iface.ZFc + GU). *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Std_iface.
From M254TG Require Import SU_def SU_gu SU_main.
From M254TGL Require Import EnumTG BridgeTG.

Theorem enum_tg_GU : enum_tg_halts <-> @tprv _ _ falsity_on class T_GU falsity.
Proof. rewrite enum_tg_SUIR. exact SU_equicons. Qed.

Theorem enum_tg_GUR : enum_tg_halts <-> @tprv _ _ falsity_on class T_GUR falsity.
Proof. rewrite enum_tg_SUIR. exact SU_equicons_R. Qed.

Print Assumptions enum_tg_GU.
Print Assumptions enum_tg_GUR.
