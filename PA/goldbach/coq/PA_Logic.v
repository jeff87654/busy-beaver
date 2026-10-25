(** * PA_Logic: the abstract enumerator of the frozen pagb machine halts iff PAeq ⊢TC GC_form. *)
From PAGB Require Import Spec PA_Thm PA_CompCode PA_Enum PA_L1.

Theorem enum_halts_iff_PA_GC : enum_halts <-> PA_proves_GC.
Proof. rewrite L1. exact thm_F_iff. Qed.

Print Assumptions enum_halts_iff_PA_GC.
