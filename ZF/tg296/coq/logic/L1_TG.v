(** * L1_TG: the abstract enumerator of the zfc_254 source halts iff the code-level calculus
    derives the code 1 (= F = Rel(0,0) = v0 e. v0). *)
From M254TGL Require Import EnumTG ThmTG L1_SoundTG L1_CompTG.

Theorem L1_TG : enum_tg_halts <-> thm_tg 1.
Proof. split; [exact enum_sound | exact enum_complete]. Qed.

Print Assumptions L1_TG.
