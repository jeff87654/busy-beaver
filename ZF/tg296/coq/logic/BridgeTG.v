(** * BridgeTG: the code-level calculus vs. the set theory SUIR (coq/settheory/SU_def.v).
      thm_tg 1 <-> SUIR ⊢TC ⊥,  hence  enum_tg_halts <-> SUIR ⊢TC ⊥. *)
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From M254TG Require Import SU_def.
From M254TGL Require Import EnumTG ThmTG L1_TG SoundTG Comp_BundleTG.

Theorem bridge_tg : thm_tg 1 <-> @tprv _ _ falsity_on class SUIR falsity.
Proof. split; [exact thm_to_SUIR | exact SUIR_to_thm]. Qed.

Theorem enum_tg_SUIR : enum_tg_halts <-> @tprv _ _ falsity_on class SUIR falsity.
Proof. rewrite L1_TG. exact bridge_tg. Qed.

Print Assumptions enum_tg_SUIR.
