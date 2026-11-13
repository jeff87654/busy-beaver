(** Independent probe for the C4 proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB11_C4.tm] is the declared machine
    1RB1RH_1RC0LD_1LD1RJ_1LE1LB_1LF1LE_1RG0LE_1RA1RG_0LI1LF_0RC1LI_1RK0RG_---0LB
    entry by entry (these 22 checks were generated from the machine string, not from the Coq file; the halting
    transition, K0, is None), and the start configuration is the blank tape in state A; (2) the main theorems have
    the stated types; (3) they use no axioms.  It also prints the definitions the statements use. *)

From BB8 Require BB11_C4 BB11_C4_bound BB11_M11b BB11_M11b_fgh BB11_C4_cmp BB12_M12 BB12_M12_bound BB11_C4_vs_M12.
From BB8 Require Import Individual112.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB11_C4.tm (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB11_C4.tm (A, 1) = Some (1, TM.R, H)).
Check (eq_refl : BB11_C4.tm (B, 0) = Some (1, TM.R, C)).  Check (eq_refl : BB11_C4.tm (B, 1) = Some (0, TM.L, D)).
Check (eq_refl : BB11_C4.tm (C, 0) = Some (1, TM.L, D)).  Check (eq_refl : BB11_C4.tm (C, 1) = Some (1, TM.R, J)).
Check (eq_refl : BB11_C4.tm (D, 0) = Some (1, TM.L, E)).  Check (eq_refl : BB11_C4.tm (D, 1) = Some (1, TM.L, B)).
Check (eq_refl : BB11_C4.tm (E, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB11_C4.tm (E, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB11_C4.tm (F, 0) = Some (1, TM.R, G)).  Check (eq_refl : BB11_C4.tm (F, 1) = Some (0, TM.L, E)).
Check (eq_refl : BB11_C4.tm (G, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB11_C4.tm (G, 1) = Some (1, TM.R, G)).
Check (eq_refl : BB11_C4.tm (H, 0) = Some (0, TM.L, I)).  Check (eq_refl : BB11_C4.tm (H, 1) = Some (1, TM.L, F)).
Check (eq_refl : BB11_C4.tm (I, 0) = Some (0, TM.R, C)).  Check (eq_refl : BB11_C4.tm (I, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB11_C4.tm (J, 0) = Some (1, TM.R, K)).  Check (eq_refl : BB11_C4.tm (J, 1) = Some (0, TM.R, G)).
Check (eq_refl : BB11_C4.tm (K, 0) = None).  Check (eq_refl : BB11_C4.tm (K, 1) = Some (0, TM.L, B)).

Print BB11_C4.iter.
Print BB11_C4.W.
Print BB11_C4_bound.f.
Print BB11_C4_bound.f_omega.
Print BB11_C4_bound.f_omega1.
Print BB11_C4_bound.f_omega2.
Print BB11_C4.sym_val.
Print BB11_C4.count1.
Print BB11_C4.ones.
Print BB11_M11b_fgh.ones.
Print BB12_M12_bound.ones.

Check BB11_C4.halt.
Check BB11_C4.score_exact.
Check BB11_C4_bound.sigma_lower_bound.
Check BB11_C4_bound.sigma_lower_bound_34.
Check BB11_C4_bound.beats_M11b.
Check BB11_C4_bound.beats_M12_lower.
Check BB11_C4_cmp.beats_M11b_score.
Check BB11_C4_vs_M12.beats_M12_exact.
Check BB11_C4_vs_M12.beats_M12_score.

Print Assumptions BB11_C4.halt.
Print Assumptions BB11_C4.score_exact.
Print Assumptions BB11_C4_bound.sigma_lower_bound.
Print Assumptions BB11_C4_bound.sigma_lower_bound_34.
Print Assumptions BB11_C4_bound.beats_M11b.
Print Assumptions BB11_C4_bound.beats_M12_lower.
Print Assumptions BB11_C4_cmp.beats_M11b_score.
Print Assumptions BB11_C4_vs_M12.beats_M12_exact.
Print Assumptions BB11_C4_vs_M12.beats_M12_score.
