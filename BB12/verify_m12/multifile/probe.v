(** Independent probe for the M12 proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB12_M12.tm] is the declared machine
    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_1RZ0LL_0LH1LK
    entry by entry (these 24 lines were generated from the machine string, not from the Coq file; the halting
    transition K0 (1RZ) is None), and the start configuration is the blank tape in state A; (2) the main theorems
    have the stated types; (3) they use no axioms.  It also prints the definitions the statements use.  The
    12-state setup names a state L, so directions are written TM.L / TM.R. *)

From BB8 Require BB12_M12 BB12_M12_bound.
From BB8 Require Import Individual122.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB12_M12.tm (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB12_M12.tm (A, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB12_M12.tm (B, 0) = Some (1, TM.R, I)).  Check (eq_refl : BB12_M12.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB12_M12.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB12_M12.tm (C, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB12_M12.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB12_M12.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB12_M12.tm (E, 0) = Some (1, TM.L, K)).  Check (eq_refl : BB12_M12.tm (E, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB12_M12.tm (F, 0) = Some (1, TM.R, G)).  Check (eq_refl : BB12_M12.tm (F, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB12_M12.tm (G, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB12_M12.tm (G, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB12_M12.tm (H, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB12_M12.tm (H, 1) = Some (1, TM.L, H)).
Check (eq_refl : BB12_M12.tm (I, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB12_M12.tm (I, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB12_M12.tm (J, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB12_M12.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB12_M12.tm (K, 0) = None).  Check (eq_refl : BB12_M12.tm (K, 1) = Some (0, TM.L, L)).
Check (eq_refl : BB12_M12.tm (L, 0) = Some (0, TM.L, H)).  Check (eq_refl : BB12_M12.tm (L, 1) = Some (1, TM.L, K)).

Print BB12_M12.iter.
Print BB12_M12_bound.f.
Print BB12_M12_bound.f_omega.
Print BB12_M12_bound.f_omega1.
Print BB12_M12_bound.f_omega2.
Print BB12_M12_bound.sym_val.
Print BB12_M12_bound.count1.
Print BB12_M12_bound.ones.

Check BB12_M12.halt.
Check BB12_M12_bound.score_exact.
Check BB12_M12_bound.sigma_lower_bound_strong.
Check BB12_M12_bound.sigma_lower_bound_m12.

Print Assumptions BB12_M12.halt.
Print Assumptions BB12_M12_bound.score_exact.
Print Assumptions BB12_M12_bound.sigma_lower_bound_strong.
Print Assumptions BB12_M12_bound.sigma_lower_bound_m12.
