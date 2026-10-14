(** Independent probe for the M13 proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB13_M13.tm] is the declared machine
    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_0LG1RI_1RE0RH_1LF0RC_1RM0LE_1LA1LE_0LL1LB_0RM1LL_1RZ1RH
    entry by entry (these 26 lines were generated from the machine string, not from the Coq file; the halting
    transition M0 (1RZ) is None), and the start configuration is the blank tape in state A; (2) the main theorems
    have the stated types; (3) they use no axioms.  It also prints the definitions the statements use.  The
    13-state setup names a state L, so directions are written TM.L / TM.R. *)

From BB8 Require BB13_M13 BB13_M13_bound.
From BB8 Require Import Individual132.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB13_M13.tm (A, 0) = Some (1, TM.L, B)).  Check (eq_refl : BB13_M13.tm (A, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB13_M13.tm (B, 0) = Some (1, TM.R, C)).  Check (eq_refl : BB13_M13.tm (B, 1) = Some (0, TM.L, A)).
Check (eq_refl : BB13_M13.tm (C, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB13_M13.tm (C, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB13_M13.tm (D, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB13_M13.tm (D, 1) = Some (1, TM.R, K)).
Check (eq_refl : BB13_M13.tm (E, 0) = Some (1, TM.R, F)).  Check (eq_refl : BB13_M13.tm (E, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB13_M13.tm (F, 0) = Some (0, TM.L, G)).  Check (eq_refl : BB13_M13.tm (F, 1) = Some (1, TM.R, I)).
Check (eq_refl : BB13_M13.tm (G, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB13_M13.tm (G, 1) = Some (0, TM.R, H)).
Check (eq_refl : BB13_M13.tm (H, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB13_M13.tm (H, 1) = Some (0, TM.R, C)).
Check (eq_refl : BB13_M13.tm (I, 0) = Some (1, TM.R, M)).  Check (eq_refl : BB13_M13.tm (I, 1) = Some (0, TM.L, E)).
Check (eq_refl : BB13_M13.tm (J, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB13_M13.tm (J, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB13_M13.tm (K, 0) = Some (0, TM.L, L)).  Check (eq_refl : BB13_M13.tm (K, 1) = Some (1, TM.L, B)).
Check (eq_refl : BB13_M13.tm (L, 0) = Some (0, TM.R, M)).  Check (eq_refl : BB13_M13.tm (L, 1) = Some (1, TM.L, L)).
Check (eq_refl : BB13_M13.tm (M, 0) = None).  Check (eq_refl : BB13_M13.tm (M, 1) = Some (1, TM.R, H)).

Print BB13_M13.iter.
Print BB13_M13_bound.f.
Print BB13_M13_bound.f_omega.
Print BB13_M13_bound.f_omega1.
Print BB13_M13_bound.f_omega2.
Print BB13_M13_bound.sym_val.
Print BB13_M13_bound.count1.
Print BB13_M13_bound.ones.

Check BB13_M13.halt.
Check BB13_M13_bound.score_exact.
Check BB13_M13_bound.sigma_lower_bound.
Check BB13_M13_bound.sigma_lower_bound_strong.

Print Assumptions BB13_M13.halt.
Print Assumptions BB13_M13_bound.score_exact.
Print Assumptions BB13_M13_bound.sigma_lower_bound.
Print Assumptions BB13_M13_bound.sigma_lower_bound_strong.
