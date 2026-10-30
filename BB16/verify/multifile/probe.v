(** Independent probe for the BB16 proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB16_halt_fw3.tm] is the declared
    machine
    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP1RM_1RZ1LI
    entry by entry (these 32 checks were generated from the machine string, not from the Coq file; the halting
    transition P0 (1RZ) is None), and the start configuration is the blank tape in state A; (2) the main theorems
    have the stated types; (3) they use no axioms.  It also prints the definitions the statements use.  The
    16-state setup names states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB16_halt_fw3.
From BB8 Require Import Individual162.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB16_halt_fw3.tm (A, 0) = Some (1, TM.L, B)).  Check (eq_refl : BB16_halt_fw3.tm (A, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB16_halt_fw3.tm (B, 0) = Some (1, TM.R, C)).  Check (eq_refl : BB16_halt_fw3.tm (B, 1) = Some (0, TM.L, A)).
Check (eq_refl : BB16_halt_fw3.tm (C, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB16_halt_fw3.tm (C, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB16_halt_fw3.tm (D, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB16_halt_fw3.tm (D, 1) = Some (1, TM.R, K)).
Check (eq_refl : BB16_halt_fw3.tm (E, 0) = Some (1, TM.R, F)).  Check (eq_refl : BB16_halt_fw3.tm (E, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB16_halt_fw3.tm (F, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB16_halt_fw3.tm (F, 1) = Some (1, TM.R, I)).
Check (eq_refl : BB16_halt_fw3.tm (G, 0) = Some (1, TM.R, M)).  Check (eq_refl : BB16_halt_fw3.tm (G, 1) = Some (0, TM.L, M)).
Check (eq_refl : BB16_halt_fw3.tm (H, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB16_halt_fw3.tm (H, 1) = Some (0, TM.R, C)).
Check (eq_refl : BB16_halt_fw3.tm (I, 0) = Some (0, TM.R, N)).  Check (eq_refl : BB16_halt_fw3.tm (I, 1) = Some (0, TM.L, E)).
Check (eq_refl : BB16_halt_fw3.tm (J, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB16_halt_fw3.tm (J, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB16_halt_fw3.tm (K, 0) = Some (0, TM.L, L)).  Check (eq_refl : BB16_halt_fw3.tm (K, 1) = Some (1, TM.L, B)).
Check (eq_refl : BB16_halt_fw3.tm (L, 0) = Some (0, TM.R, M)).  Check (eq_refl : BB16_halt_fw3.tm (L, 1) = Some (1, TM.L, L)).
Check (eq_refl : BB16_halt_fw3.tm (M, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB16_halt_fw3.tm (M, 1) = Some (1, TM.R, H)).
Check (eq_refl : BB16_halt_fw3.tm (N, 0) = Some (0, TM.R, O)).  Check (eq_refl : BB16_halt_fw3.tm (N, 1) = Some (0, TM.L, O)).
Check (eq_refl : BB16_halt_fw3.tm (O, 0) = Some (1, TM.L, P)).  Check (eq_refl : BB16_halt_fw3.tm (O, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB16_halt_fw3.tm (P, 0) = None).  Check (eq_refl : BB16_halt_fw3.tm (P, 1) = Some (1, TM.L, I)).

Print BB16_halt_fw3.iter.
Print BB16_halt_fw3.f.
Print BB16_halt_fw3.f_omega.
Print BB16_halt_fw3.f_omega1.
Print BB16_halt_fw3.f_omega2.
Print BB16_halt_fw3.f_omega3.
Print BB16_halt_fw3.sym_val.
Print BB16_halt_fw3.count1.
Print BB16_halt_fw3.ones.

Check BB16_halt_fw3.halt.
Check BB16_halt_fw3.halt_f_omega3.
Check BB16_halt_fw3.score_exact.
Check BB16_halt_fw3.sigma_lower_bound.

Print Assumptions BB16_halt_fw3.halt.
Print Assumptions BB16_halt_fw3.halt_f_omega3.
Print Assumptions BB16_halt_fw3.score_exact.
Print Assumptions BB16_halt_fw3.sigma_lower_bound.
