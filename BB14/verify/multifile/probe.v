(** Independent probe for the M14 proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB14_M14.tm] is the declared machine
    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LN1RF_1LJ0RA_1RA0LH_1LG1LH_1RK0LM_1RZ0LE_0LE0RJ_1LH1LM_0LH0LL_0LG1LN
    entry by entry (these 28 lines were generated from the machine string, not from the Coq file; the halting
    transition J0 (1RZ) is None), and the start configuration is the blank tape in state A; (2) the main theorems
    have the stated types; (3) they use no axioms.  It also prints the definitions the statements use.  The
    14-state setup names a state L, so directions are written TM.L / TM.R. *)

From BB8 Require BB14_M14 BB14_M14_bound.
From BB8 Require Import Individual142.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB14_M14.tm (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB14_M14.tm (A, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB14_M14.tm (B, 0) = Some (1, TM.R, I)).  Check (eq_refl : BB14_M14.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB14_M14.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB14_M14.tm (C, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB14_M14.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB14_M14.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB14_M14.tm (E, 0) = Some (1, TM.L, N)).  Check (eq_refl : BB14_M14.tm (E, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB14_M14.tm (F, 0) = Some (1, TM.L, J)).  Check (eq_refl : BB14_M14.tm (F, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB14_M14.tm (G, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB14_M14.tm (G, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB14_M14.tm (H, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB14_M14.tm (H, 1) = Some (1, TM.L, H)).
Check (eq_refl : BB14_M14.tm (I, 0) = Some (1, TM.R, K)).  Check (eq_refl : BB14_M14.tm (I, 1) = Some (0, TM.L, M)).
Check (eq_refl : BB14_M14.tm (J, 0) = None).  Check (eq_refl : BB14_M14.tm (J, 1) = Some (0, TM.L, E)).
Check (eq_refl : BB14_M14.tm (K, 0) = Some (0, TM.L, E)).  Check (eq_refl : BB14_M14.tm (K, 1) = Some (0, TM.R, J)).
Check (eq_refl : BB14_M14.tm (L, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB14_M14.tm (L, 1) = Some (1, TM.L, M)).
Check (eq_refl : BB14_M14.tm (M, 0) = Some (0, TM.L, H)).  Check (eq_refl : BB14_M14.tm (M, 1) = Some (0, TM.L, L)).
Check (eq_refl : BB14_M14.tm (N, 0) = Some (0, TM.L, G)).  Check (eq_refl : BB14_M14.tm (N, 1) = Some (1, TM.L, N)).

Print BB14_M14.iter.
Print BB14_M14_bound.f.
Print BB14_M14_bound.f_omega.
Print BB14_M14_bound.f_omega1.
Print BB14_M14_bound.f_omega2.
Print BB14_M14_bound.sym_val.
Print BB14_M14_bound.count1.
Print BB14_M14_bound.ones.

Check BB14_M14.halt.
Check BB14_M14_bound.score_exact.
Check BB14_M14_bound.sigma_lower_bound.
Check BB14_M14_bound.sigma_lower_bound_strong.

Print Assumptions BB14_M14.halt.
Print Assumptions BB14_M14_bound.score_exact.
Print Assumptions BB14_M14_bound.sigma_lower_bound.
Print Assumptions BB14_M14_bound.sigma_lower_bound_strong.
