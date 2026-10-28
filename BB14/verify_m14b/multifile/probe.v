(** Independent probe for the M14b proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB14_M14b.tm] is the declared machine
    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LN0LL_0LH1LK_1RZ0LH_0RJ0LI
    entry by entry (these 28 lines were generated from the machine string, not from the Coq file; the halting
    transition M0 (1RZ) is None), and the start configuration is the blank tape in state A; (2) the main theorems
    have the stated types; (3) they use no axioms.  It also prints the definitions the statements use.  The
    14-state setup names a state L, so directions are written TM.L / TM.R. *)

From BB8 Require BB14_M14b BB14_M14b_bound.
From BB8 Require Import Individual142.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB14_M14b.tm (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB14_M14b.tm (A, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB14_M14b.tm (B, 0) = Some (1, TM.R, I)).  Check (eq_refl : BB14_M14b.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB14_M14b.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB14_M14b.tm (C, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB14_M14b.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB14_M14b.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB14_M14b.tm (E, 0) = Some (1, TM.L, K)).  Check (eq_refl : BB14_M14b.tm (E, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB14_M14b.tm (F, 0) = Some (1, TM.R, M)).  Check (eq_refl : BB14_M14b.tm (F, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB14_M14b.tm (G, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB14_M14b.tm (G, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB14_M14b.tm (H, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB14_M14b.tm (H, 1) = Some (1, TM.L, H)).
Check (eq_refl : BB14_M14b.tm (I, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB14_M14b.tm (I, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB14_M14b.tm (J, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB14_M14b.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB14_M14b.tm (K, 0) = Some (0, TM.L, N)).  Check (eq_refl : BB14_M14b.tm (K, 1) = Some (0, TM.L, L)).
Check (eq_refl : BB14_M14b.tm (L, 0) = Some (0, TM.L, H)).  Check (eq_refl : BB14_M14b.tm (L, 1) = Some (1, TM.L, K)).
Check (eq_refl : BB14_M14b.tm (M, 0) = None).  Check (eq_refl : BB14_M14b.tm (M, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB14_M14b.tm (N, 0) = Some (0, TM.R, J)).  Check (eq_refl : BB14_M14b.tm (N, 1) = Some (0, TM.L, I)).

Print BB14_M14b.iter.
Print BB14_M14b_bound.f.
Print BB14_M14b_bound.f_omega.
Print BB14_M14b_bound.f_omega1.
Print BB14_M14b_bound.f_omega2.
Print BB14_M14b_bound.sym_val.
Print BB14_M14b_bound.count1.
Print BB14_M14b_bound.ones.

Check BB14_M14b.halt.
Check BB14_M14b_bound.score_exact.
Check BB14_M14b_bound.sigma_lower_bound.

Print Assumptions BB14_M14b.halt.
Print Assumptions BB14_M14b_bound.score_exact.
Print Assumptions BB14_M14b_bound.sigma_lower_bound.
