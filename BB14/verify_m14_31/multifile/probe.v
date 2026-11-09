(** Independent probe for the M14_31 (Argon) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB14_M14_31.tm] is the declared machine
    1RB1RA_1RI1RC_0LD1LG_0RE1LD_0RN1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_0LK0LH_1LM---
    entry by entry (these 28 checks were generated from the machine string, not from the Coq file; the halting
    transition (---) is None; N1 is read on a 1), and the start configuration is the blank tape in state A;
    (2) the main theorems have the stated types; (3) they use no axioms.  It also prints the definitions the
    statements use.  The setup names states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB14_M14_31 BB14_M14_31_cmp.
From BB8 Require Import Individual142.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB14_M14_31.tm (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB14_M14_31.tm (A, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB14_M14_31.tm (B, 0) = Some (1, TM.R, I)).  Check (eq_refl : BB14_M14_31.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB14_M14_31.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB14_M14_31.tm (C, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB14_M14_31.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB14_M14_31.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB14_M14_31.tm (E, 0) = Some (0, TM.R, N)).  Check (eq_refl : BB14_M14_31.tm (E, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB14_M14_31.tm (F, 0) = Some (1, TM.R, M)).  Check (eq_refl : BB14_M14_31.tm (F, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB14_M14_31.tm (G, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB14_M14_31.tm (G, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB14_M14_31.tm (H, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB14_M14_31.tm (H, 1) = Some (1, TM.L, H)).
Check (eq_refl : BB14_M14_31.tm (I, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB14_M14_31.tm (I, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB14_M14_31.tm (J, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB14_M14_31.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB14_M14_31.tm (K, 0) = Some (0, TM.L, L)).  Check (eq_refl : BB14_M14_31.tm (K, 1) = Some (0, TM.L, L)).
Check (eq_refl : BB14_M14_31.tm (L, 0) = Some (0, TM.L, H)).  Check (eq_refl : BB14_M14_31.tm (L, 1) = Some (1, TM.L, K)).
Check (eq_refl : BB14_M14_31.tm (M, 0) = Some (0, TM.L, K)).  Check (eq_refl : BB14_M14_31.tm (M, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB14_M14_31.tm (N, 0) = Some (1, TM.L, M)).  Check (eq_refl : BB14_M14_31.tm (N, 1) = None).

Print BB14_M14_31.iter.
Print BB14_M14_31.f.
Print BB14_M14_31.f_omega.
Print BB14_M14_31.f_omega1.
Print BB14_M14_31.f_omega2.
Print BB14_M14_31.sym_val.
Print BB14_M14_31.count1.
Print BB14_M14_31.ones.

Check BB14_M14_31.halt.
Check BB14_M14_31.score_exact.
Check BB14_M14_31.sigma_bound.
Check BB14_M14_31.sigma_bound_fw1.
Check BB14_M14_31_cmp.beats_M14d_18.
Check BB14_M14_31_cmp.beats_M14d_18_fw1.

Print Assumptions BB14_M14_31.halt.
Print Assumptions BB14_M14_31.score_exact.
Print Assumptions BB14_M14_31.sigma_bound.
Print Assumptions BB14_M14_31.sigma_bound_fw1.
Print Assumptions BB14_M14_31_cmp.beats_M14d_18.
Print Assumptions BB14_M14_31_cmp.beats_M14d_18_fw1.
