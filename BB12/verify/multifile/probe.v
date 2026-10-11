(** Independent probe for the T12a proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB12_T12a.tm] is the declared machine
    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF---
    entry by entry (these 24 lines were generated from the machine string, not from the Coq file; K1 is never read
    and L1 is the halting transition, 1RZ in the standard string); (2) the main theorems have the stated types; (3)
    they use no axioms.  It also prints the definitions the statements use.  The 12-state setup names a state L, so
    directions are written TM.L / TM.R. *)

From BB8 Require BB12_T12a BB12_T12a_bound BB12_T12a_fgh BB10_n1_exact BB10_n1_fgh.
From BB8 Require Import Individual122.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB12_T12a.tm (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB12_T12a.tm (A, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB12_T12a.tm (B, 0) = Some (1, TM.L, C)).  Check (eq_refl : BB12_T12a.tm (B, 1) = Some (1, TM.L, F)).
Check (eq_refl : BB12_T12a.tm (C, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB12_T12a.tm (C, 1) = Some (0, TM.L, B)).
Check (eq_refl : BB12_T12a.tm (D, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB12_T12a.tm (D, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB12_T12a.tm (E, 0) = Some (1, TM.L, I)).  Check (eq_refl : BB12_T12a.tm (E, 1) = Some (0, TM.L, C)).
Check (eq_refl : BB12_T12a.tm (F, 0) = Some (0, TM.R, G)).  Check (eq_refl : BB12_T12a.tm (F, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB12_T12a.tm (G, 0) = Some (1, TM.R, H)).  Check (eq_refl : BB12_T12a.tm (G, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB12_T12a.tm (H, 0) = Some (1, TM.L, C)).  Check (eq_refl : BB12_T12a.tm (H, 1) = Some (0, TM.R, G)).
Check (eq_refl : BB12_T12a.tm (I, 0) = Some (0, TM.L, J)).  Check (eq_refl : BB12_T12a.tm (I, 1) = Some (0, TM.L, I)).
Check (eq_refl : BB12_T12a.tm (J, 0) = Some (1, TM.R, K)).  Check (eq_refl : BB12_T12a.tm (J, 1) = Some (0, TM.L, C)).
Check (eq_refl : BB12_T12a.tm (K, 0) = Some (0, TM.R, L)).  Check (eq_refl : BB12_T12a.tm (K, 1) = None).
Check (eq_refl : BB12_T12a.tm (L, 0) = Some (0, TM.R, F)).  Check (eq_refl : BB12_T12a.tm (L, 1) = None).

Print BB12_T12a.arrow.
Print BB12_T12a.F.
Print BB12_T12a.iter.
Check BB12_T12a.T_def.
Print BB12_T12a.JJ.
Print BB12_T12a_bound.ones.
Print BB12_T12a_bound.count1.
Print BB12_T12a_bound.sym_val.
Print BB12_T12a_bound.step.
Print BB12_T12a_bound.stepn.
Print BB12_T12a_bound.g0.
Print BB12_T12a_bound.fin.
Print BB12_T12a_bound.Wf.
Print BB10_n1_exact.score_value.
Print BB10_n1_fgh.fgh.
Print BB10_n1_fgh.f_omega.
Print BB10_n1_fgh.f_omega1.

Check BB12_T12a.halt.
Check BB12_T12a_bound.sigma_lower_bound.
Check BB12_T12a_bound.score_ge_exact.
Check BB12_T12a_bound.beats_n1.
Check BB10_n1_exact.score_closed.
Check BB12_T12a_fgh.fgh_lower2.

Print Assumptions BB12_T12a.halt.
Print Assumptions BB12_T12a_bound.sigma_lower_bound.
Print Assumptions BB12_T12a_bound.score_ge_exact.
Print Assumptions BB12_T12a_bound.beats_n1.
Print Assumptions BB12_T12a_fgh.fgh_lower2.
