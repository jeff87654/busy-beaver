(** Probe for the comparison with n1 (run after compile_clean.sh and compile_vs_n1.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe_vs_n1.v).
    It checks n1's table against its machine string 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RZ0LC
    (lines generated from the string; J0 = 1RZ is None), prints the statement and runs Print Assumptions on it. *)

From BB8 Require BB10_n1 BB10_n1_bound BB11_M11b_vs_n1.
From BB8 Require Import Individual102.
Local Open Scope sym_scope.

Check (eq_refl : BB10_n1.tm (A, 0) = Some (1, R, B)).  Check (eq_refl : BB10_n1.tm (A, 1) = Some (0, R, A)).
Check (eq_refl : BB10_n1.tm (B, 0) = Some (1, L, C)).  Check (eq_refl : BB10_n1.tm (B, 1) = Some (1, L, F)).
Check (eq_refl : BB10_n1.tm (C, 0) = Some (1, R, D)).  Check (eq_refl : BB10_n1.tm (C, 1) = Some (0, L, B)).
Check (eq_refl : BB10_n1.tm (D, 0) = Some (1, R, A)).  Check (eq_refl : BB10_n1.tm (D, 1) = Some (1, L, E)).
Check (eq_refl : BB10_n1.tm (E, 0) = Some (1, L, I)).  Check (eq_refl : BB10_n1.tm (E, 1) = Some (0, L, C)).
Check (eq_refl : BB10_n1.tm (F, 0) = Some (0, R, G)).  Check (eq_refl : BB10_n1.tm (F, 1) = Some (1, L, D)).
Check (eq_refl : BB10_n1.tm (G, 0) = Some (1, R, H)).  Check (eq_refl : BB10_n1.tm (G, 1) = Some (1, L, G)).
Check (eq_refl : BB10_n1.tm (H, 0) = Some (1, L, C)).  Check (eq_refl : BB10_n1.tm (H, 1) = Some (0, R, G)).
Check (eq_refl : BB10_n1.tm (I, 0) = Some (0, L, J)).  Check (eq_refl : BB10_n1.tm (I, 1) = Some (0, L, I)).
Check (eq_refl : BB10_n1.tm (J, 0) = None).  Check (eq_refl : BB10_n1.tm (J, 1) = Some (0, L, C)).

Print BB10_n1_bound.ones.
Check BB11_M11b_vs_n1.M11_beats_n1.
Print Assumptions BB11_M11b_vs_n1.M11_beats_n1.
