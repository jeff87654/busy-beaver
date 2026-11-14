(** Independent probe for 44-B and 44-A (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . Local probe.v).

    Coq confirms here, by conversion, that (1) the compiled tables [BB44B_rules.tm] and [BB44A_rules.tm] are the machines
      44-B  1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD   (halt A3 = 1RZ)
      44-A  1LB2LC3RA0RB_2RC1RZ2LB3LB_1LB2RC3RA1LD_2RC1LC3RD2LD   (halt B1 = 1RZ)
    entry by entry (32 checks generated from the strings, not from the Coq files; the halting transition is None in
    busycoq; sigma counts the nonzero cells, which the halting write does not change), and the start configuration is
    the blank tape in state A; (2) the main theorems have the stated types; (3) they use no axioms.  [BB44_run.sigma] is
    44-C's exact score (BB44/verify_44c, byte-identical copies). *)

From Local Require Import Individual44.
From Local Require BB44_run BB44_bound BB44A_rules BB44A_run BB44A_cmp BB44B_rules BB44B_run BB44B_cmp.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB44B_rules.tm (A, S0) = Some (S1, R, B)).  Check (eq_refl : BB44B_rules.tm (A, S1) = Some (S2, L, C)).  Check (eq_refl : BB44B_rules.tm (A, S2) = Some (S3, R, A)).  Check (eq_refl : BB44B_rules.tm (A, S3) = None).
Check (eq_refl : BB44B_rules.tm (B, S0) = Some (S2, R, C)).  Check (eq_refl : BB44B_rules.tm (B, S1) = Some (S3, L, B)).  Check (eq_refl : BB44B_rules.tm (B, S2) = Some (S2, L, B)).  Check (eq_refl : BB44B_rules.tm (B, S3) = Some (S0, L, C)).
Check (eq_refl : BB44B_rules.tm (C, S0) = Some (S1, L, B)).  Check (eq_refl : BB44B_rules.tm (C, S1) = Some (S2, R, C)).  Check (eq_refl : BB44B_rules.tm (C, S2) = Some (S3, R, A)).  Check (eq_refl : BB44B_rules.tm (C, S3) = Some (S1, L, D)).
Check (eq_refl : BB44B_rules.tm (D, S0) = Some (S2, R, C)).  Check (eq_refl : BB44B_rules.tm (D, S1) = Some (S1, L, C)).  Check (eq_refl : BB44B_rules.tm (D, S2) = Some (S3, R, D)).  Check (eq_refl : BB44B_rules.tm (D, S3) = Some (S2, L, D)).
Check (eq_refl : BB44A_rules.tm (A, S0) = Some (S1, L, B)).  Check (eq_refl : BB44A_rules.tm (A, S1) = Some (S2, L, C)).  Check (eq_refl : BB44A_rules.tm (A, S2) = Some (S3, R, A)).  Check (eq_refl : BB44A_rules.tm (A, S3) = Some (S0, R, B)).
Check (eq_refl : BB44A_rules.tm (B, S0) = Some (S2, R, C)).  Check (eq_refl : BB44A_rules.tm (B, S1) = None).  Check (eq_refl : BB44A_rules.tm (B, S2) = Some (S2, L, B)).  Check (eq_refl : BB44A_rules.tm (B, S3) = Some (S3, L, B)).
Check (eq_refl : BB44A_rules.tm (C, S0) = Some (S1, L, B)).  Check (eq_refl : BB44A_rules.tm (C, S1) = Some (S2, R, C)).  Check (eq_refl : BB44A_rules.tm (C, S2) = Some (S3, R, A)).  Check (eq_refl : BB44A_rules.tm (C, S3) = Some (S1, L, D)).
Check (eq_refl : BB44A_rules.tm (D, S0) = Some (S2, R, C)).  Check (eq_refl : BB44A_rules.tm (D, S1) = Some (S1, L, C)).  Check (eq_refl : BB44A_rules.tm (D, S2) = Some (S3, R, D)).  Check (eq_refl : BB44A_rules.tm (D, S3) = Some (S2, L, D)).

Print BB44B_run.sigma.
Print BB44B_run.nonzero_cells.
Print BB44A_run.sigma.
Print BB44_run.sigma.
Print BB44B_cmp.f_omega.
Print BB44_bound.knuth.

Check BB44A_run.bb44A_halts.
Check BB44A_run.reaches_final.
Check BB44A_run.final_halted.
Check BB44A_run.c_final_nonzero.
Check BB44A_run.c_final_head.
Check BB44A_cmp.sigma_A_closed.
Check BB44A_cmp.BB44A_beats_C.
Check BB44A_cmp.BB44A_beats_official.
Check BB44B_run.bb44B_halts.
Check BB44B_run.reaches_final.
Check BB44B_run.final_halted.
Check BB44B_run.c_final_nonzero.
Check BB44B_run.c_final_head.
Check BB44B_cmp.sigma_B_closed.
Check BB44B_cmp.BB44B_beats_A.
Check BB44B_cmp.BB44B_beats_C.
Check BB44B_cmp.BB44B_beats_official.
Check BB44B_cmp.sigma_B_f_omega.

Print Assumptions BB44A_run.bb44A_halts.
Print Assumptions BB44A_run.reaches_final.
Print Assumptions BB44A_run.final_halted.
Print Assumptions BB44A_run.c_final_nonzero.
Print Assumptions BB44A_run.c_final_head.
Print Assumptions BB44A_cmp.sigma_A_closed.
Print Assumptions BB44A_cmp.BB44A_beats_C.
Print Assumptions BB44A_cmp.BB44A_beats_official.
Print Assumptions BB44B_run.bb44B_halts.
Print Assumptions BB44B_run.reaches_final.
Print Assumptions BB44B_run.final_halted.
Print Assumptions BB44B_run.c_final_nonzero.
Print Assumptions BB44B_run.c_final_head.
Print Assumptions BB44B_cmp.sigma_B_closed.
Print Assumptions BB44B_cmp.BB44B_beats_A.
Print Assumptions BB44B_cmp.BB44B_beats_C.
Print Assumptions BB44B_cmp.BB44B_beats_official.
Print Assumptions BB44B_cmp.sigma_B_f_omega.
