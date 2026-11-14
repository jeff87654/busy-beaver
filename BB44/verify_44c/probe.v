(** Independent probe for the 44-C (BB(4,4)) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q ../verify TM44 -Q . Local probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table [tm] is the machine
    1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD
    entry by entry (16 checks generated from the machine string, not from the Coq file; the halting
    transition A2 = 1RZ is None in busycoq; sigma counts the tape after its write), and the start
    configuration is the blank tape in state A; (2) the main theorems have the stated types; (3) they use no
    axioms.  It also prints the definitions the statements use. *)

From Local Require Import Individual44 BB44_rules BB44_run BB44_bound.
(* the comparison with the previous entry loads ../verify (logical path TM44) too: compile with -Q ../verify TM44 *)
From Local Require BB44C_vs_loader3229.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : tm (A, S0) = Some (S1, R, B)).  Check (eq_refl : tm (A, S1) = Some (S3, L, B)).  Check (eq_refl : tm (A, S2) = None).  Check (eq_refl : tm (A, S3) = Some (S2, R, A)).
Check (eq_refl : tm (B, S0) = Some (S1, L, C)).  Check (eq_refl : tm (B, S1) = Some (S3, R, B)).  Check (eq_refl : tm (B, S2) = Some (S1, L, D)).  Check (eq_refl : tm (B, S3) = Some (S2, R, A)).
Check (eq_refl : tm (C, S0) = Some (S3, R, B)).  Check (eq_refl : tm (C, S1) = Some (S2, L, C)).  Check (eq_refl : tm (C, S2) = Some (S1, L, C)).  Check (eq_refl : tm (C, S3) = Some (S3, L, C)).
Check (eq_refl : tm (D, S0) = Some (S3, R, B)).  Check (eq_refl : tm (D, S1) = Some (S1, L, B)).  Check (eq_refl : tm (D, S2) = Some (S3, L, D)).  Check (eq_refl : tm (D, S3) = Some (S2, R, D)).

Print BB44_bound.knuth.
Print BB44_run.sigma.
Print BB44_run.final_cells.
Print BB44_run.c_final.
Print BB44_rules.Bcfg.
Print BB44_rules.g.

Check BB44_run.bb44_halts.
Check BB44_run.reaches_final.
Check BB44_run.final_halted.
Check BB44_run.final_cells_count.
Check BB44_run.final_cells_all_nonblank.
Check BB44_bound.sigma_exact_closed_form.
Check BB44_bound.sigma_beats_official_bb44.
Check BB44_bound.bb44_new_champion_main.
Check BB44C_vs_loader3229.knuth_same.
Check BB44C_vs_loader3229.beats_loader3229_exact.
Check BB44C_vs_loader3229.beats_loader3229_score.

Print Assumptions BB44_run.bb44_halts.
Print Assumptions BB44_run.reaches_final.
Print Assumptions BB44_run.final_halted.
Print Assumptions BB44_run.final_cells_count.
Print Assumptions BB44_run.final_cells_all_nonblank.
Print Assumptions BB44_bound.sigma_exact_closed_form.
Print Assumptions BB44_bound.sigma_beats_official_bb44.
Print Assumptions BB44_bound.bb44_new_champion_main.
Print Assumptions BB44C_vs_loader3229.knuth_same.
Print Assumptions BB44C_vs_loader3229.beats_loader3229_exact.
Print Assumptions BB44C_vs_loader3229.beats_loader3229_score.
