(** Independent probe for the 54-L (BB(5,4)) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . Local probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table [tm] is the machine
    1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE
    entry by entry (20 checks generated from the machine string, not from the Coq file; the halting
    transition B1 = 1RZ is None in busycoq; sigma counts the tape after its write), and the start
    configuration is the blank tape in state A; (2) the main theorems have the stated types; (3) they use no
    axioms.  It also prints the definitions the statements use. *)

From Local Require Import Individual54 BB54_rules BB54_run BB54_bound.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : tm (A, S0) = Some (S1, R, B)).  Check (eq_refl : tm (A, S1) = Some (S3, L, C)).  Check (eq_refl : tm (A, S2) = Some (S1, L, D)).  Check (eq_refl : tm (A, S3) = Some (S2, R, A)).
Check (eq_refl : tm (B, S0) = Some (S2, R, C)).  Check (eq_refl : tm (B, S1) = None).  Check (eq_refl : tm (B, S2) = Some (S2, L, B)).  Check (eq_refl : tm (B, S3) = Some (S2, L, B)).
Check (eq_refl : tm (C, S0) = Some (S1, L, D)).  Check (eq_refl : tm (C, S1) = Some (S3, R, C)).  Check (eq_refl : tm (C, S2) = Some (S1, L, E)).  Check (eq_refl : tm (C, S3) = Some (S2, R, A)).
Check (eq_refl : tm (D, S0) = Some (S3, R, C)).  Check (eq_refl : tm (D, S1) = Some (S0, L, B)).  Check (eq_refl : tm (D, S2) = Some (S1, L, D)).  Check (eq_refl : tm (D, S3) = Some (S3, L, D)).
Check (eq_refl : tm (E, S0) = Some (S3, R, C)).  Check (eq_refl : tm (E, S1) = Some (S1, L, C)).  Check (eq_refl : tm (E, S2) = Some (S3, L, E)).  Check (eq_refl : tm (E, S3) = Some (S2, R, E)).

Print BB54_bound.knuth.
Print BB54_bound.f_omega.
Print BB54_bound.f_omega2.
Print BB54_bound.f_omega1.
Print BB54_run.sigma.
Print BB54_run.final_cells.
Print BB54_run.c_final.
Print BB54_rules.Bcfg.
Print BB54_rules.g.

Check BB54_run.bb54_halts.
Check BB54_run.reaches_final.
Check BB54_run.final_halted.
Check BB54_run.final_cells_count.
Check BB54_run.final_cells_all_nonblank.
Check BB54_bound.sigma_beats_official_bb54.
Check BB54_bound.sigma_beats_f_omega1_65536.
Check BB54_bound.bb54_new_champion_main.

Print Assumptions BB54_run.bb54_halts.
Print Assumptions BB54_run.reaches_final.
Print Assumptions BB54_run.final_halted.
Print Assumptions BB54_run.final_cells_count.
Print Assumptions BB54_run.final_cells_all_nonblank.
Print Assumptions BB54_bound.sigma_beats_official_bb54.
Print Assumptions BB54_bound.sigma_beats_f_omega1_65536.
Print Assumptions BB54_bound.bb54_new_champion_main.
