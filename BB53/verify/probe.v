(** Independent probe for the 53-Main (BB(5,3)) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . Local probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table [tm] is the machine
    1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB
    entry by entry (15 checks generated from the machine string, not from the Coq file; the halting
    transition E0 = 1RZ is None in busycoq; sigma counts the tape after its write), and the start
    configuration is the blank tape in state A; (2) the main theorems have the stated types; (3) they use no
    axioms.  It also prints the definitions the statements use. *)

From Local Require Import Individual53 BB53_rules BB53_run BB53_bound.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : tm (A, S0) = Some (S1, R, B)).  Check (eq_refl : tm (A, S1) = Some (S1, L, C)).  Check (eq_refl : tm (A, S2) = Some (S1, R, A)).
Check (eq_refl : tm (B, S0) = Some (S1, L, A)).  Check (eq_refl : tm (B, S1) = Some (S2, L, C)).  Check (eq_refl : tm (B, S2) = Some (S1, R, B)).
Check (eq_refl : tm (C, S0) = Some (S1, L, B)).  Check (eq_refl : tm (C, S1) = Some (S1, L, D)).  Check (eq_refl : tm (C, S2) = Some (S2, L, C)).
Check (eq_refl : tm (D, S0) = Some (S2, R, E)).  Check (eq_refl : tm (D, S1) = Some (S2, L, D)).  Check (eq_refl : tm (D, S2) = Some (S1, R, A)).
Check (eq_refl : tm (E, S0) = None).  Check (eq_refl : tm (E, S1) = Some (S2, R, E)).  Check (eq_refl : tm (E, S2) = Some (S1, R, B)).

Print BB53_bound.knuth.
Print BB53_bound.f_omega.
Print BB53_run.sigma.
Print BB53_run.final_cells.
Print BB53_run.c_final.
Print BB53_rules.Bcfg.
Print BB53_rules.g.

Check BB53_run.bb53_halts.
Check BB53_run.reaches_final.
Check BB53_run.final_halted.
Check BB53_run.final_cells_count.
Check BB53_run.final_cells_all_nonblank.
Check BB53_bound.sigma_exceeds_f_omega2.
Check BB53_bound.sigma_beats_official_bb43.
Check BB53_bound.bb53_new_champion_main.

Print Assumptions BB53_run.bb53_halts.
Print Assumptions BB53_run.reaches_final.
Print Assumptions BB53_run.final_halted.
Print Assumptions BB53_run.final_cells_count.
Print Assumptions BB53_run.final_cells_all_nonblank.
Print Assumptions BB53_bound.sigma_exceeds_f_omega2.
Print Assumptions BB53_bound.sigma_beats_official_bb43.
Print Assumptions BB53_bound.bb53_new_champion_main.
