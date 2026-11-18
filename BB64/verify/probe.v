(** Independent probe for the BB(6,4) proof (run after compile_clean.sh, in
      this directory).  Coq confirms here, by conversion, that

    (1) the compiled transition table [tm] is exactly the machine

          1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ

        entry by entry (24 checks generated from the machine string, not from
        the Coq file; the halting transition F3 = 1RZ is [None] in busycoq,
        and sigma counts the tape after its write), and the start configuration
        is the blank tape in state A;

    (2) the main theorems have the stated types, including the exact requested
        fast-growing-hierarchy bound f_(omega+1)^4(65536) < sigma;

    (3) they use no axioms (all "Closed under the global context"). *)

From TM64 Require Import Individual64 BB64_rules BB64_run BB64_score BB64_bound.
From BB8 Require Import Ord KnuthFGH.
From TM64 Require FGH_BB64.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).

(* state A: 1RB 3LC 1LD 2RA *)
Check (eq_refl : tm (A, S0) = Some (S1, R, B)).  Check (eq_refl : tm (A, S1) = Some (S3, L, C)).
Check (eq_refl : tm (A, S2) = Some (S1, L, D)).  Check (eq_refl : tm (A, S3) = Some (S2, R, A)).
(* state B: 2RC 1RF 2LB 2LB *)
Check (eq_refl : tm (B, S0) = Some (S2, R, C)).  Check (eq_refl : tm (B, S1) = Some (S1, R, F)).
Check (eq_refl : tm (B, S2) = Some (S2, L, B)).  Check (eq_refl : tm (B, S3) = Some (S2, L, B)).
(* state C: 1LD 3RC 1LE 2RA *)
Check (eq_refl : tm (C, S0) = Some (S1, L, D)).  Check (eq_refl : tm (C, S1) = Some (S3, R, C)).
Check (eq_refl : tm (C, S2) = Some (S1, L, E)).  Check (eq_refl : tm (C, S3) = Some (S2, R, A)).
(* state D: 3RC 0LB 1LD 3LD *)
Check (eq_refl : tm (D, S0) = Some (S3, R, C)).  Check (eq_refl : tm (D, S1) = Some (S0, L, B)).
Check (eq_refl : tm (D, S2) = Some (S1, L, D)).  Check (eq_refl : tm (D, S3) = Some (S3, L, D)).
(* state E: 3RC 1LC 3LE 2RE *)
Check (eq_refl : tm (E, S0) = Some (S3, R, C)).  Check (eq_refl : tm (E, S1) = Some (S1, L, C)).
Check (eq_refl : tm (E, S2) = Some (S3, L, E)).  Check (eq_refl : tm (E, S3) = Some (S2, R, E)).
(* state F: 0LC 0LB 0LD 1RZ (F3 halts) *)
Check (eq_refl : tm (F, S0) = Some (S0, L, C)).  Check (eq_refl : tm (F, S1) = Some (S0, L, B)).
Check (eq_refl : tm (F, S2) = Some (S0, L, D)).  Check (eq_refl : tm (F, S3) = None).

Print BB64_bound.knuth.
Print BB64_bound.f_omega.
Print BB64_bound.f_omega1.
Print BB64_score.sigma.
Print BB64_score.final_cells.
Print BB64_run.c_final.
Print BB64_rules.Bcfg.
Print BB64_rules.g.

Check BB64_run.bb64_halts.
Check BB64_run.reaches_c_final.
Check BB64_run.c_final_halted.
Check BB64_score.final_cells_count.
Check BB64_score.final_cells_all_nonblank.
Check BB64_score.bb64_score_main.
Check BB64_bound.sigma_beats_four_f_omega1.
Check FGH_BB64.bb64_fgh_four.

Print Assumptions BB64_run.bb64_halts.
Print Assumptions BB64_run.reaches_c_final.
Print Assumptions BB64_run.c_final_halted.
Print Assumptions BB64_score.final_cells_count.
Print Assumptions BB64_score.final_cells_all_nonblank.
Print Assumptions BB64_score.bb64_score_main.
Print Assumptions BB64_bound.sigma_beats_four_f_omega1.
Print Assumptions FGH_BB64.bb64_fgh_four.
