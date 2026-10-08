(** Independent probe for the n1 proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB10_n1.tm] is the declared machine
    1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_---0LC
    entry by entry (these 20 lines were generated from the machine string, not from the Coq file); (2) the main
    theorems have the stated types; (3) they use no axioms.  It also prints the definitions the statements use. *)

From BB8 Require BB10_n1 BB10_n1_bound BB10_n1_exact.
From BB8 Require Import Individual102.
From Coq Require Import PeanoNat.
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

Print BB10_n1.arrow.
Print BB10_n1.F.
Print BB10_n1.iter.
Print BB10_n1.JJ.
Print BB10_n1_bound.ones.
Print BB10_n1_exact.step.
Print BB10_n1_exact.stepn.

Check BB10_n1.halt.
Check BB10_n1_bound.score_exact.
Check BB10_n1_bound.sigma_lower_bound.
Check BB10_n1_bound.beats_champion.
Check BB10_n1_bound.beats_lead.
Check BB10_n1_bound.dominates.
Check BB10_n1_exact.score_closed_unfolded.
Check BB10_n1_exact.score_value_gt.

Print Assumptions BB10_n1.halt.
Print Assumptions BB10_n1_bound.score_exact.
Print Assumptions BB10_n1_bound.sigma_lower_bound.
Print Assumptions BB10_n1_bound.beats_champion.
Print Assumptions BB10_n1_bound.beats_lead.
Print Assumptions BB10_n1_bound.dominates.
Print Assumptions BB10_n1_exact.score_closed_unfolded.
Print Assumptions BB10_n1_exact.score_value_gt.
