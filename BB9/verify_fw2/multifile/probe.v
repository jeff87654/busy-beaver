(** Independent probe for the fw2 halting proof and score bounds (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB9_fw2_1RB0RD.tm] is the declared
    machine 1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA entry by entry (these 18 lines were
    generated from the machine string, not from the Coq file; the halting transition I0 (1RZ) is None), and the start
    configuration is the blank tape in state A; (2) the main theorems have the stated types; (3) they use no axioms.
    It also prints the definitions the statements use. *)

From BB8 Require BB9_fw2_1RB0RD BB9_fw2_bound.
From BB8 Require Import Individual92.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB9_fw2_1RB0RD.tm (A, 0) = Some (1, R, B)).  Check (eq_refl : BB9_fw2_1RB0RD.tm (A, 1) = Some (0, R, D)).
Check (eq_refl : BB9_fw2_1RB0RD.tm (B, 0) = Some (1, L, C)).  Check (eq_refl : BB9_fw2_1RB0RD.tm (B, 1) = Some (1, L, C)).
Check (eq_refl : BB9_fw2_1RB0RD.tm (C, 0) = Some (0, R, A)).  Check (eq_refl : BB9_fw2_1RB0RD.tm (C, 1) = Some (0, L, B)).
Check (eq_refl : BB9_fw2_1RB0RD.tm (D, 0) = Some (1, R, E)).  Check (eq_refl : BB9_fw2_1RB0RD.tm (D, 1) = Some (1, R, D)).
Check (eq_refl : BB9_fw2_1RB0RD.tm (E, 0) = Some (0, L, G)).  Check (eq_refl : BB9_fw2_1RB0RD.tm (E, 1) = Some (0, L, F)).
Check (eq_refl : BB9_fw2_1RB0RD.tm (F, 0) = Some (1, L, E)).  Check (eq_refl : BB9_fw2_1RB0RD.tm (F, 1) = Some (1, L, F)).
Check (eq_refl : BB9_fw2_1RB0RD.tm (G, 0) = Some (0, R, H)).  Check (eq_refl : BB9_fw2_1RB0RD.tm (G, 1) = Some (1, L, G)).
Check (eq_refl : BB9_fw2_1RB0RD.tm (H, 0) = Some (1, R, D)).  Check (eq_refl : BB9_fw2_1RB0RD.tm (H, 1) = Some (1, R, I)).
Check (eq_refl : BB9_fw2_1RB0RD.tm (I, 0) = None).  Check (eq_refl : BB9_fw2_1RB0RD.tm (I, 1) = Some (1, R, A)).

Print BB9_fw2_1RB0RD.iter.
Print BB9_fw2_bound.f.
Print BB9_fw2_bound.f_omega.
Print BB9_fw2_bound.sym_val.
Print BB9_fw2_bound.count1.
Print BB9_fw2_bound.ones.
(* the numbers in score_exact and sigma_lower_bound_strong *)
Print BB9_fw2_1RB0RD.UX.
Print BB9_fw2_1RB0RD.U.
Print BB9_fw2_1RB0RD.Tpre.
Print BB9_fw2_1RB0RD.Tv.
Print BB9_fw2_1RB0RD.second.
Print BB9_fw2_1RB0RD.b1.
Print BB9_fw2_1RB0RD.b2.
Print BB9_fw2_1RB0RD.b3.

Check BB9_fw2_1RB0RD.halt.
Check BB9_fw2_bound.score_exact.
Check BB9_fw2_bound.sigma_lower_bound.
Check BB9_fw2_bound.sigma_lower_bound_strong.

Print Assumptions BB9_fw2_1RB0RD.halt.
Print Assumptions BB9_fw2_bound.score_exact.
Print Assumptions BB9_fw2_bound.sigma_lower_bound.
Print Assumptions BB9_fw2_bound.sigma_lower_bound_strong.
