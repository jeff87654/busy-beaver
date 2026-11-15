(** Independent probe for the P12 proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB12_P12.tm] is the declared machine
    1RB1RA_1RI1RC_0LD1LG_0RE1LD_---1RF_0LL0RA_1RA0LH_1LG1LH_1RK0LJ_1LH1LI_0LL0RD_0LH1LK
    entry by entry (these 24 checks were generated from the machine string, not from the Coq file; the halting
    transition, E0, is None), and the start configuration is the blank tape in state A; (2) the main theorems have
    the stated types; (3) they use no axioms.  It also prints the definitions the statements use. *)

From BB8 Require BB12_P12 BB12_P12_bound BB12_P12_cmp BB11_C4.
From BB8 Require Import Individual122.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB12_P12.tm (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB12_P12.tm (A, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB12_P12.tm (B, 0) = Some (1, TM.R, I)).  Check (eq_refl : BB12_P12.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB12_P12.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB12_P12.tm (C, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB12_P12.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB12_P12.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB12_P12.tm (E, 0) = None).  Check (eq_refl : BB12_P12.tm (E, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB12_P12.tm (F, 0) = Some (0, TM.L, L)).  Check (eq_refl : BB12_P12.tm (F, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB12_P12.tm (G, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB12_P12.tm (G, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB12_P12.tm (H, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB12_P12.tm (H, 1) = Some (1, TM.L, H)).
Check (eq_refl : BB12_P12.tm (I, 0) = Some (1, TM.R, K)).  Check (eq_refl : BB12_P12.tm (I, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB12_P12.tm (J, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB12_P12.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB12_P12.tm (K, 0) = Some (0, TM.L, L)).  Check (eq_refl : BB12_P12.tm (K, 1) = Some (0, TM.R, D)).
Check (eq_refl : BB12_P12.tm (L, 0) = Some (0, TM.L, H)).  Check (eq_refl : BB12_P12.tm (L, 1) = Some (1, TM.L, K)).

Print BB12_P12.iter.
Print BB12_P12.W.
Print BB12_P12.Be.
Print BB12_P12.Rd.
Print BB12_P12.BigP.
Print BB12_P12.Big.
Print BB12_P12_bound.f.
Print BB12_P12_bound.f_omega.
Print BB12_P12_bound.f_omega1.
Print BB12_P12_bound.f_omega2.
Print BB12_P12.sym_val.
Print BB12_P12.count1.
Print BB12_P12.ones.
Print BB11_C4.ones.

Check BB12_P12.halt.
Check BB12_P12.score_exact.
Check BB12_P12_bound.sigma_lower_bound.
Check BB12_P12_cmp.beats_C4_exact.
Check BB12_P12_cmp.beats_C4_score.
Check BB11_C4.score_exact.

Print Assumptions BB12_P12.halt.
Print Assumptions BB12_P12.score_exact.
Print Assumptions BB12_P12_bound.sigma_lower_bound.
Print Assumptions BB12_P12_cmp.beats_C4_exact.
Print Assumptions BB12_P12_cmp.beats_C4_score.
