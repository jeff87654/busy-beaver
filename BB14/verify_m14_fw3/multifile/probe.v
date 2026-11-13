(** Independent probe for the M14_fw3 (Argon) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB14_M14_fw3.tm] is the declared machine
    1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_1LN1LK_1RK0LH_1LD0RK
    entry by entry, and that the table of [BB14_M14_fw3.tm_tnf] (the same machine with its states renamed, used by the
    _tnf theorems) is
    1RB1RA_1RC1RJ_1RD0LK_0LE1RI_---0LF_1LG1LE_1LH0RE_0RD1LH_1RL0RA_0LH1LN_1LM1LC_1RE0LM_1LN1LM_1RA0LM
    (these 56 checks were generated from the two strings, not from the Coq file; the halting transition,
    K0 in tm and E0 in tm_tnf, is None), and the start configuration is the blank tape in state A; (2) the main theorems have the
    stated types; (3) they use no axioms.  It also prints the definitions the statements use.  The setup names
    states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB14_M14_fw3 BB14_M14_31 BB14_M14_fw3_cmp.
From BB8 Require Import Individual142.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB14_M14_fw3.tm (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB14_M14_fw3.tm (A, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB14_M14_fw3.tm (B, 0) = Some (1, TM.R, I)).  Check (eq_refl : BB14_M14_fw3.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB14_M14_fw3.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB14_M14_fw3.tm (C, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB14_M14_fw3.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB14_M14_fw3.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB14_M14_fw3.tm (E, 0) = Some (0, TM.L, K)).  Check (eq_refl : BB14_M14_fw3.tm (E, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB14_M14_fw3.tm (F, 0) = Some (1, TM.R, M)).  Check (eq_refl : BB14_M14_fw3.tm (F, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB14_M14_fw3.tm (G, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB14_M14_fw3.tm (G, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB14_M14_fw3.tm (H, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB14_M14_fw3.tm (H, 1) = Some (1, TM.L, H)).
Check (eq_refl : BB14_M14_fw3.tm (I, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB14_M14_fw3.tm (I, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB14_M14_fw3.tm (J, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB14_M14_fw3.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB14_M14_fw3.tm (K, 0) = None).  Check (eq_refl : BB14_M14_fw3.tm (K, 1) = Some (0, TM.L, L)).
Check (eq_refl : BB14_M14_fw3.tm (L, 0) = Some (1, TM.L, N)).  Check (eq_refl : BB14_M14_fw3.tm (L, 1) = Some (1, TM.L, K)).
Check (eq_refl : BB14_M14_fw3.tm (M, 0) = Some (1, TM.R, K)).  Check (eq_refl : BB14_M14_fw3.tm (M, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB14_M14_fw3.tm (N, 0) = Some (1, TM.L, D)).  Check (eq_refl : BB14_M14_fw3.tm (N, 1) = Some (0, TM.R, K)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (A, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (B, 0) = Some (1, TM.R, C)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (B, 1) = Some (1, TM.R, J)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (C, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (C, 1) = Some (0, TM.L, K)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (D, 0) = Some (0, TM.L, E)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (D, 1) = Some (1, TM.R, I)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (E, 0) = None).  Check (eq_refl : BB14_M14_fw3.tm_tnf (E, 1) = Some (0, TM.L, F)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (F, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (F, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (G, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (G, 1) = Some (0, TM.R, E)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (H, 0) = Some (0, TM.R, D)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (H, 1) = Some (1, TM.L, H)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (I, 0) = Some (1, TM.R, L)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (I, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (J, 0) = Some (0, TM.L, H)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (J, 1) = Some (1, TM.L, N)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (K, 0) = Some (1, TM.L, M)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (K, 1) = Some (1, TM.L, C)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (L, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (L, 1) = Some (0, TM.L, M)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (M, 0) = Some (1, TM.L, N)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (M, 1) = Some (1, TM.L, M)).
Check (eq_refl : BB14_M14_fw3.tm_tnf (N, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB14_M14_fw3.tm_tnf (N, 1) = Some (0, TM.L, M)).

Print BB14_M14_fw3.iter.
Print BB14_M14_fw3.f.
Print BB14_M14_fw3.f_omega.
Print BB14_M14_fw3.f_omega1.
Print BB14_M14_fw3.f_omega2.
Print BB14_M14_fw3.f_omega3.
Print BB14_M14_fw3.sym_val.
Print BB14_M14_fw3.count1.
Print BB14_M14_fw3.ones.
Print BB14_M14_31.ones.

Check BB14_M14_fw3.halt.
Check BB14_M14_fw3.score_exact.
Check BB14_M14_fw3.sigma_bound.
Check BB14_M14_fw3.beats_M14_31.
Check BB14_M14_fw3.halt_tnf.
Check BB14_M14_fw3.sigma_bound_tnf.
Check BB14_M14_fw3.beats_M14_31_tnf.
Check BB14_M14_fw3_cmp.beats_M14_31_exact.
Check BB14_M14_fw3_cmp.beats_M14_31_score.

Print Assumptions BB14_M14_fw3.halt.
Print Assumptions BB14_M14_fw3.score_exact.
Print Assumptions BB14_M14_fw3.sigma_bound.
Print Assumptions BB14_M14_fw3.beats_M14_31.
Print Assumptions BB14_M14_fw3.halt_tnf.
Print Assumptions BB14_M14_fw3.sigma_bound_tnf.
Print Assumptions BB14_M14_fw3.beats_M14_31_tnf.
Print Assumptions BB14_M14_fw3_cmp.beats_M14_31_exact.
Print Assumptions BB14_M14_fw3_cmp.beats_M14_31_score.
