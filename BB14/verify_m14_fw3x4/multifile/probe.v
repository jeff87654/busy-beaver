(** Independent probe for the M14_fw3x4 (Gemini 4 Neon) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB14_M14_fw3x4_entry.tm] is the
    declared machine
    1RB0LK_1RC1RB_1RD1RM_1RE0LH_1LF1RI_0LA1LG_1RL0LF_1LK1LD_1RJ0RB_1RG0LK_1LA1LK_---0LF_0LN1LA_0RE1LN
    entry by entry, and so is Neon's [BB14_M14_fw3x4.tm_tnf] (the table its _tnf theorems use); that Neon's
    [BB14_M14_fw3x4.tm] (the same machine in the state order of M12's core) is
    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LL1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_0LG1LN_1RN0LH_1RK0LL
    and that Neon's [c0_core] is the blank tape in state G while BusyCoq's [c0] is the blank tape in state A
    (these 84 checks were generated from the two strings, not from the Coq files; the halting transition, L0 in
    the first table and K0 in the second, is None); (2) the main theorems have the stated types; (3) they use no
    axioms.  It also prints the definitions the statements use.  The setup names states L and O, so directions
    are written TM.L / TM.R. *)

From BB8 Require BB14_M14_fw3 BB14_M14_fw3x4 BB14_M14_fw3x4_entry BB14_M14_fw3x4_cmp BB14_M14_fw3x4_audit.
From BB8 Require Import Individual142.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB14_M14_fw3x4.c0_core = (G, tape0)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (A, 1) = Some (0, TM.L, K)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (B, 0) = Some (1, TM.R, C)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (B, 1) = Some (1, TM.R, B)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (C, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (C, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (D, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (D, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (E, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (E, 1) = Some (1, TM.R, I)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (F, 0) = Some (0, TM.L, A)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (F, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (G, 0) = Some (1, TM.R, L)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (G, 1) = Some (0, TM.L, F)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (H, 0) = Some (1, TM.L, K)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (H, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (I, 0) = Some (1, TM.R, J)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (I, 1) = Some (0, TM.R, B)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (J, 0) = Some (1, TM.R, G)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (J, 1) = Some (0, TM.L, K)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (K, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (K, 1) = Some (1, TM.L, K)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (L, 0) = None).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (L, 1) = Some (0, TM.L, F)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (M, 0) = Some (0, TM.L, N)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (M, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB14_M14_fw3x4_entry.tm (N, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB14_M14_fw3x4_entry.tm (N, 1) = Some (1, TM.L, N)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (A, 1) = Some (0, TM.L, K)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (B, 0) = Some (1, TM.R, C)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (B, 1) = Some (1, TM.R, B)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (C, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (C, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (D, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (D, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (E, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (E, 1) = Some (1, TM.R, I)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (F, 0) = Some (0, TM.L, A)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (F, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (G, 0) = Some (1, TM.R, L)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (G, 1) = Some (0, TM.L, F)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (H, 0) = Some (1, TM.L, K)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (H, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (I, 0) = Some (1, TM.R, J)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (I, 1) = Some (0, TM.R, B)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (J, 0) = Some (1, TM.R, G)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (J, 1) = Some (0, TM.L, K)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (K, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (K, 1) = Some (1, TM.L, K)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (L, 0) = None).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (L, 1) = Some (0, TM.L, F)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (M, 0) = Some (0, TM.L, N)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (M, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB14_M14_fw3x4.tm_tnf (N, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB14_M14_fw3x4.tm_tnf (N, 1) = Some (1, TM.L, N)).
Check (eq_refl : BB14_M14_fw3x4.tm (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB14_M14_fw3x4.tm (A, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB14_M14_fw3x4.tm (B, 0) = Some (1, TM.R, I)).  Check (eq_refl : BB14_M14_fw3x4.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB14_M14_fw3x4.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB14_M14_fw3x4.tm (C, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB14_M14_fw3x4.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB14_M14_fw3x4.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB14_M14_fw3x4.tm (E, 0) = Some (1, TM.L, L)).  Check (eq_refl : BB14_M14_fw3x4.tm (E, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB14_M14_fw3x4.tm (F, 0) = Some (1, TM.R, M)).  Check (eq_refl : BB14_M14_fw3x4.tm (F, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB14_M14_fw3x4.tm (G, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB14_M14_fw3x4.tm (G, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB14_M14_fw3x4.tm (H, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB14_M14_fw3x4.tm (H, 1) = Some (1, TM.L, H)).
Check (eq_refl : BB14_M14_fw3x4.tm (I, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB14_M14_fw3x4.tm (I, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB14_M14_fw3x4.tm (J, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB14_M14_fw3x4.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB14_M14_fw3x4.tm (K, 0) = None).  Check (eq_refl : BB14_M14_fw3x4.tm (K, 1) = Some (0, TM.L, L)).
Check (eq_refl : BB14_M14_fw3x4.tm (L, 0) = Some (0, TM.L, G)).  Check (eq_refl : BB14_M14_fw3x4.tm (L, 1) = Some (1, TM.L, N)).
Check (eq_refl : BB14_M14_fw3x4.tm (M, 0) = Some (1, TM.R, N)).  Check (eq_refl : BB14_M14_fw3x4.tm (M, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB14_M14_fw3x4.tm (N, 0) = Some (1, TM.R, K)).  Check (eq_refl : BB14_M14_fw3x4.tm (N, 1) = Some (0, TM.L, L)).

Print BB14_M14_fw3x4.iter.
Print BB14_M14_fw3x4.f.
Print BB14_M14_fw3x4.f_omega.
Print BB14_M14_fw3x4.f_omega1.
Print BB14_M14_fw3x4.f_omega2.
Print BB14_M14_fw3x4.f_omega3.
Print BB14_M14_fw3x4.sym_val.
Print BB14_M14_fw3x4.count1.
Print BB14_M14_fw3x4.ones.
Print BB14_M14_fw3.ones.

Check BB14_M14_fw3x4_entry.halt.
Check BB14_M14_fw3x4_entry.score_exact.
Check BB14_M14_fw3x4_entry.sigma_bound.
Check BB14_M14_fw3x4.halt.
Check BB14_M14_fw3x4.score_exact.
Check BB14_M14_fw3x4.sigma_bound.
Check BB14_M14_fw3x4.beats_M14_fw3_exact.
Check BB14_M14_fw3x4_cmp.M14_fw3_score_agrees.
Check BB14_M14_fw3x4_cmp.beats_M14_fw3_all.
Check BB14_M14_fw3x4_cmp.beats_M14_fw3_exact.
Check BB14_M14_fw3x4_cmp.beats_M14_fw3_score.
Check BB14_M14_fw3x4_audit.my_new_halts.
Check BB14_M14_fw3x4_audit.my_new_sigma.
Check BB14_M14_fw3x4_audit.my_beats.

Print Assumptions BB14_M14_fw3x4_entry.halt.
Print Assumptions BB14_M14_fw3x4_entry.score_exact.
Print Assumptions BB14_M14_fw3x4_entry.sigma_bound.
Print Assumptions BB14_M14_fw3x4.halt.
Print Assumptions BB14_M14_fw3x4.score_exact.
Print Assumptions BB14_M14_fw3x4.sigma_bound.
Print Assumptions BB14_M14_fw3x4.beats_M14_fw3_exact.
Print Assumptions BB14_M14_fw3x4_cmp.M14_fw3_score_agrees.
Print Assumptions BB14_M14_fw3x4_cmp.beats_M14_fw3_all.
Print Assumptions BB14_M14_fw3x4_cmp.beats_M14_fw3_exact.
Print Assumptions BB14_M14_fw3x4_cmp.beats_M14_fw3_score.
Print Assumptions BB14_M14_fw3x4_audit.my_new_halts.
Print Assumptions BB14_M14_fw3x4_audit.my_new_sigma.
Print Assumptions BB14_M14_fw3x4_audit.my_beats.
