(** Independent probe for the J17_champ (Argon) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB17_J17_w2_champ.tm] is the declared machine
    1LG1RH_0LI1RC_0LD1LQ_0RE1LD_0RP1RL_1RB1RF_1LQ1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LQ0RN_0LQ1RO_1RZ1RM_0LQ0RA_1LH0LG
    entry by entry, and that the table of [BB17_J17_w2_champ.tm_tnf] (the same machine with its states renamed, used by the
    _tnf theorems) is
    1LB1RD_1LC1LB_1LD0LB_1RE0RM_1RF1RE_0LG1RP_1LH1LG_0LI1LG_1RJ1RK_0RJ0RE_0RL1RJ_0LC0RA_1RZ1RN_0LC0RO_0LC1RM_0LQ1LC_0RK1LQ
    (these 68 checks were generated from the two strings, not from the Coq file; the halting transition,
    O0 in tm and M0 in tm_tnf, is None; the states after P are the constructors QQ),
    and the start configuration is the blank tape in state A; (2) the main theorems (and the comparisons with J16_w2's exact score, BB17_J17_cmp.v) have the stated types; (3) they
    use no axioms.  It also prints the definitions the statements use.  The setup names states L and O, so directions
    are written TM.L / TM.R. *)

From BB8 Require BB17_J17_w2_champ BB17_J17_cmp.
From BB8 Require Import Individual172.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB17_J17_w2_champ.tm (A, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB17_J17_w2_champ.tm (A, 1) = Some (1, TM.R, H)).
Check (eq_refl : BB17_J17_w2_champ.tm (B, 0) = Some (0, TM.L, I)).  Check (eq_refl : BB17_J17_w2_champ.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB17_J17_w2_champ.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB17_J17_w2_champ.tm (C, 1) = Some (1, TM.L, QQ)).
Check (eq_refl : BB17_J17_w2_champ.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB17_J17_w2_champ.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB17_J17_w2_champ.tm (E, 0) = Some (0, TM.R, P)).  Check (eq_refl : BB17_J17_w2_champ.tm (E, 1) = Some (1, TM.R, L)).
Check (eq_refl : BB17_J17_w2_champ.tm (F, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB17_J17_w2_champ.tm (F, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB17_J17_w2_champ.tm (G, 0) = Some (1, TM.L, QQ)).  Check (eq_refl : BB17_J17_w2_champ.tm (G, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB17_J17_w2_champ.tm (H, 0) = Some (1, TM.R, F)).  Check (eq_refl : BB17_J17_w2_champ.tm (H, 1) = Some (0, TM.R, O)).
Check (eq_refl : BB17_J17_w2_champ.tm (I, 0) = Some (1, TM.L, J)).  Check (eq_refl : BB17_J17_w2_champ.tm (I, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB17_J17_w2_champ.tm (J, 0) = Some (0, TM.L, K)).  Check (eq_refl : BB17_J17_w2_champ.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB17_J17_w2_champ.tm (K, 0) = Some (1, TM.R, L)).  Check (eq_refl : BB17_J17_w2_champ.tm (K, 1) = Some (1, TM.R, E)).
Check (eq_refl : BB17_J17_w2_champ.tm (L, 0) = Some (0, TM.R, L)).  Check (eq_refl : BB17_J17_w2_champ.tm (L, 1) = Some (0, TM.R, F)).
Check (eq_refl : BB17_J17_w2_champ.tm (M, 0) = Some (0, TM.L, QQ)).  Check (eq_refl : BB17_J17_w2_champ.tm (M, 1) = Some (0, TM.R, N)).
Check (eq_refl : BB17_J17_w2_champ.tm (N, 0) = Some (0, TM.L, QQ)).  Check (eq_refl : BB17_J17_w2_champ.tm (N, 1) = Some (1, TM.R, O)).
Check (eq_refl : BB17_J17_w2_champ.tm (O, 0) = None).  Check (eq_refl : BB17_J17_w2_champ.tm (O, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB17_J17_w2_champ.tm (P, 0) = Some (0, TM.L, QQ)).  Check (eq_refl : BB17_J17_w2_champ.tm (P, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB17_J17_w2_champ.tm (QQ, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB17_J17_w2_champ.tm (QQ, 1) = Some (0, TM.L, G)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (A, 0) = Some (1, TM.L, B)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (A, 1) = Some (1, TM.R, D)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (B, 0) = Some (1, TM.L, C)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (B, 1) = Some (1, TM.L, B)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (C, 0) = Some (1, TM.L, D)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (C, 1) = Some (0, TM.L, B)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (D, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (D, 1) = Some (0, TM.R, M)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (E, 0) = Some (1, TM.R, F)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (E, 1) = Some (1, TM.R, E)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (F, 0) = Some (0, TM.L, G)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (F, 1) = Some (1, TM.R, P)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (G, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (G, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (H, 0) = Some (0, TM.L, I)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (H, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (I, 0) = Some (1, TM.R, J)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (I, 1) = Some (1, TM.R, K)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (J, 0) = Some (0, TM.R, J)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (J, 1) = Some (0, TM.R, E)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (K, 0) = Some (0, TM.R, L)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (K, 1) = Some (1, TM.R, J)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (L, 0) = Some (0, TM.L, C)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (L, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (M, 0) = None).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (M, 1) = Some (1, TM.R, N)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (N, 0) = Some (0, TM.L, C)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (N, 1) = Some (0, TM.R, O)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (O, 0) = Some (0, TM.L, C)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (O, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (P, 0) = Some (0, TM.L, QQ)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (P, 1) = Some (1, TM.L, C)).
Check (eq_refl : BB17_J17_w2_champ.tm_tnf (QQ, 0) = Some (0, TM.R, K)).  Check (eq_refl : BB17_J17_w2_champ.tm_tnf (QQ, 1) = Some (1, TM.L, QQ)).

Print BB17_J17_w2_champ.iter.
Print BB17_J17_w2_champ.f.
Print BB17_J17_w2_champ.f_omega.
Print BB17_J17_w2_champ.f_wk.
Print BB17_J17_w2_champ.f_w2.
Print BB17_J17_w2_champ.h.
Print BB17_J17_w2_champ.hc.
Print BB17_J17_w2_champ.Gk.
Print BB17_J17_w2_champ.G.
Print BB17_J17_w2_champ.ho.
Print BB17_J17_w2_champ.hoc.
Print BB17_J17_w2_champ.sym_val.
Print BB17_J17_w2_champ.count1.
Print BB17_J17_w2_champ.ones.

Check BB17_J17_w2_champ.halt.
Check BB17_J17_w2_champ.score_exact.
Check BB17_J17_w2_champ.sigma_lower_bound.
Check BB17_J17_w2_champ.halt_tnf.
Check BB17_J17_w2_champ.sigma_lower_bound_tnf.

Check BB17_J17_cmp.beats_J16_exact.
Check BB17_J17_cmp.beats_J16_score.

Print Assumptions BB17_J17_w2_champ.halt.
Print Assumptions BB17_J17_w2_champ.score_exact.
Print Assumptions BB17_J17_w2_champ.sigma_lower_bound.
Print Assumptions BB17_J17_w2_champ.halt_tnf.
Print Assumptions BB17_J17_w2_champ.sigma_lower_bound_tnf.
Print Assumptions BB17_J17_cmp.beats_J16_exact.
Print Assumptions BB17_J17_cmp.beats_J16_score.
