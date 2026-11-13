(** Independent probe for the M13_19 (Argon) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB13_M13_19.tm] is the declared machine
    1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_0LM1LK_0LG1LL
    entry by entry, and that the table of [BB13_M13_19.tm_tnf] (the same machine with its states renamed, used by the
    _tnf theorems) is
    1RB1RA_1RC1RK_1RD0LM_0LE1RI_0LH1LF_0LE1LG_---0LF_1RA0LJ_1RH0RA_1LH1LJ_0LL1LH_0RD1LL_1LJ1LC
    (these 52 checks were generated from the two strings, not from the Coq file; the halting transition,
    K0 in tm and G0 in tm_tnf, is None), and the start configuration is the blank tape in state A; (2) the main theorems have the
    stated types; (3) they use no axioms.  It also prints the definitions the statements use.  The setup names
    states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB13_M13_19 BB13_M13b BB13_M13b_bound BB13_M13_19_cmp.
From BB8 Require Import Individual132.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB13_M13_19.tm (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB13_M13_19.tm (A, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB13_M13_19.tm (B, 0) = Some (1, TM.R, I)).  Check (eq_refl : BB13_M13_19.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB13_M13_19.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB13_M13_19.tm (C, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB13_M13_19.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB13_M13_19.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB13_M13_19.tm (E, 0) = Some (0, TM.L, M)).  Check (eq_refl : BB13_M13_19.tm (E, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB13_M13_19.tm (F, 0) = Some (1, TM.R, G)).  Check (eq_refl : BB13_M13_19.tm (F, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB13_M13_19.tm (G, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB13_M13_19.tm (G, 1) = Some (0, TM.L, H)).
Check (eq_refl : BB13_M13_19.tm (H, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB13_M13_19.tm (H, 1) = Some (1, TM.L, H)).
Check (eq_refl : BB13_M13_19.tm (I, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB13_M13_19.tm (I, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB13_M13_19.tm (J, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB13_M13_19.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB13_M13_19.tm (K, 0) = None).  Check (eq_refl : BB13_M13_19.tm (K, 1) = Some (0, TM.L, L)).
Check (eq_refl : BB13_M13_19.tm (L, 0) = Some (0, TM.L, M)).  Check (eq_refl : BB13_M13_19.tm (L, 1) = Some (1, TM.L, K)).
Check (eq_refl : BB13_M13_19.tm (M, 0) = Some (0, TM.L, G)).  Check (eq_refl : BB13_M13_19.tm (M, 1) = Some (1, TM.L, L)).
Check (eq_refl : BB13_M13_19.tm_tnf (A, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB13_M13_19.tm_tnf (A, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB13_M13_19.tm_tnf (B, 0) = Some (1, TM.R, C)).  Check (eq_refl : BB13_M13_19.tm_tnf (B, 1) = Some (1, TM.R, K)).
Check (eq_refl : BB13_M13_19.tm_tnf (C, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB13_M13_19.tm_tnf (C, 1) = Some (0, TM.L, M)).
Check (eq_refl : BB13_M13_19.tm_tnf (D, 0) = Some (0, TM.L, E)).  Check (eq_refl : BB13_M13_19.tm_tnf (D, 1) = Some (1, TM.R, I)).
Check (eq_refl : BB13_M13_19.tm_tnf (E, 0) = Some (0, TM.L, H)).  Check (eq_refl : BB13_M13_19.tm_tnf (E, 1) = Some (1, TM.L, F)).
Check (eq_refl : BB13_M13_19.tm_tnf (F, 0) = Some (0, TM.L, E)).  Check (eq_refl : BB13_M13_19.tm_tnf (F, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB13_M13_19.tm_tnf (G, 0) = None).  Check (eq_refl : BB13_M13_19.tm_tnf (G, 1) = Some (0, TM.L, F)).
Check (eq_refl : BB13_M13_19.tm_tnf (H, 0) = Some (1, TM.R, A)).  Check (eq_refl : BB13_M13_19.tm_tnf (H, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB13_M13_19.tm_tnf (I, 0) = Some (1, TM.R, H)).  Check (eq_refl : BB13_M13_19.tm_tnf (I, 1) = Some (0, TM.R, A)).
Check (eq_refl : BB13_M13_19.tm_tnf (J, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB13_M13_19.tm_tnf (J, 1) = Some (1, TM.L, J)).
Check (eq_refl : BB13_M13_19.tm_tnf (K, 0) = Some (0, TM.L, L)).  Check (eq_refl : BB13_M13_19.tm_tnf (K, 1) = Some (1, TM.L, H)).
Check (eq_refl : BB13_M13_19.tm_tnf (L, 0) = Some (0, TM.R, D)).  Check (eq_refl : BB13_M13_19.tm_tnf (L, 1) = Some (1, TM.L, L)).
Check (eq_refl : BB13_M13_19.tm_tnf (M, 0) = Some (1, TM.L, J)).  Check (eq_refl : BB13_M13_19.tm_tnf (M, 1) = Some (1, TM.L, C)).

Print BB13_M13_19.iter.
Print BB13_M13_19.f.
Print BB13_M13_19.f_omega.
Print BB13_M13_19.f_omega1.
Print BB13_M13_19.f_omega2.
Print BB13_M13_19.sym_val.
Print BB13_M13_19.count1.
Print BB13_M13_19.ones.
Print BB13_M13b_bound.ones.

Check BB13_M13_19.halt.
Check BB13_M13_19.sigma_bound.
Check BB13_M13_19.sigma_bound_fw1.
Check BB13_M13_19.beats_M13b.
Check BB13_M13_19.halt_tnf.
Check BB13_M13_19.sigma_bound_tnf.
Check BB13_M13_19.beats_M13b_tnf.
Check BB13_M13_19_cmp.beats_M13b_exact.
Check BB13_M13_19_cmp.beats_M13b_score.

Print Assumptions BB13_M13_19.halt.
Print Assumptions BB13_M13_19.sigma_bound.
Print Assumptions BB13_M13_19.sigma_bound_fw1.
Print Assumptions BB13_M13_19.beats_M13b.
Print Assumptions BB13_M13_19.halt_tnf.
Print Assumptions BB13_M13_19.sigma_bound_tnf.
Print Assumptions BB13_M13_19.beats_M13b_tnf.
Print Assumptions BB13_M13_19_cmp.beats_M13b_exact.
Print Assumptions BB13_M13_19_cmp.beats_M13b_score.
