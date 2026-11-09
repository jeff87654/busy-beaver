(** Independent probe for the J16_w2 (Argon) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB16_J16_w2.tm] is the declared machine
    1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI
    entry by entry (these 32 checks were generated from the machine string, not from the Coq file; the halting
    transition (1RZ) is None), and the start configuration is the blank tape in state A;
    (2) the main theorems have the stated types; (3) they use no axioms.  It also prints the definitions the
    statements use.  The setup names states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB16_J16_w2 BB16_J16_w2_cmp.
From BB8 Require Import Individual162.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB16_J16_w2.tm (A, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB16_J16_w2.tm (A, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB16_J16_w2.tm (B, 0) = Some (0, TM.L, I)).  Check (eq_refl : BB16_J16_w2.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB16_J16_w2.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB16_J16_w2.tm (C, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB16_J16_w2.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB16_J16_w2.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB16_J16_w2.tm (E, 0) = Some (0, TM.R, M)).  Check (eq_refl : BB16_J16_w2.tm (E, 1) = Some (1, TM.R, L)).
Check (eq_refl : BB16_J16_w2.tm (F, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB16_J16_w2.tm (F, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB16_J16_w2.tm (G, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB16_J16_w2.tm (G, 1) = Some (0, TM.L, A)).
Check (eq_refl : BB16_J16_w2.tm (H, 0) = Some (1, TM.R, F)).  Check (eq_refl : BB16_J16_w2.tm (H, 1) = Some (0, TM.R, N)).
Check (eq_refl : BB16_J16_w2.tm (I, 0) = Some (1, TM.L, J)).  Check (eq_refl : BB16_J16_w2.tm (I, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB16_J16_w2.tm (J, 0) = Some (0, TM.L, K)).  Check (eq_refl : BB16_J16_w2.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB16_J16_w2.tm (K, 0) = Some (1, TM.R, L)).  Check (eq_refl : BB16_J16_w2.tm (K, 1) = Some (1, TM.R, E)).
Check (eq_refl : BB16_J16_w2.tm (L, 0) = Some (0, TM.R, L)).  Check (eq_refl : BB16_J16_w2.tm (L, 1) = Some (0, TM.R, F)).
Check (eq_refl : BB16_J16_w2.tm (M, 0) = Some (0, TM.L, G)).  Check (eq_refl : BB16_J16_w2.tm (M, 1) = Some (0, TM.R, N)).
Check (eq_refl : BB16_J16_w2.tm (N, 0) = Some (0, TM.R, P)).  Check (eq_refl : BB16_J16_w2.tm (N, 1) = Some (1, TM.R, O)).
Check (eq_refl : BB16_J16_w2.tm (O, 0) = None).  Check (eq_refl : BB16_J16_w2.tm (O, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB16_J16_w2.tm (P, 0) = Some (1, TM.L, B)).  Check (eq_refl : BB16_J16_w2.tm (P, 1) = Some (1, TM.L, I)).

Print BB16_J16_w2.iter.
Print BB16_J16_w2.f.
Print BB16_J16_w2.f_omega.
Print BB16_J16_w2.f_wk.
Print BB16_J16_w2.f_w2.
Print BB16_J16_w2.h.
Print BB16_J16_w2.hc.
Print BB16_J16_w2.G.
Print BB16_J16_w2.Gk.
Print BB16_J16_w2.ho.
Print BB16_J16_w2.hoc.
Print BB16_J16_w2.sym_val.
Print BB16_J16_w2.count1.
Print BB16_J16_w2.ones.
Print BB16_J16_w2_cmp.f_omega1.
Print BB16_J16_w2_cmp.f_omega2.
Print BB16_J16_w2_cmp.f_omega3.

Check BB16_J16_w2.halt.
Check BB16_J16_w2.score_exact.
Check BB16_J16_w2.sigma_lower_bound.
Check BB16_J16_w2_cmp.beats_J15.
Check BB16_J16_w2_cmp.beats_M14_31.
Check BB16_J16_w2_cmp.beats_M16_C.
Check BB16_J16_w2_cmp.beats_M17_B.

Print Assumptions BB16_J16_w2.halt.
Print Assumptions BB16_J16_w2.score_exact.
Print Assumptions BB16_J16_w2.sigma_lower_bound.
Print Assumptions BB16_J16_w2_cmp.beats_J15.
Print Assumptions BB16_J16_w2_cmp.beats_M14_31.
Print Assumptions BB16_J16_w2_cmp.beats_M16_C.
Print Assumptions BB16_J16_w2_cmp.beats_M17_B.
