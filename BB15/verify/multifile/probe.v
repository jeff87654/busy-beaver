(** Independent probe for the J15_fw13 (Argon) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB15_J15_fw13.tm] is the declared machine
    1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM
    entry by entry (these 30 checks were generated from the machine string, not from the Coq file; the halting
    transition (1RZ) is None), and the start configuration is the blank tape in state A;
    (2) the main theorems have the stated types; (3) they use no axioms.  It also prints the definitions the
    statements use.  The setup names states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB15_J15_fw13 BB15_J15_fw13_cmp.
From BB8 Require Import Individual152.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB15_J15_fw13.tm (A, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB15_J15_fw13.tm (A, 1) = Some (0, TM.L, G)).
Check (eq_refl : BB15_J15_fw13.tm (B, 0) = Some (0, TM.L, I)).  Check (eq_refl : BB15_J15_fw13.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB15_J15_fw13.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB15_J15_fw13.tm (C, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB15_J15_fw13.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB15_J15_fw13.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB15_J15_fw13.tm (E, 0) = Some (0, TM.R, H)).  Check (eq_refl : BB15_J15_fw13.tm (E, 1) = Some (1, TM.R, L)).
Check (eq_refl : BB15_J15_fw13.tm (F, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB15_J15_fw13.tm (F, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB15_J15_fw13.tm (G, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB15_J15_fw13.tm (G, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB15_J15_fw13.tm (H, 0) = Some (1, TM.R, F)).  Check (eq_refl : BB15_J15_fw13.tm (H, 1) = Some (0, TM.R, O)).
Check (eq_refl : BB15_J15_fw13.tm (I, 0) = Some (1, TM.L, J)).  Check (eq_refl : BB15_J15_fw13.tm (I, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB15_J15_fw13.tm (J, 0) = Some (0, TM.L, K)).  Check (eq_refl : BB15_J15_fw13.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB15_J15_fw13.tm (K, 0) = Some (1, TM.R, L)).  Check (eq_refl : BB15_J15_fw13.tm (K, 1) = Some (1, TM.R, E)).
Check (eq_refl : BB15_J15_fw13.tm (L, 0) = Some (0, TM.R, L)).  Check (eq_refl : BB15_J15_fw13.tm (L, 1) = Some (0, TM.R, F)).
Check (eq_refl : BB15_J15_fw13.tm (M, 0) = Some (0, TM.L, A)).  Check (eq_refl : BB15_J15_fw13.tm (M, 1) = Some (0, TM.R, N)).
Check (eq_refl : BB15_J15_fw13.tm (N, 0) = Some (0, TM.L, A)).  Check (eq_refl : BB15_J15_fw13.tm (N, 1) = Some (1, TM.R, O)).
Check (eq_refl : BB15_J15_fw13.tm (O, 0) = None).  Check (eq_refl : BB15_J15_fw13.tm (O, 1) = Some (1, TM.R, M)).

Print BB15_J15_fw13.iter.
Print BB15_J15_fw13.f.
Print BB15_J15_fw13.f_omega.
Print BB15_J15_fw13.f_wk.
Print BB15_J15_fw13.h.
Print BB15_J15_fw13.hc.
Print BB15_J15_fw13.G.
Print BB15_J15_fw13.ho.
Print BB15_J15_fw13.hoc.
Print BB15_J15_fw13.sym_val.
Print BB15_J15_fw13.count1.
Print BB15_J15_fw13.ones.
Print BB15_J15_fw13_cmp.f_omega1.
Print BB15_J15_fw13_cmp.f_omega2.

Check BB15_J15_fw13.halt.
Check BB15_J15_fw13.step_1012.
Check BB15_J15_fw13.score_exact.
Check BB15_J15_fw13.sigma_lower_bound.
Check BB15_J15_fw13_cmp.beats_M14_31.

Print Assumptions BB15_J15_fw13.halt.
Print Assumptions BB15_J15_fw13.step_1012.
Print Assumptions BB15_J15_fw13.score_exact.
Print Assumptions BB15_J15_fw13.sigma_lower_bound.
Print Assumptions BB15_J15_fw13_cmp.beats_M14_31.
