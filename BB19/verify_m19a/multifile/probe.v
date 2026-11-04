(** Independent probe for the M19_fw4_A proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB19_fw4_fw3_9.tm] is the declared machine
    1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_1RQ0LO_1LP1RR_0RB1LI_1RS0LQ_1LN0LR_0LR1RZ
    entry by entry (these 38 checks were generated from the machine string, not from the Coq file; the halting
    transition S1 (1RZ) is None; the 17th, 18th and 19th states, letters Q, R and S, are the constructors QQ, RR and SS), and the start configuration is the blank tape in state A;
    (2) the main theorems have the stated types; (3) they use no axioms.  It also prints the definitions the
    statements use.  The setup names states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB19_fw4_fw3_9.
From BB8 Require Import Individual192.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB19_fw4_fw3_9.tm (A, 0) = Some (1, TM.L, B)).  Check (eq_refl : BB19_fw4_fw3_9.tm (A, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB19_fw4_fw3_9.tm (B, 0) = Some (1, TM.R, C)).  Check (eq_refl : BB19_fw4_fw3_9.tm (B, 1) = Some (0, TM.L, A)).
Check (eq_refl : BB19_fw4_fw3_9.tm (C, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB19_fw4_fw3_9.tm (C, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB19_fw4_fw3_9.tm (D, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB19_fw4_fw3_9.tm (D, 1) = Some (1, TM.R, K)).
Check (eq_refl : BB19_fw4_fw3_9.tm (E, 0) = Some (1, TM.R, F)).  Check (eq_refl : BB19_fw4_fw3_9.tm (E, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB19_fw4_fw3_9.tm (F, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB19_fw4_fw3_9.tm (F, 1) = Some (1, TM.R, I)).
Check (eq_refl : BB19_fw4_fw3_9.tm (G, 0) = Some (1, TM.R, M)).  Check (eq_refl : BB19_fw4_fw3_9.tm (G, 1) = Some (0, TM.L, M)).
Check (eq_refl : BB19_fw4_fw3_9.tm (H, 0) = Some (1, TM.L, G)).  Check (eq_refl : BB19_fw4_fw3_9.tm (H, 1) = Some (0, TM.R, C)).
Check (eq_refl : BB19_fw4_fw3_9.tm (I, 0) = Some (0, TM.R, N)).  Check (eq_refl : BB19_fw4_fw3_9.tm (I, 1) = Some (0, TM.L, E)).
Check (eq_refl : BB19_fw4_fw3_9.tm (J, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB19_fw4_fw3_9.tm (J, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB19_fw4_fw3_9.tm (K, 0) = Some (0, TM.L, L)).  Check (eq_refl : BB19_fw4_fw3_9.tm (K, 1) = Some (1, TM.L, B)).
Check (eq_refl : BB19_fw4_fw3_9.tm (L, 0) = Some (0, TM.R, M)).  Check (eq_refl : BB19_fw4_fw3_9.tm (L, 1) = Some (1, TM.L, L)).
Check (eq_refl : BB19_fw4_fw3_9.tm (M, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB19_fw4_fw3_9.tm (M, 1) = Some (1, TM.R, H)).
Check (eq_refl : BB19_fw4_fw3_9.tm (N, 0) = Some (1, TM.R, QQ)).  Check (eq_refl : BB19_fw4_fw3_9.tm (N, 1) = Some (0, TM.L, O)).
Check (eq_refl : BB19_fw4_fw3_9.tm (O, 0) = Some (1, TM.L, P)).  Check (eq_refl : BB19_fw4_fw3_9.tm (O, 1) = Some (1, TM.R, RR)).
Check (eq_refl : BB19_fw4_fw3_9.tm (P, 0) = Some (0, TM.R, B)).  Check (eq_refl : BB19_fw4_fw3_9.tm (P, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB19_fw4_fw3_9.tm (QQ, 0) = Some (1, TM.R, SS)).  Check (eq_refl : BB19_fw4_fw3_9.tm (QQ, 1) = Some (0, TM.L, QQ)).
Check (eq_refl : BB19_fw4_fw3_9.tm (RR, 0) = Some (1, TM.L, N)).  Check (eq_refl : BB19_fw4_fw3_9.tm (RR, 1) = Some (0, TM.L, RR)).
Check (eq_refl : BB19_fw4_fw3_9.tm (SS, 0) = Some (0, TM.L, RR)).  Check (eq_refl : BB19_fw4_fw3_9.tm (SS, 1) = None).

Print BB19_fw4_fw3_9.iter.
Print BB19_fw4_fw3_9.f.
Print BB19_fw4_fw3_9.f_omega.
Print BB19_fw4_fw3_9.f_omega1.
Print BB19_fw4_fw3_9.f_omega2.
Print BB19_fw4_fw3_9.f_omega3.
Print BB19_fw4_fw3_9.f_omega4.
Print BB19_fw4_fw3_9.sym_val.
Print BB19_fw4_fw3_9.count1.
Print BB19_fw4_fw3_9.ones.

Check BB19_fw4_fw3_9.halt.
Check BB19_fw4_fw3_9.score_exact.
Check BB19_fw4_fw3_9.sigma_lower_bound.

Print Assumptions BB19_fw4_fw3_9.halt.
Print Assumptions BB19_fw4_fw3_9.score_exact.
Print Assumptions BB19_fw4_fw3_9.sigma_lower_bound.
