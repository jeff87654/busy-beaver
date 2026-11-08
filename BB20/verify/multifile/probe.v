(** Independent probe for the J20 (Jacobzheng) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB20_JZ20.tm] is the declared machine
    1LH0LG_0LI1RC_0LD1LA_0RE1LD_1RQ1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0RF0LO_0RF1LP_0RF1LN_1LR1RQ_1RZ1LS_0LF1LT_0LF0LR
    entry by entry (these 40 checks were generated from the machine string, not from the Coq file; the halting
    transition (1RZ) is None; the 17th to 20th states, letters Q, R, S and T, are the constructors QQ, RR, SS and TT), and the start configuration is the blank tape in state A;
    (2) the main theorems have the stated types; (3) they use no axioms.  It also prints the definitions the
    statements use.  The setup names states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB20_JZ20.
From BB8 Require Import Individual202.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB20_JZ20.tm (A, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB20_JZ20.tm (A, 1) = Some (0, TM.L, G)).
Check (eq_refl : BB20_JZ20.tm (B, 0) = Some (0, TM.L, I)).  Check (eq_refl : BB20_JZ20.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB20_JZ20.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB20_JZ20.tm (C, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB20_JZ20.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB20_JZ20.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB20_JZ20.tm (E, 0) = Some (1, TM.R, QQ)).  Check (eq_refl : BB20_JZ20.tm (E, 1) = Some (1, TM.R, L)).
Check (eq_refl : BB20_JZ20.tm (F, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB20_JZ20.tm (F, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB20_JZ20.tm (G, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB20_JZ20.tm (G, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB20_JZ20.tm (H, 0) = Some (1, TM.R, F)).  Check (eq_refl : BB20_JZ20.tm (H, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB20_JZ20.tm (I, 0) = Some (1, TM.L, J)).  Check (eq_refl : BB20_JZ20.tm (I, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB20_JZ20.tm (J, 0) = Some (0, TM.L, K)).  Check (eq_refl : BB20_JZ20.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB20_JZ20.tm (K, 0) = Some (1, TM.R, L)).  Check (eq_refl : BB20_JZ20.tm (K, 1) = Some (1, TM.R, E)).
Check (eq_refl : BB20_JZ20.tm (L, 0) = Some (0, TM.R, L)).  Check (eq_refl : BB20_JZ20.tm (L, 1) = Some (0, TM.R, F)).
Check (eq_refl : BB20_JZ20.tm (M, 0) = Some (0, TM.L, N)).  Check (eq_refl : BB20_JZ20.tm (M, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB20_JZ20.tm (N, 0) = Some (0, TM.R, F)).  Check (eq_refl : BB20_JZ20.tm (N, 1) = Some (0, TM.L, O)).
Check (eq_refl : BB20_JZ20.tm (O, 0) = Some (0, TM.R, F)).  Check (eq_refl : BB20_JZ20.tm (O, 1) = Some (1, TM.L, P)).
Check (eq_refl : BB20_JZ20.tm (P, 0) = Some (0, TM.R, F)).  Check (eq_refl : BB20_JZ20.tm (P, 1) = Some (1, TM.L, N)).
Check (eq_refl : BB20_JZ20.tm (QQ, 0) = Some (1, TM.L, RR)).  Check (eq_refl : BB20_JZ20.tm (QQ, 1) = Some (1, TM.R, QQ)).
Check (eq_refl : BB20_JZ20.tm (RR, 0) = None).  Check (eq_refl : BB20_JZ20.tm (RR, 1) = Some (1, TM.L, SS)).
Check (eq_refl : BB20_JZ20.tm (SS, 0) = Some (0, TM.L, F)).  Check (eq_refl : BB20_JZ20.tm (SS, 1) = Some (1, TM.L, TT)).
Check (eq_refl : BB20_JZ20.tm (TT, 0) = Some (0, TM.L, F)).  Check (eq_refl : BB20_JZ20.tm (TT, 1) = Some (0, TM.L, RR)).

Print BB20_JZ20.iter.
Print BB20_JZ20.h.
Print BB20_JZ20.hc.
Print BB20_JZ20.Gcy.
Print BB20_JZ20.G.
Print BB20_JZ20.ho.
Print BB20_JZ20.hoc.
Print BB20_JZ20.f.
Print BB20_JZ20.f_omega.
Print BB20_JZ20.f_wk.
Print BB20_JZ20.f_w2.
Print BB20_JZ20.sym_val.
Print BB20_JZ20.count1.
Print BB20_JZ20.ones.

Check BB20_JZ20.halt.
Check BB20_JZ20.score_exact.
Check BB20_JZ20.sigma_lower_bound.

Print Assumptions BB20_JZ20.halt.
Print Assumptions BB20_JZ20.score_exact.
Print Assumptions BB20_JZ20.sigma_lower_bound.
