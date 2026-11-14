(** Independent probe for the J20_cube (Argon) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB20_J20_w2_cube.tm] is the declared machine
    1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RT0RK_1LS1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_0LA0LA_1RZ1LK
    entry by entry (these 40 checks were generated from the machine string, not from the Coq file; the
    halting transition, T0, is None; the states after P are the constructors QQ, RR, SS, TT),
    and the start configuration is the blank tape in state A; (2) the main theorems have the stated types; (3) they
    use no axioms.  It also prints the definitions the statements use.  The setup names states L and O, so directions
    are written TM.L / TM.R. *)

From BB8 Require BB20_J20_w2_cube.
From BB8 Require Import Individual202.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB20_J20_w2_cube.tm (A, 0) = Some (1, TM.L, B)).  Check (eq_refl : BB20_J20_w2_cube.tm (A, 1) = Some (0, TM.L, M)).
Check (eq_refl : BB20_J20_w2_cube.tm (B, 0) = Some (1, TM.R, C)).  Check (eq_refl : BB20_J20_w2_cube.tm (B, 1) = Some (1, TM.R, N)).
Check (eq_refl : BB20_J20_w2_cube.tm (C, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB20_J20_w2_cube.tm (C, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB20_J20_w2_cube.tm (D, 0) = Some (0, TM.L, E)).  Check (eq_refl : BB20_J20_w2_cube.tm (D, 1) = Some (1, TM.R, QQ)).
Check (eq_refl : BB20_J20_w2_cube.tm (E, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB20_J20_w2_cube.tm (E, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB20_J20_w2_cube.tm (F, 0) = Some (0, TM.L, G)).  Check (eq_refl : BB20_J20_w2_cube.tm (F, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB20_J20_w2_cube.tm (G, 0) = Some (1, TM.R, H)).  Check (eq_refl : BB20_J20_w2_cube.tm (G, 1) = Some (1, TM.R, I)).
Check (eq_refl : BB20_J20_w2_cube.tm (H, 0) = Some (0, TM.R, H)).  Check (eq_refl : BB20_J20_w2_cube.tm (H, 1) = Some (0, TM.R, C)).
Check (eq_refl : BB20_J20_w2_cube.tm (I, 0) = Some (0, TM.R, J)).  Check (eq_refl : BB20_J20_w2_cube.tm (I, 1) = Some (1, TM.R, H)).
Check (eq_refl : BB20_J20_w2_cube.tm (J, 0) = Some (0, TM.R, TT)).  Check (eq_refl : BB20_J20_w2_cube.tm (J, 1) = Some (0, TM.R, K)).
Check (eq_refl : BB20_J20_w2_cube.tm (K, 0) = Some (1, TM.L, SS)).  Check (eq_refl : BB20_J20_w2_cube.tm (K, 1) = Some (1, TM.R, L)).
Check (eq_refl : BB20_J20_w2_cube.tm (L, 0) = Some (1, TM.L, M)).  Check (eq_refl : BB20_J20_w2_cube.tm (L, 1) = Some (1, TM.R, J)).
Check (eq_refl : BB20_J20_w2_cube.tm (M, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB20_J20_w2_cube.tm (M, 1) = Some (1, TM.L, M)).
Check (eq_refl : BB20_J20_w2_cube.tm (N, 0) = Some (0, TM.L, A)).  Check (eq_refl : BB20_J20_w2_cube.tm (N, 1) = Some (0, TM.R, O)).
Check (eq_refl : BB20_J20_w2_cube.tm (O, 0) = Some (0, TM.L, C)).  Check (eq_refl : BB20_J20_w2_cube.tm (O, 1) = Some (1, TM.R, P)).
Check (eq_refl : BB20_J20_w2_cube.tm (P, 0) = Some (0, TM.L, A)).  Check (eq_refl : BB20_J20_w2_cube.tm (P, 1) = Some (1, TM.R, N)).
Check (eq_refl : BB20_J20_w2_cube.tm (QQ, 0) = Some (0, TM.L, RR)).  Check (eq_refl : BB20_J20_w2_cube.tm (QQ, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB20_J20_w2_cube.tm (RR, 0) = Some (0, TM.R, I)).  Check (eq_refl : BB20_J20_w2_cube.tm (RR, 1) = Some (1, TM.L, RR)).
Check (eq_refl : BB20_J20_w2_cube.tm (SS, 0) = Some (0, TM.L, A)).  Check (eq_refl : BB20_J20_w2_cube.tm (SS, 1) = Some (0, TM.L, A)).
Check (eq_refl : BB20_J20_w2_cube.tm (TT, 0) = None).  Check (eq_refl : BB20_J20_w2_cube.tm (TT, 1) = Some (1, TM.L, K)).

Print BB20_J20_w2_cube.iter.
Print BB20_J20_w2_cube.f.
Print BB20_J20_w2_cube.f_omega.
Print BB20_J20_w2_cube.f_wk.
Print BB20_J20_w2_cube.f_w2.
Print BB20_J20_w2_cube.h.
Print BB20_J20_w2_cube.hc.
Print BB20_J20_w2_cube.G0.
Print BB20_J20_w2_cube.Gcy.
Print BB20_J20_w2_cube.G.
Print BB20_J20_w2_cube.ho.
Print BB20_J20_w2_cube.hoc.
Print BB20_J20_w2_cube.sym_val.
Print BB20_J20_w2_cube.count1.
Print BB20_J20_w2_cube.ones.

Check BB20_J20_w2_cube.halt.
Check BB20_J20_w2_cube.score_exact.
Check BB20_J20_w2_cube.sigma_lower_bound.

Print Assumptions BB20_J20_w2_cube.halt.
Print Assumptions BB20_J20_w2_cube.score_exact.
Print Assumptions BB20_J20_w2_cube.sigma_lower_bound.
