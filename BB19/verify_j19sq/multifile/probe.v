(** Independent probe for the J19_sq (Argon) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB19_J19_w2_sq.tm] is the declared machine
    1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RS0RK_1LN1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_1RZ1LL
    entry by entry (these 38 checks were generated from the machine string, not from the Coq file; the
    halting transition, S0, is None; the states after P are the constructors QQ, RR, SS),
    and the start configuration is the blank tape in state A; (2) the main theorems have the stated types; (3) they
    use no axioms.  It also prints the definitions the statements use.  The setup names states L and O, so directions
    are written TM.L / TM.R. *)

From BB8 Require BB19_J19_w2_sq.
From BB8 Require Import Individual192.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB19_J19_w2_sq.tm (A, 0) = Some (1, TM.L, B)).  Check (eq_refl : BB19_J19_w2_sq.tm (A, 1) = Some (0, TM.L, M)).
Check (eq_refl : BB19_J19_w2_sq.tm (B, 0) = Some (1, TM.R, C)).  Check (eq_refl : BB19_J19_w2_sq.tm (B, 1) = Some (1, TM.R, N)).
Check (eq_refl : BB19_J19_w2_sq.tm (C, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB19_J19_w2_sq.tm (C, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB19_J19_w2_sq.tm (D, 0) = Some (0, TM.L, E)).  Check (eq_refl : BB19_J19_w2_sq.tm (D, 1) = Some (1, TM.R, QQ)).
Check (eq_refl : BB19_J19_w2_sq.tm (E, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB19_J19_w2_sq.tm (E, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB19_J19_w2_sq.tm (F, 0) = Some (0, TM.L, G)).  Check (eq_refl : BB19_J19_w2_sq.tm (F, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB19_J19_w2_sq.tm (G, 0) = Some (1, TM.R, H)).  Check (eq_refl : BB19_J19_w2_sq.tm (G, 1) = Some (1, TM.R, I)).
Check (eq_refl : BB19_J19_w2_sq.tm (H, 0) = Some (0, TM.R, H)).  Check (eq_refl : BB19_J19_w2_sq.tm (H, 1) = Some (0, TM.R, C)).
Check (eq_refl : BB19_J19_w2_sq.tm (I, 0) = Some (0, TM.R, J)).  Check (eq_refl : BB19_J19_w2_sq.tm (I, 1) = Some (1, TM.R, H)).
Check (eq_refl : BB19_J19_w2_sq.tm (J, 0) = Some (0, TM.R, SS)).  Check (eq_refl : BB19_J19_w2_sq.tm (J, 1) = Some (0, TM.R, K)).
Check (eq_refl : BB19_J19_w2_sq.tm (K, 0) = Some (1, TM.L, N)).  Check (eq_refl : BB19_J19_w2_sq.tm (K, 1) = Some (1, TM.R, L)).
Check (eq_refl : BB19_J19_w2_sq.tm (L, 0) = Some (1, TM.L, M)).  Check (eq_refl : BB19_J19_w2_sq.tm (L, 1) = Some (1, TM.R, J)).
Check (eq_refl : BB19_J19_w2_sq.tm (M, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB19_J19_w2_sq.tm (M, 1) = Some (1, TM.L, M)).
Check (eq_refl : BB19_J19_w2_sq.tm (N, 0) = Some (0, TM.L, A)).  Check (eq_refl : BB19_J19_w2_sq.tm (N, 1) = Some (0, TM.R, O)).
Check (eq_refl : BB19_J19_w2_sq.tm (O, 0) = Some (0, TM.L, C)).  Check (eq_refl : BB19_J19_w2_sq.tm (O, 1) = Some (1, TM.R, P)).
Check (eq_refl : BB19_J19_w2_sq.tm (P, 0) = Some (0, TM.L, A)).  Check (eq_refl : BB19_J19_w2_sq.tm (P, 1) = Some (1, TM.R, N)).
Check (eq_refl : BB19_J19_w2_sq.tm (QQ, 0) = Some (0, TM.L, RR)).  Check (eq_refl : BB19_J19_w2_sq.tm (QQ, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB19_J19_w2_sq.tm (RR, 0) = Some (0, TM.R, I)).  Check (eq_refl : BB19_J19_w2_sq.tm (RR, 1) = Some (1, TM.L, RR)).
Check (eq_refl : BB19_J19_w2_sq.tm (SS, 0) = None).  Check (eq_refl : BB19_J19_w2_sq.tm (SS, 1) = Some (1, TM.L, L)).

Print BB19_J19_w2_sq.iter.
Print BB19_J19_w2_sq.f.
Print BB19_J19_w2_sq.f_omega.
Print BB19_J19_w2_sq.f_wk.
Print BB19_J19_w2_sq.f_w2.
Print BB19_J19_w2_sq.h.
Print BB19_J19_w2_sq.hc.
Print BB19_J19_w2_sq.G0.
Print BB19_J19_w2_sq.Gcy.
Print BB19_J19_w2_sq.G.
Print BB19_J19_w2_sq.ho.
Print BB19_J19_w2_sq.hoc.
Print BB19_J19_w2_sq.sym_val.
Print BB19_J19_w2_sq.count1.
Print BB19_J19_w2_sq.ones.

Check BB19_J19_w2_sq.halt.
Check BB19_J19_w2_sq.score_exact.
Check BB19_J19_w2_sq.sigma_lower_bound.

Print Assumptions BB19_J19_w2_sq.halt.
Print Assumptions BB19_J19_w2_sq.score_exact.
Print Assumptions BB19_J19_w2_sq.sigma_lower_bound.
