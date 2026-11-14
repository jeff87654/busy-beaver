(** Independent probe for the R18c proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB18_R18c.tm] is the declared machine
    1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_1LQ0LO_0LR1LP_1LQ1LN_1LF0LM_0RC1RZ
    entry by entry, and that the table of [BB18_R18c.tm_tnf] (the same machine with its states renamed, used by the
    _tnf theorems) is
    1LB0LP_1RC1RJ_1RD1RC_0LE1RO_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RB1RH_0LK1RJ_1LN0LL_0LR1LM_1LN1LK_1LC0LJ_0LQ1LA_1LA1LP_0RI1LQ_0RO1RZ
    (these 72 checks were generated from the two strings, not from the Coq file; the halting transition,
    R1 in tm and R1 in tm_tnf, is None; the states after P are the constructors QQ, RR),
    and the start configuration is the blank tape in state A; (2) the main theorems have the stated types; (3) they
    use no axioms.  It also prints the definitions the statements use.  The setup names states L and O, so directions
    are written TM.L / TM.R. *)

From BB8 Require BB18_R18c.
From BB8 Require Import Individual182.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB18_R18c.tm (A, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB18_R18c.tm (A, 1) = Some (0, TM.L, G)).
Check (eq_refl : BB18_R18c.tm (B, 0) = Some (0, TM.L, I)).  Check (eq_refl : BB18_R18c.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB18_R18c.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB18_R18c.tm (C, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB18_R18c.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB18_R18c.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB18_R18c.tm (E, 0) = Some (0, TM.R, H)).  Check (eq_refl : BB18_R18c.tm (E, 1) = Some (1, TM.R, L)).
Check (eq_refl : BB18_R18c.tm (F, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB18_R18c.tm (F, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB18_R18c.tm (G, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB18_R18c.tm (G, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB18_R18c.tm (H, 0) = Some (1, TM.R, F)).  Check (eq_refl : BB18_R18c.tm (H, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB18_R18c.tm (I, 0) = Some (1, TM.L, J)).  Check (eq_refl : BB18_R18c.tm (I, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB18_R18c.tm (J, 0) = Some (0, TM.L, K)).  Check (eq_refl : BB18_R18c.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB18_R18c.tm (K, 0) = Some (1, TM.R, L)).  Check (eq_refl : BB18_R18c.tm (K, 1) = Some (1, TM.R, E)).
Check (eq_refl : BB18_R18c.tm (L, 0) = Some (0, TM.R, L)).  Check (eq_refl : BB18_R18c.tm (L, 1) = Some (0, TM.R, F)).
Check (eq_refl : BB18_R18c.tm (M, 0) = Some (0, TM.L, N)).  Check (eq_refl : BB18_R18c.tm (M, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB18_R18c.tm (N, 0) = Some (1, TM.L, QQ)).  Check (eq_refl : BB18_R18c.tm (N, 1) = Some (0, TM.L, O)).
Check (eq_refl : BB18_R18c.tm (O, 0) = Some (0, TM.L, RR)).  Check (eq_refl : BB18_R18c.tm (O, 1) = Some (1, TM.L, P)).
Check (eq_refl : BB18_R18c.tm (P, 0) = Some (1, TM.L, QQ)).  Check (eq_refl : BB18_R18c.tm (P, 1) = Some (1, TM.L, N)).
Check (eq_refl : BB18_R18c.tm (QQ, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB18_R18c.tm (QQ, 1) = Some (0, TM.L, M)).
Check (eq_refl : BB18_R18c.tm (RR, 0) = Some (0, TM.R, C)).  Check (eq_refl : BB18_R18c.tm (RR, 1) = None).
Check (eq_refl : BB18_R18c.tm_tnf (A, 0) = Some (1, TM.L, B)).  Check (eq_refl : BB18_R18c.tm_tnf (A, 1) = Some (0, TM.L, P)).
Check (eq_refl : BB18_R18c.tm_tnf (B, 0) = Some (1, TM.R, C)).  Check (eq_refl : BB18_R18c.tm_tnf (B, 1) = Some (1, TM.R, J)).
Check (eq_refl : BB18_R18c.tm_tnf (C, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB18_R18c.tm_tnf (C, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB18_R18c.tm_tnf (D, 0) = Some (0, TM.L, E)).  Check (eq_refl : BB18_R18c.tm_tnf (D, 1) = Some (1, TM.R, O)).
Check (eq_refl : BB18_R18c.tm_tnf (E, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB18_R18c.tm_tnf (E, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB18_R18c.tm_tnf (F, 0) = Some (0, TM.L, G)).  Check (eq_refl : BB18_R18c.tm_tnf (F, 1) = Some (1, TM.L, E)).
Check (eq_refl : BB18_R18c.tm_tnf (G, 0) = Some (1, TM.R, H)).  Check (eq_refl : BB18_R18c.tm_tnf (G, 1) = Some (1, TM.R, I)).
Check (eq_refl : BB18_R18c.tm_tnf (H, 0) = Some (0, TM.R, H)).  Check (eq_refl : BB18_R18c.tm_tnf (H, 1) = Some (0, TM.R, C)).
Check (eq_refl : BB18_R18c.tm_tnf (I, 0) = Some (0, TM.R, B)).  Check (eq_refl : BB18_R18c.tm_tnf (I, 1) = Some (1, TM.R, H)).
Check (eq_refl : BB18_R18c.tm_tnf (J, 0) = Some (0, TM.L, K)).  Check (eq_refl : BB18_R18c.tm_tnf (J, 1) = Some (1, TM.R, J)).
Check (eq_refl : BB18_R18c.tm_tnf (K, 0) = Some (1, TM.L, N)).  Check (eq_refl : BB18_R18c.tm_tnf (K, 1) = Some (0, TM.L, L)).
Check (eq_refl : BB18_R18c.tm_tnf (L, 0) = Some (0, TM.L, RR)).  Check (eq_refl : BB18_R18c.tm_tnf (L, 1) = Some (1, TM.L, M)).
Check (eq_refl : BB18_R18c.tm_tnf (M, 0) = Some (1, TM.L, N)).  Check (eq_refl : BB18_R18c.tm_tnf (M, 1) = Some (1, TM.L, K)).
Check (eq_refl : BB18_R18c.tm_tnf (N, 0) = Some (1, TM.L, C)).  Check (eq_refl : BB18_R18c.tm_tnf (N, 1) = Some (0, TM.L, J)).
Check (eq_refl : BB18_R18c.tm_tnf (O, 0) = Some (0, TM.L, QQ)).  Check (eq_refl : BB18_R18c.tm_tnf (O, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB18_R18c.tm_tnf (P, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB18_R18c.tm_tnf (P, 1) = Some (1, TM.L, P)).
Check (eq_refl : BB18_R18c.tm_tnf (QQ, 0) = Some (0, TM.R, I)).  Check (eq_refl : BB18_R18c.tm_tnf (QQ, 1) = Some (1, TM.L, QQ)).
Check (eq_refl : BB18_R18c.tm_tnf (RR, 0) = Some (0, TM.R, O)).  Check (eq_refl : BB18_R18c.tm_tnf (RR, 1) = None).

Print BB18_R18c.iter.
Print BB18_R18c.f.
Print BB18_R18c.f_omega.
Print BB18_R18c.f_wk.
Print BB18_R18c.f_w2.
Print BB18_R18c.h.
Print BB18_R18c.hc.
Print BB18_R18c.Gcy.
Print BB18_R18c.G.
Print BB18_R18c.ho.
Print BB18_R18c.hoc.
Print BB18_R18c.sym_val.
Print BB18_R18c.count1.
Print BB18_R18c.ones.

Check BB18_R18c.halt.
Check BB18_R18c.score_exact.
Check BB18_R18c.sigma_lower_bound.
Check BB18_R18c.halt_tnf.
Check BB18_R18c.sigma_lower_bound_tnf.

Print Assumptions BB18_R18c.halt.
Print Assumptions BB18_R18c.score_exact.
Print Assumptions BB18_R18c.sigma_lower_bound.
Print Assumptions BB18_R18c.halt_tnf.
Print Assumptions BB18_R18c.sigma_lower_bound_tnf.
