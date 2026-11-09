(** Independent probe for the R18a proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB18_R18a.tm] is the declared machine
    1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0LQ0LO_1LR1LP_0LQ1LN_0RO1LB_0LL1RZ
    entry by entry (these 36 checks were generated from the machine string, not from the Coq file; the halting
    transition (1RZ) is None; the 17th and 18th states, letters Q and R, are the constructors QQ and RR), and the start configuration is the blank tape in state A;
    (2) the main theorems have the stated types; (3) they use no axioms.  It also prints the definitions the
    statements use.  The setup names states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB18_R18a.
From BB8 Require Import Individual182.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB18_R18a.tm (A, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB18_R18a.tm (A, 1) = Some (0, TM.L, G)).
Check (eq_refl : BB18_R18a.tm (B, 0) = Some (0, TM.L, I)).  Check (eq_refl : BB18_R18a.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB18_R18a.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB18_R18a.tm (C, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB18_R18a.tm (D, 0) = Some (0, TM.R, E)).  Check (eq_refl : BB18_R18a.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB18_R18a.tm (E, 0) = Some (0, TM.R, H)).  Check (eq_refl : BB18_R18a.tm (E, 1) = Some (1, TM.R, L)).
Check (eq_refl : BB18_R18a.tm (F, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB18_R18a.tm (F, 1) = Some (1, TM.R, F)).
Check (eq_refl : BB18_R18a.tm (G, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB18_R18a.tm (G, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB18_R18a.tm (H, 0) = Some (1, TM.R, F)).  Check (eq_refl : BB18_R18a.tm (H, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB18_R18a.tm (I, 0) = Some (1, TM.L, J)).  Check (eq_refl : BB18_R18a.tm (I, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB18_R18a.tm (J, 0) = Some (0, TM.L, K)).  Check (eq_refl : BB18_R18a.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB18_R18a.tm (K, 0) = Some (1, TM.R, L)).  Check (eq_refl : BB18_R18a.tm (K, 1) = Some (1, TM.R, E)).
Check (eq_refl : BB18_R18a.tm (L, 0) = Some (0, TM.R, L)).  Check (eq_refl : BB18_R18a.tm (L, 1) = Some (0, TM.R, F)).
Check (eq_refl : BB18_R18a.tm (M, 0) = Some (0, TM.L, N)).  Check (eq_refl : BB18_R18a.tm (M, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB18_R18a.tm (N, 0) = Some (0, TM.L, QQ)).  Check (eq_refl : BB18_R18a.tm (N, 1) = Some (0, TM.L, O)).
Check (eq_refl : BB18_R18a.tm (O, 0) = Some (1, TM.L, RR)).  Check (eq_refl : BB18_R18a.tm (O, 1) = Some (1, TM.L, P)).
Check (eq_refl : BB18_R18a.tm (P, 0) = Some (0, TM.L, QQ)).  Check (eq_refl : BB18_R18a.tm (P, 1) = Some (1, TM.L, N)).
Check (eq_refl : BB18_R18a.tm (QQ, 0) = Some (0, TM.R, O)).  Check (eq_refl : BB18_R18a.tm (QQ, 1) = Some (1, TM.L, B)).
Check (eq_refl : BB18_R18a.tm (RR, 0) = Some (0, TM.L, L)).  Check (eq_refl : BB18_R18a.tm (RR, 1) = None).

Print BB18_R18a.iter.
Print BB18_R18a.h.
Print BB18_R18a.hc.
Print BB18_R18a.Gcy.
Print BB18_R18a.G.
Print BB18_R18a.ho.
Print BB18_R18a.hoc.
Print BB18_R18a.f.
Print BB18_R18a.f_omega.
Print BB18_R18a.f_wk.
Print BB18_R18a.f_w2.
Print BB18_R18a.sym_val.
Print BB18_R18a.count1.
Print BB18_R18a.ones.

Check BB18_R18a.halt.
Check BB18_R18a.score_exact.
Check BB18_R18a.sigma_lower_bound.
Check BB18_R18a.beats_J19.
Check BB18_R18a.beats_M18_229.

Print Assumptions BB18_R18a.halt.
Print Assumptions BB18_R18a.score_exact.
Print Assumptions BB18_R18a.sigma_lower_bound.
Print Assumptions BB18_R18a.beats_J19.
Print Assumptions BB18_R18a.beats_M18_229.
