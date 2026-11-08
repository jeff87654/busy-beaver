(** Independent probe for the J19 (Jacobzheng) proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB19_JZ19.tm] is the declared machine
    1RQ1RL_0LI1RC_0LD1LF_0RA1LD_1RB1RE_1LH0LG_1LF1LG_1RE1RM_1LJ1LI_0LK1LI_1RL1RA_0RL0RE_0LN1RM_1LO0LO_1RE1LP_1LN1LN_1LR1RQ_1RZ1LS_0LE0LR
    entry by entry (these 38 checks were generated from the machine string, not from the Coq file; the halting
    transition (1RZ) is None; the 17th, 18th and 19th states, letters Q, R and S, are the constructors QQ, RR and SS), and the start configuration is the blank tape in state A;
    (2) the main theorems have the stated types; (3) they use no axioms.  It also prints the definitions the
    statements use.  The setup names states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB19_JZ19.
From BB8 Require Import Individual192.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB19_JZ19.tm (A, 0) = Some (1, TM.R, QQ)).  Check (eq_refl : BB19_JZ19.tm (A, 1) = Some (1, TM.R, L)).
Check (eq_refl : BB19_JZ19.tm (B, 0) = Some (0, TM.L, I)).  Check (eq_refl : BB19_JZ19.tm (B, 1) = Some (1, TM.R, C)).
Check (eq_refl : BB19_JZ19.tm (C, 0) = Some (0, TM.L, D)).  Check (eq_refl : BB19_JZ19.tm (C, 1) = Some (1, TM.L, F)).
Check (eq_refl : BB19_JZ19.tm (D, 0) = Some (0, TM.R, A)).  Check (eq_refl : BB19_JZ19.tm (D, 1) = Some (1, TM.L, D)).
Check (eq_refl : BB19_JZ19.tm (E, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB19_JZ19.tm (E, 1) = Some (1, TM.R, E)).
Check (eq_refl : BB19_JZ19.tm (F, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB19_JZ19.tm (F, 1) = Some (0, TM.L, G)).
Check (eq_refl : BB19_JZ19.tm (G, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB19_JZ19.tm (G, 1) = Some (1, TM.L, G)).
Check (eq_refl : BB19_JZ19.tm (H, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB19_JZ19.tm (H, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB19_JZ19.tm (I, 0) = Some (1, TM.L, J)).  Check (eq_refl : BB19_JZ19.tm (I, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB19_JZ19.tm (J, 0) = Some (0, TM.L, K)).  Check (eq_refl : BB19_JZ19.tm (J, 1) = Some (1, TM.L, I)).
Check (eq_refl : BB19_JZ19.tm (K, 0) = Some (1, TM.R, L)).  Check (eq_refl : BB19_JZ19.tm (K, 1) = Some (1, TM.R, A)).
Check (eq_refl : BB19_JZ19.tm (L, 0) = Some (0, TM.R, L)).  Check (eq_refl : BB19_JZ19.tm (L, 1) = Some (0, TM.R, E)).
Check (eq_refl : BB19_JZ19.tm (M, 0) = Some (0, TM.L, N)).  Check (eq_refl : BB19_JZ19.tm (M, 1) = Some (1, TM.R, M)).
Check (eq_refl : BB19_JZ19.tm (N, 0) = Some (1, TM.L, O)).  Check (eq_refl : BB19_JZ19.tm (N, 1) = Some (0, TM.L, O)).
Check (eq_refl : BB19_JZ19.tm (O, 0) = Some (1, TM.R, E)).  Check (eq_refl : BB19_JZ19.tm (O, 1) = Some (1, TM.L, P)).
Check (eq_refl : BB19_JZ19.tm (P, 0) = Some (1, TM.L, N)).  Check (eq_refl : BB19_JZ19.tm (P, 1) = Some (1, TM.L, N)).
Check (eq_refl : BB19_JZ19.tm (QQ, 0) = Some (1, TM.L, RR)).  Check (eq_refl : BB19_JZ19.tm (QQ, 1) = Some (1, TM.R, QQ)).
Check (eq_refl : BB19_JZ19.tm (RR, 0) = None).  Check (eq_refl : BB19_JZ19.tm (RR, 1) = Some (1, TM.L, SS)).
Check (eq_refl : BB19_JZ19.tm (SS, 0) = Some (0, TM.L, E)).  Check (eq_refl : BB19_JZ19.tm (SS, 1) = Some (0, TM.L, RR)).

Print BB19_JZ19.iter.
Print BB19_JZ19.U.
Print BB19_JZ19.Wc.
Print BB19_JZ19.G.
Print BB19_JZ19.T.
Print BB19_JZ19.f.
Print BB19_JZ19.f_omega.
Print BB19_JZ19.f_wk.
Print BB19_JZ19.sym_val.
Print BB19_JZ19.count1.
Print BB19_JZ19.ones.

Check BB19_JZ19.halt.
Check BB19_JZ19.score_exact.
Check BB19_JZ19.sigma_lower_bound.

Print Assumptions BB19_JZ19.halt.
Print Assumptions BB19_JZ19.score_exact.
Print Assumptions BB19_JZ19.sigma_lower_bound.
