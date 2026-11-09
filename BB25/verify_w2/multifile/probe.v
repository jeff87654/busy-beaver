(** Independent probe for the W2PR omega^2 bound proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB25_W2PR_w2.tm] is the declared machine
    0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR
    entry by entry (these 50 checks were generated from the machine string, not from the Coq file; the halting
    transition (1RZ) is None; the 17th to 25th states, letters Q to Y, are the constructors QQ, RR, SS, TT, UU, VV, WW, XX and YY), and the start configuration is the blank tape in state A;
    (2) the main theorems have the stated types; (3) they use no axioms.  It also prints the definitions the
    statements use.  The setup names states L and O, so directions are written TM.L / TM.R. *)

From BB8 Require BB25_W2PR_w2 BB_FGH_wa BB21_B21_absdef BB25_W2PR_run BB25_W2PR_score BB21_B21_score.
From BB8 Require Import Individual252.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB25_W2PR_w2.tm (A, 0) = Some (0, TM.L, I)).  Check (eq_refl : BB25_W2PR_w2.tm (A, 1) = Some (0, TM.L, F)).
Check (eq_refl : BB25_W2PR_w2.tm (B, 0) = Some (0, TM.R, J)).  Check (eq_refl : BB25_W2PR_w2.tm (B, 1) = Some (1, TM.R, G)).
Check (eq_refl : BB25_W2PR_w2.tm (C, 0) = Some (0, TM.R, D)).  Check (eq_refl : BB25_W2PR_w2.tm (C, 1) = Some (1, TM.L, C)).
Check (eq_refl : BB25_W2PR_w2.tm (D, 0) = Some (1, TM.R, H)).  Check (eq_refl : BB25_W2PR_w2.tm (D, 1) = Some (1, TM.R, E)).
Check (eq_refl : BB25_W2PR_w2.tm (E, 0) = Some (1, TM.L, O)).  Check (eq_refl : BB25_W2PR_w2.tm (E, 1) = Some (0, TM.R, H)).
Check (eq_refl : BB25_W2PR_w2.tm (F, 0) = Some (1, TM.L, A)).  Check (eq_refl : BB25_W2PR_w2.tm (F, 1) = Some (1, TM.L, F)).
Check (eq_refl : BB25_W2PR_w2.tm (G, 0) = Some (0, TM.L, C)).  Check (eq_refl : BB25_W2PR_w2.tm (G, 1) = Some (1, TM.L, A)).
Check (eq_refl : BB25_W2PR_w2.tm (H, 0) = Some (1, TM.R, B)).  Check (eq_refl : BB25_W2PR_w2.tm (H, 1) = Some (1, TM.R, H)).
Check (eq_refl : BB25_W2PR_w2.tm (I, 0) = Some (1, TM.R, D)).  Check (eq_refl : BB25_W2PR_w2.tm (I, 1) = Some (0, TM.L, F)).
Check (eq_refl : BB25_W2PR_w2.tm (J, 0) = Some (1, TM.L, P)).  Check (eq_refl : BB25_W2PR_w2.tm (J, 1) = Some (0, TM.R, K)).
Check (eq_refl : BB25_W2PR_w2.tm (K, 0) = Some (0, TM.L, M)).  Check (eq_refl : BB25_W2PR_w2.tm (K, 1) = Some (1, TM.L, L)).
Check (eq_refl : BB25_W2PR_w2.tm (L, 0) = Some (0, TM.L, L)).  Check (eq_refl : BB25_W2PR_w2.tm (L, 1) = Some (1, TM.L, M)).
Check (eq_refl : BB25_W2PR_w2.tm (M, 0) = Some (1, TM.L, E)).  Check (eq_refl : BB25_W2PR_w2.tm (M, 1) = Some (1, TM.L, N)).
Check (eq_refl : BB25_W2PR_w2.tm (N, 0) = Some (0, TM.R, QQ)).  Check (eq_refl : BB25_W2PR_w2.tm (N, 1) = Some (0, TM.L, M)).
Check (eq_refl : BB25_W2PR_w2.tm (O, 0) = Some (0, TM.R, P)).  Check (eq_refl : BB25_W2PR_w2.tm (O, 1) = Some (1, TM.L, O)).
Check (eq_refl : BB25_W2PR_w2.tm (P, 0) = Some (1, TM.L, RR)).  Check (eq_refl : BB25_W2PR_w2.tm (P, 1) = Some (0, TM.R, H)).
Check (eq_refl : BB25_W2PR_w2.tm (QQ, 0) = Some (1, TM.L, F)).  Check (eq_refl : BB25_W2PR_w2.tm (QQ, 1) = Some (1, TM.R, QQ)).
Check (eq_refl : BB25_W2PR_w2.tm (RR, 0) = None).  Check (eq_refl : BB25_W2PR_w2.tm (RR, 1) = Some (0, TM.L, SS)).
Check (eq_refl : BB25_W2PR_w2.tm (SS, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB25_W2PR_w2.tm (SS, 1) = Some (0, TM.L, TT)).
Check (eq_refl : BB25_W2PR_w2.tm (TT, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB25_W2PR_w2.tm (TT, 1) = Some (1, TM.L, UU)).
Check (eq_refl : BB25_W2PR_w2.tm (UU, 0) = Some (0, TM.L, E)).  Check (eq_refl : BB25_W2PR_w2.tm (UU, 1) = Some (1, TM.L, VV)).
Check (eq_refl : BB25_W2PR_w2.tm (VV, 0) = Some (0, TM.L, H)).  Check (eq_refl : BB25_W2PR_w2.tm (VV, 1) = Some (0, TM.L, WW)).
Check (eq_refl : BB25_W2PR_w2.tm (WW, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB25_W2PR_w2.tm (WW, 1) = Some (0, TM.L, XX)).
Check (eq_refl : BB25_W2PR_w2.tm (XX, 0) = Some (1, TM.L, H)).  Check (eq_refl : BB25_W2PR_w2.tm (XX, 1) = Some (1, TM.L, YY)).
Check (eq_refl : BB25_W2PR_w2.tm (YY, 0) = Some (0, TM.L, E)).  Check (eq_refl : BB25_W2PR_w2.tm (YY, 1) = Some (1, TM.L, RR)).

Print BB_FGH_wa.f.
Print BB_FGH_wa.f_wa.
Print BB_FGH_wa.f_wsq.
Print BB21_B21_absdef.iter.
Print BB21_B21_absdef.h.
Print BB25_W2PR_run.Fh.
Print BB25_W2PR_run.tet.
Print BB21_B21_score.tet.
Print BB25_W2PR_score.sym_val.
Print BB25_W2PR_score.count1.
Print BB25_W2PR_score.onesN.

Check BB25_W2PR_w2.halt.
Check BB25_W2PR_w2.sigma_lower_bound.
Check BB25_W2PR_w2.sigma_lower_bound_wsq.
Check BB25_W2PR_w2.beats_B21.

Print Assumptions BB25_W2PR_w2.halt.
Print Assumptions BB25_W2PR_w2.sigma_lower_bound.
Print Assumptions BB25_W2PR_w2.sigma_lower_bound_wsq.
Print Assumptions BB25_W2PR_w2.beats_B21.
