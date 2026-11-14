(** Independent probe for the BB30 proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB30_tm.tm] is the machine
    1RC1L[_---0LY_0RD1RW_0RE0RN_0RF0RF_0RG1RX_0RH1RF_0RI1RI_0LJ1RH_1LK1LU_0LL1LP_1LM0RD_0RD1LT_0RO1RV_1LP1RN_0LQ1LQ_0LR1LP_0LS1LA_1RD1LR_0RQ1LZ_0LT1LM_0RN1RN_1RH0R\_0LY1RF_1LU0LB_0LU1LJ_0LA1LA_0R^1R]_0R\1R\_1LJ1R\
    entry by entry (30 lines generated from the machine string, not from the Coq file; rows are fixed-width,
    state character c is constructor q + column(ord(c) - 65): A..Z -> qA..qZ, [ \ ] ^ -> qAA..qAD;
    Z is an ordinary state here; the only halt is B0 = ---, which is None), and the start configuration is the
    blank tape in state A; (2) the main theorems have the stated types; (3) they use no axioms.  It also prints
    the definitions the statements use. *)

From BB8 Require BB30_bound BB30_game BB30_halt Ord.
From BB8 Require Import Individual302.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = qA).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB30_tm.tm (qA, 0) = Some (1, R, qC)).  Check (eq_refl : BB30_tm.tm (qA, 1) = Some (1, L, qAA)).
Check (eq_refl : BB30_tm.tm (qB, 0) = None).  Check (eq_refl : BB30_tm.tm (qB, 1) = Some (0, L, qY)).
Check (eq_refl : BB30_tm.tm (qC, 0) = Some (0, R, qD)).  Check (eq_refl : BB30_tm.tm (qC, 1) = Some (1, R, qW)).
Check (eq_refl : BB30_tm.tm (qD, 0) = Some (0, R, qE)).  Check (eq_refl : BB30_tm.tm (qD, 1) = Some (0, R, qN)).
Check (eq_refl : BB30_tm.tm (qE, 0) = Some (0, R, qF)).  Check (eq_refl : BB30_tm.tm (qE, 1) = Some (0, R, qF)).
Check (eq_refl : BB30_tm.tm (qF, 0) = Some (0, R, qG)).  Check (eq_refl : BB30_tm.tm (qF, 1) = Some (1, R, qX)).
Check (eq_refl : BB30_tm.tm (qG, 0) = Some (0, R, qH)).  Check (eq_refl : BB30_tm.tm (qG, 1) = Some (1, R, qF)).
Check (eq_refl : BB30_tm.tm (qH, 0) = Some (0, R, qI)).  Check (eq_refl : BB30_tm.tm (qH, 1) = Some (1, R, qI)).
Check (eq_refl : BB30_tm.tm (qI, 0) = Some (0, L, qJ)).  Check (eq_refl : BB30_tm.tm (qI, 1) = Some (1, R, qH)).
Check (eq_refl : BB30_tm.tm (qJ, 0) = Some (1, L, qK)).  Check (eq_refl : BB30_tm.tm (qJ, 1) = Some (1, L, qU)).
Check (eq_refl : BB30_tm.tm (qK, 0) = Some (0, L, qL)).  Check (eq_refl : BB30_tm.tm (qK, 1) = Some (1, L, qP)).
Check (eq_refl : BB30_tm.tm (qL, 0) = Some (1, L, qM)).  Check (eq_refl : BB30_tm.tm (qL, 1) = Some (0, R, qD)).
Check (eq_refl : BB30_tm.tm (qM, 0) = Some (0, R, qD)).  Check (eq_refl : BB30_tm.tm (qM, 1) = Some (1, L, qT)).
Check (eq_refl : BB30_tm.tm (qN, 0) = Some (0, R, qO)).  Check (eq_refl : BB30_tm.tm (qN, 1) = Some (1, R, qV)).
Check (eq_refl : BB30_tm.tm (qO, 0) = Some (1, L, qP)).  Check (eq_refl : BB30_tm.tm (qO, 1) = Some (1, R, qN)).
Check (eq_refl : BB30_tm.tm (qP, 0) = Some (0, L, qQ)).  Check (eq_refl : BB30_tm.tm (qP, 1) = Some (1, L, qQ)).
Check (eq_refl : BB30_tm.tm (qQ, 0) = Some (0, L, qR)).  Check (eq_refl : BB30_tm.tm (qQ, 1) = Some (1, L, qP)).
Check (eq_refl : BB30_tm.tm (qR, 0) = Some (0, L, qS)).  Check (eq_refl : BB30_tm.tm (qR, 1) = Some (1, L, qA)).
Check (eq_refl : BB30_tm.tm (qS, 0) = Some (1, R, qD)).  Check (eq_refl : BB30_tm.tm (qS, 1) = Some (1, L, qR)).
Check (eq_refl : BB30_tm.tm (qT, 0) = Some (0, R, qQ)).  Check (eq_refl : BB30_tm.tm (qT, 1) = Some (1, L, qZ)).
Check (eq_refl : BB30_tm.tm (qU, 0) = Some (0, L, qT)).  Check (eq_refl : BB30_tm.tm (qU, 1) = Some (1, L, qM)).
Check (eq_refl : BB30_tm.tm (qV, 0) = Some (0, R, qN)).  Check (eq_refl : BB30_tm.tm (qV, 1) = Some (1, R, qN)).
Check (eq_refl : BB30_tm.tm (qW, 0) = Some (1, R, qH)).  Check (eq_refl : BB30_tm.tm (qW, 1) = Some (0, R, qAB)).
Check (eq_refl : BB30_tm.tm (qX, 0) = Some (0, L, qY)).  Check (eq_refl : BB30_tm.tm (qX, 1) = Some (1, R, qF)).
Check (eq_refl : BB30_tm.tm (qY, 0) = Some (1, L, qU)).  Check (eq_refl : BB30_tm.tm (qY, 1) = Some (0, L, qB)).
Check (eq_refl : BB30_tm.tm (qZ, 0) = Some (0, L, qU)).  Check (eq_refl : BB30_tm.tm (qZ, 1) = Some (1, L, qJ)).
Check (eq_refl : BB30_tm.tm (qAA, 0) = Some (0, L, qA)).  Check (eq_refl : BB30_tm.tm (qAA, 1) = Some (1, L, qA)).
Check (eq_refl : BB30_tm.tm (qAB, 0) = Some (0, R, qAD)).  Check (eq_refl : BB30_tm.tm (qAB, 1) = Some (1, R, qAC)).
Check (eq_refl : BB30_tm.tm (qAC, 0) = Some (0, R, qAB)).  Check (eq_refl : BB30_tm.tm (qAC, 1) = Some (1, R, qAB)).
Check (eq_refl : BB30_tm.tm (qAD, 0) = Some (1, L, qJ)).  Check (eq_refl : BB30_tm.tm (qAD, 1) = Some (1, R, qAB)).

Print Ord.fs.
Print Ord.fgh.
Print Ord.FGH.
Print Ord.tower.
Print Ord.powtower.
Print Ord.opow.
Print Ord.ofin.
Print Ord.orep.
Print Ord.one.
Print Hardy.HH.
Print BB30_halt.hs0.
Print BB30_game.ones.
Print BB30_game.count1.
Print BB30_game.sym_val.

Check BB30_halt.halt.
Check BB30_halt.hardy_bound.
Check BB30_halt.x0_eq.
Check BB30_bound.hardy_score.
Check BB30_bound.sigma_lower_bound_w2_9.
Check BB30_bound.sigma_lower_bound.

Print Assumptions BB30_halt.halt.
Print Assumptions BB30_halt.hardy_bound.
Print Assumptions BB30_halt.x0_eq.
Print Assumptions BB30_bound.hardy_score.
Print Assumptions BB30_bound.sigma_lower_bound_w2_9.
Print Assumptions BB30_bound.sigma_lower_bound.
