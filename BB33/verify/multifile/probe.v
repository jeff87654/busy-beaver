(** Independent probe for the BB33 proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB33_tm.tm] is the posted machine
    1LH1L^_---0LC_1LR0LB_1RF1LE_0LD1LD_0R_1RG_1RN0RK_0RI1RJ_1L^1RH_0RH1RH_0RL1RM_1L`1RK_0RK1RK_0RO1RO_0L`1RN_1R_1La_0RZ0RZ_0LX1LS_0R_1LT_0L`1LU_0LR1LV_0LS1LW_0LT1LX_0R]1LY_0LV1L`_0R[1R\_0RN1RZ_0LC1RZ_0La1L^_0L]1L]_0RQ0RH_1LA1LR_0LP1LD
    entry by entry (66 lines generated from the machine string, not from the Coq file; rows are fixed-width,
    state character c is constructor q + column(ord(c) - 65): A..Z -> qA..qZ, [ \ ] ^ _ ` a -> qAA..qAG; the halt B0 is
    None), and the start configuration is the blank tape in state A; (2) the main theorems have the stated types;
    (3) they use no axioms.  It also prints the definitions the statements use. *)

From BB8 Require BB33_bound BB33_game BB33_halt Ord.
From BB8 Require Import Individual332.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = qA).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB33_tm.tm (qA, 0) = Some (1, L, qH)).  Check (eq_refl : BB33_tm.tm (qA, 1) = Some (1, L, qAD)).
Check (eq_refl : BB33_tm.tm (qB, 0) = None).  Check (eq_refl : BB33_tm.tm (qB, 1) = Some (0, L, qC)).
Check (eq_refl : BB33_tm.tm (qC, 0) = Some (1, L, qR)).  Check (eq_refl : BB33_tm.tm (qC, 1) = Some (0, L, qB)).
Check (eq_refl : BB33_tm.tm (qD, 0) = Some (1, R, qF)).  Check (eq_refl : BB33_tm.tm (qD, 1) = Some (1, L, qE)).
Check (eq_refl : BB33_tm.tm (qE, 0) = Some (0, L, qD)).  Check (eq_refl : BB33_tm.tm (qE, 1) = Some (1, L, qD)).
Check (eq_refl : BB33_tm.tm (qF, 0) = Some (0, R, qAE)).  Check (eq_refl : BB33_tm.tm (qF, 1) = Some (1, R, qG)).
Check (eq_refl : BB33_tm.tm (qG, 0) = Some (1, R, qN)).  Check (eq_refl : BB33_tm.tm (qG, 1) = Some (0, R, qK)).
Check (eq_refl : BB33_tm.tm (qH, 0) = Some (0, R, qI)).  Check (eq_refl : BB33_tm.tm (qH, 1) = Some (1, R, qJ)).
Check (eq_refl : BB33_tm.tm (qI, 0) = Some (1, L, qAD)).  Check (eq_refl : BB33_tm.tm (qI, 1) = Some (1, R, qH)).
Check (eq_refl : BB33_tm.tm (qJ, 0) = Some (0, R, qH)).  Check (eq_refl : BB33_tm.tm (qJ, 1) = Some (1, R, qH)).
Check (eq_refl : BB33_tm.tm (qK, 0) = Some (0, R, qL)).  Check (eq_refl : BB33_tm.tm (qK, 1) = Some (1, R, qM)).
Check (eq_refl : BB33_tm.tm (qL, 0) = Some (1, L, qAF)).  Check (eq_refl : BB33_tm.tm (qL, 1) = Some (1, R, qK)).
Check (eq_refl : BB33_tm.tm (qM, 0) = Some (0, R, qK)).  Check (eq_refl : BB33_tm.tm (qM, 1) = Some (1, R, qK)).
Check (eq_refl : BB33_tm.tm (qN, 0) = Some (0, R, qO)).  Check (eq_refl : BB33_tm.tm (qN, 1) = Some (1, R, qO)).
Check (eq_refl : BB33_tm.tm (qO, 0) = Some (0, L, qAF)).  Check (eq_refl : BB33_tm.tm (qO, 1) = Some (1, R, qN)).
Check (eq_refl : BB33_tm.tm (qP, 0) = Some (1, R, qAE)).  Check (eq_refl : BB33_tm.tm (qP, 1) = Some (1, L, qAG)).
Check (eq_refl : BB33_tm.tm (qQ, 0) = Some (0, R, qZ)).  Check (eq_refl : BB33_tm.tm (qQ, 1) = Some (0, R, qZ)).
Check (eq_refl : BB33_tm.tm (qR, 0) = Some (0, L, qX)).  Check (eq_refl : BB33_tm.tm (qR, 1) = Some (1, L, qS)).
Check (eq_refl : BB33_tm.tm (qS, 0) = Some (0, R, qAE)).  Check (eq_refl : BB33_tm.tm (qS, 1) = Some (1, L, qT)).
Check (eq_refl : BB33_tm.tm (qT, 0) = Some (0, L, qAF)).  Check (eq_refl : BB33_tm.tm (qT, 1) = Some (1, L, qU)).
Check (eq_refl : BB33_tm.tm (qU, 0) = Some (0, L, qR)).  Check (eq_refl : BB33_tm.tm (qU, 1) = Some (1, L, qV)).
Check (eq_refl : BB33_tm.tm (qV, 0) = Some (0, L, qS)).  Check (eq_refl : BB33_tm.tm (qV, 1) = Some (1, L, qW)).
Check (eq_refl : BB33_tm.tm (qW, 0) = Some (0, L, qT)).  Check (eq_refl : BB33_tm.tm (qW, 1) = Some (1, L, qX)).
Check (eq_refl : BB33_tm.tm (qX, 0) = Some (0, R, qAC)).  Check (eq_refl : BB33_tm.tm (qX, 1) = Some (1, L, qY)).
Check (eq_refl : BB33_tm.tm (qY, 0) = Some (0, L, qV)).  Check (eq_refl : BB33_tm.tm (qY, 1) = Some (1, L, qAF)).
Check (eq_refl : BB33_tm.tm (qZ, 0) = Some (0, R, qAA)).  Check (eq_refl : BB33_tm.tm (qZ, 1) = Some (1, R, qAB)).
Check (eq_refl : BB33_tm.tm (qAA, 0) = Some (0, R, qN)).  Check (eq_refl : BB33_tm.tm (qAA, 1) = Some (1, R, qZ)).
Check (eq_refl : BB33_tm.tm (qAB, 0) = Some (0, L, qC)).  Check (eq_refl : BB33_tm.tm (qAB, 1) = Some (1, R, qZ)).
Check (eq_refl : BB33_tm.tm (qAC, 0) = Some (0, L, qAG)).  Check (eq_refl : BB33_tm.tm (qAC, 1) = Some (1, L, qAD)).
Check (eq_refl : BB33_tm.tm (qAD, 0) = Some (0, L, qAC)).  Check (eq_refl : BB33_tm.tm (qAD, 1) = Some (1, L, qAC)).
Check (eq_refl : BB33_tm.tm (qAE, 0) = Some (0, R, qQ)).  Check (eq_refl : BB33_tm.tm (qAE, 1) = Some (0, R, qH)).
Check (eq_refl : BB33_tm.tm (qAF, 0) = Some (1, L, qA)).  Check (eq_refl : BB33_tm.tm (qAF, 1) = Some (1, L, qR)).
Check (eq_refl : BB33_tm.tm (qAG, 0) = Some (0, L, qP)).  Check (eq_refl : BB33_tm.tm (qAG, 1) = Some (1, L, qD)).

Print Ord.fs.
Print Ord.fgh.
Print Ord.FGH.
Print Ord.tower.
Print Ord.powtower.
Print Ord.opow.
Print Ord.ofin.
Print Ord.orep.
Print Ord.one.
Print BB33_game.ones.
Print BB33_game.count1.
Print BB33_game.sym_val.

Check BB33_halt.halt.
Check BB33_bound.hardy_score.
Check BB33_bound.sigma_lower_bound_w6.
Check BB33_bound.sigma_lower_bound.

Print Assumptions BB33_halt.halt.
Print Assumptions BB33_bound.hardy_score.
Print Assumptions BB33_bound.sigma_lower_bound_w6.
Print Assumptions BB33_bound.sigma_lower_bound.
