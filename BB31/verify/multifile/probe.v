(** Independent probe for the BB31 proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB31_tm.tm] is the posted machine
    0RK1RK_---0LC_1LQ0LB_1RF1LE_0LD1LD_0R\1RG_1RM0RK_0RI1RJ_1L[1RH_0RH1RH_0RL1RA_1L]1RK_0RN1RN_0L]1RM_1R\1L^_0RW0RW_0LU1LR_0R\1LS_0L]1LT_0LQ1LU_0RZ1LV_0LS1L]_0RX1RY_0RM1RW_0LC1RW_0L^1L[_0LZ1LZ_0RP0RH_1L_1LQ_0LO1LD_1LH1L[
    entry by entry (62 lines generated from the machine string, not from the Coq file; rows are fixed-width,
    state character c is constructor q + column(ord(c) - 65): A..Z -> qA..qZ, [ \ ] ^ _ ` a -> qAA..qAG; the halt B0 is
    None), and the start configuration is the blank tape in state A; (2) the main theorems have the stated types;
    (3) they use no axioms.  It also prints the definitions the statements use. *)

From BB8 Require BB31_bound BB31_game BB31_halt Ord.
From BB8 Require Import Individual312.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = qA).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB31_tm.tm (qA, 0) = Some (0, R, qK)).  Check (eq_refl : BB31_tm.tm (qA, 1) = Some (1, R, qK)).
Check (eq_refl : BB31_tm.tm (qB, 0) = None).  Check (eq_refl : BB31_tm.tm (qB, 1) = Some (0, L, qC)).
Check (eq_refl : BB31_tm.tm (qC, 0) = Some (1, L, qQ)).  Check (eq_refl : BB31_tm.tm (qC, 1) = Some (0, L, qB)).
Check (eq_refl : BB31_tm.tm (qD, 0) = Some (1, R, qF)).  Check (eq_refl : BB31_tm.tm (qD, 1) = Some (1, L, qE)).
Check (eq_refl : BB31_tm.tm (qE, 0) = Some (0, L, qD)).  Check (eq_refl : BB31_tm.tm (qE, 1) = Some (1, L, qD)).
Check (eq_refl : BB31_tm.tm (qF, 0) = Some (0, R, qAB)).  Check (eq_refl : BB31_tm.tm (qF, 1) = Some (1, R, qG)).
Check (eq_refl : BB31_tm.tm (qG, 0) = Some (1, R, qM)).  Check (eq_refl : BB31_tm.tm (qG, 1) = Some (0, R, qK)).
Check (eq_refl : BB31_tm.tm (qH, 0) = Some (0, R, qI)).  Check (eq_refl : BB31_tm.tm (qH, 1) = Some (1, R, qJ)).
Check (eq_refl : BB31_tm.tm (qI, 0) = Some (1, L, qAA)).  Check (eq_refl : BB31_tm.tm (qI, 1) = Some (1, R, qH)).
Check (eq_refl : BB31_tm.tm (qJ, 0) = Some (0, R, qH)).  Check (eq_refl : BB31_tm.tm (qJ, 1) = Some (1, R, qH)).
Check (eq_refl : BB31_tm.tm (qK, 0) = Some (0, R, qL)).  Check (eq_refl : BB31_tm.tm (qK, 1) = Some (1, R, qA)).
Check (eq_refl : BB31_tm.tm (qL, 0) = Some (1, L, qAC)).  Check (eq_refl : BB31_tm.tm (qL, 1) = Some (1, R, qK)).
Check (eq_refl : BB31_tm.tm (qM, 0) = Some (0, R, qN)).  Check (eq_refl : BB31_tm.tm (qM, 1) = Some (1, R, qN)).
Check (eq_refl : BB31_tm.tm (qN, 0) = Some (0, L, qAC)).  Check (eq_refl : BB31_tm.tm (qN, 1) = Some (1, R, qM)).
Check (eq_refl : BB31_tm.tm (qO, 0) = Some (1, R, qAB)).  Check (eq_refl : BB31_tm.tm (qO, 1) = Some (1, L, qAD)).
Check (eq_refl : BB31_tm.tm (qP, 0) = Some (0, R, qW)).  Check (eq_refl : BB31_tm.tm (qP, 1) = Some (0, R, qW)).
Check (eq_refl : BB31_tm.tm (qQ, 0) = Some (0, L, qU)).  Check (eq_refl : BB31_tm.tm (qQ, 1) = Some (1, L, qR)).
Check (eq_refl : BB31_tm.tm (qR, 0) = Some (0, R, qAB)).  Check (eq_refl : BB31_tm.tm (qR, 1) = Some (1, L, qS)).
Check (eq_refl : BB31_tm.tm (qS, 0) = Some (0, L, qAC)).  Check (eq_refl : BB31_tm.tm (qS, 1) = Some (1, L, qT)).
Check (eq_refl : BB31_tm.tm (qT, 0) = Some (0, L, qQ)).  Check (eq_refl : BB31_tm.tm (qT, 1) = Some (1, L, qU)).
Check (eq_refl : BB31_tm.tm (qU, 0) = Some (0, R, qZ)).  Check (eq_refl : BB31_tm.tm (qU, 1) = Some (1, L, qV)).
Check (eq_refl : BB31_tm.tm (qV, 0) = Some (0, L, qS)).  Check (eq_refl : BB31_tm.tm (qV, 1) = Some (1, L, qAC)).
Check (eq_refl : BB31_tm.tm (qW, 0) = Some (0, R, qX)).  Check (eq_refl : BB31_tm.tm (qW, 1) = Some (1, R, qY)).
Check (eq_refl : BB31_tm.tm (qX, 0) = Some (0, R, qM)).  Check (eq_refl : BB31_tm.tm (qX, 1) = Some (1, R, qW)).
Check (eq_refl : BB31_tm.tm (qY, 0) = Some (0, L, qC)).  Check (eq_refl : BB31_tm.tm (qY, 1) = Some (1, R, qW)).
Check (eq_refl : BB31_tm.tm (qZ, 0) = Some (0, L, qAD)).  Check (eq_refl : BB31_tm.tm (qZ, 1) = Some (1, L, qAA)).
Check (eq_refl : BB31_tm.tm (qAA, 0) = Some (0, L, qZ)).  Check (eq_refl : BB31_tm.tm (qAA, 1) = Some (1, L, qZ)).
Check (eq_refl : BB31_tm.tm (qAB, 0) = Some (0, R, qP)).  Check (eq_refl : BB31_tm.tm (qAB, 1) = Some (0, R, qH)).
Check (eq_refl : BB31_tm.tm (qAC, 0) = Some (1, L, qAE)).  Check (eq_refl : BB31_tm.tm (qAC, 1) = Some (1, L, qQ)).
Check (eq_refl : BB31_tm.tm (qAD, 0) = Some (0, L, qO)).  Check (eq_refl : BB31_tm.tm (qAD, 1) = Some (1, L, qD)).
Check (eq_refl : BB31_tm.tm (qAE, 0) = Some (1, L, qH)).  Check (eq_refl : BB31_tm.tm (qAE, 1) = Some (1, L, qAA)).

Print Ord.fs.
Print Ord.fgh.
Print Ord.FGH.
Print Ord.tower.
Print Ord.opow.
Print Ord.one.
Print BB31_game.ones.
Print BB31_game.count1.
Print BB31_game.sym_val.

Check BB31_halt.halt.
Check BB31_bound.hardy_score.
Check BB31_bound.sigma_lower_bound_w4.
Check BB31_bound.sigma_lower_bound.

Print Assumptions BB31_halt.halt.
Print Assumptions BB31_bound.hardy_score.
Print Assumptions BB31_bound.sigma_lower_bound_w4.
Print Assumptions BB31_bound.sigma_lower_bound.
