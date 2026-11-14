(** Independent probe for the BB32 proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB32_tm.tm] is the machine
    1RC1LT_---0LZ_0RD1RU_0RE0RW_0RF0RF_0RG1RS_0RH1RF_0RI1RI_0LJ1RH_1LK1L[_0RL1LO_1RM1RL_0RN1RV_1LJ1RM_0LP1LP_0LQ1LO_0LR1LA_1RD1LQ_0LZ1RF_0LA1LA_1RH0RM_0RM1RM_0RX1RY_1LO1RW_0RW1RW_1L[0LB_0L_1L\_0RD1L]_0LJ1L^_0L[1L__0RP1L`_0L]1LJ
    entry by entry (32 lines generated from the machine string, not from the Coq file; rows are fixed-width,
    state character c is constructor q + column(ord(c) - 65): A..Z -> qA..qZ, [ \ ] ^ _ ` -> qAA..qAF;
    Z is an ordinary state here; the only halt is B0 = ---, which is None), and the start configuration is the
    blank tape in state A; (2) the main theorems have the stated types; (3) they use no axioms.  It also prints
    the definitions the statements use. *)

From BB8 Require BB32_bound BB32_game BB32_halt Ord.
From BB8 Require Import Individual322.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = qA).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB32_tm.tm (qA, 0) = Some (1, R, qC)).  Check (eq_refl : BB32_tm.tm (qA, 1) = Some (1, L, qT)).
Check (eq_refl : BB32_tm.tm (qB, 0) = None).  Check (eq_refl : BB32_tm.tm (qB, 1) = Some (0, L, qZ)).
Check (eq_refl : BB32_tm.tm (qC, 0) = Some (0, R, qD)).  Check (eq_refl : BB32_tm.tm (qC, 1) = Some (1, R, qU)).
Check (eq_refl : BB32_tm.tm (qD, 0) = Some (0, R, qE)).  Check (eq_refl : BB32_tm.tm (qD, 1) = Some (0, R, qW)).
Check (eq_refl : BB32_tm.tm (qE, 0) = Some (0, R, qF)).  Check (eq_refl : BB32_tm.tm (qE, 1) = Some (0, R, qF)).
Check (eq_refl : BB32_tm.tm (qF, 0) = Some (0, R, qG)).  Check (eq_refl : BB32_tm.tm (qF, 1) = Some (1, R, qS)).
Check (eq_refl : BB32_tm.tm (qG, 0) = Some (0, R, qH)).  Check (eq_refl : BB32_tm.tm (qG, 1) = Some (1, R, qF)).
Check (eq_refl : BB32_tm.tm (qH, 0) = Some (0, R, qI)).  Check (eq_refl : BB32_tm.tm (qH, 1) = Some (1, R, qI)).
Check (eq_refl : BB32_tm.tm (qI, 0) = Some (0, L, qJ)).  Check (eq_refl : BB32_tm.tm (qI, 1) = Some (1, R, qH)).
Check (eq_refl : BB32_tm.tm (qJ, 0) = Some (1, L, qK)).  Check (eq_refl : BB32_tm.tm (qJ, 1) = Some (1, L, qAA)).
Check (eq_refl : BB32_tm.tm (qK, 0) = Some (0, R, qL)).  Check (eq_refl : BB32_tm.tm (qK, 1) = Some (1, L, qO)).
Check (eq_refl : BB32_tm.tm (qL, 0) = Some (1, R, qM)).  Check (eq_refl : BB32_tm.tm (qL, 1) = Some (1, R, qL)).
Check (eq_refl : BB32_tm.tm (qM, 0) = Some (0, R, qN)).  Check (eq_refl : BB32_tm.tm (qM, 1) = Some (1, R, qV)).
Check (eq_refl : BB32_tm.tm (qN, 0) = Some (1, L, qJ)).  Check (eq_refl : BB32_tm.tm (qN, 1) = Some (1, R, qM)).
Check (eq_refl : BB32_tm.tm (qO, 0) = Some (0, L, qP)).  Check (eq_refl : BB32_tm.tm (qO, 1) = Some (1, L, qP)).
Check (eq_refl : BB32_tm.tm (qP, 0) = Some (0, L, qQ)).  Check (eq_refl : BB32_tm.tm (qP, 1) = Some (1, L, qO)).
Check (eq_refl : BB32_tm.tm (qQ, 0) = Some (0, L, qR)).  Check (eq_refl : BB32_tm.tm (qQ, 1) = Some (1, L, qA)).
Check (eq_refl : BB32_tm.tm (qR, 0) = Some (1, R, qD)).  Check (eq_refl : BB32_tm.tm (qR, 1) = Some (1, L, qQ)).
Check (eq_refl : BB32_tm.tm (qS, 0) = Some (0, L, qZ)).  Check (eq_refl : BB32_tm.tm (qS, 1) = Some (1, R, qF)).
Check (eq_refl : BB32_tm.tm (qT, 0) = Some (0, L, qA)).  Check (eq_refl : BB32_tm.tm (qT, 1) = Some (1, L, qA)).
Check (eq_refl : BB32_tm.tm (qU, 0) = Some (1, R, qH)).  Check (eq_refl : BB32_tm.tm (qU, 1) = Some (0, R, qM)).
Check (eq_refl : BB32_tm.tm (qV, 0) = Some (0, R, qM)).  Check (eq_refl : BB32_tm.tm (qV, 1) = Some (1, R, qM)).
Check (eq_refl : BB32_tm.tm (qW, 0) = Some (0, R, qX)).  Check (eq_refl : BB32_tm.tm (qW, 1) = Some (1, R, qY)).
Check (eq_refl : BB32_tm.tm (qX, 0) = Some (1, L, qO)).  Check (eq_refl : BB32_tm.tm (qX, 1) = Some (1, R, qW)).
Check (eq_refl : BB32_tm.tm (qY, 0) = Some (0, R, qW)).  Check (eq_refl : BB32_tm.tm (qY, 1) = Some (1, R, qW)).
Check (eq_refl : BB32_tm.tm (qZ, 0) = Some (1, L, qAA)).  Check (eq_refl : BB32_tm.tm (qZ, 1) = Some (0, L, qB)).
Check (eq_refl : BB32_tm.tm (qAA, 0) = Some (0, L, qAE)).  Check (eq_refl : BB32_tm.tm (qAA, 1) = Some (1, L, qAB)).
Check (eq_refl : BB32_tm.tm (qAB, 0) = Some (0, R, qD)).  Check (eq_refl : BB32_tm.tm (qAB, 1) = Some (1, L, qAC)).
Check (eq_refl : BB32_tm.tm (qAC, 0) = Some (0, L, qJ)).  Check (eq_refl : BB32_tm.tm (qAC, 1) = Some (1, L, qAD)).
Check (eq_refl : BB32_tm.tm (qAD, 0) = Some (0, L, qAA)).  Check (eq_refl : BB32_tm.tm (qAD, 1) = Some (1, L, qAE)).
Check (eq_refl : BB32_tm.tm (qAE, 0) = Some (0, R, qP)).  Check (eq_refl : BB32_tm.tm (qAE, 1) = Some (1, L, qAF)).
Check (eq_refl : BB32_tm.tm (qAF, 0) = Some (0, L, qAC)).  Check (eq_refl : BB32_tm.tm (qAF, 1) = Some (1, L, qJ)).

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
Print BB32_halt.hs0.
Print BB32_game.ones.
Print BB32_game.count1.
Print BB32_game.sym_val.
Print BB32_bound.a32.

Check BB32_halt.halt.
Check BB32_halt.hardy_bound.
Check BB32_halt.x0_eq.
Check BB32_bound.hardy_score.
Check BB32_bound.sigma_lower_bound_w4_8.
Check BB32_bound.sigma_lower_bound_w4.
Check BB32_bound.sigma_lower_bound.

Print Assumptions BB32_halt.halt.
Print Assumptions BB32_halt.hardy_bound.
Print Assumptions BB32_halt.x0_eq.
Print Assumptions BB32_bound.hardy_score.
Print Assumptions BB32_bound.sigma_lower_bound_w4_8.
Print Assumptions BB32_bound.sigma_lower_bound_w4.
Print Assumptions BB32_bound.sigma_lower_bound.
