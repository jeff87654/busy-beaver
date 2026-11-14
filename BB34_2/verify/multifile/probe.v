(** Independent probe for the BB34 proofs (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe.v).

    Coq confirms here, by conversion, that (1) the compiled transition table of [BB34_tm.tm] is the machine
    1LC1LT_---0LS_1RD1LH_0RE0RC_0RF1RF_0RG1RE_1LA1RF_0LI1LI_0LJ1LH_0LK1LY_1RL1LJ_0RM0RV_0RN0RN_0RO1RR_0RP1RN_0RQ1RQ_0LA1RP_0LS1RN_1LT0LB_0La1LU_0RL1L\_0RX1RW_0RV1RV_1LH1RV_1RZ1L^_0RL1R[_1RP0RF_0LA1L]_0LT1L__0LY1LY_0LU1L`_0L\1La_0RI1Lb_0L_1LA
    entry by entry (34 lines generated from the machine string, not from the Coq file; rows are fixed-width,
    state character c is constructor q + column(ord(c) - 65): A..Z -> qA..qZ, [ \ ] ^ _ ` a b -> qAA..qAH;
    Z is an ordinary state here; the only halt is B0 = ---, which is None), and the start configuration is the
    blank tape in state A; (2) the main theorems have the stated types; (3) they use no axioms.  It also prints
    the definitions the statements use. *)

From BB8 Require BB34_bound BB34_game BB34_halt Ord.
From BB8 Require Import Individual342.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = qA).  Check (eq_refl : s0 = S0).
Check (eq_refl : BB34_tm.tm (qA, 0) = Some (1, L, qC)).  Check (eq_refl : BB34_tm.tm (qA, 1) = Some (1, L, qT)).
Check (eq_refl : BB34_tm.tm (qB, 0) = None).  Check (eq_refl : BB34_tm.tm (qB, 1) = Some (0, L, qS)).
Check (eq_refl : BB34_tm.tm (qC, 0) = Some (1, R, qD)).  Check (eq_refl : BB34_tm.tm (qC, 1) = Some (1, L, qH)).
Check (eq_refl : BB34_tm.tm (qD, 0) = Some (0, R, qE)).  Check (eq_refl : BB34_tm.tm (qD, 1) = Some (0, R, qC)).
Check (eq_refl : BB34_tm.tm (qE, 0) = Some (0, R, qF)).  Check (eq_refl : BB34_tm.tm (qE, 1) = Some (1, R, qF)).
Check (eq_refl : BB34_tm.tm (qF, 0) = Some (0, R, qG)).  Check (eq_refl : BB34_tm.tm (qF, 1) = Some (1, R, qE)).
Check (eq_refl : BB34_tm.tm (qG, 0) = Some (1, L, qA)).  Check (eq_refl : BB34_tm.tm (qG, 1) = Some (1, R, qF)).
Check (eq_refl : BB34_tm.tm (qH, 0) = Some (0, L, qI)).  Check (eq_refl : BB34_tm.tm (qH, 1) = Some (1, L, qI)).
Check (eq_refl : BB34_tm.tm (qI, 0) = Some (0, L, qJ)).  Check (eq_refl : BB34_tm.tm (qI, 1) = Some (1, L, qH)).
Check (eq_refl : BB34_tm.tm (qJ, 0) = Some (0, L, qK)).  Check (eq_refl : BB34_tm.tm (qJ, 1) = Some (1, L, qY)).
Check (eq_refl : BB34_tm.tm (qK, 0) = Some (1, R, qL)).  Check (eq_refl : BB34_tm.tm (qK, 1) = Some (1, L, qJ)).
Check (eq_refl : BB34_tm.tm (qL, 0) = Some (0, R, qM)).  Check (eq_refl : BB34_tm.tm (qL, 1) = Some (0, R, qV)).
Check (eq_refl : BB34_tm.tm (qM, 0) = Some (0, R, qN)).  Check (eq_refl : BB34_tm.tm (qM, 1) = Some (0, R, qN)).
Check (eq_refl : BB34_tm.tm (qN, 0) = Some (0, R, qO)).  Check (eq_refl : BB34_tm.tm (qN, 1) = Some (1, R, qR)).
Check (eq_refl : BB34_tm.tm (qO, 0) = Some (0, R, qP)).  Check (eq_refl : BB34_tm.tm (qO, 1) = Some (1, R, qN)).
Check (eq_refl : BB34_tm.tm (qP, 0) = Some (0, R, qQ)).  Check (eq_refl : BB34_tm.tm (qP, 1) = Some (1, R, qQ)).
Check (eq_refl : BB34_tm.tm (qQ, 0) = Some (0, L, qA)).  Check (eq_refl : BB34_tm.tm (qQ, 1) = Some (1, R, qP)).
Check (eq_refl : BB34_tm.tm (qR, 0) = Some (0, L, qS)).  Check (eq_refl : BB34_tm.tm (qR, 1) = Some (1, R, qN)).
Check (eq_refl : BB34_tm.tm (qS, 0) = Some (1, L, qT)).  Check (eq_refl : BB34_tm.tm (qS, 1) = Some (0, L, qB)).
Check (eq_refl : BB34_tm.tm (qT, 0) = Some (0, L, qAG)).  Check (eq_refl : BB34_tm.tm (qT, 1) = Some (1, L, qU)).
Check (eq_refl : BB34_tm.tm (qU, 0) = Some (0, R, qL)).  Check (eq_refl : BB34_tm.tm (qU, 1) = Some (1, L, qAB)).
Check (eq_refl : BB34_tm.tm (qV, 0) = Some (0, R, qX)).  Check (eq_refl : BB34_tm.tm (qV, 1) = Some (1, R, qW)).
Check (eq_refl : BB34_tm.tm (qW, 0) = Some (0, R, qV)).  Check (eq_refl : BB34_tm.tm (qW, 1) = Some (1, R, qV)).
Check (eq_refl : BB34_tm.tm (qX, 0) = Some (1, L, qH)).  Check (eq_refl : BB34_tm.tm (qX, 1) = Some (1, R, qV)).
Check (eq_refl : BB34_tm.tm (qY, 0) = Some (1, R, qZ)).  Check (eq_refl : BB34_tm.tm (qY, 1) = Some (1, L, qAD)).
Check (eq_refl : BB34_tm.tm (qZ, 0) = Some (0, R, qL)).  Check (eq_refl : BB34_tm.tm (qZ, 1) = Some (1, R, qAA)).
Check (eq_refl : BB34_tm.tm (qAA, 0) = Some (1, R, qP)).  Check (eq_refl : BB34_tm.tm (qAA, 1) = Some (0, R, qF)).
Check (eq_refl : BB34_tm.tm (qAB, 0) = Some (0, L, qA)).  Check (eq_refl : BB34_tm.tm (qAB, 1) = Some (1, L, qAC)).
Check (eq_refl : BB34_tm.tm (qAC, 0) = Some (0, L, qT)).  Check (eq_refl : BB34_tm.tm (qAC, 1) = Some (1, L, qAE)).
Check (eq_refl : BB34_tm.tm (qAD, 0) = Some (0, L, qY)).  Check (eq_refl : BB34_tm.tm (qAD, 1) = Some (1, L, qY)).
Check (eq_refl : BB34_tm.tm (qAE, 0) = Some (0, L, qU)).  Check (eq_refl : BB34_tm.tm (qAE, 1) = Some (1, L, qAF)).
Check (eq_refl : BB34_tm.tm (qAF, 0) = Some (0, L, qAB)).  Check (eq_refl : BB34_tm.tm (qAF, 1) = Some (1, L, qAG)).
Check (eq_refl : BB34_tm.tm (qAG, 0) = Some (0, R, qI)).  Check (eq_refl : BB34_tm.tm (qAG, 1) = Some (1, L, qAH)).
Check (eq_refl : BB34_tm.tm (qAH, 0) = Some (0, L, qAE)).  Check (eq_refl : BB34_tm.tm (qAH, 1) = Some (1, L, qA)).

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
Print BB34_halt.hs0.
Print BB34_game.ones.
Print BB34_game.count1.
Print BB34_game.sym_val.

Check BB34_halt.halt.
Check BB34_halt.hardy_bound.
Check BB34_halt.x0_eq.
Check BB34_bound.hardy_score.
Check BB34_bound.sigma_lower_bound_w6_4.
Check BB34_bound.sigma_lower_bound_w6.
Check BB34_bound.sigma_lower_bound.

Print Assumptions BB34_halt.halt.
Print Assumptions BB34_halt.hardy_bound.
Print Assumptions BB34_halt.x0_eq.
Print Assumptions BB34_bound.hardy_score.
Print Assumptions BB34_bound.sigma_lower_bound_w6_4.
Print Assumptions BB34_bound.sigma_lower_bound_w6.
Print Assumptions BB34_bound.sigma_lower_bound.
