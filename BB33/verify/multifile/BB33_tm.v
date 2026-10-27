(** * Transition table of BB33 (33 states), generated from the machine string.
    State character c is constructor q + column(ord(c) - 65): A..Z -> qA..qZ, [ -> qAA, 
    \ -> qAB, ] -> qAC, ^ -> qAD, _ -> qAE, ` -> qAF, a -> qAG *)

From BB8 Require Export Individual332.
Set Default Goal Selector "!".

(* machine: 1LH1L^_---0LC_1LR0LB_1RF1LE_0LD1LD_0R_1RG_1RN0RK_0RI1RJ_1L^1RH_0RH1RH_0RL1RM_1L`1RK_0RK1RK_0RO1RO_0L`1RN_1R_1La_0RZ0RZ_0LX1LS_0R_1LT_0L`1LU_0LR1LV_0LS1LW_0LT1LX_0R]1LY_0LV1L`_0R[1R\_0RN1RZ_0LC1RZ_0La1L^_0L]1L]_0RQ0RH_1LA1LR_0LP1LD *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | qA, 0 => Some (1, L, qH)     | qA, 1 => Some (1, L, qAD)  (* A *)
  | qB, 0 => None                | qB, 1 => Some (0, L, qC)  (* B *)
  | qC, 0 => Some (1, L, qR)     | qC, 1 => Some (0, L, qB)  (* C *)
  | qD, 0 => Some (1, R, qF)     | qD, 1 => Some (1, L, qE)  (* D *)
  | qE, 0 => Some (0, L, qD)     | qE, 1 => Some (1, L, qD)  (* E *)
  | qF, 0 => Some (0, R, qAE)    | qF, 1 => Some (1, R, qG)  (* F *)
  | qG, 0 => Some (1, R, qN)     | qG, 1 => Some (0, R, qK)  (* G *)
  | qH, 0 => Some (0, R, qI)     | qH, 1 => Some (1, R, qJ)  (* H *)
  | qI, 0 => Some (1, L, qAD)    | qI, 1 => Some (1, R, qH)  (* I *)
  | qJ, 0 => Some (0, R, qH)     | qJ, 1 => Some (1, R, qH)  (* J *)
  | qK, 0 => Some (0, R, qL)     | qK, 1 => Some (1, R, qM)  (* K *)
  | qL, 0 => Some (1, L, qAF)    | qL, 1 => Some (1, R, qK)  (* L *)
  | qM, 0 => Some (0, R, qK)     | qM, 1 => Some (1, R, qK)  (* M *)
  | qN, 0 => Some (0, R, qO)     | qN, 1 => Some (1, R, qO)  (* N *)
  | qO, 0 => Some (0, L, qAF)    | qO, 1 => Some (1, R, qN)  (* O *)
  | qP, 0 => Some (1, R, qAE)    | qP, 1 => Some (1, L, qAG)  (* P *)
  | qQ, 0 => Some (0, R, qZ)     | qQ, 1 => Some (0, R, qZ)  (* Q *)
  | qR, 0 => Some (0, L, qX)     | qR, 1 => Some (1, L, qS)  (* R *)
  | qS, 0 => Some (0, R, qAE)    | qS, 1 => Some (1, L, qT)  (* S *)
  | qT, 0 => Some (0, L, qAF)    | qT, 1 => Some (1, L, qU)  (* T *)
  | qU, 0 => Some (0, L, qR)     | qU, 1 => Some (1, L, qV)  (* U *)
  | qV, 0 => Some (0, L, qS)     | qV, 1 => Some (1, L, qW)  (* V *)
  | qW, 0 => Some (0, L, qT)     | qW, 1 => Some (1, L, qX)  (* W *)
  | qX, 0 => Some (0, R, qAC)    | qX, 1 => Some (1, L, qY)  (* X *)
  | qY, 0 => Some (0, L, qV)     | qY, 1 => Some (1, L, qAF)  (* Y *)
  | qZ, 0 => Some (0, R, qAA)    | qZ, 1 => Some (1, R, qAB)  (* Z *)
  | qAA, 0 => Some (0, R, qN)    | qAA, 1 => Some (1, R, qZ)  (* [ *)
  | qAB, 0 => Some (0, L, qC)    | qAB, 1 => Some (1, R, qZ)  (* \ *)
  | qAC, 0 => Some (0, L, qAG)   | qAC, 1 => Some (1, L, qAD)  (* ] *)
  | qAD, 0 => Some (0, L, qAC)   | qAD, 1 => Some (1, L, qAC)  (* ^ *)
  | qAE, 0 => Some (0, R, qQ)    | qAE, 1 => Some (0, R, qH)  (* _ *)
  | qAF, 0 => Some (1, L, qA)    | qAF, 1 => Some (1, L, qR)  (* ` *)
  | qAG, 0 => Some (0, L, qP)    | qAG, 1 => Some (1, L, qD)  (* a *)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
