(** * Transition table of BB29 (29 states), generated from the machine string.
    State character c is constructor q + column(ord(c) - 65): A..Z -> qA..qZ, [ -> qAA, 
    \ -> qAB, ] -> qAC, ^ -> qAD, _ -> qAE, ` -> qAF, a -> qAG *)

From BB8 Require Export Individual292.
Set Default Goal Selector "!".

(* machine: 0LP1LD_---0LC_1LR0LB_1RF1LE_0LD1LD_0R[1RG_1RN0RK_0RI1RJ_1LZ1RH_0RH1RH_0RL1RM_1L\1RK_0RK1RK_0RO1RO_0L\1RN_1R[1LA_0RV0RV_0LT1LS_0R[1LT_0RY1LU_0LR1L\_0RW1RX_0RN1RV_0LC1RV_0LA1LZ_0LY1LY_0RQ0RH_1L]1LR_1LH1LZ *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | qA, 0 => Some (0, L, qP)     | qA, 1 => Some (1, L, qD)  (* A *)
  | qB, 0 => None                | qB, 1 => Some (0, L, qC)  (* B *)
  | qC, 0 => Some (1, L, qR)     | qC, 1 => Some (0, L, qB)  (* C *)
  | qD, 0 => Some (1, R, qF)     | qD, 1 => Some (1, L, qE)  (* D *)
  | qE, 0 => Some (0, L, qD)     | qE, 1 => Some (1, L, qD)  (* E *)
  | qF, 0 => Some (0, R, qAA)    | qF, 1 => Some (1, R, qG)  (* F *)
  | qG, 0 => Some (1, R, qN)     | qG, 1 => Some (0, R, qK)  (* G *)
  | qH, 0 => Some (0, R, qI)     | qH, 1 => Some (1, R, qJ)  (* H *)
  | qI, 0 => Some (1, L, qZ)     | qI, 1 => Some (1, R, qH)  (* I *)
  | qJ, 0 => Some (0, R, qH)     | qJ, 1 => Some (1, R, qH)  (* J *)
  | qK, 0 => Some (0, R, qL)     | qK, 1 => Some (1, R, qM)  (* K *)
  | qL, 0 => Some (1, L, qAB)    | qL, 1 => Some (1, R, qK)  (* L *)
  | qM, 0 => Some (0, R, qK)     | qM, 1 => Some (1, R, qK)  (* M *)
  | qN, 0 => Some (0, R, qO)     | qN, 1 => Some (1, R, qO)  (* N *)
  | qO, 0 => Some (0, L, qAB)    | qO, 1 => Some (1, R, qN)  (* O *)
  | qP, 0 => Some (1, R, qAA)    | qP, 1 => Some (1, L, qA)  (* P *)
  | qQ, 0 => Some (0, R, qV)     | qQ, 1 => Some (0, R, qV)  (* Q *)
  | qR, 0 => Some (0, L, qT)     | qR, 1 => Some (1, L, qS)  (* R *)
  | qS, 0 => Some (0, R, qAA)    | qS, 1 => Some (1, L, qT)  (* S *)
  | qT, 0 => Some (0, R, qY)     | qT, 1 => Some (1, L, qU)  (* T *)
  | qU, 0 => Some (0, L, qR)     | qU, 1 => Some (1, L, qAB)  (* U *)
  | qV, 0 => Some (0, R, qW)     | qV, 1 => Some (1, R, qX)  (* V *)
  | qW, 0 => Some (0, R, qN)     | qW, 1 => Some (1, R, qV)  (* W *)
  | qX, 0 => Some (0, L, qC)     | qX, 1 => Some (1, R, qV)  (* X *)
  | qY, 0 => Some (0, L, qA)     | qY, 1 => Some (1, L, qZ)  (* Y *)
  | qZ, 0 => Some (0, L, qY)     | qZ, 1 => Some (1, L, qY)  (* Z *)
  | qAA, 0 => Some (0, R, qQ)    | qAA, 1 => Some (0, R, qH)  (* [ *)
  | qAB, 0 => Some (1, L, qAC)   | qAB, 1 => Some (1, L, qR)  (* \ *)
  | qAC, 0 => Some (1, L, qH)    | qAC, 1 => Some (1, L, qZ)  (* ] *)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
