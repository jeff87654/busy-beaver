(** * Transition table of BB31 (31 states), generated from the machine string.
    State character c is constructor q + column(ord(c) - 65): A..Z -> qA..qZ, [ -> qAA, 
    \ -> qAB, ] -> qAC, ^ -> qAD, _ -> qAE, ` -> qAF, a -> qAG *)

From BB8 Require Export Individual312.
Set Default Goal Selector "!".

(* machine: 0RK1RK_---0LC_1LQ0LB_1RF1LE_0LD1LD_0R\1RG_1RM0RK_0RI1RJ_1L[1RH_0RH1RH_0RL1RA_1L]1RK_0RN1RN_0L]1RM_1R\1L^_0RW0RW_0LU1LR_0R\1LS_0L]1LT_0LQ1LU_0RZ1LV_0LS1L]_0RX1RY_0RM1RW_0LC1RW_0L^1L[_0LZ1LZ_0RP0RH_1L_1LQ_0LO1LD_1LH1L[ *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | qA, 0 => Some (0, R, qK)     | qA, 1 => Some (1, R, qK)  (* A *)
  | qB, 0 => None                | qB, 1 => Some (0, L, qC)  (* B *)
  | qC, 0 => Some (1, L, qQ)     | qC, 1 => Some (0, L, qB)  (* C *)
  | qD, 0 => Some (1, R, qF)     | qD, 1 => Some (1, L, qE)  (* D *)
  | qE, 0 => Some (0, L, qD)     | qE, 1 => Some (1, L, qD)  (* E *)
  | qF, 0 => Some (0, R, qAB)    | qF, 1 => Some (1, R, qG)  (* F *)
  | qG, 0 => Some (1, R, qM)     | qG, 1 => Some (0, R, qK)  (* G *)
  | qH, 0 => Some (0, R, qI)     | qH, 1 => Some (1, R, qJ)  (* H *)
  | qI, 0 => Some (1, L, qAA)    | qI, 1 => Some (1, R, qH)  (* I *)
  | qJ, 0 => Some (0, R, qH)     | qJ, 1 => Some (1, R, qH)  (* J *)
  | qK, 0 => Some (0, R, qL)     | qK, 1 => Some (1, R, qA)  (* K *)
  | qL, 0 => Some (1, L, qAC)    | qL, 1 => Some (1, R, qK)  (* L *)
  | qM, 0 => Some (0, R, qN)     | qM, 1 => Some (1, R, qN)  (* M *)
  | qN, 0 => Some (0, L, qAC)    | qN, 1 => Some (1, R, qM)  (* N *)
  | qO, 0 => Some (1, R, qAB)    | qO, 1 => Some (1, L, qAD)  (* O *)
  | qP, 0 => Some (0, R, qW)     | qP, 1 => Some (0, R, qW)  (* P *)
  | qQ, 0 => Some (0, L, qU)     | qQ, 1 => Some (1, L, qR)  (* Q *)
  | qR, 0 => Some (0, R, qAB)    | qR, 1 => Some (1, L, qS)  (* R *)
  | qS, 0 => Some (0, L, qAC)    | qS, 1 => Some (1, L, qT)  (* S *)
  | qT, 0 => Some (0, L, qQ)     | qT, 1 => Some (1, L, qU)  (* T *)
  | qU, 0 => Some (0, R, qZ)     | qU, 1 => Some (1, L, qV)  (* U *)
  | qV, 0 => Some (0, L, qS)     | qV, 1 => Some (1, L, qAC)  (* V *)
  | qW, 0 => Some (0, R, qX)     | qW, 1 => Some (1, R, qY)  (* W *)
  | qX, 0 => Some (0, R, qM)     | qX, 1 => Some (1, R, qW)  (* X *)
  | qY, 0 => Some (0, L, qC)     | qY, 1 => Some (1, R, qW)  (* Y *)
  | qZ, 0 => Some (0, L, qAD)    | qZ, 1 => Some (1, L, qAA)  (* Z *)
  | qAA, 0 => Some (0, L, qZ)    | qAA, 1 => Some (1, L, qZ)  (* [ *)
  | qAB, 0 => Some (0, R, qP)    | qAB, 1 => Some (0, R, qH)  (* \ *)
  | qAC, 0 => Some (1, L, qAE)   | qAC, 1 => Some (1, L, qQ)  (* ] *)
  | qAD, 0 => Some (0, L, qO)    | qAD, 1 => Some (1, L, qD)  (* ^ *)
  | qAE, 0 => Some (1, L, qH)    | qAE, 1 => Some (1, L, qAA)  (* _ *)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
