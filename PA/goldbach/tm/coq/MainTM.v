(** * MainTM: the TM layer of pagb (TM halts iff PA proves Goldbach).

    [tm] is the 449-state machine pa_wade.tm (ZFTM.v; [tm_table] proves it equals the literal
    table [pa_table] of TablePA.v, which check_tm.py compares with the .tm file).  [dagpa] is its Wade
    decision DAG (DagPA.v) and [rm_halts] the path semantics of RM.v, started from the empty IP with
    every register 0.  Proof: Sim.v (list-zipper simulation, boot by certified computation). *)

From Coq Require Import Lists.List.
From BusyCoq Require Import TM.
From PAGBT Require Import RM DagPA ZFTM Sim.
Import ListNotations.

Theorem tmpa_rm : halts tm c0 <-> rm_halts dagpa ([], regs0).
Proof. exact tm_halts_iff_rm. Qed.

Print Assumptions tmpa_rm.
