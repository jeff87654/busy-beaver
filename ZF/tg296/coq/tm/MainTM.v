(** * MainTM: the TM layer of m254tg.

    [tm] is the 296-state machine m254tg_wade.tm (ZFTM.v; [tm_table] proves it equals the literal
    table [tg_table] of TableTG.v, which check.py compares with the .tm file).  [dagtg] is its Wade
    decision DAG (DagTG.v) and [rm_halts] the path semantics of RM.v, started from the empty IP with
    every register 0.  Proof: Sim.v (list-zipper simulation, boot by certified computation). *)

From Coq Require Import Lists.List.
From BusyCoq Require Import TM.
From M254TGT Require Import RM DagTG ZFTM Sim.
Import ListNotations.

Theorem tmtg_rm : halts tm c0 <-> rm_halts dagtg ([], regs0).
Proof. exact tm_halts_iff_rm. Qed.

Print Assumptions tmtg_rm.
