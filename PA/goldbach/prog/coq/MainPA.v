(** * MainPA: the program layer of the pagb machine.

    [progpa : rm_halts dagpa ([], regs0) <-> enum_halts]

    dagpa (PAGBT.DagPA, the TM layer's file) is the decision DAG of the frozen machine/pa_wade.tm (Wade
    TMBuilder compile of machine/source_pa.py) in the path semantics of PAGBT.RM, started at the IP []
    with all registers 0.  enum_halts is the abstract enumerator (PAGB.PA_Enum) started from s0 = all
    zeros.  Chain: path semantics = structured semantics for the well-formed dagpa
    (PAGBT.RMEquiv.dagpa_wf); one structured run of the root = one enum_step (L2RootPA); regs0 encodes s0. *)
From Coq Require Import Lists.List Arith.Arith.
From PAGBT Require Import RM DagPA RMEquiv.
From PAGBP Require Import ProgLibPA L2RootPA.
From PAGB Require Import PA_Enum.
Import ListNotations.

Lemma regs0_enc : approx regs0 (enc s0).
Proof. intros i. do 9 (destruct i as [|i]; [reflexivity|]). reflexivity. Qed.

Theorem progpa_iter : iter_halts dagpa regs0 <-> enum_halts.
Proof. exact (iter_halts_dag s0 regs0 regs0_enc). Qed.

Theorem progpa : rm_halts dagpa ([], regs0) <-> enum_halts.
Proof. rewrite (rm_halts_iff_iter _ dagpa_wf). exact progpa_iter. Qed.

Print Assumptions progpa.
Print Assumptions progpa_iter.
