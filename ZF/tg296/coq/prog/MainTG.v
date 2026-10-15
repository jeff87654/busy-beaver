(** * MainTG: the program layer of the m254tg machine.

    [progtg : rm_halts dagtg ([], regs0) <-> enum_tg_halts]

    dagtg (M254TGT.DagTG, the TM layer's frozen file) is the decision DAG of the frozen machine/m254tg_wade.tm (Wade TMBuilder compile of
    machine/source_tg.py) in the path semantics of M254TGT.RM (= ZF/verify/336/RM.v), started at the IP []
    with all registers 0 (where the Wade framework's boot lands).  enum_tg_halts is the abstract
    enumerator started from s0 = all zeros.

    Chain: path semantics = structured semantics for the well-formed dagtg (M254TGT.RMEquiv.dagtg_wf); one structured
    run of the root of dagtg = one enum_step (L2RootTG); regs0 encodes s0. *)
From Coq Require Import Lists.List Arith.Arith.
From M254TGT Require Import RM DagTG RMEquiv.
From M254TGP Require Import ProgLibTG L2RootTG.
From M254TGL Require Import CodesTG EnumTG.
Import ListNotations.

Lemma regs0_enc : approx regs0 (enc s0).
Proof. intros i. do 9 (destruct i as [|i]; [reflexivity|]). reflexivity. Qed.

Theorem progtg_iter : iter_halts dagtg regs0 <-> enum_tg_halts.
Proof. exact (iter_halts_dag s0 regs0 regs0_enc). Qed.

Theorem progtg : rm_halts dagtg ([], regs0) <-> enum_tg_halts.
Proof. rewrite (rm_halts_iff_iter _ dagtg_wf). exact progtg_iter. Qed.

Print Assumptions progtg.
Print Assumptions progtg_iter.
