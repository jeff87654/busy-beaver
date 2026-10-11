(** * Main: Wade's 393-state Turing machine (zf2.tm) halts iff the formal system of Logic.v
    (Tarski S2 variant + ZF without regularity and choice, O'Rear's zf2.nql) proves "v_0 e. v_0".

    - [tm], [halts], [c0]: busycoq's TM semantics (TM.v) instantiated in ZFTM.v; [tm_table] there
      proves [tm] equals the literal transition table of zf2.tm (checked against the file by check_zf.py).
    - [prov]: Logic.v (trusted spec; compare with the axiom list in zf2.nql).
    Layers: Sim.v (TM <-> register machine), RMEquiv.v (path <-> big-step semantics),
    Prog.v (program <-> abstract enumerator), L1.v (enumerator <-> provability), MainGlue.v. *)

From BusyCoq Require Import TM.
From ZF Require Import Logic Enum L1 RM ZF2Dag RMEquiv ZFTM Sim Prog MainGlue.

Theorem zf_machine : halts tm c0 <-> prov (Wel v0 v0).
Proof. exact (glue _ tm_halts_iff_rm iter_halts_iff). Qed.

Print Assumptions zf_machine.
