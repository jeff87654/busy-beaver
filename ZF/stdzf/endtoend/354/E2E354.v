(** * E2E354: end to end, the 354-state ZF machine (endtoend/machines/B354.tm) halts iff the library's
    ZF (closed schemes) is inconsistent.  [halts], [c0]: busycoq's TM semantics (vendor/busycoq/TM.v);
    [tm]: ZFTM.v, proved equal to the literal table [zf2_table] of ZF2Dag.v, which check.py compares
    with the .tm file.  [prov] (Logic.v) is only an intermediate here. *)
From Undecidability.FOL Require Syntax.Core Syntax.BinSig Sets.Signatures Deduction.FullND.
From BusyCoq Require Import TM.
From ZF Require Import Logic ZFTM Main Std_iface Std_Main.
From RegCon Require MinZF Main.

Theorem zf354_halts_iff_ZF : halts tm c0 <-> incons Std_iface.ZFc.
Proof. exact (iff_trans zf_machine prov_iff_ZFc). Qed.

Theorem zf354_halts_iff_ZF_reg : halts tm c0 <-> incons ZFc_reg.
Proof. exact (iff_trans zf_machine prov_iff_ZFc_reg). Qed.

Theorem zf354_halts_iff_ZF_fun : halts tm c0 <-> incons_fun RegCon.Main.ZFc.
Proof. exact (iff_trans zf_machine prov_iff_ZFc_fun). Qed.

Theorem zf354_halts_iff_ZF_reg_fun : halts tm c0 <-> incons_fun RegCon.Main.ZFcReg.
Proof. exact (iff_trans zf_machine prov_iff_ZFcReg_fun). Qed.

(* the statements again, spelled out in the library's raw terms (fully qualified, so that the library's
   notations, which clash with busycoq's, need not be imported) *)
Notation tprv := Undecidability.FOL.Deduction.FullND.tprv.
Notation sig0 := Undecidability.FOL.Syntax.BinSig.sig_empty.
Notation zfp := Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_pred_sig.
Notation zff := Undecidability.FOL.Sets.Signatures.ZFSignature.ZF_func_sig.
Notation fon := Undecidability.FOL.Syntax.Core.falsity_on.
Notation cls := Undecidability.FOL.Syntax.Core.class.
Notation bot := Undecidability.FOL.Syntax.Core.falsity.
Check (zf354_halts_iff_ZF : halts tm c0 <-> @tprv sig0 zfp fon cls Std_iface.ZFc bot).
Check (zf354_halts_iff_ZF_reg : halts tm c0 <->
  @tprv sig0 zfp fon cls (fun phi => Std_iface.ZFc phi \/ phi = RegCon.MinZF.ax_reg') bot).
Check (zf354_halts_iff_ZF_fun : halts tm c0 <-> @tprv zff zfp fon cls RegCon.Main.ZFc bot).
Check (zf354_halts_iff_ZF_reg_fun : halts tm c0 <-> @tprv zff zfp fon cls RegCon.Main.ZFcReg bot).

Print Assumptions zf354_halts_iff_ZF.
Print Assumptions zf354_halts_iff_ZF_reg.
Print Assumptions zf354_halts_iff_ZF_fun.
Print Assumptions zf354_halts_iff_ZF_reg_fun.
