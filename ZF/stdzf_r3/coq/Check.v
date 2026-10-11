(** * Check: the final statements for the R3s system (zf-axtext; the logic of the 335- and 336-state machines),
    restated by type ascription, and their assumptions.  Read together with Logic.v (prov),
    Std_iface.v (ZFc) and the vendored library. *)
From Coq Require Import List.
From Undecidability.FOL Require Import Sets.ZF Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic Std_iface Std_Main.
From RegCon Require Main MinZF MainR3s.

Check (prov_iff_ZFc : prov (Wel v0 v0) <->
  @tprv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on class Std_iface.ZFc falsity).
Check (MainR3s.prov_iff_ZFc_reg : prov (Wel v0 v0) <->
  @tprv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on class
        (fun phi => Std_iface.ZFc phi \/ phi = MinZF.ax_reg') falsity).
Check (MainR3s.prov_iff_ZFc_fun : prov (Wel v0 v0) <->
  @tprv ZFSignature.ZF_func_sig ZFSignature.ZF_pred_sig falsity_on class Main.ZFc falsity).
Check (MainR3s.prov_iff_ZFcReg_fun : prov (Wel v0 v0) <->
  @tprv ZFSignature.ZF_func_sig ZFSignature.ZF_pred_sig falsity_on class Main.ZFcReg falsity).
Check (minZFeq_to_prov :
  @tprv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on class minZFeq falsity -> prov (Wel v0 v0)).
Check (ZFeq_to_prov :
  @tprv ZFSignature.ZF_func_sig ZFSignature.ZF_pred_sig falsity_on class ZFeq falsity -> prov (Wel v0 v0)).

Print Assumptions prov_iff_ZFc.
Print Assumptions MainR3s.prov_iff_ZFc_reg.
Print Assumptions MainR3s.prov_iff_ZFc_fun.
Print Assumptions MainR3s.prov_iff_ZFcReg_fun.
Print Assumptions minZFeq_to_prov.
Print Assumptions ZFeq_to_prov.
