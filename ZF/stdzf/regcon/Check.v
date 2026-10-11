(* Statement check: the type ascriptions fail to compile unless the theorems have exactly
   these statements (classical natural deduction of the library: ⊢TC). *)
Require Import Undecidability.FOL.Sets.ZF.
Require Import Undecidability.FOL.Sets.minZF.
From RegCon Require Import Main MinZF Link.
From ZF Require Std_iface.
Open Scope syn.

Check (regularity_relcon : ZFcReg ⊢TC ⊥ -> ZFc ⊢TC ⊥).
Check (fun phi => @ZFeq_ZFc class phi : ZFeq ⊢TC phi -> ZFc ⊢TC phi).
Check (fun phi => @ZFeq_ZFc intu phi : ZFeq ⊢TI phi -> ZFc ⊢TI phi).
Check (regularity_relcon_min : ZFclReg ⊢TC ⊥ -> ZFcl_min ⊢TC ⊥).
Check (regularity_relcon_all : ZFclReg ⊢TC ⊥ -> ZFcl_all ⊢TC ⊥).
Check regularity_relcon_closed.
Check bridge.
Check (regularity_relcon_std : (fun phi => Std_iface.ZFc phi \/ phi = ax_reg') ⊢TC ⊥ -> Std_iface.ZFc ⊢TC ⊥).
Check (bridge_std : Std_iface.ZFc ⊢TC ⊥ <-> ZFc ⊢TC ⊥).
Check bridge_reg_std.
Check bridge_reg.
Check regularity_relcon_min'.
Print ax_reg'.
Print ZFcl_all.
Print ZFcl_closed.
Print ZFclReg.
Print ZFcl_min.
Print ax_reg.
Print ZFc.
Print ZFcReg.
Print Assumptions regularity_relcon.
Print Assumptions ZFeq_ZFc.
Print Assumptions regularity_relcon_min'.
Print Assumptions bridge.
Print Assumptions bridge_reg.
Print Assumptions regularity_relcon_std.
Print Assumptions bridge_std.
Print Assumptions bridge_reg_std.
Print Assumptions regularity_relcon_thm.
