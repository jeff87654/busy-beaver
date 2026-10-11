(** * MainR3s: the regularity and function-symbol variants of the zf-axtext R3s main theorem,
    composing ZF.Std_Main.prov_iff_ZFc (zf/axtext/coq/R3) with zf-regcon's Link.v (copied
    unchanged from zf/regcon; it only concerns ZFc).  Mirrors zf/stdzf/coq/Std_Main.v. *)
From Undecidability.FOL Require Import Sets.ZF Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic Std_iface Std_Main.
From RegCon Require Main MinZF Link.

Definition ZFc_reg (phi : @form BinSig.sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on) : Prop :=
  Std_iface.ZFc phi \/ phi = MinZF.ax_reg'.

Theorem prov_iff_ZFc_reg : prov (Wel v0 v0) <-> incons ZFc_reg.
Proof.
  rewrite prov_iff_ZFc. split.
  - intros [A [HA D]]. exists A. split; [intros psi Hp; left; exact (HA psi Hp) | exact D].
  - exact (Link.regularity_relcon_std).
Qed.

Theorem prov_iff_ZFc_fun : prov (Wel v0 v0) <-> incons_fun Main.ZFc.
Proof. rewrite prov_iff_ZFc. exact Link.bridge_std. Qed.

Theorem prov_iff_ZFcReg_fun : prov (Wel v0 v0) <-> incons_fun Main.ZFcReg.
Proof. rewrite prov_iff_ZFc_reg. exact Link.bridge_reg_std. Qed.

Print Assumptions prov_iff_ZFc_reg.
Print Assumptions prov_iff_ZFc_fun.
Print Assumptions prov_iff_ZFcReg_fun.
