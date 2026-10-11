(** * Std_Main: O'Rear's ZF proof system vs. the ZF of the Coq Library of Undecidability Proofs.

    [prov] (Logic.v): O'Rear's Hilbert system (Tarski S2 variant + EXT REP POW UNI INF), the
    system searched by the ZF Turing machines (393/361/354 states).

    The library (Kirst & Hermes; vendor/theories, unmodified): de Bruijn first-order logic,
    classical natural deduction [⊢TC] (FOL/Deduction/FullND.v), ZF in the minimal signature
    (∈, ≡; FOL/Sets/minZF.v) and with Skolem function symbols (FOL/Sets/ZF.v).

    [ZFc] (Std_iface.v) = the library's minZFeq axioms with every separation / replacement instance
    universally closed, the axiom set of the library's own semantic entailment (which demands the
    axioms under every assignment).  [ZFc + Reg] adds regularity [ax_reg'] (zf-regcon,
    zf/regcon/MinZF.v).  [RegCon.Main.ZFc] / [ZFcReg]: the same in the function-symbol signature.

      prov (Wel v0 v0) <-> ZFc ⊢TC ⊥ <-> (ZFc + Reg) ⊢TC ⊥ <-> ZFc_fun ⊢TC ⊥ <-> ZFcReg_fun ⊢TC ⊥

    and, for the library's theories verbatim (open scheme instances):
      minZFeq ⊢TC ⊥ -> prov (Wel v0 v0),   ZFeq ⊢TC ⊥ -> prov (Wel v0 v0).                        *)
From Coq Require Import List.
From Undecidability.FOL Require Import Sets.ZF Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic Std_iface Std_iface2 Std_glue Std_ZFeq Std_brzf Std_brax Std_brpow.
From RegCon Require Main MinZF Link.
Import ListNotations.

(** classical theory derivability of falsity in the minimal / function-symbol signature *)
Notation incons T := (@tprv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on class T falsity).
Notation incons_fun T := (@tprv ZFSignature.ZF_func_sig ZFSignature.ZF_pred_sig falsity_on class T falsity).

Definition ZFc_reg (phi : @form BinSig.sig_empty ZFSignature.ZF_pred_sig full_operators falsity_on) : Prop :=
  Std_iface.ZFc phi \/ phi = MinZF.ax_reg'.

Theorem prov_iff_ZFc : prov (Wel v0 v0) <-> incons Std_iface.ZFc.
Proof.
  split.
  - exact (prov_to_ZFc bridge_EXT_proof bridge_POW_proof bridge_UNI_proof bridge_INFo_proof bridge_REP_proof).
  - exact (ZFc_to_prov bridge_ZF0_proof bridge_INF_proof).
Qed.

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

(** the library's theories verbatim: one direction *)
Theorem minZFeq_to_ZFc phi :
  @tprv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on class minZFeq phi ->
  @tprv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on class Std_iface.ZFc phi.
Proof. intro H. exact (thm_trans _ _ _ H minZFeq_from_ZFc). Qed.

Theorem minZFeq_to_prov : incons minZFeq -> prov (Wel v0 v0).
Proof. intro H. apply prov_iff_ZFc. exact (minZFeq_to_ZFc H). Qed.

Theorem ZFeq_to_prov : incons_fun ZFeq -> prov (Wel v0 v0).
Proof. intro H. exact (minZFeq_to_prov (ZFeq_to_minZFeq H)). Qed.
