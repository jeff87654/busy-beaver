(** * Std_Main: the zf-axtext R3s proof system [prov] (Logic.v: the S2-style logic of O'Rear's
    system plus EXT, the bounded-fiber replacement scheme REP and INF; no POW, no UNI) vs. the ZF of
    the Coq Library of Undecidability Proofs.

    [ZFc] (Std_iface.v) = the library's minZFeq axioms with every separation / replacement instance
    universally closed.

      prov (Wel v0 v0) <-> ZFc ⊢TC ⊥
    and, for the library's theories verbatim (open scheme instances):
      minZFeq ⊢TC ⊥ -> prov (Wel v0 v0),   ZFeq ⊢TC ⊥ -> prov (Wel v0 v0).

    (The regularity / function-symbol variants of zf/stdzf/coq/Std_Main.v follow by composing
    [prov_iff_ZFc] with zf/regcon/Link.v, which only concerns [ZFc].) *)
From Coq Require Import List.
From Undecidability.FOL Require Import Sets.ZF Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic Std_iface Std_iface2 Std_glue Std_ZFeq Std_brzf Std_brax.
Import ListNotations.

Notation incons T := (@tprv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on class T falsity).
Notation incons_fun T := (@tprv ZFSignature.ZF_func_sig ZFSignature.ZF_pred_sig falsity_on class T falsity).

Theorem prov_iff_ZFc : prov (Wel v0 v0) <-> incons Std_iface.ZFc.
Proof.
  split.
  - exact (prov_to_ZFc bridge_EXT_proof bridge_INFo_proof bridge_REP_proof).
  - exact (ZFc_to_prov bridge_ZF0_proof bridge_INF_proof).
Qed.

Theorem minZFeq_to_ZFc phi :
  @tprv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on class minZFeq phi ->
  @tprv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on class Std_iface.ZFc phi.
Proof. intro H. exact (thm_trans _ _ _ H minZFeq_from_ZFc). Qed.

Theorem minZFeq_to_prov : incons minZFeq -> prov (Wel v0 v0).
Proof. intro H. apply prov_iff_ZFc. exact (minZFeq_to_ZFc H). Qed.

Theorem ZFeq_to_prov : incons_fun ZFeq -> prov (Wel v0 v0).
Proof. intro H. exact (minZFeq_to_prov (ZFeq_to_minZFeq H)). Qed.
