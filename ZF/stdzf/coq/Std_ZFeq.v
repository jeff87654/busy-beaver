(** * Std_ZFeq: the function-symbol version of the library's ZF (FOL/Sets/ZF.v, theory [ZFeq],
    Skolem symbols for empty set, pairing, union, power set, omega).  By the library's own
    conservativity theorem (Sets/Models/ZF_conservativity.v), [ZFeq ⊢TC ⊥ -> minZFeq ⊢TC ⊥]. *)
From Undecidability.FOL Require Import Sets.ZF Sets.minZF Deduction.FullNDFacts.
From Undecidability.FOL.Reductions Require Import PCPb_to_minZF.
From Undecidability.FOL.Sets.Models Require Import ZF_conservativity.

Lemma ZFeq_to_minZFeq :
  @tprv ZFSignature.ZF_func_sig ZFSignature.ZF_pred_sig falsity_on class ZFeq falsity ->
  @tprv BinSig.sig_empty ZFSignature.ZF_pred_sig falsity_on class minZFeq falsity.
Proof. intro H. exact (@conservativity_ZF class falsity H). Qed.
