(* Original finite PA empty-set producer. Code zero has no member because
   actual Ackermann membership implies a strictly smaller position, and
   the constructed PA zero-minimality certificate excludes that position. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAOrder238 CompactInPA238 PABitPosition238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 CompactInPA238 PABitPosition238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PAEmptyCode238.

Definition zero_cutoff_sentence : pa_form := ∀ ¬ ($0 ⧀ zero).
Definition empty_context : list pa_form := List.cons zero_cutoff_sentence bit_context.
Lemma empty_proof phi : empty_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := zero_cutoff_sentence).
  - apply bit_proof, II. exact HD.
  - exact PAOrder238.zero_minimal.
Qed.

Theorem actual_empty_producer : empty_producer_goal.
Proof.
  change (paeq_derivable (∃ ∀ ¬ coded_member $1 $0)).
  apply empty_proof, (ExI zero).
  change (empty_context ⊢C ∀ ¬ coded_member zero $0).
  apply AllI_named. intros x.
  change (empty_context ⊢C ¬ (coded_member zero $0)[x..]).
  rewrite coded_member_subst.
  change (empty_context ⊢C ¬ coded_member zero x). apply II.
  set (G := List.cons (coded_member zero x) empty_context).
  change (G ⊢C falsity).
  assert (HG : has_bit_context G).
  { intros phi Hphi. unfold G, empty_context. right. right. exact Hphi. }
  assert (HM : G ⊢C coded_member zero x).
  { apply Ctx. unfold G. now left. }
  pose proof (bit_position G zero x HG HM) as HX.
  assert (HO : G ⊢C zero_cutoff_sentence).
  { apply Ctx. unfold G, empty_context. right. now left. }
  pose proof (AllE x HO) as HK.
  change (G ⊢C ¬ (PAlt $0 zero)[x..]) in HK.
  rewrite PAlt_subst in HK.
  change (G ⊢C ¬ (x ⧀ zero)) in HK. exact (IE HK HX).
Qed.

End PAEmptyCode238.

Print Assumptions PAEmptyCode238.actual_empty_producer.
