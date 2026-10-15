(* Original finite interpretation of the actual beta remainder relation.
   The two existential quotient witnesses are fed to the constructed PA
   bounded-remainder certificate. No beta totality or power producer is
   assumed, and the beta definition is kept unchanged. *)
From Coq Require Import List.
From P238.arith Require Import PAeq238 PAEqCongruence238 PAQuotient238
  PARemainderUnique238 CompactInPA238.
Local Unset Implicit Arguments.
Local Set Strict Implicit.
Import ListNotations FullSyntax PA238 PAQuotient238 PARemainderUnique238 CompactInPA238.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PABetaUnique238.

Definition remainder_unique_sentence : pa_form :=
  ∀ ∀ ∀ ∀ ∀ remainder_matrix $1 $0 $2 $3 $4.
Definition beta_context : list pa_form :=
  List.cons remainder_unique_sentence quotient_context.
Lemma beta_proof phi : beta_context ⊢C phi -> paeq_derivable phi.
Proof.
  intros HD. eapply paeq_modus_ponens with (phi := remainder_unique_sentence).
  - apply quotient_proof, II. exact HD.
  - exact bounded_remainder_unique.
Qed.
Lemma remainder_instance G q qp m r s : List.In remainder_unique_sentence G ->
  G ⊢C remainder_matrix q qp m r s.
Proof.
  intros H. assert (HH : G ⊢C remainder_unique_sentence) by now apply Ctx.
  assert (HB : bounded 5 (remainder_matrix $1 $0 $2 $3 $4)).
  { unfold remainder_matrix, quotient_row, PAlt. solve_bounds. }
  pose proof (subst_forall_prv (phi := remainder_matrix $1 $0 $2 $3 $4)
    (N := 5) HH HB (qp .: q .: m .: r .: s .: var)) as HK.
  rewrite matrix_subst in HK.
  change (G ⊢C remainder_matrix q qp m r s) in HK. exact HK.
Qed.

Theorem beta_unique :
  paeq_derivable (∀ ∀ ∀ ∀ ∀
    (beta $0 $1 $2 $3 → beta $0 $1 $2 $4 → $3 == $4)).
Proof.
  apply paeq_generalize, paeq_generalize, paeq_generalize,
    paeq_generalize, paeq_generalize, beta_proof, II, II.
  set (G := List.cons (beta $0 $1 $2 $4) (List.cons (beta $0 $1 $2 $3) beta_context)).
  change (G ⊢C ($3 == $4)).
  assert (HX : G ⊢C beta $0 $1 $2 $3).
  { apply Ctx. unfold G. right. now left. }
  unfold beta in HX. eapply ExE_named; [exact HX|]. intros q. cbn.
  set (m := beta_modulus $1 $2).
  set (D := List.cons (($0 == quotient_row q m $3) ∧ ($3 ⧀ m)) G).
  change (D ⊢C ($3 == $4)).
  assert (HY : D ⊢C beta $0 $1 $2 $4).
  { apply Ctx. unfold D, G. right. now left. }
  unfold beta in HY. eapply ExE_named; [exact HY|]. intros qp. cbn.
  set (E := List.cons (($0 == quotient_row qp m $4) ∧ ($4 ⧀ m)) D).
  change (E ⊢C ($3 == $4)).
  assert (HG : has_quotient_context E).
  { intros phi Hphi. unfold E, D, G, beta_context.
    right. right. right. right. right. exact Hphi. }
  pose proof (quotient_has_equality E HG) as HE.
  assert (HL : E ⊢C ($0 == quotient_row q m $3)).
  { eapply CE1. apply Ctx. unfold E, D. right. now left. }
  assert (HR : E ⊢C ($0 == quotient_row qp m $4)).
  { eapply CE1. apply Ctx. unfold E. now left. }
  assert (HBL : E ⊢C ($3 ⧀ m)).
  { eapply CE2. apply Ctx. unfold E, D. right. now left. }
  assert (HBR : E ⊢C ($4 ⧀ m)).
  { eapply CE2. apply Ctx. unfold E. now left. }
  pose proof (PAEqCongruence238.equality_symmetry E $0 (quotient_row q m $3) HE HL) as HS.
  pose proof (PAEqCongruence238.equality_transitivity E
    (quotient_row q m $3) $0 (quotient_row qp m $4) HE HS HR) as HQ.
  assert (HU : List.In remainder_unique_sentence E).
  { unfold E, D, G, beta_context. right. right. right. right. now left. }
  pose proof (remainder_instance E q qp m $3 $4 HU) as HM.
  unfold remainder_matrix in HM. exact (IE (IE (IE HM HQ) HBL) HBR).
Qed.

End PABetaUnique238.

Print Assumptions PABetaUnique238.beta_unique.
