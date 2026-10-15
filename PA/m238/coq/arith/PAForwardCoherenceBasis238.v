(** Original finite source basis for joint PA term-value comparison.
    Numerical equality uses the actual Iso graphs. Each arithmetic clause
    below is a derived finite S0 proof, including successor congruence. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 IsoGraph238 IsoZero238
  IsoSuccessorS0238 AddCoherence238 MulCoherence238 PAForwardBasis238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  IsoGraph238.IsoGraph238 IsoZero238.IsoZero238 IsoSuccessorS0238.IsoSuccessorS0238
  AddCoherence238.AddCoherence238 MulCoherence238.MulCoherence238
  PAForwardBasis238.PAForwardBasis238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardCoherenceBasis238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition zero_iso_ax : set_form :=
  ∀ ∀ (raw_zero $1 → (raw_zero $0 → order_iso $1 $0)).
Definition term_coherence_basis : set_form :=
  (∀ E $0 $0) ∧ (equality_membership_ax ∧ (equality_symmetry_ax ∧
    (zero_iso_ax ∧ (iso_successor_congruence_ax ∧
      (add_comparison_ax ∧ mul_comparison_ax))))).

Theorem S0_zero_order_iso a b :
  derivable finite_set_S0 (raw_zero a → (raw_zero b → order_iso a b)).
Proof.
  destruct S0_empty as [G [HG HE]]. exists G. split; [exact HG|].
  apply II, II, (zero_order_iso _ a b).
  - inherit HE.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Theorem S0_zero_iso_ax : derivable finite_set_S0 zero_iso_ax.
Proof.
  unfold zero_iso_ax. apply S0_generalize, S0_generalize.
  exact (S0_zero_order_iso $1 $0).
Qed.

Theorem S0_term_coherence_basis : derivable finite_set_S0 term_coherence_basis.
Proof.
  unfold term_coherence_basis. apply finite_derivable_conjunction.
  - apply derivable_axiom, S0_base. apply in_or_app. left.
    unfold equality_base. cbn. now left.
  - apply finite_derivable_conjunction.
    + apply derivable_axiom, S0_base. apply in_or_app. left.
      unfold equality_base, equality_membership_ax. cbn. right. right. right. now left.
    + apply finite_derivable_conjunction.
      * apply derivable_axiom, S0_base. apply in_or_app. left.
        unfold equality_base, equality_symmetry_ax. cbn. right. now left.
      * apply finite_derivable_conjunction; [exact S0_zero_iso_ax|].
        apply finite_derivable_conjunction; [exact S0_order_iso_successor_congruence_closed|].
        apply finite_derivable_conjunction; [exact S0_add_comparison_closed|].
        exact S0_mul_comparison_closed.
Qed.

Lemma term_basis_zero_compare G a b :
  G ⊢238 term_coherence_basis -> G ⊢238 raw_zero a -> G ⊢238 raw_zero b ->
  G ⊢238 order_iso a b.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HB HA HC.
  pose proof (CE1 (CE2 (CE2 (CE2 HB)))) as HZ. unfold zero_iso_ax in HZ.
  pose proof (AllE $ib (AllE $ia HZ)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HC]. eapply IE; [exact H|exact HA].
Qed.

Lemma term_basis_successor_compare G a sa b sb :
  G ⊢238 term_coherence_basis -> G ⊢238 ordinal_representative a ->
  G ⊢238 ordinal_representative b -> G ⊢238 raw_successor a sa ->
  G ⊢238 raw_successor b sb -> G ⊢238 order_iso a b -> G ⊢238 order_iso sa sb.
Proof.
  intros HC HA HB HS HT HI. apply (iso_successor_congruence_instance G a sa b sb);
    [exact (CE1 (CE2 (CE2 (CE2 (CE2 HC)))))|exact HA|exact HB|exact HS|exact HT|exact HI].
Qed.

Lemma term_basis_addition_compare G x x' y y' z z' :
  G ⊢238 term_coherence_basis -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative x' -> G ⊢238 ordinal_representative y ->
  G ⊢238 ordinal_representative y' -> G ⊢238 order_iso x x' ->
  G ⊢238 order_iso y y' ->
  G ⊢238 AddGraph238.AddGraph238.add_result x y z ->
  G ⊢238 AddGraph238.AddGraph238.add_result x' y' z' -> G ⊢238 order_iso z z'.
Proof.
  intros HC HX HX' HY HY' HI HJ HM HN. apply (add_comparison_instance G x x' y y' z z');
    [exact (CE1 (CE2 (CE2 (CE2 (CE2 (CE2 HC))))))|
     exact HX|exact HX'|exact HY|exact HY'|exact HI|exact HJ|exact HM|exact HN].
Qed.

Lemma term_basis_multiplication_compare G x x' y y' z z' :
  G ⊢238 term_coherence_basis -> G ⊢238 ordinal_representative x ->
  G ⊢238 ordinal_representative x' -> G ⊢238 ordinal_representative y ->
  G ⊢238 ordinal_representative y' -> G ⊢238 order_iso x x' ->
  G ⊢238 order_iso y y' ->
  G ⊢238 MulGraph238.MulGraph238.mul_result x y z ->
  G ⊢238 MulGraph238.MulGraph238.mul_result x' y' z' -> G ⊢238 order_iso z z'.
Proof.
  intros HC HX HX' HY HY' HI HJ HM HN. apply (mul_comparison_instance G x x' y y' z z');
    [exact (CE2 (CE2 (CE2 (CE2 (CE2 (CE2 HC))))))|
     exact HX|exact HX'|exact HY|exact HY'|exact HI|exact HJ|exact HM|exact HN].
Qed.

Print Assumptions S0_zero_order_iso.
Print Assumptions S0_zero_iso_ax.
Print Assumptions S0_term_coherence_basis.
Print Assumptions term_basis_zero_compare.
Print Assumptions term_basis_successor_compare.
Print Assumptions term_basis_addition_compare.
Print Assumptions term_basis_multiplication_compare.
End PAForwardCoherenceBasis238.
