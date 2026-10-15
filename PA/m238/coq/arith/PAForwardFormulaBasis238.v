(** Derived finite S0 basis for transporting ordinary PA formulas. Symmetry
    and transitivity are proved with actual inverse and composition graphs. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 PairGraph238 IsoGraph238
  InverseGraph238 CompositionIso238 PAForwardBasis238 PAForwardCoherenceBasis238
  PAForwardDeterminacy238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 PairGraph238.PairGraph238
  IsoGraph238.IsoGraph238 InverseGraph238.InverseGraph238 CompositionIso238.CompositionIso238
  PAForwardBasis238.PAForwardBasis238 PAForwardCoherenceBasis238.PAForwardCoherenceBasis238
  PAForwardDeterminacy238.PAForwardDeterminacy238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardFormulaBasis238.
Definition iso_symmetry_ax : set_form :=
  ∀ ∀ (ordinal_representative $1 → (order_iso $1 $0 → order_iso $0 $1)).
Definition formula_transport_basis : set_form :=
  term_totality_basis ∧ (term_coherence_basis ∧
    (iso_reflexivity_ax ∧ (iso_symmetry_ax ∧ iso_transitivity_ax))).

Theorem S0_iso_symmetry_ax : derivable finite_set_S0 iso_symmetry_ax.
Proof.
  unfold iso_symmetry_ax. apply S0_generalize, S0_generalize.
  exact (S0_order_iso_symmetric $1 $0).
Qed.

Theorem S0_formula_transport_basis : derivable finite_set_S0 formula_transport_basis.
Proof.
  unfold formula_transport_basis. apply finite_derivable_conjunction; [exact S0_term_totality_basis|].
  apply finite_derivable_conjunction; [exact S0_term_coherence_basis|].
  apply finite_derivable_conjunction; [exact S0_iso_reflexivity_ax|].
  apply finite_derivable_conjunction; [exact S0_iso_symmetry_ax|].
  exact S0_order_iso_transitive_closed.
Qed.

Lemma formula_basis_iso_symmetric G a b :
  G ⊢238 formula_transport_basis -> G ⊢238 ordinal_representative a ->
  G ⊢238 order_iso a b -> G ⊢238 order_iso b a.
Proof.
  destruct a as [ia|[]], b as [ib|[]]. intros HB HA HI.
  pose proof (CE1 (CE2 (CE2 (CE2 HB)))) as HS. unfold iso_symmetry_ax in HS.
  pose proof (AllE $ib (AllE $ia HS)) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HI]. eapply IE; [exact H|exact HA].
Qed.

Lemma formula_basis_iso_transitive G a b c :
  G ⊢238 formula_transport_basis -> G ⊢238 ordinal_representative a ->
  G ⊢238 order_iso a b -> G ⊢238 order_iso b c -> G ⊢238 order_iso a c.
Proof.
  destruct a as [ia|[]], b as [ib|[]], c as [ic|[]]. intros HB HA HI HJ.
  pose proof (CE2 (CE2 (CE2 (CE2 HB)))) as HT. unfold iso_transitivity_ax in HT.
  pose proof (AllE $ic (AllE $ib (AllE $ia HT))) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  eapply IE; [|exact HJ]. eapply IE; [|exact HI]. eapply IE; [exact H|exact HA].
Qed.

Print Assumptions S0_iso_symmetry_ax.
Print Assumptions S0_formula_transport_basis.
Print Assumptions formula_basis_iso_symmetric.
Print Assumptions formula_basis_iso_transitive.
End PAForwardFormulaBasis238.
