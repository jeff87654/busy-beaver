(** Ordinary PA equality laws are actual S0 derivations about the retained
    numerical equality graphs. Bound variables retain their ordinal guards. *)
From Coq Require Import List Vector.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 IsoGraph238 IsoEquality238
  PAForwardTerms238 PAForwardFormula238 PAForwardEquality238 PAForwardFormulaBasis238
  PAForwardQuantifier238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 IsoGraph238.IsoGraph238
  IsoEquality238.IsoEquality238 PAForwardTerms238.PAForwardTerms238
  PAForwardFormula238.PAForwardFormula238 PAForwardEquality238.PAForwardEquality238
  PAForwardFormulaBasis238.PAForwardFormulaBasis238 PAForwardQuantifier238.PAForwardQuantifier238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardEqualityLaws238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition pa_equality_formula (t u : PA238.pa_term) : PA238.pa_form :=
  @atom PA_funcs_signature PA_preds_signature full_operators falsity_on Eq
    (Vector.cons PA238.pa_term t 1 (Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term))).

Lemma interpreted_variable_equality_intro G rho n m :
  G ⊢238 formula_transport_basis -> G ⊢238 ordinal_representative (rho n) ->
  G ⊢238 ordinal_representative (rho m) -> G ⊢238 order_iso (rho n) (rho m) ->
  G ⊢238 interpreted_equality (pa_variable n) (pa_variable m) rho.
Proof.
  intros HB Hn Hm HI. apply (interpreted_equality_intro G (pa_variable n) (pa_variable m) rho (rho n) (rho m)).
  - exact (variable_value_intro G rho n (CE1 (CE1 (CE2 HB))) Hn).
  - exact (variable_value_intro G rho m (CE1 (CE1 (CE2 HB))) Hm).
  - exact HI.
Qed.

Lemma interpreted_variable_equality_elim G rho n m :
  G ⊢238 formula_transport_basis ->
  G ⊢238 interpreted_equality (pa_variable n) (pa_variable m) rho ->
  G ⊢238 order_iso (rho n) (rho m).
Proof.
  intros HB HE. apply (interpreted_equality_elim G (pa_variable n) (pa_variable m) rho _ HE).
  intros x y.
  assert (HJ : (pa_term_value (pa_variable n) rho x ∧
    (pa_term_value (pa_variable m) rho y ∧ order_iso x y) :: G)
      ⊢238 (pa_term_value (pa_variable n) rho x ∧
        (pa_term_value (pa_variable m) rho y ∧ order_iso x y))).
  { apply Ctx. now left. }
  apply (order_iso_coordinate_transport _ x y (rho n) (rho m)).
  - inherit (CE1 (CE1 (CE2 HB))).
  - inherit (CE1 (CE2 (CE1 (CE2 HB)))).
  - inherit (CE1 (CE2 (CE2 (CE1 (CE2 HB))))).
  - exact (CE2 (CE1 HJ)).
  - exact (CE2 (CE1 (CE2 HJ))).
  - exact (CE2 (CE2 HJ)).
Qed.

Lemma interpreted_pa_symmetry_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 pa_formula_value ax_sym rho.
Proof.
  intro HB.
  change (G ⊢238 pa_formula_value
    (∀ ∀ (pa_equality_formula (pa_variable 1) (pa_variable 0) →
      pa_equality_formula (pa_variable 0) (pa_variable 1))) rho).
  apply interpreted_all_introduce. intro x.
  assert (HX : (ordinal_representative x :: G) ⊢238 ordinal_representative x).
  { apply Ctx. now left. }
  apply interpreted_all_introduce. intro y.
  assert (HY : (ordinal_representative y :: ordinal_representative x :: G) ⊢238 ordinal_representative y).
  { apply Ctx. now left. }
  change ((ordinal_representative y :: ordinal_representative x :: G) ⊢238
    (interpreted_equality (pa_variable 1) (pa_variable 0) (y .: x .: rho) →
      interpreted_equality (pa_variable 0) (pa_variable 1) (y .: x .: rho))).
  apply II, (interpreted_variable_equality_intro _ (y .: x .: rho) 0 1).
  - inherit HB.
  - inherit HY.
  - inherit HX.
  - apply (formula_basis_iso_symmetric _ x y); [inherit HB|inherit HX|].
    apply (interpreted_variable_equality_elim _ (y .: x .: rho) 1 0);
      [inherit HB|apply Ctx; now left].
Qed.

Lemma interpreted_pa_transitivity_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 pa_formula_value ax_trans rho.
Proof.
  intro HB.
  change (G ⊢238 pa_formula_value
    (∀ ∀ ∀ (pa_equality_formula (pa_variable 2) (pa_variable 1) →
      pa_equality_formula (pa_variable 1) (pa_variable 0) →
        pa_equality_formula (pa_variable 2) (pa_variable 0))) rho).
  apply interpreted_all_introduce. intro x.
  assert (HX : (ordinal_representative x :: G) ⊢238 ordinal_representative x).
  { apply Ctx. now left. }
  apply interpreted_all_introduce. intro y. apply interpreted_all_introduce. intro z.
  assert (HZ : (ordinal_representative z :: ordinal_representative y ::
    ordinal_representative x :: G) ⊢238 ordinal_representative z).
  { apply Ctx. now left. }
  change ((ordinal_representative z :: ordinal_representative y :: ordinal_representative x :: G) ⊢238
    (interpreted_equality (pa_variable 2) (pa_variable 1) (z .: y .: x .: rho) →
      interpreted_equality (pa_variable 1) (pa_variable 0) (z .: y .: x .: rho) →
        interpreted_equality (pa_variable 2) (pa_variable 0) (z .: y .: x .: rho))).
  apply II, II, (interpreted_variable_equality_intro _ (z .: y .: x .: rho) 2 0).
  - inherit HB.
  - inherit HX.
  - inherit HZ.
  - apply (formula_basis_iso_transitive _ x y z); [inherit HB|inherit HX| |].
    + apply (interpreted_variable_equality_elim _ (z .: y .: x .: rho) 2 1);
        [inherit HB|apply Ctx; right; now left].
    + apply (interpreted_variable_equality_elim _ (z .: y .: x .: rho) 1 0);
        [inherit HB|apply Ctx; now left].
Qed.

Theorem S0_pa_symmetry_axiom rho : derivable finite_set_S0 (pa_formula_value ax_sym rho).
Proof.
  destruct S0_formula_transport_basis as [G [HG HB]]. exists G. split; [exact HG|].
  exact (interpreted_pa_symmetry_axiom G rho HB).
Qed.

Theorem S0_pa_transitivity_axiom rho : derivable finite_set_S0 (pa_formula_value ax_trans rho).
Proof.
  destruct S0_formula_transport_basis as [G [HG HB]]. exists G. split; [exact HG|].
  exact (interpreted_pa_transitivity_axiom G rho HB).
Qed.

Print Assumptions interpreted_variable_equality_intro.
Print Assumptions interpreted_variable_equality_elim.
Print Assumptions interpreted_pa_symmetry_axiom.
Print Assumptions interpreted_pa_transitivity_axiom.
Print Assumptions S0_pa_symmetry_axiom.
Print Assumptions S0_pa_transitivity_axiom.
End PAForwardEqualityLaws238.
