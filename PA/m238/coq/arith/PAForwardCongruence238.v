(** Actual operation congruence for interpreted PA equality. The retained
    input equality supplies real operand values; successor construction
    and comparison supply the actual output equality graph. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 IsoGraph238
  PAForwardTerms238 PAForwardFormula238 PAForwardEquality238 PAForwardEqualityLaws238
  PAForwardBasis238 PAForwardCoherenceBasis238 PAForwardFormulaBasis238 PAForwardQuantifier238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 IsoGraph238.IsoGraph238
  PAForwardTerms238.PAForwardTerms238 PAForwardFormula238.PAForwardFormula238
  PAForwardEquality238.PAForwardEquality238 PAForwardEqualityLaws238.PAForwardEqualityLaws238
  PAForwardBasis238.PAForwardBasis238 PAForwardCoherenceBasis238.PAForwardCoherenceBasis238
  PAForwardFormulaBasis238.PAForwardFormulaBasis238 PAForwardQuantifier238.PAForwardQuantifier238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardCongruence238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma represented_successor_body_specialize a b :
  (ordinal_representative $0 ∧ raw_successor a`[↑] $0)[b..] =
    (ordinal_representative b ∧ raw_successor a b).
Proof.
  change (((ordinal_representative $0)[b..] ∧ (raw_successor a`[↑] $0)[b..]) =
    (ordinal_representative b ∧ raw_successor a b)).
  rewrite ordinal_value_subst, raw_successor_subst.
  change ((ordinal_representative b ∧ raw_successor a`[↑]`[b..] b) =
    (ordinal_representative b ∧ raw_successor a b)).
  now rewrite source_shift_witness_cancel.
Qed.

Lemma represented_successor_elim G a (phi : set_form) :
  G ⊢238 ∃ (ordinal_representative $0 ∧ raw_successor a`[↑] $0) ->
  (forall b, (ordinal_representative b ∧ raw_successor a b :: G) ⊢238 phi) ->
  G ⊢238 phi.
Proof.
  intros HE HB. eapply ExE_named; [exact HE|]. intro b.
  apply (derivation_head_replace G
    ((ordinal_representative $0 ∧ raw_successor a`[↑] $0)[b..])
    (ordinal_representative b ∧ raw_successor a b) phi).
  - exact (represented_successor_body_specialize a b).
  - exact (HB b).
Qed.

Lemma interpreted_successor_congruence G t u rho :
  G ⊢238 formula_transport_basis -> G ⊢238 interpreted_equality t u rho ->
  G ⊢238 interpreted_equality (pa_successor t) (pa_successor u) rho.
Proof.
  intros HB HE. apply (interpreted_equality_elim G t u rho _ HE). intros x y.
  assert (HJ : (pa_term_value t rho x ∧ (pa_term_value u rho y ∧ order_iso x y) :: G)
    ⊢238 (pa_term_value t rho x ∧ (pa_term_value u rho y ∧ order_iso x y))).
  { apply Ctx. now left. }
  eapply (represented_successor_elim _ x).
  - apply term_basis_successor; [inherit (CE1 HB)|].
    exact (pa_term_value_ordinal _ t rho x (CE1 HJ)).
  - intro a.
    assert (HA : (ordinal_representative a ∧ raw_successor x a ::
      pa_term_value t rho x ∧ (pa_term_value u rho y ∧ order_iso x y) :: G)
        ⊢238 (ordinal_representative a ∧ raw_successor x a)).
    { apply Ctx. now left. }
    eapply (represented_successor_elim _ y).
    + apply term_basis_successor; [inherit (CE1 HB)|].
      apply (pa_term_value_ordinal _ u rho y). inherit (CE1 (CE2 HJ)).
    + intro b.
      assert (HB' : (ordinal_representative b ∧ raw_successor y b ::
        ordinal_representative a ∧ raw_successor x a ::
        pa_term_value t rho x ∧ (pa_term_value u rho y ∧ order_iso x y) :: G)
          ⊢238 (ordinal_representative b ∧ raw_successor y b)).
      { apply Ctx. now left. }
      apply (interpreted_equality_intro _ (pa_successor t) (pa_successor u) rho a b).
      * apply (successor_value_intro _ t rho x a); [inherit (CE1 HA)|inherit (CE1 HJ)|inherit (CE2 HA)].
      * apply (successor_value_intro _ u rho y b);
          [exact (CE1 HB')|inherit (CE1 (CE2 HJ))|exact (CE2 HB')].
      * apply (term_basis_successor_compare _ x a y b).
        -- inherit (CE1 (CE2 HB)).
        -- apply (pa_term_value_ordinal _ t rho x). inherit (CE1 HJ).
        -- apply (pa_term_value_ordinal _ u rho y). inherit (CE1 (CE2 HJ)).
        -- inherit (CE2 HA).
        -- exact (CE2 HB').
        -- inherit (CE2 (CE2 HJ)).
Qed.

Lemma interpreted_pa_successor_congruence_axiom G rho :
  G ⊢238 formula_transport_basis -> G ⊢238 pa_formula_value ax_succ_congr rho.
Proof.
  intro HB. change (G ⊢238 pa_formula_value
    (∀ ∀ (pa_equality_formula (pa_variable 0) (pa_variable 1) →
      pa_equality_formula (pa_successor (pa_variable 0)) (pa_successor (pa_variable 1)))) rho).
  apply interpreted_all_introduce. intro x. apply interpreted_all_introduce. intro y.
  change ((ordinal_representative y :: ordinal_representative x :: G) ⊢238
    (interpreted_equality (pa_variable 0) (pa_variable 1) (y .: x .: rho) →
      interpreted_equality (pa_successor (pa_variable 0)) (pa_successor (pa_variable 1)) (y .: x .: rho))).
  apply II, interpreted_successor_congruence; [inherit HB|apply Ctx; now left].
Qed.

Theorem S0_pa_successor_congruence_axiom rho :
  derivable finite_set_S0 (pa_formula_value ax_succ_congr rho).
Proof.
  destruct S0_formula_transport_basis as [G [HG HB]]. exists G. split; [exact HG|].
  exact (interpreted_pa_successor_congruence_axiom G rho HB).
Qed.

Print Assumptions represented_successor_body_specialize.
Print Assumptions represented_successor_elim.
Print Assumptions interpreted_successor_congruence.
Print Assumptions interpreted_pa_successor_congruence_axiom.
Print Assumptions S0_pa_successor_congruence_axiom.
End PAForwardCongruence238.
