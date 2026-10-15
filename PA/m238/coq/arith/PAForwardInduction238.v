(** Actual transport of the pinned PA induction axiom. The ordinal
    minimum-counterexample induction family is fixed before selecting
    any parameter or predecessor witness. No model argument is used. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 OrdinalTrace238 AddGraph238
  PAForwardTerms238 PAForwardFormula238 PAForwardFormulaBasis238
  PAForwardFormulaSubstitution238 PAForwardInductionFamily238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 OrdinalTrace238.OrdinalTrace238
  AddGraph238.AddGraph238 PAForwardTerms238.PAForwardTerms238
  PAForwardFormula238.PAForwardFormula238 PAForwardFormulaBasis238.PAForwardFormulaBasis238
  PAForwardFormulaSubstitution238.PAForwardFormulaSubstitution238
  PAForwardInductionFamily238.PAForwardInductionFamily238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardInduction238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition pa_induction_step_substitution : nat -> PA238.pa_term :=
  pa_successor (pa_variable 0) .: (fun k => pa_variable (S k)).

Lemma interpreted_pa_induction_axiom G (phi : PA238.pa_form) rho :
  G ⊢238 formula_transport_basis ->
  G ⊢238 ordinal_induction (pa_formula_value phi (source_binder_environment rho)) ->
  (forall n, G ⊢238 ordinal_representative (rho n)) ->
  G ⊢238 pa_formula_value (ax_induction phi) rho.
Proof.
  intros HB HI HD.
  change (G ⊢238 (pa_formula_value (phi[pa_zero..]) rho →
    pa_formula_value (∀ (phi → phi[pa_induction_step_substitution])) rho →
      ∀ (ordinal_representative $0 → pa_formula_value phi (source_binder_environment rho)))).
  apply II, II.
  assert (HStep : (pa_formula_value (∀ (phi → phi[pa_induction_step_substitution])) rho ::
    pa_formula_value (phi[pa_zero..]) rho :: G)
      ⊢238 pa_formula_value (∀ (phi → phi[pa_induction_step_substitution])) rho).
  { apply Ctx. now left. }
  eapply IE; [eapply IE; [inherit HI|]|].
  - unfold ordinal_base. apply AllI_named. intro x.
    change ((pa_formula_value (∀ (phi → phi[pa_induction_step_substitution])) rho ::
      pa_formula_value (phi[pa_zero..]) rho :: G)
        ⊢238 ((ordinal_representative x ∧ raw_zero x) →
          (pa_formula_value phi (source_binder_environment rho))[x..])).
    rewrite pa_formula_value_binder_witness. apply II.
    eapply IE; [eapply CE1|apply Ctx; right; right; now left].
    apply (pa_formula_value_single_substitution _ phi pa_zero rho x).
    + inherit HB.
    + change ((ordinal_representative x ∧ raw_zero x ::
        pa_formula_value (∀ (phi → phi[pa_induction_step_substitution])) rho ::
        pa_formula_value (phi[pa_zero..]) rho :: G) ⊢238 (ordinal_representative x ∧ raw_zero x)).
      apply Ctx. now left.
    + intro n. inherit (HD n).
  - apply add_ordinal_step_intro. intros x y.
    rewrite !pa_formula_value_binder_witness.
    assert (HP : (pa_formula_value phi (x .: rho) ::
      ordinal_representative x ∧ (ordinal_representative y ∧ raw_successor x y) ::
      pa_formula_value (∀ (phi → phi[pa_induction_step_substitution])) rho ::
      pa_formula_value (phi[pa_zero..]) rho :: G)
        ⊢238 (ordinal_representative x ∧ (ordinal_representative y ∧ raw_successor x y))).
    { apply Ctx. right. now left. }
    eapply IE; [eapply CE1|].
    + apply (pa_formula_value_pa_substitution phi _ pa_induction_step_substitution
        (x .: rho) (y .: rho)).
      * inherit HB.
      * intros [|n].
        -- change ((pa_formula_value phi (x .: rho) ::
             ordinal_representative x ∧ (ordinal_representative y ∧ raw_successor x y) ::
             pa_formula_value (∀ (phi → phi[pa_induction_step_substitution])) rho ::
             pa_formula_value (phi[pa_zero..]) rho :: G) ⊢238 pa_term_value (pa_successor (pa_variable 0)) (x .: rho) y).
           apply (successor_value_intro _ (pa_variable 0) (x .: rho) x y).
           ++ exact (CE1 (CE2 HP)).
           ++ apply (variable_value_intro _ (x .: rho) 0).
              ** inherit (CE1 (CE1 (CE2 HB))).
              ** exact (CE1 HP).
           ++ exact (CE2 (CE2 HP)).
        -- change ((pa_formula_value phi (x .: rho) ::
             ordinal_representative x ∧ (ordinal_representative y ∧ raw_successor x y) ::
             pa_formula_value (∀ (phi → phi[pa_induction_step_substitution])) rho ::
             pa_formula_value (phi[pa_zero..]) rho :: G) ⊢238 variable_value (S n) (x .: rho) (rho n)).
           apply (variable_value_intro _ (x .: rho) (S n));
             [inherit (CE1 (CE1 (CE2 HB)))|inherit (HD n)].
    + change ((pa_formula_value (∀ (phi → phi[pa_induction_step_substitution])) rho ::
        pa_formula_value (phi[pa_zero..]) rho :: G) ⊢238 ∀ (ordinal_representative $0 →
          pa_formula_value (phi → phi[pa_induction_step_substitution]) (source_binder_environment rho))) in HStep.
      pose proof (AllE x HStep) as Hx.
      change ((pa_formula_value (∀ (phi → phi[pa_induction_step_substitution])) rho ::
        pa_formula_value (phi[pa_zero..]) rho :: G) ⊢238 (ordinal_representative x →
          (pa_formula_value (phi → phi[pa_induction_step_substitution]) (source_binder_environment rho))[x..])) in Hx.
      rewrite pa_formula_value_binder_witness in Hx.
      eapply IE; [|apply Ctx; now left].
      eapply IE; [inherit Hx|exact (CE1 HP)].
Qed.

(** The finite S0 list is chosen once for the PA formula. A caller may
    weaken it by ordinary ordinal guards; every supplied proof is an ND
    derivation in that concrete finite caller context. *)
Theorem S0_pa_induction_proof_family (phi : PA238.pa_form) :
  exists G : list set_form,
    (forall psi, List.In psi G -> finite_set_S0 psi) /\
    forall D rho, List.incl G D ->
      (forall n, D ⊢238 ordinal_representative (rho n)) ->
      D ⊢238 pa_formula_value (ax_induction phi) rho.
Proof.
  destruct S0_formula_transport_basis as [Gb [HGb HB]].
  destruct (S0_pa_induction_family phi) as [Gi [HGi HI]].
  set (G := Gb ++ Gi). exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGb|now apply HGi].
  - intros D rho Hinc HD. apply (interpreted_pa_induction_axiom D phi rho); [| |exact HD].
    + eapply Weak; [exact HB|]. intros psi Hpsi. apply Hinc. unfold G. apply in_or_app. now left.
    + eapply Weak; [exact (HI rho)|]. intros psi Hpsi. apply Hinc. unfold G. apply in_or_app. now right.
Qed.

Print Assumptions interpreted_pa_induction_axiom.
Print Assumptions S0_pa_induction_proof_family.
End PAForwardInduction238.
