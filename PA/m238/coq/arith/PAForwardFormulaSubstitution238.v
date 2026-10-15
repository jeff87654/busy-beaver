(** Syntactic finite natural-deduction transport of PA substitution through
    every formula, including both guarded binders. The environment premise
    consists of actual finite proofs and is lifted with the bound ordinal. *)
From Coq Require Import List Vector.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 PAForwardTerms238
  PAForwardFormula238 PAForwardEquality238 PAForwardSubstitution238
  PAForwardSubstitutionGuard238 PAForwardFormulaBasis238 PAForwardAtomicSubstitution238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 PAForwardTerms238.PAForwardTerms238
  PAForwardFormula238.PAForwardFormula238 PAForwardEquality238.PAForwardEquality238
  PAForwardSubstitution238.PAForwardSubstitution238
  PAForwardSubstitutionGuard238.PAForwardSubstitutionGuard238
  PAForwardFormulaBasis238.PAForwardFormulaBasis238
  PAForwardAtomicSubstitution238.PAForwardAtomicSubstitution238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardFormulaSubstitution238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Lemma pa_formula_value_binder_witness {ff} (phi : @form PA_funcs_signature
  PA_preds_signature full_operators ff) rho x :
  (pa_formula_value phi (source_binder_environment rho))[x..] =
    pa_formula_value phi (x .: rho).
Proof.
  rewrite pa_formula_value_source_subst.
  apply pa_formula_value_environment_ext. apply source_binder_environment_witness.
Qed.

Lemma source_bin_equivalence G op (a a' b b' : set_form) :
  G ⊢238 (a ↔ a') -> G ⊢238 (b ↔ b') ->
  G ⊢238 (bin op a b ↔ bin op a' b').
Proof.
  intros HA HB. destruct op; apply CI.
  - apply II, CI.
    + eapply IE; [inherit (CE1 HA)|]. eapply CE1, Ctx. now left.
    + eapply IE; [inherit (CE1 HB)|]. eapply CE2, Ctx. now left.
  - apply II, CI.
    + eapply IE; [inherit (CE2 HA)|]. eapply CE1, Ctx. now left.
    + eapply IE; [inherit (CE2 HB)|]. eapply CE2, Ctx. now left.
  - apply II. eapply DE; [apply Ctx; now left| |].
    + apply DI1. eapply IE; [inherit (CE1 HA)|apply Ctx; now left].
    + apply DI2. eapply IE; [inherit (CE1 HB)|apply Ctx; now left].
  - apply II. eapply DE; [apply Ctx; now left| |].
    + apply DI1. eapply IE; [inherit (CE2 HA)|apply Ctx; now left].
    + apply DI2. eapply IE; [inherit (CE2 HB)|apply Ctx; now left].
  - apply II, II. eapply IE; [inherit (CE1 HB)|].
    eapply IE; [apply Ctx; right; now left|].
    eapply IE; [inherit (CE2 HA)|apply Ctx; now left].
  - apply II, II. eapply IE; [inherit (CE2 HB)|].
    eapply IE; [apply Ctx; right; now left|].
    eapply IE; [inherit (CE1 HA)|apply Ctx; now left].
Qed.

Definition formula_substitution_rule {ff} (phi : @form PA_funcs_signature
  PA_preds_signature full_operators ff) : Prop :=
  forall G sigma rho tau,
    G ⊢238 formula_transport_basis ->
    (forall n, G ⊢238 pa_term_value (sigma n) rho (tau n)) ->
    G ⊢238 (pa_formula_value (phi[sigma]) rho ↔ pa_formula_value phi tau).

Theorem pa_formula_value_pa_substitution {ff} (phi : @form PA_funcs_signature
  PA_preds_signature full_operators ff) : formula_substitution_rule phi.
Proof.
  induction phi as [|ff' p args|ff' op psi IHpsi chi IHchi|ff' q psi IHpsi].
  - intros G sigma rho tau HB HV. apply CI; apply II, Ctx; now left.
  - intros G sigma rho tau HB HV. destruct p.
    remember (Vector.hd args) as t eqn:Ht.
    remember (Vector.hd (Vector.tl args)) as u eqn:Hu.
    assert (V : args = Vector.cons PA238.pa_term t 1
      (Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term))).
    { rewrite Ht, Hu. apply pa_vector2_eta. }
    rewrite V. change (G ⊢238 (interpreted_equality (t`[sigma]) (u`[sigma]) rho ↔
      interpreted_equality t u tau)). apply CI.
    + apply II, (interpreted_equality_substitution_forward _ t u sigma rho tau).
      * inherit HB.
      * apply pa_substitution_values_from_environment. intro n. inherit (HV n).
      * apply pa_substitution_values_from_environment. intro n. inherit (HV n).
      * apply Ctx. now left.
    + apply II, (interpreted_equality_substitution_backward _ t u sigma rho tau).
      * inherit HB.
      * apply pa_substitution_values_from_environment. intro n. inherit (HV n).
      * apply pa_substitution_values_from_environment. intro n. inherit (HV n).
      * apply Ctx. now left.
  - intros G sigma rho tau HB HV.
    change (G ⊢238 (bin op (pa_formula_value (psi[sigma]) rho) (pa_formula_value (chi[sigma]) rho) ↔
      bin op (pa_formula_value psi tau) (pa_formula_value chi tau))).
    apply source_bin_equivalence; [exact (IHpsi G sigma rho tau HB HV)|exact (IHchi G sigma rho tau HB HV)].
  - intros G sigma rho tau HB HV. destruct q.
    + change (G ⊢238 ((∀ (ordinal_representative $0 →
        pa_formula_value (psi[up sigma]) (source_binder_environment rho))) ↔
      (∀ (ordinal_representative $0 → pa_formula_value psi (source_binder_environment tau))))).
      apply CI.
      * apply II.
        assert (HA : (∀ (ordinal_representative $0 →
          pa_formula_value (psi[up sigma]) (source_binder_environment rho)) :: G)
            ⊢238 ∀ (ordinal_representative $0 →
              pa_formula_value (psi[up sigma]) (source_binder_environment rho))).
        { apply Ctx. now left. }
        apply AllI_named. intro x.
        change ((∀ (ordinal_representative $0 →
          pa_formula_value (psi[up sigma]) (source_binder_environment rho)) :: G)
            ⊢238 (ordinal_representative x →
              (pa_formula_value psi (source_binder_environment tau))[x..])).
        rewrite pa_formula_value_binder_witness. apply II.
        assert (HI : (ordinal_representative x :: ∀ (ordinal_representative $0 →
          pa_formula_value (psi[up sigma]) (source_binder_environment rho)) :: G)
            ⊢238 (pa_formula_value (psi[up sigma]) (x .: rho) ↔ pa_formula_value psi (x .: tau))).
        { apply (IHpsi _ (up sigma) (x .: rho) (x .: tau)).
          - inherit HB.
          - apply lifted_substitution_environment.
            + inherit (CE1 (CE1 (CE2 HB))).
            + apply Ctx. now left.
            + intro n. inherit (HV n). }
        eapply IE; [exact (CE1 HI)|].
        pose proof (AllE x HA) as Hx.
        change ((∀ (ordinal_representative $0 →
          pa_formula_value (psi[up sigma]) (source_binder_environment rho)) :: G)
            ⊢238 (ordinal_representative x →
              (pa_formula_value (psi[up sigma]) (source_binder_environment rho))[x..])) in Hx.
        rewrite pa_formula_value_binder_witness in Hx.
        eapply IE; [inherit Hx|apply Ctx; now left].
      * apply II.
        assert (HA : (∀ (ordinal_representative $0 →
          pa_formula_value psi (source_binder_environment tau)) :: G)
            ⊢238 ∀ (ordinal_representative $0 → pa_formula_value psi (source_binder_environment tau))).
        { apply Ctx. now left. }
        apply AllI_named. intro x.
        change ((∀ (ordinal_representative $0 → pa_formula_value psi (source_binder_environment tau)) :: G)
          ⊢238 (ordinal_representative x →
            (pa_formula_value (psi[up sigma]) (source_binder_environment rho))[x..])).
        rewrite pa_formula_value_binder_witness. apply II.
        assert (HI : (ordinal_representative x :: ∀ (ordinal_representative $0 →
          pa_formula_value psi (source_binder_environment tau)) :: G)
            ⊢238 (pa_formula_value (psi[up sigma]) (x .: rho) ↔ pa_formula_value psi (x .: tau))).
        { apply (IHpsi _ (up sigma) (x .: rho) (x .: tau)).
          - inherit HB.
          - apply lifted_substitution_environment.
            + inherit (CE1 (CE1 (CE2 HB))).
            + apply Ctx. now left.
            + intro n. inherit (HV n). }
        eapply IE; [exact (CE2 HI)|].
        pose proof (AllE x HA) as Hx.
        change ((∀ (ordinal_representative $0 →
          pa_formula_value psi (source_binder_environment tau)) :: G)
            ⊢238 (ordinal_representative x →
              (pa_formula_value psi (source_binder_environment tau))[x..])) in Hx.
        rewrite pa_formula_value_binder_witness in Hx.
        eapply IE; [inherit Hx|apply Ctx; now left].
    + change (G ⊢238 ((∃ (ordinal_representative $0 ∧
        pa_formula_value (psi[up sigma]) (source_binder_environment rho))) ↔
      (∃ (ordinal_representative $0 ∧ pa_formula_value psi (source_binder_environment tau))))).
      apply CI.
      * apply II. eapply ExE_named; [apply Ctx; now left|]. intro x.
        change ((ordinal_representative x ∧
          (pa_formula_value (psi[up sigma]) (source_binder_environment rho))[x..] ::
            ∃ (ordinal_representative $0 ∧
              pa_formula_value (psi[up sigma]) (source_binder_environment rho)) :: G)
                ⊢238 ∃ (ordinal_representative $0 ∧ pa_formula_value psi (source_binder_environment tau))).
        rewrite pa_formula_value_binder_witness.
        assert (HX : (ordinal_representative x ∧ pa_formula_value (psi[up sigma]) (x .: rho) ::
          ∃ (ordinal_representative $0 ∧
            pa_formula_value (psi[up sigma]) (source_binder_environment rho)) :: G)
              ⊢238 (ordinal_representative x ∧ pa_formula_value (psi[up sigma]) (x .: rho))).
        { apply Ctx. now left. }
        apply (ExI x).
        change ((ordinal_representative x ∧ pa_formula_value (psi[up sigma]) (x .: rho) ::
          ∃ (ordinal_representative $0 ∧
            pa_formula_value (psi[up sigma]) (source_binder_environment rho)) :: G)
              ⊢238 (ordinal_representative x ∧
                (pa_formula_value psi (source_binder_environment tau))[x..])).
        rewrite pa_formula_value_binder_witness. apply CI; [exact (CE1 HX)|].
        eapply IE; [|exact (CE2 HX)]. eapply CE1.
        apply (IHpsi _ (up sigma) (x .: rho) (x .: tau)).
        -- inherit HB.
        -- apply lifted_substitution_environment.
           ++ inherit (CE1 (CE1 (CE2 HB))).
           ++ exact (CE1 HX).
           ++ intro n. inherit (HV n).
      * apply II. eapply ExE_named; [apply Ctx; now left|]. intro x.
        change ((ordinal_representative x ∧
          (pa_formula_value psi (source_binder_environment tau))[x..] ::
            ∃ (ordinal_representative $0 ∧ pa_formula_value psi (source_binder_environment tau)) :: G)
              ⊢238 ∃ (ordinal_representative $0 ∧
                pa_formula_value (psi[up sigma]) (source_binder_environment rho))).
        rewrite pa_formula_value_binder_witness.
        assert (HX : (ordinal_representative x ∧ pa_formula_value psi (x .: tau) ::
          ∃ (ordinal_representative $0 ∧ pa_formula_value psi (source_binder_environment tau)) :: G)
            ⊢238 (ordinal_representative x ∧ pa_formula_value psi (x .: tau))).
        { apply Ctx. now left. }
        apply (ExI x).
        change ((ordinal_representative x ∧ pa_formula_value psi (x .: tau) ::
          ∃ (ordinal_representative $0 ∧ pa_formula_value psi (source_binder_environment tau)) :: G)
            ⊢238 (ordinal_representative x ∧
              (pa_formula_value (psi[up sigma]) (source_binder_environment rho))[x..])).
        rewrite pa_formula_value_binder_witness. apply CI; [exact (CE1 HX)|].
        eapply IE; [|exact (CE2 HX)]. eapply CE2.
        apply (IHpsi _ (up sigma) (x .: rho) (x .: tau)).
        -- inherit HB.
        -- apply lifted_substitution_environment.
           ++ inherit (CE1 (CE1 (CE2 HB))).
           ++ exact (CE1 HX).
           ++ intro n. inherit (HV n).
Qed.

Lemma pa_formula_value_single_substitution G (phi : PA238.pa_form) u rho x :
  G ⊢238 formula_transport_basis -> G ⊢238 pa_term_value u rho x ->
  (forall n, G ⊢238 ordinal_representative (rho n)) ->
  G ⊢238 (pa_formula_value (phi[u..]) rho ↔ pa_formula_value phi (x .: rho)).
Proof.
  intros HB HV HD. apply pa_formula_value_pa_substitution; [exact HB|].
  exact (single_term_substitution_environment G u rho x (CE1 (CE1 (CE2 HB))) HV HD).
Qed.

Print Assumptions pa_formula_value_binder_witness.
Print Assumptions source_bin_equivalence.
Print Assumptions pa_formula_value_pa_substitution.
Print Assumptions pa_formula_value_single_substitution.
End PAForwardFormulaSubstitution238.
