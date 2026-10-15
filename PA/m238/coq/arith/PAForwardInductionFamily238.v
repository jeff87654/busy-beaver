(** One finite S0 context supplies the whole parameter family for an
    interpreted PA induction formula. Substitution only instantiates the
    source parameters; the ordinal-induction variable remains bound. *)
From Coq Require Import List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 OrdinalTrace238
  PAForwardTerms238 PAForwardFormula238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 OrdinalTrace238.OrdinalTrace238
  PAForwardTerms238.PAForwardTerms238 PAForwardFormula238.PAForwardFormula238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardInductionFamily238.

Lemma predecessor_slots_parameters (phi : set_form) sigma :
  (phi[predecessor_slots])[up (up sigma)] = (phi[up sigma])[predecessor_slots].
Proof.
  rewrite !subst_comp. apply subst_ext. intros [|k]; [reflexivity|].
  change ((sigma k)`[↑]`[↑] = (sigma k)`[↑]`[predecessor_slots]).
  destruct (sigma k) as [i|[]]. reflexivity.
Qed.

Lemma successor_slots_parameters (phi : set_form) sigma :
  (phi[successor_slots])[up (up sigma)] = (phi[up sigma])[successor_slots].
Proof.
  rewrite !subst_comp. apply subst_ext. intros [|k]; [reflexivity|].
  change ((sigma k)`[↑]`[↑] = (sigma k)`[↑]`[successor_slots]).
  destruct (sigma k) as [i|[]]. reflexivity.
Qed.

Lemma ordinal_induction_source_subst (phi : set_form) sigma :
  (ordinal_induction phi)[sigma] = ordinal_induction (phi[up sigma]).
Proof.
  unfold ordinal_induction, ordinal_base, ordinal_step.
  change (((∀ (((ordinal_representative $0)[up sigma] ∧ (raw_zero $0)[up sigma]) → phi[up sigma])) →
    (∀ ∀ (((ordinal_representative $1)[up (up sigma)] ∧
      ((ordinal_representative $0)[up (up sigma)] ∧ (raw_successor $1 $0)[up (up sigma)])) →
        ((phi[predecessor_slots])[up (up sigma)] → (phi[successor_slots])[up (up sigma)]))) →
    ∀ ((ordinal_representative $0)[up sigma] → phi[up sigma])) =
      ((∀ ((ordinal_representative $0 ∧ raw_zero $0) → phi[up sigma])) →
        (∀ ∀ ((ordinal_representative $1 ∧
          (ordinal_representative $0 ∧ raw_successor $1 $0)) →
            ((phi[up sigma])[predecessor_slots] → (phi[up sigma])[successor_slots]))) →
        ∀ (ordinal_representative $0 → phi[up sigma]))).
  rewrite !ordinal_value_subst, source_zero_subst, raw_successor_subst,
    predecessor_slots_parameters, successor_slots_parameters. reflexivity.
Qed.

Lemma finite_S0_context_subst G sigma :
  (forall phi, List.In phi G -> finite_set_S0 phi) ->
  List.map (subst_form sigma) G = G.
Proof.
  induction G as [|phi G IH]; intro HG; [reflexivity|]. cbn. f_equal.
  - apply bounded_0_subst, finite_set_S0_closed, HG. now left.
  - apply IH. intros psi Hpsi. apply HG. now right.
Qed.

Theorem S0_pa_induction_family (phi : PA238.pa_form) :
  exists G : list set_form,
    (forall psi, List.In psi G -> finite_set_S0 psi) /\
    forall rho, G ⊢238 ordinal_induction
      (pa_formula_value phi (source_binder_environment rho)).
Proof.
  set (P := pa_formula_value phi (fun k => $k)).
  destruct (find_bounded P) as [n Hn].
  assert (HP : bounded (1 + n) P). { eapply bounded_up; [exact Hn|lia]. }
  destruct (S0_ordinal_induction n P HP) as [G [HG HI]].
  exists G. split; [exact HG|]. intro rho.
  pose proof (@FullNDFacts.subst_Weak sig_empty ZF_pred_sig falsity_on class
    G (ordinal_induction P) rho HI) as HS.
  change (List.map (subst_form rho) G ⊢238 (ordinal_induction P)[rho]) in HS.
  rewrite (finite_S0_context_subst G rho HG), ordinal_induction_source_subst in HS.
  unfold P in HS. rewrite pa_formula_value_source_subst in HS.
  assert (Henv : forall k, ($k)`[up rho] = source_binder_environment rho k).
  { intros [|k]; reflexivity. }
  rewrite (pa_formula_value_environment_ext phi _ _ Henv) in HS. exact HS.
Qed.

Print Assumptions predecessor_slots_parameters.
Print Assumptions successor_slots_parameters.
Print Assumptions ordinal_induction_source_subst.
Print Assumptions finite_S0_context_subst.
Print Assumptions S0_pa_induction_family.
End PAForwardInductionFamily238.
