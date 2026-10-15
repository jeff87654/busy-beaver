(** Original source formulas for the pinned ordinary PA syntax.
    Equality retains two actual term values and an actual Iso graph.
    Quantifiers range over the derived ordinal domain. This is syntactic
    interpretation groundwork, not a model-validity consistency argument. *)
From Coq Require Import List Vector.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 PairGraph238
  IsoGraph238 PAForwardTerms238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 PairGraph238.PairGraph238
  IsoGraph238.IsoGraph238 PAForwardTerms238.PAForwardTerms238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardFormula238.

Definition source_binder_environment (rho : nat -> set_term) : nat -> set_term :=
  $0 .: shifted_environment rho.
Definition interpreted_equality (t u : PA238.pa_term) (rho : nat -> set_term) : set_form :=
  ∃ ∃ (pa_term_value t (twice_shifted_environment rho) $1 ∧
    (pa_term_value u (twice_shifted_environment rho) $0 ∧ order_iso $1 $0)).
Definition pa_atom_value (p : PA_preds) :
  Vector.t PA238.pa_term (PA_preds_ar p) -> (nat -> set_term) -> set_form :=
  match p as p' return Vector.t PA238.pa_term (PA_preds_ar p') ->
      (nat -> set_term) -> set_form with
  | Eq => fun args rho => interpreted_equality (Vector.hd args) (Vector.hd (Vector.tl args)) rho
  end.

Fixpoint pa_formula_value {ff : falsity_flag}
  (phi : @form PA_funcs_signature PA_preds_signature full_operators ff)
  (rho : nat -> set_term) : set_form :=
  match phi with
  | falsity => falsity
  | atom p args => pa_atom_value p args rho
  | bin op psi chi => bin op (pa_formula_value psi rho) (pa_formula_value chi rho)
  | quant q psi =>
    match q with
    | All => ∀ (ordinal_representative $0 → pa_formula_value psi (source_binder_environment rho))
    | Ex => ∃ (ordinal_representative $0 ∧ pa_formula_value psi (source_binder_environment rho))
    end
  end.
Definition translate_pa_formula (phi : PA238.pa_form) : set_form :=
  pa_formula_value phi (fun k => $k).

Lemma interpreted_equality_environment_ext t u rho tau :
  (forall k, rho k = tau k) -> interpreted_equality t u rho = interpreted_equality t u tau.
Proof.
  intro H. unfold interpreted_equality.
  assert (Henv : forall k, twice_shifted_environment rho k = twice_shifted_environment tau k).
  { intro k. unfold twice_shifted_environment, shifted_environment. now rewrite (H k). }
  rewrite (pa_term_value_environment_ext t _ _ $1 Henv),
    (pa_term_value_environment_ext u _ _ $0 Henv). reflexivity.
Qed.

Lemma source_binder_environment_ext rho tau :
  (forall k, rho k = tau k) ->
  forall k, source_binder_environment rho k = source_binder_environment tau k.
Proof.
  intros H [|k]; [reflexivity|].
  unfold source_binder_environment, scons, shifted_environment. now rewrite (H k).
Qed.

Lemma pa_formula_value_environment_ext {ff} (phi : @form PA_funcs_signature
  PA_preds_signature full_operators ff) rho tau :
  (forall k, rho k = tau k) -> pa_formula_value phi rho = pa_formula_value phi tau.
Proof.
  revert rho tau. induction phi as [|ff' p args|ff' op psi IHpsi chi IHchi|ff' q psi IHpsi].
  - intros rho tau H. reflexivity.
  - intros rho tau H. destruct p.
    change (interpreted_equality (Vector.hd args) (Vector.hd (Vector.tl args)) rho =
      interpreted_equality (Vector.hd args) (Vector.hd (Vector.tl args)) tau).
    apply interpreted_equality_environment_ext. exact H.
  - intros rho tau H.
    change (bin op (pa_formula_value psi rho) (pa_formula_value chi rho) =
      bin op (pa_formula_value psi tau) (pa_formula_value chi tau)).
    now rewrite (IHpsi rho tau H), (IHchi rho tau H).
  - intros rho tau H. destruct q.
    + change ((∀ (ordinal_representative $0 → pa_formula_value psi (source_binder_environment rho))) =
        (∀ (ordinal_representative $0 → pa_formula_value psi (source_binder_environment tau)))).
      now rewrite (IHpsi _ _ (source_binder_environment_ext rho tau H)).
    + change ((∃ (ordinal_representative $0 ∧ pa_formula_value psi (source_binder_environment rho))) =
        (∃ (ordinal_representative $0 ∧ pa_formula_value psi (source_binder_environment tau)))).
      now rewrite (IHpsi _ _ (source_binder_environment_ext rho tau H)).
Qed.

Lemma source_iso_subst x y sigma :
  (order_iso x y)[sigma] = order_iso x`[sigma] y`[sigma].
Proof.
  unfold order_iso, order_bijection, graph_entries, entry_witness, graph_typed,
    graph_left_total, graph_right_total, IsoGraph238.IsoGraph238.graph_functional,
    graph_injective, graph_order, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma interpreted_equality_source_subst t u rho sigma :
  (interpreted_equality t u rho)[sigma] =
    interpreted_equality t u (fun k => (rho k)`[sigma]).
Proof.
  change ((∃ ∃ ((pa_term_value t (twice_shifted_environment rho) $1)[up (up sigma)] ∧
    ((pa_term_value u (twice_shifted_environment rho) $0)[up (up sigma)] ∧
      (order_iso $1 $0)[up (up sigma)]))) = interpreted_equality t u (fun k => (rho k)`[sigma])).
  rewrite !pa_term_value_source_subst, source_iso_subst.
  change ((∃ ∃ (pa_term_value t
    (fun k => (twice_shifted_environment rho k)`[up (up sigma)]) $1 ∧
      (pa_term_value u (fun k => (twice_shifted_environment rho k)`[up (up sigma)]) $0 ∧
        order_iso $1 $0))) = interpreted_equality t u (fun k => (rho k)`[sigma])).
  assert (Henv : forall k, (twice_shifted_environment rho k)`[up (up sigma)] =
    twice_shifted_environment (fun k => (rho k)`[sigma]) k).
  { intro k. unfold twice_shifted_environment, shifted_environment. now rewrite !up_term. }
  rewrite (pa_term_value_environment_ext t _ _ $1 Henv),
    (pa_term_value_environment_ext u _ _ $0 Henv). reflexivity.
Qed.

Lemma source_binder_environment_subst rho sigma k :
  (source_binder_environment rho k)`[up sigma] =
    source_binder_environment (fun n => (rho n)`[sigma]) k.
Proof.
  destruct k as [|k]; [reflexivity|].
  unfold source_binder_environment, scons, shifted_environment. apply up_term.
Qed.

Theorem pa_formula_value_source_subst {ff} (phi : @form PA_funcs_signature
  PA_preds_signature full_operators ff) rho sigma :
  (pa_formula_value phi rho)[sigma] = pa_formula_value phi (fun k => (rho k)`[sigma]).
Proof.
  revert rho sigma. induction phi as [|ff' p args|ff' op psi IHpsi chi IHchi|ff' q psi IHpsi].
  - intros rho sigma. reflexivity.
  - intros rho sigma. destruct p.
    change ((interpreted_equality (Vector.hd args) (Vector.hd (Vector.tl args)) rho)[sigma] =
      interpreted_equality (Vector.hd args) (Vector.hd (Vector.tl args))
        (fun k => (rho k)`[sigma])).
    apply interpreted_equality_source_subst.
  - intros rho sigma.
    change (bin op (pa_formula_value psi rho)[sigma] (pa_formula_value chi rho)[sigma] =
      bin op (pa_formula_value psi (fun k => (rho k)`[sigma]))
        (pa_formula_value chi (fun k => (rho k)`[sigma]))).
    now rewrite IHpsi, IHchi.
  - intros rho sigma. destruct q.
    + change ((∀ ((ordinal_representative $0)[up sigma] →
        (pa_formula_value psi (source_binder_environment rho))[up sigma])) =
      (∀ (ordinal_representative $0 →
        pa_formula_value psi (source_binder_environment (fun k => (rho k)`[sigma]))))).
      rewrite ordinal_value_subst, IHpsi.
      change ((∀ (ordinal_representative $0 → pa_formula_value psi
        (fun k => (source_binder_environment rho k)`[up sigma]))) =
        (∀ (ordinal_representative $0 →
          pa_formula_value psi (source_binder_environment (fun k => (rho k)`[sigma]))))).
      now rewrite (pa_formula_value_environment_ext psi _ _ (source_binder_environment_subst rho sigma)).
    + change ((∃ ((ordinal_representative $0)[up sigma] ∧
        (pa_formula_value psi (source_binder_environment rho))[up sigma])) =
      (∃ (ordinal_representative $0 ∧
        pa_formula_value psi (source_binder_environment (fun k => (rho k)`[sigma]))))).
      rewrite ordinal_value_subst, IHpsi.
      change ((∃ (ordinal_representative $0 ∧ pa_formula_value psi
        (fun k => (source_binder_environment rho k)`[up sigma]))) =
        (∃ (ordinal_representative $0 ∧
          pa_formula_value psi (source_binder_environment (fun k => (rho k)`[sigma]))))).
      now rewrite (pa_formula_value_environment_ext psi _ _ (source_binder_environment_subst rho sigma)).
Qed.

Print Assumptions interpreted_equality_environment_ext.
Print Assumptions pa_formula_value_environment_ext.
Print Assumptions source_iso_subst.
Print Assumptions interpreted_equality_source_subst.
Print Assumptions source_binder_environment_subst.
Print Assumptions pa_formula_value_source_subst.
End PAForwardFormula238.
