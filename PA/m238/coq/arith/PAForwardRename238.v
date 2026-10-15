(** Original renaming equations for finite PA proof transport.
    PA variables are renamed in the pinned syntax. Their source values
    use the corresponding indexed environment, including under binders. *)
From Coq Require Import List Vector.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238
  PAForwardTerms238 PAForwardFormula238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  PAForwardTerms238.PAForwardTerms238 PAForwardFormula238.PAForwardFormula238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardRename238.
Definition pa_renaming (xi : nat -> nat) : nat -> PA238.pa_term :=
  fun k => @var PA_funcs_signature (xi k).
Definition lifted_renaming (xi : nat -> nat) : nat -> nat :=
  0 .: (fun k => S (xi k)).

Lemma pa_renaming_up xi k : up (pa_renaming xi) k = pa_renaming (lifted_renaming xi) k.
Proof. destruct k; reflexivity. Qed.

Theorem pa_term_value_pa_rename t xi rho z :
  pa_term_value (t`[pa_renaming xi]) rho z = pa_term_value t (fun k => rho (xi k)) z.
Proof.
  revert xi rho z. induction t as [n|f args IH] using term_ind.
  - intros xi rho z. reflexivity.
  - intros xi rho z. destruct f.
    + reflexivity.
    + remember (Vector.hd args) as u eqn:Hu.
      assert (V : args = Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term)).
      { rewrite Hu. apply destruct_vector_single. }
      rewrite V in IH |- *.
      change ((ordinal_representative z ∧
        ∃ (pa_term_value (u`[pa_renaming xi]) (shifted_environment rho) $0 ∧ raw_successor $0 z`[↑])) =
        (ordinal_representative z ∧
          ∃ (pa_term_value u (shifted_environment (fun k => rho (xi k))) $0 ∧ raw_successor $0 z`[↑]))).
      rewrite (IH u ltac:(constructor) xi (shifted_environment rho) $0). reflexivity.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH |- *.
      change ((ordinal_representative z ∧
        ∃ ∃ (pa_term_value (u`[pa_renaming xi]) (twice_shifted_environment rho) $1 ∧
          (pa_term_value (v`[pa_renaming xi]) (twice_shifted_environment rho) $0 ∧
            AddGraph238.AddGraph238.add_result $1 $0 z`[↑]`[↑]))) =
        (ordinal_representative z ∧
          ∃ ∃ (pa_term_value u (twice_shifted_environment (fun k => rho (xi k))) $1 ∧
            (pa_term_value v (twice_shifted_environment (fun k => rho (xi k))) $0 ∧
              AddGraph238.AddGraph238.add_result $1 $0 z`[↑]`[↑])))).
      rewrite (IH u ltac:(constructor) xi (twice_shifted_environment rho) $1),
        (IH v ltac:(constructor 2; constructor) xi (twice_shifted_environment rho) $0).
      reflexivity.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH |- *.
      change ((ordinal_representative z ∧
        ∃ ∃ (pa_term_value (u`[pa_renaming xi]) (twice_shifted_environment rho) $1 ∧
          (pa_term_value (v`[pa_renaming xi]) (twice_shifted_environment rho) $0 ∧
            MulGraph238.MulGraph238.mul_result $1 $0 z`[↑]`[↑]))) =
        (ordinal_representative z ∧
          ∃ ∃ (pa_term_value u (twice_shifted_environment (fun k => rho (xi k))) $1 ∧
            (pa_term_value v (twice_shifted_environment (fun k => rho (xi k))) $0 ∧
              MulGraph238.MulGraph238.mul_result $1 $0 z`[↑]`[↑])))).
      rewrite (IH u ltac:(constructor) xi (twice_shifted_environment rho) $1),
        (IH v ltac:(constructor 2; constructor) xi (twice_shifted_environment rho) $0).
      reflexivity.
Qed.

Lemma interpreted_equality_pa_rename t u xi rho :
  interpreted_equality (t`[pa_renaming xi]) (u`[pa_renaming xi]) rho =
    interpreted_equality t u (fun k => rho (xi k)).
Proof.
  unfold interpreted_equality. rewrite !pa_term_value_pa_rename. reflexivity.
Qed.

Lemma binder_index_rename rho xi k :
  source_binder_environment rho (lifted_renaming xi k) =
    source_binder_environment (fun n => rho (xi n)) k.
Proof. destruct k; reflexivity. Qed.

Theorem pa_formula_value_pa_rename {ff} (phi : @form PA_funcs_signature
  PA_preds_signature full_operators ff) xi rho :
  pa_formula_value (phi[pa_renaming xi]) rho = pa_formula_value phi (fun k => rho (xi k)).
Proof.
  revert xi rho. induction phi as [|ff' p args|ff' op psi IHpsi chi IHchi|ff' q psi IHpsi].
  - intros xi rho. reflexivity.
  - intros xi rho. destruct p.
    remember (Vector.hd args) as u eqn:Hu.
    remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
    assert (V : args = Vector.cons PA238.pa_term u 1
      (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
    { rewrite Hu, Hv. apply pa_vector2_eta. }
    rewrite V. apply interpreted_equality_pa_rename.
  - intros xi rho.
    change (bin op (pa_formula_value (psi[pa_renaming xi]) rho)
      (pa_formula_value (chi[pa_renaming xi]) rho) =
        bin op (pa_formula_value psi (fun k => rho (xi k)))
          (pa_formula_value chi (fun k => rho (xi k)))).
    now rewrite IHpsi, IHchi.
  - intros xi rho.
    assert (Hup : psi[up (pa_renaming xi)] = psi[pa_renaming (lifted_renaming xi)]).
    { apply subst_ext. apply pa_renaming_up. }
    destruct q.
    + change ((∀ (ordinal_representative $0 →
        pa_formula_value (psi[up (pa_renaming xi)]) (source_binder_environment rho))) =
      (∀ (ordinal_representative $0 →
        pa_formula_value psi (source_binder_environment (fun k => rho (xi k)))))).
      rewrite Hup, IHpsi.
      now rewrite (pa_formula_value_environment_ext psi _ _ (binder_index_rename rho xi)).
    + change ((∃ (ordinal_representative $0 ∧
        pa_formula_value (psi[up (pa_renaming xi)]) (source_binder_environment rho))) =
      (∃ (ordinal_representative $0 ∧
        pa_formula_value psi (source_binder_environment (fun k => rho (xi k)))))).
      rewrite Hup, IHpsi.
      now rewrite (pa_formula_value_environment_ext psi _ _ (binder_index_rename rho xi)).
Qed.

Lemma pa_formula_value_shift {ff} (phi : @form PA_funcs_signature
  PA_preds_signature full_operators ff) rho x :
  pa_formula_value (phi[pa_renaming S]) (x .: rho) = pa_formula_value phi rho.
Proof. rewrite pa_formula_value_pa_rename. reflexivity. Qed.

Print Assumptions pa_renaming_up.
Print Assumptions pa_term_value_pa_rename.
Print Assumptions interpreted_equality_pa_rename.
Print Assumptions binder_index_rename.
Print Assumptions pa_formula_value_pa_rename.
Print Assumptions pa_formula_value_shift.
End PAForwardRename238.
