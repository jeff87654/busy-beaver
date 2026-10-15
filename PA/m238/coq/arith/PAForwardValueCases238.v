(** Original binder equations for eliminating actual PA value witnesses.
    Both input witnesses are retained with their term relations and the
    concrete source arithmetic relation; no selected evaluation is used. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import Compact238 PAinCompact238 PAForwardTerms238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  PAForwardTerms238.PAForwardTerms238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardValueCases238.

Definition successor_value_body t rho z : set_form :=
  pa_term_value t (shifted_environment rho) $0 ∧ raw_successor $0 z`[↑].
Definition binary_value_body op s t rho z : set_form :=
  pa_term_value s (twice_shifted_environment rho) $1 ∧
    (pa_term_value t (twice_shifted_environment rho) $0 ∧ op $1 $0 z`[↑]`[↑]).

Lemma successor_value_body_specialize t rho z x :
  (successor_value_body t rho z)[x..] =
    (pa_term_value t rho x ∧ raw_successor x z).
Proof.
  unfold successor_value_body.
  change (((pa_term_value t (shifted_environment rho) $0)[x..] ∧
    (raw_successor $0 z`[↑])[x..]) = (pa_term_value t rho x ∧ raw_successor x z)).
  rewrite pa_term_value_witness_specialize, raw_successor_subst.
  change ((pa_term_value t rho x ∧ raw_successor x z`[↑]`[x..]) =
    (pa_term_value t rho x ∧ raw_successor x z)).
  now rewrite source_shift_witness_cancel.
Qed.

Lemma binary_value_body_specialize op s t rho z x y :
  (forall a b c sigma, (op a b c)[sigma] = op a`[sigma] b`[sigma] c`[sigma]) ->
  ((binary_value_body op s t rho z)[up (x.. )])[y..] =
    (pa_term_value s rho x ∧ (pa_term_value t rho y ∧ op x y z)).
Proof.
  intro Hop. rewrite source_two_witness_subst. unfold binary_value_body.
  change (((pa_term_value s (twice_shifted_environment rho) $1)[y .: x .: var] ∧
    ((pa_term_value t (twice_shifted_environment rho) $0)[y .: x .: var] ∧
      (op $1 $0 z`[↑]`[↑])[y .: x .: var])) =
    (pa_term_value s rho x ∧ (pa_term_value t rho y ∧ op x y z))).
  rewrite !pa_term_value_source_subst, Hop.
  change ((pa_term_value s (fun k => (twice_shifted_environment rho k)`[y .: x .: var]) x ∧
    (pa_term_value t (fun k => (twice_shifted_environment rho k)`[y .: x .: var]) y ∧
      op x y z`[↑]`[↑]`[y .: x .: var])) =
    (pa_term_value s rho x ∧ (pa_term_value t rho y ∧ op x y z))).
  assert (Henv : forall k, (twice_shifted_environment rho k)`[y .: x .: var] = rho k).
  { intro k. unfold twice_shifted_environment, shifted_environment.
    apply source_twice_shift_witness_cancel. }
  rewrite (pa_term_value_environment_ext s _ rho x Henv),
    (pa_term_value_environment_ext t _ rho y Henv), source_twice_shift_witness_cancel.
  reflexivity.
Qed.

Lemma successor_value_inputs G t rho z :
  G ⊢238 pa_term_value (pa_successor t) rho z ->
  G ⊢238 ∃ successor_value_body t rho z.
Proof. intro H. exact (CE2 H). Qed.

Lemma binary_value_inputs G op s t rho z :
  G ⊢238 binary_value op (pa_term_value s) (pa_term_value t) rho z ->
  G ⊢238 ∃ ∃ binary_value_body op s t rho z.
Proof. intro H. exact (CE2 H). Qed.

Print Assumptions successor_value_body_specialize.
Print Assumptions binary_value_body_specialize.
Print Assumptions successor_value_inputs.
Print Assumptions binary_value_inputs.
End PAForwardValueCases238.
