(** Finite source guards for ordinary PA substitution. A variable input is
    an actual value proof; no graph or witness is chosen in the metatheory. *)
From Coq Require Import List Vector.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238
  PAForwardTerms238 PAForwardTotal238 PAForwardDomains238 PAForwardSubstitution238
  PAForwardRename238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  PAForwardTerms238.PAForwardTerms238 PAForwardTotal238.PAForwardTotal238
  PAForwardDomains238.PAForwardDomains238 PAForwardSubstitution238.PAForwardSubstitution238
  PAForwardRename238.PAForwardRename238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardSubstitutionGuard238.

Lemma pa_substitution_values_domains t G sigma rho tau :
  G ⊢238 pa_substitution_values t sigma rho tau -> G ⊢238 pa_term_domains t tau.
Proof.
  revert G sigma rho tau. induction t as [n|f args IH] using term_ind.
  - intros G sigma rho tau HV. apply (pa_term_value_ordinal G (sigma n) rho (tau n)). exact HV.
  - intros G sigma rho tau HV. destruct f.
    + apply II, Ctx. now left.
    + remember (Vector.hd args) as u eqn:Hu.
      assert (V : args = Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term)).
      { rewrite Hu. apply destruct_vector_single. }
      rewrite V in IH, HV |- *. exact (IH u ltac:(constructor) G sigma rho tau HV).
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HV |- *. apply CI.
      * exact (IH u ltac:(constructor) G sigma rho tau (CE1 HV)).
      * exact (IH v ltac:(constructor 2; constructor) G sigma rho tau (CE2 HV)).
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HV |- *. apply CI.
      * exact (IH u ltac:(constructor) G sigma rho tau (CE1 HV)).
      * exact (IH v ltac:(constructor 2; constructor) G sigma rho tau (CE2 HV)).
Qed.

Lemma pa_substitution_values_input_domains t G sigma rho tau :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
  G ⊢238 equality_symmetry_ax -> G ⊢238 pa_substitution_values t sigma rho tau ->
  G ⊢238 pa_term_domains (t`[sigma]) rho.
Proof.
  revert G sigma rho tau. induction t as [n|f args IH] using term_ind.
  - intros G sigma rho tau HE HM HS HV.
    exact (pa_term_value_domains (sigma n) G rho (tau n) HE HM HS HV).
  - intros G sigma rho tau HE HM HS HV. destruct f.
    + apply II, Ctx. now left.
    + remember (Vector.hd args) as u eqn:Hu.
      assert (V : args = Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term)).
      { rewrite Hu. apply destruct_vector_single. }
      rewrite V in IH, HV |- *. exact (IH u ltac:(constructor) G sigma rho tau HE HM HS HV).
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HV |- *. apply CI.
      * exact (IH u ltac:(constructor) G sigma rho tau HE HM HS (CE1 HV)).
      * exact (IH v ltac:(constructor 2; constructor) G sigma rho tau HE HM HS (CE2 HV)).
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HV |- *. apply CI.
      * exact (IH u ltac:(constructor) G sigma rho tau HE HM HS (CE1 HV)).
      * exact (IH v ltac:(constructor 2; constructor) G sigma rho tau HE HM HS (CE2 HV)).
Qed.

Lemma pa_substitution_values_from_environment t G sigma rho tau :
  (forall n, G ⊢238 pa_term_value (sigma n) rho (tau n)) ->
  G ⊢238 pa_substitution_values t sigma rho tau.
Proof.
  revert G sigma rho tau. induction t as [n|f args IH] using term_ind.
  - intros G sigma rho tau HV. exact (HV n).
  - intros G sigma rho tau HV. destruct f.
    + apply II, Ctx. now left.
    + remember (Vector.hd args) as u eqn:Hu.
      assert (V : args = Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term)).
      { rewrite Hu. apply destruct_vector_single. }
      rewrite V in IH |- *. exact (IH u ltac:(constructor) G sigma rho tau HV).
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH |- *. apply CI.
      * exact (IH u ltac:(constructor) G sigma rho tau HV).
      * exact (IH v ltac:(constructor 2; constructor) G sigma rho tau HV).
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH |- *. apply CI.
      * exact (IH u ltac:(constructor) G sigma rho tau HV).
      * exact (IH v ltac:(constructor 2; constructor) G sigma rho tau HV).
Qed.

Lemma single_term_substitution_environment G u rho x :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 pa_term_value u rho x ->
  (forall n, G ⊢238 ordinal_representative (rho n)) ->
  forall n, G ⊢238 pa_term_value ((u..) n) rho ((x .: rho) n).
Proof.
  intros HE HU HD [|n]; [exact HU|].
  change (G ⊢238 variable_value n rho (rho n)).
  exact (variable_value_intro G rho n HE (HD n)).
Qed.

Lemma single_term_substitution_values t G u rho x :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 pa_term_value u rho x ->
  (forall n, G ⊢238 ordinal_representative (rho n)) ->
  G ⊢238 pa_substitution_values t (u..) rho (x .: rho).
Proof.
  intros HE HU HD. apply pa_substitution_values_from_environment.
  exact (single_term_substitution_environment G u rho x HE HU HD).
Qed.

Lemma lifted_substitution_environment G sigma rho tau x :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 ordinal_representative x ->
  (forall n, G ⊢238 pa_term_value (sigma n) rho (tau n)) ->
  forall n, G ⊢238 pa_term_value (up sigma n) (x .: rho) ((x .: tau) n).
Proof.
  intros HE HX HV [|n].
  - change (G ⊢238 variable_value 0 (x .: rho) x).
    exact (variable_value_intro G (x .: rho) 0 HE HX).
  - change (G ⊢238 pa_term_value ((sigma n)`[pa_renaming S]) (x .: rho) (tau n)).
    rewrite pa_term_value_pa_rename. exact (HV n).
Qed.

Print Assumptions pa_substitution_values_domains.
Print Assumptions pa_substitution_values_input_domains.
Print Assumptions pa_substitution_values_from_environment.
Print Assumptions single_term_substitution_environment.
Print Assumptions single_term_substitution_values.
Print Assumptions lifted_substitution_environment.
End PAForwardSubstitutionGuard238.
