(** Original realization comparison for ordinary PA term substitution.
    The substitution guard is finite: it retains source values only for
    variables occurring in the given PA term. All comparisons are finite
    natural-deduction proofs using the derived arithmetic graph basis. *)
From Coq Require Import List Vector.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 IsoGraph238 IsoEquality238
  PAForwardTerms238 PAForwardValueCases238 PAForwardCoherenceBasis238 PAForwardCovariance238
  PAForwardTotal238 PAForwardDomains238 PAForwardDeterminacy238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 IsoGraph238.IsoGraph238
  IsoEquality238.IsoEquality238 PAForwardTerms238.PAForwardTerms238
  PAForwardValueCases238.PAForwardValueCases238 PAForwardCoherenceBasis238.PAForwardCoherenceBasis238
  PAForwardCovariance238.PAForwardCovariance238 PAForwardTotal238.PAForwardTotal238
  PAForwardDomains238.PAForwardDomains238 PAForwardDeterminacy238.PAForwardDeterminacy238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardSubstitution238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition substitution_relation :=
  (nat -> PA238.pa_term) -> (nat -> set_term) -> (nat -> set_term) -> set_form.
Definition function_substitutions (f : PA_funcs) :
  Vector.t substitution_relation (PA_funcs_ar f) -> substitution_relation :=
  match f as f' return Vector.t substitution_relation (PA_funcs_ar f') -> substitution_relation with
  | Zero => fun _ _ _ _ => (falsity → falsity)
  | Succ => fun args => Vector.hd args
  | Plus => fun args sigma rho tau => Vector.hd args sigma rho tau ∧ Vector.hd (Vector.tl args) sigma rho tau
  | Mult => fun args sigma rho tau => Vector.hd args sigma rho tau ∧ Vector.hd (Vector.tl args) sigma rho tau
  end.
Fixpoint pa_substitution_values (t : PA238.pa_term) : substitution_relation :=
  match t with
  | var n => fun sigma rho tau => pa_term_value (sigma n) rho (tau n)
  | func f args => function_substitutions f (Vector.map pa_substitution_values args)
  end.
Definition term_substitution_rule (t : PA238.pa_term) : Prop :=
  forall G sigma rho tau z w,
    G ⊢238 term_coherence_basis -> G ⊢238 iso_reflexivity_ax ->
    G ⊢238 pa_substitution_values t sigma rho tau ->
    G ⊢238 pa_term_value (t`[sigma]) rho z ->
    G ⊢238 pa_term_value t tau w -> G ⊢238 order_iso z w.

Lemma binary_substitution_comparison G op s t sigma rho tau z w :
  (forall a b c xi, (op a b c)[xi] = op a`[xi] b`[xi] c`[xi]) ->
  (forall D a a' b b' c c', D ⊢238 term_coherence_basis ->
    D ⊢238 ordinal_representative a -> D ⊢238 ordinal_representative a' ->
    D ⊢238 ordinal_representative b -> D ⊢238 ordinal_representative b' ->
    D ⊢238 order_iso a a' -> D ⊢238 order_iso b b' ->
    D ⊢238 op a b c -> D ⊢238 op a' b' c' -> D ⊢238 order_iso c c') ->
  term_substitution_rule s -> term_substitution_rule t ->
  G ⊢238 term_coherence_basis -> G ⊢238 iso_reflexivity_ax ->
  G ⊢238 pa_substitution_values s sigma rho tau -> G ⊢238 pa_substitution_values t sigma rho tau ->
  G ⊢238 binary_value op (pa_term_value (s`[sigma])) (pa_term_value (t`[sigma])) rho z ->
  G ⊢238 binary_value op (pa_term_value s) (pa_term_value t) tau w -> G ⊢238 order_iso z w.
Proof.
  intros Hop HC HS HT HB HR HD HE HZ HW. eapply ExE_named.
  - apply (binary_value_inputs G op (s`[sigma]) (t`[sigma]) rho z). exact HZ.
  - intro x. change ((∃ (binary_value_body op (s`[sigma]) (t`[sigma]) rho z)[up (x..)] :: G)
      ⊢238 order_iso z w).
    eapply ExE_named; [apply Ctx; now left|]. intro y.
    rewrite (binary_value_body_specialize op (s`[sigma]) (t`[sigma]) rho z x y Hop).
    assert (HL : (pa_term_value (s`[sigma]) rho x ∧ (pa_term_value (t`[sigma]) rho y ∧ op x y z) ::
      (∃ (binary_value_body op (s`[sigma]) (t`[sigma]) rho z)[up (x..)]) :: G)
        ⊢238 (pa_term_value (s`[sigma]) rho x ∧ (pa_term_value (t`[sigma]) rho y ∧ op x y z))).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (binary_value_inputs _ op s t tau w). inherit HW.
    + intro x'. change ((∃ (binary_value_body op s t tau w)[up (x'..)] ::
        pa_term_value (s`[sigma]) rho x ∧ (pa_term_value (t`[sigma]) rho y ∧ op x y z) ::
        (∃ (binary_value_body op (s`[sigma]) (t`[sigma]) rho z)[up (x..)]) :: G) ⊢238 order_iso z w).
      eapply ExE_named; [apply Ctx; now left|]. intro y'.
      rewrite (binary_value_body_specialize op s t tau w x' y' Hop).
      assert (HV : (pa_term_value s tau x' ∧ (pa_term_value t tau y' ∧ op x' y' w) ::
        (∃ (binary_value_body op s t tau w)[up (x'..)]) ::
        pa_term_value (s`[sigma]) rho x ∧ (pa_term_value (t`[sigma]) rho y ∧ op x y z) ::
        (∃ (binary_value_body op (s`[sigma]) (t`[sigma]) rho z)[up (x..)]) :: G)
          ⊢238 (pa_term_value s tau x' ∧ (pa_term_value t tau y' ∧ op x' y' w))).
      { apply Ctx. now left. }
      apply (HC _ x x' y y' z w).
      * inherit HB.
      * apply (pa_term_value_ordinal _ (s`[sigma]) rho x). inherit (CE1 HL).
      * apply (pa_term_value_ordinal _ s tau x'). exact (CE1 HV).
      * apply (pa_term_value_ordinal _ (t`[sigma]) rho y). inherit (CE1 (CE2 HL)).
      * apply (pa_term_value_ordinal _ t tau y'). exact (CE1 (CE2 HV)).
      * apply (HS _ sigma rho tau x x');
          [inherit HB|inherit HR|inherit HD|inherit (CE1 HL)|exact (CE1 HV)].
      * apply (HT _ sigma rho tau y y');
          [inherit HB|inherit HR|inherit HE|inherit (CE1 (CE2 HL))|exact (CE1 (CE2 HV))].
      * inherit (CE2 (CE2 HL)).
      * exact (CE2 (CE2 HV)).
Qed.

Theorem pa_term_value_pa_substitution t : term_substitution_rule t.
Proof.
  induction t as [n|f args IH] using term_ind.
  - intros G sigma rho tau z w HB HR HD HZ HW.
    apply (order_iso_coordinate_transport G z (tau n) z w).
    + exact (CE1 HB).
    + exact (CE1 (CE2 HB)).
    + exact (CE1 (CE2 (CE2 HB))).
    + exact (AllE z (CE1 HB)).
    + apply equality_symmetry_instance; [exact (CE1 (CE2 (CE2 HB)))|exact (CE2 HW)].
    + apply (pa_term_value_comparison (sigma n) G rho rho z (tau n)).
      * exact HB.
      * apply (pa_term_comparisons_reflexive G (sigma n) rho); [exact HR|].
        apply (pa_term_value_domains (sigma n) G rho (tau n));
          [exact (CE1 HB)|exact (CE1 (CE2 HB))|exact (CE1 (CE2 (CE2 HB)))|exact HD].
      * exact HZ.
      * exact HD.
  - intros G sigma rho tau z w HB HR HD HZ HW. destruct f.
    + apply (term_basis_zero_compare G z w); [exact HB|exact (CE2 HZ)|exact (CE2 HW)].
    + remember (Vector.hd args) as u eqn:Hu.
      assert (V : args = Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term)).
      { rewrite Hu. apply destruct_vector_single. }
      rewrite V in IH, HD, HZ, HW. eapply ExE_named.
      * apply (successor_value_inputs G (u`[sigma]) rho z). exact HZ.
      * intro x. rewrite successor_value_body_specialize.
        assert (HX : (pa_term_value (u`[sigma]) rho x ∧ raw_successor x z :: G)
          ⊢238 (pa_term_value (u`[sigma]) rho x ∧ raw_successor x z)).
        { apply Ctx. now left. }
        eapply ExE_named.
        -- apply (successor_value_inputs _ u tau w). inherit HW.
        -- intro y. rewrite successor_value_body_specialize.
           apply (term_basis_successor_compare _ x z y w).
           ++ inherit HB.
           ++ apply (pa_term_value_ordinal _ (u`[sigma]) rho x). inherit (CE1 HX).
           ++ apply (pa_term_value_ordinal _ u tau y). eapply CE1, Ctx. now left.
           ++ inherit (CE2 HX).
           ++ eapply CE2, Ctx. now left.
           ++ apply (IH u ltac:(constructor) _ sigma rho tau x y).
              ** inherit HB.
              ** inherit HR.
              ** inherit HD.
              ** inherit (CE1 HX).
              ** eapply CE1, Ctx. now left.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HD, HZ, HW.
      apply (binary_substitution_comparison G AddGraph238.AddGraph238.add_result u v sigma rho tau z w).
      * exact source_add_result_subst.
      * exact term_basis_addition_compare.
      * exact (IH u ltac:(constructor)).
      * exact (IH v ltac:(constructor 2; constructor)).
      * exact HB.
      * exact HR.
      * exact (CE1 HD).
      * exact (CE2 HD).
      * exact HZ.
      * exact HW.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HD, HZ, HW.
      apply (binary_substitution_comparison G MulGraph238.MulGraph238.mul_result u v sigma rho tau z w).
      * exact source_mul_result_subst.
      * exact term_basis_multiplication_compare.
      * exact (IH u ltac:(constructor)).
      * exact (IH v ltac:(constructor 2; constructor)).
      * exact HB.
      * exact HR.
      * exact (CE1 HD).
      * exact (CE2 HD).
      * exact HZ.
      * exact HW.
Qed.

Theorem S0_pa_term_substitution_comparison t sigma rho tau z w :
  derivable finite_set_S0
    (pa_substitution_values t sigma rho tau →
      (pa_term_value (t`[sigma]) rho z → (pa_term_value t tau w → order_iso z w))).
Proof.
  destruct S0_term_coherence_basis as [Gc [HGc HC]].
  destruct S0_iso_reflexivity_ax as [Gr [HGr HR]]. set (G := Gc ++ Gr).
  assert (HC' : G ⊢238 term_coherence_basis).
  { eapply Weak; [exact HC|]. intros psi Hpsi. unfold G. apply in_or_app. now left. }
  assert (HR' : G ⊢238 iso_reflexivity_ax).
  { eapply Weak; [exact HR|]. intros psi Hpsi. unfold G. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGc|now apply HGr].
  - apply II, II, II. apply (pa_term_value_pa_substitution t _ sigma rho tau z w).
    + inherit HC'.
    + inherit HR'.
    + apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Print Assumptions binary_substitution_comparison.
Print Assumptions pa_term_value_pa_substitution.
Print Assumptions S0_pa_term_substitution_comparison.
End PAForwardSubstitution238.
