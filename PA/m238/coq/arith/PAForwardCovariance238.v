(** Original joint comparison for every pinned ordinary PA term.
    Every operator comparison uses the actually derived finite S0 basis;
    all independently selected input and output witnesses are retained. *)
From Coq Require Import List Vector.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 IsoGraph238
  IsoEquality238 PAForwardTerms238 PAForwardValueCases238 PAForwardCoherenceBasis238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 IsoGraph238.IsoGraph238
  IsoEquality238.IsoEquality238 PAForwardTerms238.PAForwardTerms238
  PAForwardValueCases238.PAForwardValueCases238
  PAForwardCoherenceBasis238.PAForwardCoherenceBasis238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardCovariance238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition comparison_relation := (nat -> set_term) -> (nat -> set_term) -> set_form.
Definition function_comparisons (f : PA_funcs) :
  Vector.t comparison_relation (PA_funcs_ar f) -> comparison_relation :=
  match f as f' return Vector.t comparison_relation (PA_funcs_ar f') -> comparison_relation with
  | Zero => fun _ _ _ => (falsity → falsity)
  | Succ => fun args => Vector.hd args
  | Plus => fun args rho tau => Vector.hd args rho tau ∧ Vector.hd (Vector.tl args) rho tau
  | Mult => fun args rho tau => Vector.hd args rho tau ∧ Vector.hd (Vector.tl args) rho tau
  end.
Fixpoint pa_term_comparisons (t : PA238.pa_term) : comparison_relation :=
  match t with
  | var n => fun rho tau => order_iso (rho n) (tau n)
  | func f args => function_comparisons f (Vector.map pa_term_comparisons args)
  end.
Definition term_comparison_rule (t : PA238.pa_term) : Prop :=
  forall G rho tau z w,
    G ⊢238 term_coherence_basis -> G ⊢238 pa_term_comparisons t rho tau ->
    G ⊢238 pa_term_value t rho z -> G ⊢238 pa_term_value t tau w -> G ⊢238 order_iso z w.

Lemma successor_values_comparison G t rho tau z w :
  term_comparison_rule t -> G ⊢238 term_coherence_basis ->
  G ⊢238 pa_term_comparisons t rho tau ->
  G ⊢238 pa_term_value (pa_successor t) rho z ->
  G ⊢238 pa_term_value (pa_successor t) tau w -> G ⊢238 order_iso z w.
Proof.
  intros HC HB HD HZ HW. eapply ExE_named.
  - apply (successor_value_inputs G t rho z). exact HZ.
  - intro x. rewrite successor_value_body_specialize.
    assert (HX : (pa_term_value t rho x ∧ raw_successor x z :: G)
      ⊢238 (pa_term_value t rho x ∧ raw_successor x z)).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (successor_value_inputs _ t tau w). inherit HW.
    + intro y. rewrite successor_value_body_specialize.
      apply (term_basis_successor_compare _ x z y w).
      * inherit HB.
      * apply (pa_term_value_ordinal _ t rho x). inherit (CE1 HX).
      * apply (pa_term_value_ordinal _ t tau y). eapply CE1, Ctx. now left.
      * inherit (CE2 HX).
      * eapply CE2, Ctx. now left.
      * apply (HC _ rho tau x y).
        -- inherit HB.
        -- inherit HD.
        -- inherit (CE1 HX).
        -- eapply CE1, Ctx. now left.
Qed.

Lemma binary_values_comparison G op s t rho tau z w :
  (forall a b c sigma, (op a b c)[sigma] = op a`[sigma] b`[sigma] c`[sigma]) ->
  (forall D a a' b b' c c',
    D ⊢238 term_coherence_basis -> D ⊢238 ordinal_representative a ->
    D ⊢238 ordinal_representative a' -> D ⊢238 ordinal_representative b ->
    D ⊢238 ordinal_representative b' -> D ⊢238 order_iso a a' -> D ⊢238 order_iso b b' ->
    D ⊢238 op a b c -> D ⊢238 op a' b' c' -> D ⊢238 order_iso c c') ->
  term_comparison_rule s -> term_comparison_rule t ->
  G ⊢238 term_coherence_basis -> G ⊢238 pa_term_comparisons s rho tau ->
  G ⊢238 pa_term_comparisons t rho tau ->
  G ⊢238 binary_value op (pa_term_value s) (pa_term_value t) rho z ->
  G ⊢238 binary_value op (pa_term_value s) (pa_term_value t) tau w ->
  G ⊢238 order_iso z w.
Proof.
  intros Hop Hcompare HS HT HB HD HE HZ HW. eapply ExE_named.
  - apply (binary_value_inputs G op s t rho z). exact HZ.
  - intro x. change ((∃ (binary_value_body op s t rho z)[up (x..)] :: G) ⊢238 order_iso z w).
    eapply ExE_named; [apply Ctx; now left|]. intro y.
    rewrite (binary_value_body_specialize op s t rho z x y Hop).
    assert (HL : (pa_term_value s rho x ∧ (pa_term_value t rho y ∧ op x y z) ::
      (∃ (binary_value_body op s t rho z)[up (x..)]) :: G)
        ⊢238 (pa_term_value s rho x ∧ (pa_term_value t rho y ∧ op x y z))).
    { apply Ctx. now left. }
    eapply ExE_named.
    + apply (binary_value_inputs _ op s t tau w). inherit HW.
    + intro x'. change ((∃ (binary_value_body op s t tau w)[up (x'..)] ::
        pa_term_value s rho x ∧ (pa_term_value t rho y ∧ op x y z) ::
        (∃ (binary_value_body op s t rho z)[up (x..)]) :: G) ⊢238 order_iso z w).
      eapply ExE_named; [apply Ctx; now left|]. intro y'.
      rewrite (binary_value_body_specialize op s t tau w x' y' Hop).
      assert (HR : (pa_term_value s tau x' ∧ (pa_term_value t tau y' ∧ op x' y' w) ::
        (∃ (binary_value_body op s t tau w)[up (x'..)]) ::
        pa_term_value s rho x ∧ (pa_term_value t rho y ∧ op x y z) ::
        (∃ (binary_value_body op s t rho z)[up (x..)]) :: G)
          ⊢238 (pa_term_value s tau x' ∧ (pa_term_value t tau y' ∧ op x' y' w))).
      { apply Ctx. now left. }
      apply (Hcompare _ x x' y y' z w).
      * inherit HB.
      * apply (pa_term_value_ordinal _ s rho x). inherit (CE1 HL).
      * apply (pa_term_value_ordinal _ s tau x'). exact (CE1 HR).
      * apply (pa_term_value_ordinal _ t rho y). inherit (CE1 (CE2 HL)).
      * apply (pa_term_value_ordinal _ t tau y'). exact (CE1 (CE2 HR)).
      * apply (HS _ rho tau x x');
          [inherit HB|inherit HD|inherit (CE1 HL)|exact (CE1 HR)].
      * apply (HT _ rho tau y y');
          [inherit HB|inherit HE|inherit (CE1 (CE2 HL))|exact (CE1 (CE2 HR))].
      * inherit (CE2 (CE2 HL)).
      * exact (CE2 (CE2 HR)).
Qed.

Theorem pa_term_value_comparison t : term_comparison_rule t.
Proof.
  induction t as [n|f args IH] using term_ind.
  - intros G rho tau z w HB HD HZ HW.
    apply (order_iso_coordinate_transport G (rho n) (tau n) z w).
    + exact (CE1 HB).
    + exact (CE1 (CE2 HB)).
    + exact (CE1 (CE2 (CE2 HB))).
    + apply equality_symmetry_instance; [exact (CE1 (CE2 (CE2 HB)))|exact (CE2 HZ)].
    + apply equality_symmetry_instance; [exact (CE1 (CE2 (CE2 HB)))|exact (CE2 HW)].
    + exact HD.
  - intros G rho tau z w HB HD HZ HW. destruct f.
    + apply (term_basis_zero_compare G z w); [exact HB|exact (CE2 HZ)|exact (CE2 HW)].
    + remember (Vector.hd args) as u eqn:Hu.
      assert (V : args = Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term)).
      { rewrite Hu. apply destruct_vector_single. }
      rewrite V in IH, HD, HZ, HW.
      apply (successor_values_comparison G u rho tau z w);
        [exact (IH u ltac:(constructor))|exact HB|exact HD|exact HZ|exact HW].
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HD, HZ, HW.
      apply (binary_values_comparison G AddGraph238.AddGraph238.add_result u v rho tau z w).
      * exact source_add_result_subst.
      * exact term_basis_addition_compare.
      * exact (IH u ltac:(constructor)).
      * exact (IH v ltac:(constructor 2; constructor)).
      * exact HB.
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
      apply (binary_values_comparison G MulGraph238.MulGraph238.mul_result u v rho tau z w).
      * exact source_mul_result_subst.
      * exact term_basis_multiplication_compare.
      * exact (IH u ltac:(constructor)).
      * exact (IH v ltac:(constructor 2; constructor)).
      * exact HB.
      * exact (CE1 HD).
      * exact (CE2 HD).
      * exact HZ.
      * exact HW.
Qed.

Theorem S0_pa_term_covariance t rho tau z w :
  derivable finite_set_S0
    (pa_term_comparisons t rho tau →
      (pa_term_value t rho z → (pa_term_value t tau w → order_iso z w))).
Proof.
  destruct S0_term_coherence_basis as [G [HG HB]]. exists G. split; [exact HG|].
  apply II, II, II. apply (pa_term_value_comparison t _ rho tau z w).
  - inherit HB.
  - apply Ctx. right. right. now left.
  - apply Ctx. right. now left.
  - apply Ctx. now left.
Qed.

Print Assumptions successor_values_comparison.
Print Assumptions binary_values_comparison.
Print Assumptions pa_term_value_comparison.
Print Assumptions S0_pa_term_covariance.
End PAForwardCovariance238.
