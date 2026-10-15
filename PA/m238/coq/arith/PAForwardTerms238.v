(** Original source-value relations for the pinned ordinary PA terms.
    Function symbols are eliminated into actual source graph predicates.
    Every value carries an ordinal-domain guard. No ambient structure,
    chosen representative, or semantic consistency premise is used. *)
From Coq Require Import List Vector.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 OrdinalSuccessor238
  PairGraph238 TraceGraph238 AddGraph238 MulGraph238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  OrdinalSuccessor238.OrdinalSuccessor238 PairGraph238.PairGraph238
  TraceGraph238.TraceGraph238 AddGraph238.AddGraph238 MulGraph238.MulGraph238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardTerms238.

Definition value_relation := (nat -> set_term) -> set_term -> set_form.
Definition shifted_environment (rho : nat -> set_term) : nat -> set_term :=
  fun k => (rho k)`[↑].
Definition twice_shifted_environment (rho : nat -> set_term) : nat -> set_term :=
  shifted_environment (shifted_environment rho).

Definition variable_value (n : nat) : value_relation :=
  fun rho z => ordinal_representative z ∧ E z (rho n).
Definition zero_value : value_relation :=
  fun rho z => ordinal_representative z ∧ raw_zero z.
Definition successor_value (child : value_relation) : value_relation :=
  fun rho z => ordinal_representative z ∧
    ∃ (child (shifted_environment rho) $0 ∧ raw_successor $0 z`[↑]).
Definition binary_value (op : set_term -> set_term -> set_term -> set_form)
  (left right : value_relation) : value_relation :=
  fun rho z => ordinal_representative z ∧
    ∃ ∃ (left (twice_shifted_environment rho) $1 ∧
      (right (twice_shifted_environment rho) $0 ∧ op $1 $0 z`[↑]`[↑])).

Definition function_value (f : PA_funcs) :
  Vector.t value_relation (PA_funcs_ar f) -> value_relation :=
  match f as f' return Vector.t value_relation (PA_funcs_ar f') -> value_relation with
  | Zero => fun _ => zero_value
  | Succ => fun args => successor_value (Vector.hd args)
  | Plus => fun args => binary_value add_result (Vector.hd args) (Vector.hd (Vector.tl args))
  | Mult => fun args => binary_value mul_result (Vector.hd args) (Vector.hd (Vector.tl args))
  end.

(** This recursion is directly on the upstream PA term syntax. Its vector
    map follows the same nested-term recursion as upstream substitution. *)
Fixpoint pa_term_value (t : PA238.pa_term) : value_relation :=
  match t with
  | var n => variable_value n
  | func f args => function_value f (Vector.map pa_term_value args)
  end.

Definition pa_variable n : PA238.pa_term := @var PA_funcs_signature n.
Definition pa_zero : PA238.pa_term :=
  @func PA_funcs_signature Zero (Vector.nil PA238.pa_term).
Definition pa_successor (t : PA238.pa_term) : PA238.pa_term :=
  @func PA_funcs_signature Succ
    (Vector.cons PA238.pa_term t 0 (Vector.nil PA238.pa_term)).
Definition pa_addition (s t : PA238.pa_term) : PA238.pa_term :=
  @func PA_funcs_signature Plus
    (Vector.cons PA238.pa_term s 1
      (Vector.cons PA238.pa_term t 0 (Vector.nil PA238.pa_term))).
Definition pa_multiplication (s t : PA238.pa_term) : PA238.pa_term :=
  @func PA_funcs_signature Mult
    (Vector.cons PA238.pa_term s 1
      (Vector.cons PA238.pa_term t 0 (Vector.nil PA238.pa_term))).

Lemma pa_variable_value n rho z :
  pa_term_value (pa_variable n) rho z = variable_value n rho z.
Proof. reflexivity. Qed.
Lemma pa_zero_value rho z : pa_term_value pa_zero rho z = zero_value rho z.
Proof. reflexivity. Qed.
Lemma pa_successor_value t rho z :
  pa_term_value (pa_successor t) rho z = successor_value (pa_term_value t) rho z.
Proof. reflexivity. Qed.
Lemma pa_addition_value s t rho z :
  pa_term_value (pa_addition s t) rho z =
    binary_value add_result (pa_term_value s) (pa_term_value t) rho z.
Proof. reflexivity. Qed.
Lemma pa_multiplication_value s t rho z :
  pa_term_value (pa_multiplication s t) rho z =
    binary_value mul_result (pa_term_value s) (pa_term_value t) rho z.
Proof. reflexivity. Qed.

Lemma pa_term_value_ordinal G t rho z :
  G ⊢238 pa_term_value t rho z -> G ⊢238 ordinal_representative z.
Proof.
  destruct t as [n|f args].
  - intro H. exact (CE1 H).
  - destruct f; intro H; exact (CE1 H).
Qed.

Lemma variable_value_intro G rho n :
  G ⊢238 (∀ E $0 $0) -> G ⊢238 ordinal_representative (rho n) ->
  G ⊢238 pa_term_value (pa_variable n) rho (rho n).
Proof. intros HE HR. apply CI; [exact HR|exact (AllE (rho n) HE)]. Qed.

Lemma variable_value_witness_specialize rho n z :
  (variable_value n (shifted_environment rho) $0)[z..] = variable_value n rho z.
Proof.
  unfold variable_value, shifted_environment, ordinal_representative, representative,
    member_ir, transitive, member_transitive, member_linear, internal_extrema,
    subset, nonempty, least, greatest, R, E.
  destruct z as [iz|[]], (rho n) as [ir|[]].
  cbn [terms2 Vector.map subst_form subst_term up scons funcomp]. reflexivity.
Qed.

Theorem S0_pa_variable_total rho n :
  derivable finite_set_S0
    (ordinal_representative (rho n) →
      ∃ pa_term_value (pa_variable n) (shifted_environment rho) $0).
Proof.
  exists [∀ E $0 $0]. split.
  - intros psi [<-|[]]. apply S0_base. apply in_or_app. left. now left.
  - apply II, (ExI (rho n)).
    change ((ordinal_representative (rho n) :: [∀ E $0 $0]) ⊢238
      (variable_value n (shifted_environment rho) $0)[(rho n)..]).
    rewrite variable_value_witness_specialize. apply variable_value_intro.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Theorem S0_pa_zero_total rho :
  derivable finite_set_S0
    (∃ pa_term_value pa_zero (shifted_environment rho) $0).
Proof.
  destruct S0_empty as [G [HG HE]]. exists G. split; [exact HG|].
  eapply ExE_named; [exact HE|]. intro e. destruct e as [ie|[]].
  apply (ExI $ie).
  cbn [pa_term_value pa_zero function_value zero_value R E terms2 Vector.map
    subst_form subst_term up scons funcomp]. apply CI.
  - apply empty_ordinal_representative, Ctx. now left.
  - apply Ctx. now left.
Qed.

Lemma pa_vector2_eta (args : Vector.t PA238.pa_term 2) :
  args = Vector.cons PA238.pa_term (Vector.hd args) 1
    (Vector.cons PA238.pa_term (Vector.hd (Vector.tl args)) 0 (Vector.nil PA238.pa_term)).
Proof.
  rewrite (Vector.eta args) at 1. f_equal. apply destruct_vector_single.
Qed.

(** Pointwise environment equality suffices; no functional extensionality
    principle is used to identify the environments themselves. *)
Lemma pa_term_value_environment_ext t rho tau z :
  (forall n, rho n = tau n) -> pa_term_value t rho z = pa_term_value t tau z.
Proof.
  revert rho tau z. induction t as [n|f args IH] using term_ind.
  - intros rho tau z H.
    change ((ordinal_representative z ∧ E z (rho n)) =
      (ordinal_representative z ∧ E z (tau n))). now rewrite (H n).
  - intros rho tau z H. destruct f.
    + reflexivity.
    + remember (Vector.hd args) as u eqn:Hu.
      assert (V : args = Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term)).
      { rewrite Hu. apply destruct_vector_single. }
      rewrite V in IH |- *.
      change ((ordinal_representative z ∧
        ∃ (pa_term_value u (shifted_environment rho) $0 ∧ raw_successor $0 z`[↑])) =
        (ordinal_representative z ∧
          ∃ (pa_term_value u (shifted_environment tau) $0 ∧ raw_successor $0 z`[↑]))).
      assert (Hs : forall k, shifted_environment rho k = shifted_environment tau k).
      { intro k. unfold shifted_environment. now rewrite H. }
      rewrite (IH u ltac:(constructor) (shifted_environment rho)
        (shifted_environment tau) $0 Hs). reflexivity.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH |- *.
      change ((ordinal_representative z ∧
        ∃ ∃ (pa_term_value u (twice_shifted_environment rho) $1 ∧
          (pa_term_value v (twice_shifted_environment rho) $0 ∧ add_result $1 $0 z`[↑]`[↑]))) =
        (ordinal_representative z ∧
          ∃ ∃ (pa_term_value u (twice_shifted_environment tau) $1 ∧
            (pa_term_value v (twice_shifted_environment tau) $0 ∧ add_result $1 $0 z`[↑]`[↑])))).
      assert (Hs : forall k, twice_shifted_environment rho k = twice_shifted_environment tau k).
      { intro k. unfold twice_shifted_environment, shifted_environment. now rewrite H. }
      rewrite (IH u ltac:(constructor) (twice_shifted_environment rho)
        (twice_shifted_environment tau) $1 Hs).
      rewrite (IH v ltac:(constructor 2; constructor) (twice_shifted_environment rho)
        (twice_shifted_environment tau) $0 Hs). reflexivity.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH |- *.
      change ((ordinal_representative z ∧
        ∃ ∃ (pa_term_value u (twice_shifted_environment rho) $1 ∧
          (pa_term_value v (twice_shifted_environment rho) $0 ∧ mul_result $1 $0 z`[↑]`[↑]))) =
        (ordinal_representative z ∧
          ∃ ∃ (pa_term_value u (twice_shifted_environment tau) $1 ∧
            (pa_term_value v (twice_shifted_environment tau) $0 ∧ mul_result $1 $0 z`[↑]`[↑])))).
      assert (Hs : forall k, twice_shifted_environment rho k = twice_shifted_environment tau k).
      { intro k. unfold twice_shifted_environment, shifted_environment. now rewrite H. }
      rewrite (IH u ltac:(constructor) (twice_shifted_environment rho)
        (twice_shifted_environment tau) $1 Hs).
      rewrite (IH v ltac:(constructor 2; constructor) (twice_shifted_environment rho)
        (twice_shifted_environment tau) $0 Hs). reflexivity.
Qed.

Lemma ordinal_value_subst z sigma :
  (ordinal_representative z)[sigma] = ordinal_representative z`[sigma].
Proof.
  unfold ordinal_representative, representative, member_ir, transitive,
    member_transitive, member_linear, internal_extrema, subset, nonempty,
    least, greatest, R, E. cbn. repeat rewrite up_term. reflexivity.
Qed.
Lemma source_equality_subst x y sigma : (E x y)[sigma] = E x`[sigma] y`[sigma].
Proof. unfold E, terms2. reflexivity. Qed.
Lemma source_zero_subst z sigma : (raw_zero z)[sigma] = raw_zero z`[sigma].
Proof. unfold raw_zero, R. cbn. now rewrite up_term. Qed.
Lemma source_add_result_subst x y z sigma :
  (add_result x y z)[sigma] = add_result x`[sigma] y`[sigma] z`[sigma].
Proof.
  unfold add_result. cbn [subst_form]. rewrite add_prefix_subst.
  unfold raw_zero, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.
Lemma source_mul_result_subst x y z sigma :
  (mul_result x y z)[sigma] = mul_result x`[sigma] y`[sigma] z`[sigma].
Proof.
  unfold mul_result. cbn [subst_form]. rewrite mul_prefix_subst.
  unfold raw_zero, graph_edge, raw_kuratowski, raw_pair, raw_singleton, R, E.
  cbn. repeat rewrite up_term. reflexivity.
Qed.

Lemma pa_term_value_source_subst t rho z sigma :
  (pa_term_value t rho z)[sigma] =
    pa_term_value t (fun k => (rho k)`[sigma]) z`[sigma].
Proof.
  revert rho z sigma. induction t as [n|f args IH] using term_ind.
  - intros rho z sigma.
    change (((ordinal_representative z)[sigma] ∧ (E z (rho n))[sigma]) =
      (ordinal_representative z`[sigma] ∧ E z`[sigma] (rho n)`[sigma])).
    rewrite ordinal_value_subst, source_equality_subst. reflexivity.
  - intros rho z sigma. destruct f.
    + change (((ordinal_representative z)[sigma] ∧ (raw_zero z)[sigma]) =
        (ordinal_representative z`[sigma] ∧ raw_zero z`[sigma])).
      rewrite ordinal_value_subst, source_zero_subst. reflexivity.
    + remember (Vector.hd args) as u eqn:Hu.
      assert (V : args = Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term)).
      { rewrite Hu. apply destruct_vector_single. }
      rewrite V in IH |- *.
      change (((ordinal_representative z)[sigma] ∧
        ∃ ((pa_term_value u (shifted_environment rho) $0)[up sigma] ∧
          (raw_successor $0 z`[↑])[up sigma])) =
        (ordinal_representative z`[sigma] ∧
          ∃ (pa_term_value u (shifted_environment (fun k => (rho k)`[sigma])) $0 ∧
            raw_successor $0 z`[sigma]`[↑]))).
      rewrite ordinal_value_subst, (IH u ltac:(constructor)), raw_successor_subst.
      rewrite up_term. cbn [subst_term up scons funcomp].
      rewrite (pa_term_value_environment_ext u
        (fun k => (shifted_environment rho k)`[up sigma])
        (shifted_environment (fun k => (rho k)`[sigma])) $0
        ltac:(intro k; unfold shifted_environment; apply up_term)). reflexivity.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH |- *.
      change (((ordinal_representative z)[sigma] ∧
        ∃ ∃ ((pa_term_value u (twice_shifted_environment rho) $1)[up (up sigma)] ∧
          ((pa_term_value v (twice_shifted_environment rho) $0)[up (up sigma)] ∧
            (add_result $1 $0 z`[↑]`[↑])[up (up sigma)]))) =
        (ordinal_representative z`[sigma] ∧
          ∃ ∃ (pa_term_value u (twice_shifted_environment (fun k => (rho k)`[sigma])) $1 ∧
            (pa_term_value v (twice_shifted_environment (fun k => (rho k)`[sigma])) $0 ∧
              add_result $1 $0 z`[sigma]`[↑]`[↑])))).
      rewrite ordinal_value_subst, (IH u ltac:(constructor)),
        (IH v ltac:(constructor 2; constructor)), source_add_result_subst.
      rewrite (@up_term sig_empty z`[↑] (up sigma)), (@up_term sig_empty z sigma).
      change ((ordinal_representative z`[sigma] ∧
        ∃ ∃ (pa_term_value u
          (fun k => (twice_shifted_environment rho k)`[up (up sigma)]) $1 ∧
            (pa_term_value v (fun k => (twice_shifted_environment rho k)`[up (up sigma)]) $0 ∧
              add_result $1 $0 z`[sigma]`[↑]`[↑]))) =
        (ordinal_representative z`[sigma] ∧
          ∃ ∃ (pa_term_value u (twice_shifted_environment (fun k => (rho k)`[sigma])) $1 ∧
            (pa_term_value v (twice_shifted_environment (fun k => (rho k)`[sigma])) $0 ∧
              add_result $1 $0 z`[sigma]`[↑]`[↑])))).
      assert (Henv : forall k, (twice_shifted_environment rho k)`[up (up sigma)] =
        twice_shifted_environment (fun k => (rho k)`[sigma]) k).
      { intro k. unfold twice_shifted_environment, shifted_environment.
        now rewrite !up_term. }
      rewrite (pa_term_value_environment_ext u _ _ $1 Henv),
        (pa_term_value_environment_ext v _ _ $0 Henv). reflexivity.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH |- *.
      change (((ordinal_representative z)[sigma] ∧
        ∃ ∃ ((pa_term_value u (twice_shifted_environment rho) $1)[up (up sigma)] ∧
          ((pa_term_value v (twice_shifted_environment rho) $0)[up (up sigma)] ∧
            (mul_result $1 $0 z`[↑]`[↑])[up (up sigma)]))) =
        (ordinal_representative z`[sigma] ∧
          ∃ ∃ (pa_term_value u (twice_shifted_environment (fun k => (rho k)`[sigma])) $1 ∧
            (pa_term_value v (twice_shifted_environment (fun k => (rho k)`[sigma])) $0 ∧
              mul_result $1 $0 z`[sigma]`[↑]`[↑])))).
      rewrite ordinal_value_subst, (IH u ltac:(constructor)),
        (IH v ltac:(constructor 2; constructor)), source_mul_result_subst.
      rewrite (@up_term sig_empty z`[↑] (up sigma)), (@up_term sig_empty z sigma).
      change ((ordinal_representative z`[sigma] ∧
        ∃ ∃ (pa_term_value u
          (fun k => (twice_shifted_environment rho k)`[up (up sigma)]) $1 ∧
            (pa_term_value v (fun k => (twice_shifted_environment rho k)`[up (up sigma)]) $0 ∧
              mul_result $1 $0 z`[sigma]`[↑]`[↑]))) =
        (ordinal_representative z`[sigma] ∧
          ∃ ∃ (pa_term_value u (twice_shifted_environment (fun k => (rho k)`[sigma])) $1 ∧
            (pa_term_value v (twice_shifted_environment (fun k => (rho k)`[sigma])) $0 ∧
              mul_result $1 $0 z`[sigma]`[↑]`[↑])))).
      assert (Henv : forall k, (twice_shifted_environment rho k)`[up (up sigma)] =
        twice_shifted_environment (fun k => (rho k)`[sigma]) k).
      { intro k. unfold twice_shifted_environment, shifted_environment.
        now rewrite !up_term. }
      rewrite (pa_term_value_environment_ext u _ _ $1 Henv),
        (pa_term_value_environment_ext v _ _ $0 Henv). reflexivity.
Qed.

Lemma source_shift_witness_cancel t x : t`[↑]`[x..] = t.
Proof. destruct t as [it|[]]. reflexivity. Qed.
Lemma source_twice_shift_witness_cancel t x y :
  t`[↑]`[↑]`[y .: x .: var] = t.
Proof. destruct t as [it|[]]. reflexivity. Qed.

Lemma pa_term_value_witness_specialize t rho z :
  (pa_term_value t (shifted_environment rho) $0)[z..] = pa_term_value t rho z.
Proof.
  rewrite pa_term_value_source_subst.
  change (pa_term_value t (fun k => (shifted_environment rho k)`[z..]) z =
    pa_term_value t rho z).
  apply pa_term_value_environment_ext. intro k. unfold shifted_environment.
  apply source_shift_witness_cancel.
Qed.

Lemma source_two_witness_subst (phi : set_form) (x y : set_term) :
  (phi[up (x.. )])[y..] = phi[y .: x .: var].
Proof.
  rewrite subst_comp. apply subst_ext. intros [|[|k]].
  - reflexivity.
  - change (x`[↑]`[y..] = x). apply source_shift_witness_cancel.
  - reflexivity.
Qed.

Lemma successor_value_intro G t rho x z :
  G ⊢238 ordinal_representative z -> G ⊢238 pa_term_value t rho x ->
  G ⊢238 raw_successor x z -> G ⊢238 pa_term_value (pa_successor t) rho z.
Proof.
  intros HZ HT HS. rewrite pa_successor_value. unfold successor_value.
  apply CI; [exact HZ|]. apply (ExI x).
  change (G ⊢238 ((pa_term_value t (shifted_environment rho) $0)[x..] ∧
    (raw_successor $0 z`[↑])[x..])).
  rewrite pa_term_value_witness_specialize, raw_successor_subst.
  change (G ⊢238 (pa_term_value t rho x ∧ raw_successor x z`[↑]`[x..])).
  rewrite source_shift_witness_cancel. apply CI; assumption.
Qed.

Lemma binary_value_intro G op s t rho x y z :
  (forall a b c sigma, (op a b c)[sigma] = op a`[sigma] b`[sigma] c`[sigma]) ->
  G ⊢238 ordinal_representative z -> G ⊢238 pa_term_value s rho x ->
  G ⊢238 pa_term_value t rho y -> G ⊢238 op x y z ->
  G ⊢238 binary_value op (pa_term_value s) (pa_term_value t) rho z.
Proof.
  intros Hop HZ HS HT HO. unfold binary_value. apply CI; [exact HZ|].
  apply (ExI x).
  change (G ⊢238 ∃ ((pa_term_value s (twice_shifted_environment rho) $1 ∧
    (pa_term_value t (twice_shifted_environment rho) $0 ∧ op $1 $0 z`[↑]`[↑]))[up (x..)])).
  apply (ExI y). rewrite source_two_witness_subst.
  change (G ⊢238 ((pa_term_value s (twice_shifted_environment rho) $1)[y .: x .: var] ∧
    ((pa_term_value t (twice_shifted_environment rho) $0)[y .: x .: var] ∧
      (op $1 $0 z`[↑]`[↑])[y .: x .: var]))).
  rewrite !pa_term_value_source_subst, Hop.
  change (G ⊢238 (pa_term_value s
    (fun k => (twice_shifted_environment rho k)`[y .: x .: var]) x ∧
      (pa_term_value t (fun k => (twice_shifted_environment rho k)`[y .: x .: var]) y ∧
        op x y z`[↑]`[↑]`[y .: x .: var]))).
  assert (Henv : forall k, (twice_shifted_environment rho k)`[y .: x .: var] = rho k).
  { intro k. unfold twice_shifted_environment, shifted_environment.
    apply source_twice_shift_witness_cancel. }
  rewrite (pa_term_value_environment_ext s _ rho x Henv),
    (pa_term_value_environment_ext t _ rho y Henv), source_twice_shift_witness_cancel.
  apply CI; [exact HS|]. apply CI; assumption.
Qed.

Lemma addition_value_intro G s t rho x y z :
  G ⊢238 pa_term_value s rho x -> G ⊢238 pa_term_value t rho y ->
  G ⊢238 add_result x y z -> G ⊢238 pa_term_value (pa_addition s t) rho z.
Proof.
  intros HS HT HA. rewrite pa_addition_value. apply (binary_value_intro _ add_result s t rho x y z).
  - exact source_add_result_subst.
  - apply (add_result_ordinal _ x y z). exact HA.
  - exact HS.
  - exact HT.
  - exact HA.
Qed.

Lemma multiplication_value_intro G s t rho x y z :
  G ⊢238 pa_term_value s rho x -> G ⊢238 pa_term_value t rho y ->
  G ⊢238 mul_result x y z -> G ⊢238 pa_term_value (pa_multiplication s t) rho z.
Proof.
  intros HS HT HM. rewrite pa_multiplication_value. apply (binary_value_intro _ mul_result s t rho x y z).
  - exact source_mul_result_subst.
  - apply (mul_result_ordinal _ x y z). exact HM.
  - exact HS.
  - exact HT.
  - exact HM.
Qed.

Print Assumptions pa_term_value_witness_specialize.
Print Assumptions source_two_witness_subst.
Print Assumptions successor_value_intro.
Print Assumptions binary_value_intro.
Print Assumptions addition_value_intro.
Print Assumptions multiplication_value_intro.
Print Assumptions ordinal_value_subst.
Print Assumptions source_add_result_subst.
Print Assumptions source_mul_result_subst.
Print Assumptions pa_term_value_source_subst.
Print Assumptions pa_term_value_environment_ext.
Print Assumptions pa_term_value_ordinal.
Print Assumptions variable_value_intro.
Print Assumptions variable_value_witness_specialize.
Print Assumptions S0_pa_variable_total.
Print Assumptions S0_pa_zero_total.
End PAForwardTerms238.
