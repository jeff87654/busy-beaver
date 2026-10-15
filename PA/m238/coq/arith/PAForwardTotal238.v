(** Original finite derivations of every ordinary PA term's source value.
    The domain guard is a finite formula over exactly the term's variable
    occurrences. All operation witnesses come from the derived S0 basis. *)
From Coq Require Import List Vector.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238
  PAForwardTerms238 PAForwardBasis238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  PAForwardTerms238.PAForwardTerms238 PAForwardBasis238.PAForwardBasis238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardTotal238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition domain_relation := (nat -> set_term) -> set_form.
Definition function_domains (f : PA_funcs) :
  Vector.t domain_relation (PA_funcs_ar f) -> domain_relation :=
  match f as f' return Vector.t domain_relation (PA_funcs_ar f') -> domain_relation with
  | Zero => fun _ _ => (falsity → falsity)
  | Succ => fun args => Vector.hd args
  | Plus => fun args rho => Vector.hd args rho ∧ Vector.hd (Vector.tl args) rho
  | Mult => fun args rho => Vector.hd args rho ∧ Vector.hd (Vector.tl args) rho
  end.
Fixpoint pa_term_domains (t : PA238.pa_term) : domain_relation :=
  match t with
  | var n => fun rho => ordinal_representative (rho n)
  | func f args => function_domains f (Vector.map pa_term_domains args)
  end.

Theorem pa_term_value_total G t rho :
  G ⊢238 term_totality_basis -> G ⊢238 pa_term_domains t rho ->
  G ⊢238 ∃ pa_term_value t (shifted_environment rho) $0.
Proof.
  revert G rho. induction t as [n|f args IH] using term_ind.
  - intros G rho HB HD. apply (ExI (rho n)).
    rewrite pa_term_value_witness_specialize.
    apply variable_value_intro; [exact (CE1 HB)|exact HD].
  - intros G rho HB HD. destruct f.
    + exact (term_basis_zero G HB).
    + remember (Vector.hd args) as u eqn:Hu.
      assert (V : args = Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term)).
      { rewrite Hu. apply destruct_vector_single. }
      rewrite V in IH, HD |- *. eapply ExE_named.
      * apply (IH u ltac:(constructor) G rho); [exact HB|exact HD].
      * intro x. rewrite pa_term_value_witness_specialize.
        assert (HX : (pa_term_value u rho x :: G) ⊢238 pa_term_value u rho x).
        { apply Ctx. now left. }
        eapply ExE_named.
        -- apply (term_basis_successor _ x); [inherit HB|].
           apply (pa_term_value_ordinal _ u rho x). exact HX.
        -- intro z. destruct x as [ix|[]], z as [iz|[]].
           cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
           apply (ExI $iz). rewrite pa_term_value_witness_specialize.
           apply (successor_value_intro _ u rho $ix $iz).
           ++ eapply CE1, Ctx. now left.
           ++ inherit HX.
           ++ eapply CE2, Ctx. now left.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HD |- *. eapply ExE_named.
      * apply (IH u ltac:(constructor) G rho); [exact HB|exact (CE1 HD)].
      * intro x. rewrite pa_term_value_witness_specialize.
        assert (HX : (pa_term_value u rho x :: G) ⊢238 pa_term_value u rho x).
        { apply Ctx. now left. }
        eapply ExE_named.
        -- apply (IH v ltac:(constructor 2; constructor) _ rho);
             [inherit HB|inherit (CE2 HD)].
        -- intro y. rewrite pa_term_value_witness_specialize.
           assert (HY : (pa_term_value v rho y :: pa_term_value u rho x :: G)
             ⊢238 pa_term_value v rho y).
           { apply Ctx. now left. }
           eapply ExE_named.
           ++ apply (term_basis_addition _ x y).
              ** inherit HB.
              ** apply (pa_term_value_ordinal _ u rho x). inherit HX.
              ** apply (pa_term_value_ordinal _ v rho y). exact HY.
           ++ intro z. destruct x as [ix|[]], y as [iy|[]], z as [iz|[]].
              cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
              apply (ExI $iz). rewrite pa_term_value_witness_specialize.
              apply (addition_value_intro _ u v rho $ix $iy $iz).
              ** inherit HX.
              ** inherit HY.
              ** apply Ctx. now left.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HD |- *. eapply ExE_named.
      * apply (IH u ltac:(constructor) G rho); [exact HB|exact (CE1 HD)].
      * intro x. rewrite pa_term_value_witness_specialize.
        assert (HX : (pa_term_value u rho x :: G) ⊢238 pa_term_value u rho x).
        { apply Ctx. now left. }
        eapply ExE_named.
        -- apply (IH v ltac:(constructor 2; constructor) _ rho);
             [inherit HB|inherit (CE2 HD)].
        -- intro y. rewrite pa_term_value_witness_specialize.
           assert (HY : (pa_term_value v rho y :: pa_term_value u rho x :: G)
             ⊢238 pa_term_value v rho y).
           { apply Ctx. now left. }
           eapply ExE_named.
           ++ apply (term_basis_multiplication _ x y).
              ** inherit HB.
              ** apply (pa_term_value_ordinal _ u rho x). inherit HX.
              ** apply (pa_term_value_ordinal _ v rho y). exact HY.
           ++ intro z. destruct x as [ix|[]], y as [iy|[]], z as [iz|[]].
              cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp].
              apply (ExI $iz). rewrite pa_term_value_witness_specialize.
              apply (multiplication_value_intro _ u v rho $ix $iy $iz).
              ** inherit HX.
              ** inherit HY.
              ** apply Ctx. now left.
Qed.

Theorem S0_pa_term_total t rho :
  derivable finite_set_S0
    (pa_term_domains t rho → ∃ pa_term_value t (shifted_environment rho) $0).
Proof.
  destruct S0_term_totality_basis as [G [HG HB]]. exists G. split; [exact HG|].
  apply II, (pa_term_value_total _ t rho).
  - apply weaken_one. exact HB.
  - apply Ctx. now left.
Qed.

Print Assumptions pa_term_value_total.
Print Assumptions S0_pa_term_total.
End PAForwardTotal238.
