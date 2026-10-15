(** Original extraction of finite variable-domain guards from actual PA
    value witnesses. Raw equality transports the ordinal guard in the
    variable case; compound values retain every actual child witness. *)
From Coq Require Import List Vector.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 TraceGraph238
  PAForwardTerms238 PAForwardTotal238 PAForwardValueCases238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 TraceGraph238.TraceGraph238
  PAForwardTerms238.PAForwardTerms238 PAForwardTotal238.PAForwardTotal238
  PAForwardValueCases238.PAForwardValueCases238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardDomains238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition term_domain_rule (t : PA238.pa_term) : Prop :=
  forall G rho z,
    G ⊢238 (∀ E $0 $0) -> G ⊢238 equality_membership_ax ->
    G ⊢238 equality_symmetry_ax -> G ⊢238 pa_term_value t rho z ->
    G ⊢238 pa_term_domains t rho.

Lemma binary_value_domains G op s t rho z :
  (forall a b c sigma, (op a b c)[sigma] = op a`[sigma] b`[sigma] c`[sigma]) ->
  term_domain_rule s -> term_domain_rule t -> G ⊢238 (∀ E $0 $0) ->
  G ⊢238 equality_membership_ax -> G ⊢238 equality_symmetry_ax ->
  G ⊢238 binary_value op (pa_term_value s) (pa_term_value t) rho z ->
  G ⊢238 (pa_term_domains s rho ∧ pa_term_domains t rho).
Proof.
  intros Hop HS HT HE HQ HEq HV. eapply ExE_named.
  - apply (binary_value_inputs G op s t rho z). exact HV.
  - intro x. change ((∃ (binary_value_body op s t rho z)[up (x..)] :: G)
      ⊢238 (pa_term_domains s rho ∧ pa_term_domains t rho)).
    eapply ExE_named; [apply Ctx; now left|]. intro y.
    rewrite (binary_value_body_specialize op s t rho z x y Hop). apply CI.
    + apply (HS _ rho x); [inherit HE|inherit HQ|inherit HEq|].
      eapply CE1, Ctx. now left.
    + apply (HT _ rho y); [inherit HE|inherit HQ|inherit HEq|].
      eapply CE1, CE2, Ctx. now left.
Qed.

Theorem pa_term_value_domains t : term_domain_rule t.
Proof.
  induction t as [n|f args IH] using term_ind.
  - intros G rho z HE HQ HEq HV.
    apply (equality_ordinal_representative_transport G z (rho n));
      [exact HE|exact HQ|exact HEq|exact (CE2 HV)|exact (CE1 HV)].
  - intros G rho z HE HQ HEq HV. destruct f.
    + apply II, Ctx. now left.
    + remember (Vector.hd args) as u eqn:Hu.
      assert (V : args = Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term)).
      { rewrite Hu. apply destruct_vector_single. }
      rewrite V in IH, HV |- *. eapply ExE_named.
      * apply (successor_value_inputs G u rho z). exact HV.
      * intro x. rewrite successor_value_body_specialize.
        apply (IH u ltac:(constructor) _ rho x); [inherit HE|inherit HQ|inherit HEq|].
        eapply CE1, Ctx. now left.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HV |- *.
      apply (binary_value_domains G AddGraph238.AddGraph238.add_result u v rho z).
      * exact source_add_result_subst.
      * exact (IH u ltac:(constructor)).
      * exact (IH v ltac:(constructor 2; constructor)).
      * exact HE.
      * exact HQ.
      * exact HEq.
      * exact HV.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HV |- *.
      apply (binary_value_domains G MulGraph238.MulGraph238.mul_result u v rho z).
      * exact source_mul_result_subst.
      * exact (IH u ltac:(constructor)).
      * exact (IH v ltac:(constructor 2; constructor)).
      * exact HE.
      * exact HQ.
      * exact HEq.
      * exact HV.
Qed.

Theorem S0_pa_term_domains_from_value t rho z :
  derivable finite_set_S0 (pa_term_value t rho z → pa_term_domains t rho).
Proof.
  exists equality_base. split.
  - intros psi Hpsi. apply S0_base. apply in_or_app. now left.
  - apply II, (pa_term_value_domains t _ rho z).
    + apply Ctx. right. unfold equality_base. now left.
    + apply Ctx. right. unfold equality_base, equality_membership_ax.
      right. right. right. now left.
    + apply Ctx. right. unfold equality_base, equality_symmetry_ax. right. now left.
    + apply Ctx. now left.
Qed.

Print Assumptions binary_value_domains.
Print Assumptions pa_term_value_domains.
Print Assumptions S0_pa_term_domains_from_value.
End PAForwardDomains238.
