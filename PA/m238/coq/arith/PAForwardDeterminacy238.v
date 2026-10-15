(** Original numerical determinacy of actual PA term values.
    Finite variable-domain guards construct the needed identity Isos.
    Joint covariance then compares all independent value witnesses. *)
From Coq Require Import List Vector.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From Undecidability.Shared.Libs.PSL.Vectors Require Import Vectors.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238 IsoGraph238
  PAForwardTerms238 PAForwardTotal238 PAForwardCoherenceBasis238 PAForwardCovariance238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238 IsoGraph238.IsoGraph238
  PAForwardTerms238.PAForwardTerms238 PAForwardTotal238.PAForwardTotal238
  PAForwardCoherenceBasis238.PAForwardCoherenceBasis238
  PAForwardCovariance238.PAForwardCovariance238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardDeterminacy238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition iso_reflexivity_ax : set_form :=
  ∀ (ordinal_representative $0 → order_iso $0 $0).
Theorem S0_iso_reflexivity_ax : derivable finite_set_S0 iso_reflexivity_ax.
Proof.
  unfold iso_reflexivity_ax. apply S0_generalize.
  exact (S0_order_iso_reflexive $0).
Qed.

Lemma iso_reflexivity_instance G x :
  G ⊢238 iso_reflexivity_ax -> G ⊢238 ordinal_representative x -> G ⊢238 order_iso x x.
Proof.
  destruct x as [ix|[]]. intros HR HX. unfold iso_reflexivity_ax in HR.
  pose proof (AllE $ix HR) as H.
  cbn [R E terms2 Vector.map subst_form subst_term up scons funcomp] in H.
  exact (IE H HX).
Qed.

Lemma pa_term_comparisons_reflexive G t rho :
  G ⊢238 iso_reflexivity_ax -> G ⊢238 pa_term_domains t rho ->
  G ⊢238 pa_term_comparisons t rho rho.
Proof.
  revert G rho. induction t as [n|f args IH] using term_ind.
  - intros G rho HR HD. apply (iso_reflexivity_instance G (rho n)); assumption.
  - intros G rho HR HD. destruct f.
    + apply II, Ctx. now left.
    + remember (Vector.hd args) as u eqn:Hu.
      assert (V : args = Vector.cons PA238.pa_term u 0 (Vector.nil PA238.pa_term)).
      { rewrite Hu. apply destruct_vector_single. }
      rewrite V in IH, HD |- *.
      apply (IH u ltac:(constructor) G rho); assumption.
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HD |- *. apply CI.
      * apply (IH u ltac:(constructor) G rho); [exact HR|exact (CE1 HD)].
      * apply (IH v ltac:(constructor 2; constructor) G rho); [exact HR|exact (CE2 HD)].
    + remember (Vector.hd args) as u eqn:Hu.
      remember (Vector.hd (Vector.tl args)) as v eqn:Hv.
      assert (V : args = Vector.cons PA238.pa_term u 1
        (Vector.cons PA238.pa_term v 0 (Vector.nil PA238.pa_term))).
      { rewrite Hu, Hv. apply pa_vector2_eta. }
      rewrite V in IH, HD |- *. apply CI.
      * apply (IH u ltac:(constructor) G rho); [exact HR|exact (CE1 HD)].
      * apply (IH v ltac:(constructor 2; constructor) G rho); [exact HR|exact (CE2 HD)].
Qed.

Theorem S0_pa_term_determinacy t rho z w :
  derivable finite_set_S0
    (pa_term_domains t rho →
      (pa_term_value t rho z → (pa_term_value t rho w → order_iso z w))).
Proof.
  destruct S0_term_coherence_basis as [Gc [HGc HC]].
  destruct S0_iso_reflexivity_ax as [Gr [HGr HR]].
  set (G := Gc ++ Gr).
  assert (HC' : G ⊢238 term_coherence_basis).
  { eapply Weak; [exact HC|]. intros psi Hpsi. unfold G. apply in_or_app. now left. }
  assert (HR' : G ⊢238 iso_reflexivity_ax).
  { eapply Weak; [exact HR|]. intros psi Hpsi. unfold G. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
      [now apply HGc|now apply HGr].
  - apply II, II, II. apply (pa_term_value_comparison t _ rho rho z w).
    + inherit HC'.
    + apply (pa_term_comparisons_reflexive _ t rho); [inherit HR'|].
      apply Ctx. right. right. now left.
    + apply Ctx. right. now left.
    + apply Ctx. now left.
Qed.

Print Assumptions S0_iso_reflexivity_ax.
Print Assumptions iso_reflexivity_instance.
Print Assumptions pa_term_comparisons_reflexive.
Print Assumptions S0_pa_term_determinacy.
End PAForwardDeterminacy238.
