(** Original native property readback primitives for exact PA238 R9.
    These equations connect the named property encoding to ordinary term
    substitution when a fresh member is opened. They are syntax proofs;
    any IR used by subsequent finite ND readback is supplied by the actual
    derived numeric theorem, not by the pointed/equality producer. *)
From Coq Require Import Arith List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.logic Require Import NumericSyntax238 NativeNamed238 RawInterpret238.
From P238.arith Require Import Compact238.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module NativeProperty238.
Module C := Compact238.Compact238.
Module N := NumericSyntax238.NumericSyntax238.
Module T := NativeNamed238.NativeNamed238.
Module R := RawInterpret238.RawInterpret238.

Notation "G ⊢NP phi" :=
  (@prv sig_empty ZF_pred_sig falsity_on class G phi) (at level 61).

Definition property_encoding (phi : C.set_form) (rho : T.label_env)
  (fresh : nat) (env : N.named_env) : C.set_form :=
  N.interpret_named (T.native_named phi rho fresh) env.

Lemma term_label_reading rho env sigma t :
  (forall i, env (rho i) = sigma i) -> env (T.term_label rho t) = t`[sigma].
Proof. destruct t as [i|[]]; intro H; apply H. Qed.

Lemma opened_native_up (phi : C.set_form) sigma t :
  (phi[up sigma])[t..] = phi[t .: sigma].
Proof.
  rewrite subst_comp; apply subst_ext; intros [|i]; [reflexivity|].
  change ((sigma i)`[↑]`[t..] = sigma i); apply subst_term_shift.
Qed.

Lemma opened_label_coherence rho env sigma fresh t :
  (forall i, rho i < fresh) -> (forall i, env (rho i) = sigma i) -> forall i,
  N.update_env env fresh t (T.push_label rho fresh i) = (t .: sigma) i.
Proof.
  intros Hbound Hread [|i]; cbn [T.push_label scons]; unfold N.update_env.
  - now rewrite Nat.eqb_refl.
  - rewrite (proj2 (Nat.eqb_neq (rho i) fresh) ltac:(specialize (Hbound i); lia)); apply Hread.
Qed.

Lemma raised_labels_bound rho fresh : (forall i, rho i < fresh) ->
  forall i, T.push_label rho fresh i < S fresh.
Proof.
  intros H [|i]; cbn [T.push_label]; [lia|specialize (H i); lia].
Qed.

Lemma bound_label_coherence rho env sigma fresh :
  (forall i, rho i < fresh) -> (forall i, env (rho i) = sigma i) -> forall i,
  N.bind_env env fresh (T.push_label rho fresh i) = up sigma i.
Proof.
  intros Hbound Hread [|i]; cbn [T.push_label up scons]; unfold N.bind_env.
  - now rewrite Nat.eqb_refl.
  - rewrite (proj2 (Nat.eqb_neq (rho i) fresh) ltac:(specialize (Hbound i); lia)).
    now rewrite Hread.
Qed.

Lemma native_atom_reading (p : ZF_Preds)
  (ts : Vector.t C.set_term (ar_preds p)) rho fresh env sigma :
  (forall i, env (rho i) = sigma i) ->
  property_encoding (atom p ts) rho fresh env = (atom p ts)[sigma].
Proof.
  intro Hread; destruct p; cbn in ts; rewrite (T.native_vector2_eta ts);
    cbn [property_encoding T.native_named N.interpret_named C.R C.E C.terms2
      subst_form Vector.map Vector.hd Vector.tl];
    rewrite !(term_label_reading rho env sigma) by exact Hread; reflexivity.
Qed.

Lemma finite_weaken G (phi psi : C.set_form) :
  G ⊢NP phi -> psi :: G ⊢NP phi.
Proof.
  intro H; eapply Weak; [exact H|]; intros chi Hchi; now right.
Qed.

Lemma finite_identity G (phi : C.set_form) : G ⊢NP (phi → phi).
Proof. apply II, Ctx; now left. Qed.

Lemma finite_implication_compose G (phi psi chi : C.set_form) :
  G ⊢NP (phi → psi) -> G ⊢NP (psi → chi) -> G ⊢NP (phi → chi).
Proof.
  intros Hphi Hpsi; apply II; eapply IE.
  - apply finite_weaken; exact Hpsi.
  - eapply IE; [apply finite_weaken; exact Hphi|apply Ctx; now left].
Qed.

Lemma finite_implication_congruence G (phi phi' psi psi' : C.set_form) :
  G ⊢NP (phi' → phi) -> G ⊢NP (psi → psi') ->
  G ⊢NP ((phi → psi) → (phi' → psi')).
Proof.
  intros Hphi Hpsi; apply II, II; eapply IE.
  - apply finite_weaken, finite_weaken; exact Hpsi.
  - eapply IE; [apply Ctx; right; now left|].
    eapply IE; [apply finite_weaken, finite_weaken; exact Hphi|apply Ctx; now left].
Qed.

Lemma finite_conjunction_congruence G (phi phi' psi psi' : C.set_form) :
  G ⊢NP (phi → phi') -> G ⊢NP (psi → psi') ->
  G ⊢NP ((phi ∧ psi) → (phi' ∧ psi')).
Proof.
  intros Hphi Hpsi; apply II, CI.
  - eapply IE; [apply finite_weaken; exact Hphi|eapply CE1; apply Ctx; now left].
  - eapply IE; [apply finite_weaken; exact Hpsi|eapply CE2; apply Ctx; now left].
Qed.

Lemma finite_disjunction_congruence G (phi phi' psi psi' : C.set_form) :
  G ⊢NP (phi → phi') -> G ⊢NP (psi → psi') ->
  G ⊢NP ((phi ∨ psi) → (phi' ∨ psi')).
Proof.
  intros Hphi Hpsi; apply II; eapply DE; [apply Ctx; now left| |].
  - apply DI1; eapply IE;
      [apply finite_weaken, finite_weaken; exact Hphi|apply Ctx; now left].
  - apply DI2; eapply IE;
      [apply finite_weaken, finite_weaken; exact Hpsi|apply Ctx; now left].
Qed.

Lemma finite_universal_congruence G (phi psi : C.set_form) :
  (forall t, G ⊢NP (phi[t..] → psi[t..])) -> G ⊢NP ((∀ phi) → ∀ psi).
Proof.
  intro Hinstances; apply II, AllI_named; intro t; eapply IE.
  - apply finite_weaken; exact (Hinstances t).
  - assert (Hall : (∀ phi) :: G ⊢NP ∀ phi) by (apply Ctx; now left).
    exact (AllE t Hall).
Qed.

Lemma finite_existential_congruence G (phi psi : C.set_form) :
  (forall t, G ⊢NP (phi[t..] → psi[t..])) -> G ⊢NP ((∃ phi) → ∃ psi).
Proof.
  intro Hinstances; apply II.
  assert (Hex : (∃ phi) :: G ⊢NP ∃ phi) by (apply Ctx; now left).
  eapply ExE_named; [exact Hex|]; intro t; apply (ExI t); eapply IE.
  - apply finite_weaken, finite_weaken; exact (Hinstances t).
  - apply Ctx; now left.
Qed.

Lemma finite_dual_conjunction G (phi psi : C.set_form) :
  G ⊢NP (¬ (phi → ¬ psi) → (phi ∧ psi)) /\
  G ⊢NP ((phi ∧ psi) → ¬ (phi → ¬ psi)).
Proof.
  split; apply II.
  - apply CI; [eapply R.dual_conjunction_left|eapply R.dual_conjunction_right];
      apply Ctx; now left.
  - apply R.dual_conjunction_intro;
      [eapply CE1|eapply CE2]; apply Ctx; now left.
Qed.

Lemma finite_dual_disjunction G (phi psi : C.set_form) :
  G ⊢NP ((¬ phi → psi) → (phi ∨ psi)) /\
  G ⊢NP ((phi ∨ psi) → (¬ phi → psi)).
Proof.
  split; apply II; [apply R.dual_disjunction_native|apply R.native_disjunction_dual];
    apply Ctx; now left.
Qed.

Lemma finite_dual_existential G (phi : C.set_form) :
  G ⊢NP (¬ (∀ ¬ phi) → ∃ phi) /\
  G ⊢NP ((∃ phi) → ¬ (∀ ¬ phi)).
Proof.
  split; apply II; [apply R.dual_existential_native|apply R.native_existential_dual];
    apply Ctx; now left.
Qed.

(** The supplied IR derivation is essential only for native bottom's
    self-membership alias. Every connective and quantifier case below
    constructs ordinary finite ND derivations. The theorem does not
    provide IR for the source pointed/equality theory. *)
Theorem native_property_equivalence (phi : C.set_form) : forall G rho fresh env sigma,
  G ⊢NP C.ir ->
  (forall i, rho i < fresh) -> (forall i, env (rho i) = sigma i) ->
  G ⊢NP (property_encoding phi rho fresh env → phi[sigma]) /\
  G ⊢NP (phi[sigma] → property_encoding phi rho fresh env).
Proof.
  induction phi as [|p ts|op phi IHphi psi IHpsi|op phi IH] using form_ind_falsity;
    intros G rho fresh env sigma HIR Hbound Hread.
  - change (G ⊢NP (C.R (env 0) (env 0) → ⊥) /\
      G ⊢NP (⊥ → C.R (env 0) (env 0))).
    apply R.native_falsity_alias; exact HIR.
  - rewrite (native_atom_reading p ts rho fresh env sigma Hread).
    split; apply finite_identity.
  - destruct (IHphi G rho fresh env sigma HIR Hbound Hread) as [Hphi Hphi'];
      destruct (IHpsi G rho fresh env sigma HIR Hbound Hread) as [Hpsi Hpsi'];
      destruct op; cbn [property_encoding T.native_named N.interpret_named subst_form].
    + destruct (finite_dual_conjunction G
        (property_encoding phi rho fresh env) (property_encoding psi rho fresh env)) as [Hdual Hdual'];
        split.
      * eapply finite_implication_compose; [exact Hdual|].
        apply finite_conjunction_congruence; assumption.
      * eapply finite_implication_compose; [|exact Hdual'].
        apply finite_conjunction_congruence; assumption.
    + destruct (finite_dual_disjunction G
        (property_encoding phi rho fresh env) (property_encoding psi rho fresh env)) as [Hdual Hdual'];
        split.
      * eapply finite_implication_compose; [exact Hdual|].
        apply finite_disjunction_congruence; assumption.
      * eapply finite_implication_compose; [|exact Hdual'].
        apply finite_disjunction_congruence; assumption.
    + split; apply finite_implication_congruence; assumption.
  - set (body := property_encoding phi (T.push_label rho fresh) (S fresh) (N.bind_env env fresh)).
    set (source := phi[up sigma]).
    assert (Hinstances : forall t,
      G ⊢NP (body[t..] → source[t..]) /\ G ⊢NP (source[t..] → body[t..])).
    { intro t; unfold body, source, property_encoding.
      rewrite N.interpret_binder_instance, opened_native_up.
      apply IH; [exact HIR|apply raised_labels_bound; exact Hbound|].
      apply opened_label_coherence; assumption. }
    destruct op; cbn [property_encoding T.native_named N.interpret_named subst_form].
    + change (G ⊢NP ((∀ body) → ∀ source) /\ G ⊢NP ((∀ source) → ∀ body)).
      split; apply finite_universal_congruence; intro t;
        [exact (proj1 (Hinstances t))|exact (proj2 (Hinstances t))].
    + change (G ⊢NP (¬ (∀ ¬ body) → ∃ source) /\
        G ⊢NP ((∃ source) → ¬ (∀ ¬ body))).
      destruct (finite_dual_existential G body) as [Hdual Hdual']; split.
      * eapply finite_implication_compose; [exact Hdual|].
        apply finite_existential_congruence; intro t; exact (proj1 (Hinstances t)).
      * eapply finite_implication_compose; [|exact Hdual'].
        apply finite_existential_congruence; intro t; exact (proj2 (Hinstances t)).
Qed.

Corollary native_property_biconditional G phi rho fresh env sigma :
  G ⊢NP C.ir ->
  (forall i, rho i < fresh) -> (forall i, env (rho i) = sigma i) ->
  G ⊢NP (property_encoding phi rho fresh env ↔ phi[sigma]).
Proof.
  intros HIR Hbound Hread.
  destruct (native_property_equivalence phi G rho fresh env sigma HIR Hbound Hread) as [H H'];
    apply CI; assumption.
Qed.

Corollary native_property_derivability G phi rho fresh env sigma :
  G ⊢NP C.ir ->
  (forall i, rho i < fresh) -> (forall i, env (rho i) = sigma i) ->
  (G ⊢NP property_encoding phi rho fresh env <-> G ⊢NP phi[sigma]).
Proof.
  intros HIR Hbound Hread.
  destruct (native_property_equivalence phi G rho fresh env sigma HIR Hbound Hread) as [H H'];
    split; intro D; [exact (IE H D)|exact (IE H' D)].
Qed.

Print Assumptions term_label_reading.
Print Assumptions opened_native_up.
Print Assumptions opened_label_coherence.
Print Assumptions bound_label_coherence.
Print Assumptions native_property_equivalence.
Print Assumptions native_property_biconditional.
Print Assumptions native_property_derivability.
End NativeProperty238.
