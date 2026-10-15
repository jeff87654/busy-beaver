(* Original PA238 endpoint. Upstream arithmetic syntax and axioms are vendored
   unchanged under MPL-2.0; see ../../vendor/undecidability/README.md. *)

From Coq Require Import List.
From Undecidability.FOL.Arithmetics Require Export PA.
From Undecidability.Shared Require Import Dec.

(* Imported library files set global argument options. Fix the options for
   the original declarations below; upstream argument declarations persist. *)
Local Unset Implicit Arguments.
Local Set Strict Implicit.

Import ListNotations FullSyntax.
Open Scope PA_Notation.
Open Scope subst_scope.
Open Scope full_syntax.

Module PA238.

Definition pa_term := @term PA_funcs_signature.
Definition pa_form :=
  @form PA_funcs_signature PA_preds_signature full_operators falsity_on.

(* These are concrete decision procedures, not additional assumptions. *)
#[local] Instance PA_funcs_dec : eq_dec PA_funcs_signature := PA_funcs_eq.
#[local] Instance PA_preds_dec : eq_dec PA_preds_signature := PA_preds_eq.

Definition universal_close (phi : pa_form) : pa_form := close All phi.

(* Upstream PAeq supplies every induction formula. Close all free parameters
   of each axiom, including induction instances, before adding it to PA. *)
Definition ordinary_PAeq (phi : pa_form) : Prop :=
  exists psi : pa_form, PAeq psi /\ universal_close psi = phi.

(* TC explicitly fixes classical natural deduction, including Peirce's rule.
   tprv requires a finite axiom list; there is no extra hypothesis context. *)
Definition paeq_derivable (phi : pa_form) : Prop :=
  ordinary_PAeq ⊢TC phi.

Definition PAeq_inconsistent : Prop := paeq_derivable falsity.

Lemma universal_close_closed phi : closed (universal_close phi).
Proof. apply close_closed. Qed.

Lemma ordinary_PAeq_closed phi : ordinary_PAeq phi -> closed phi.
Proof.
  intros (psi & Hpsi & <-). apply universal_close_closed.
Qed.

Lemma ordinary_PAeq_subst phi (rho : nat -> pa_term) :
  ordinary_PAeq phi -> phi[rho] = phi.
Proof.
  intros Hphi. apply subst_closed. now apply ordinary_PAeq_closed.
Qed.

Lemma paeq_finite_context phi :
  paeq_derivable phi <->
  exists A : list pa_form,
    (forall psi, List.In psi A -> ordinary_PAeq psi) /\ A ⊢C phi.
Proof. reflexivity. Qed.

Lemma paeq_context_subst A (rho : nat -> pa_term) :
  (forall phi : pa_form, List.In phi A -> ordinary_PAeq phi) ->
  List.map (subst_form rho) A = A.
Proof.
  induction A as [|psi A IH]; intros HA; cbn.
  - reflexivity.
  - f_equal.
    + apply ordinary_PAeq_subst, HA. now left.
    + apply IH. intros phi Hphi. apply HA. now right.
Qed.

Lemma paeq_axiom_closed phi :
  PAeq phi -> ordinary_PAeq (universal_close phi).
Proof. intros Hphi. exists phi. now split. Qed.

Lemma paeq_axiom phi : PAeq phi -> paeq_derivable phi.
Proof.
  intros Hphi. exists [universal_close phi]. split.
  - intros psi [<-|[]]. now apply paeq_axiom_closed.
  - apply close_extract. apply Ctx. now left.
Qed.

Lemma paeq_substitution phi (rho : nat -> pa_term) :
  paeq_derivable phi -> paeq_derivable phi[rho].
Proof.
  intros (A & HA & HD). exists A. split; [exact HA|].
  pose proof (subst_Weak rho HD) as HS.
  change (List.map (subst_form rho) A ⊢C phi[rho]) in HS.
  rewrite (paeq_context_subst A rho HA) in HS. exact HS.
Qed.

Lemma paeq_axiom_instance phi (rho : nat -> pa_term) :
  PAeq phi -> paeq_derivable phi[rho].
Proof. intros Hphi. apply paeq_substitution. now apply paeq_axiom. Qed.

Lemma paeq_generalize phi : paeq_derivable phi -> paeq_derivable (∀ phi).
Proof.
  intros (A & HA & HD). exists A. split; [exact HA|].
  apply AllI. rewrite (paeq_context_subst A (S >> var) HA). exact HD.
Qed.

Lemma paeq_capture n phi :
  paeq_derivable phi -> paeq_derivable (capture All n phi).
Proof.
  induction n; cbn; intros Hphi; [exact Hphi|].
  apply paeq_generalize. now apply IHn.
Qed.

Lemma paeq_close phi :
  paeq_derivable phi -> paeq_derivable (universal_close phi).
Proof. unfold universal_close, close. apply paeq_capture. Qed.

Lemma paeq_modus_ponens phi psi :
  paeq_derivable (phi → psi) -> paeq_derivable phi -> paeq_derivable psi.
Proof.
  intros (A & HA & HD) (B & HB & HE). exists (A ++ B). split.
  - intros theta Htheta. apply List.in_app_iff in Htheta.
    destruct Htheta as [Htheta|Htheta]; [now apply HA|now apply HB].
  - eapply IE.
    + eapply Weak; [exact HD|]. intros theta Htheta.
      apply List.in_app_iff. now left.
    + eapply Weak; [exact HE|]. intros theta Htheta.
      apply List.in_app_iff. now right.
Qed.

Lemma paeq_ex_falso phi : PAeq_inconsistent -> paeq_derivable phi.
Proof.
  intros (A & HA & HD). exists A. split; [exact HA|]. now apply Exp.
Qed.

Lemma paeq_peirce phi psi : paeq_derivable (((phi → psi) → phi) → phi).
Proof.
  exists []. split; [intros theta Htheta; inversion Htheta|apply Pc].
Qed.

(* No restriction on phi: full induction, including arbitrary parameters. *)
Lemma paeq_induction_closed phi :
  ordinary_PAeq (universal_close (ax_induction phi)).
Proof. apply paeq_axiom_closed. apply PAeq_induction. Qed.

Lemma paeq_induction phi : paeq_derivable (ax_induction phi).
Proof. apply paeq_axiom. apply PAeq_induction. Qed.

Lemma paeq_induction_instance phi (rho : nat -> pa_term) :
  paeq_derivable (ax_induction phi)[rho].
Proof. apply paeq_axiom_instance. apply PAeq_induction. Qed.

Lemma paeq_induction_rule phi :
  paeq_derivable phi[zero..] ->
  paeq_derivable (∀ (phi → phi[σ $0 .: S >> var])) ->
  paeq_derivable (∀ phi).
Proof.
  intros Hbase Hstep.
  eapply paeq_modus_ponens; [|exact Hstep].
  eapply paeq_modus_ponens; [|exact Hbase].
  apply paeq_induction.
Qed.

(* An explicit proof transformation: replace the finite upstream axiom list
   by its universal closures and extract every original axiom by AllE. *)
Lemma paeq_from_upstream phi : PAeq ⊢TC phi -> paeq_derivable phi.
Proof.
  intros (A & HA & HD). exists (List.map universal_close A). split.
  - intros theta Htheta. apply List.in_map_iff in Htheta.
    destruct Htheta as (psi & <- & Hpsi).
    apply paeq_axiom_closed. now apply HA.
  - eapply prv_cut; [exact HD|]. intros psi Hpsi.
    apply close_extract. apply Ctx. now apply List.in_map.
Qed.

Lemma paeq_reflexivity : paeq_derivable (∀ ($0 == $0)).
Proof.
  apply paeq_axiom, PAeq_FA.
  unfold FAeq, EQ, ax_refl. cbn. now left.
Qed.

(* Literal arithmetic image of Not(All(0, Eq(V0,V0))). *)
Definition old_contradiction : pa_form := ¬ (∀ ($0 == $0)).

Lemma old_contradiction_closed : closed old_contradiction.
Proof. unfold old_contradiction, closed. solve_bounds. Qed.

Theorem paeq_falsity_iff_old_contradiction :
  PAeq_inconsistent <-> paeq_derivable old_contradiction.
Proof.
  split.
  - apply paeq_ex_falso.
  - intros Hcontra. unfold PAeq_inconsistent.
    eapply paeq_modus_ponens; [exact Hcontra|apply paeq_reflexivity].
Qed.

End PA238.
