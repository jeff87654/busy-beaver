(** Actual finite full natural-deduction transport from the pinned PA
    syntax into S0 source formulas. All derivation constructors, including
    Peirce and the two eigenvariable rules, are handled syntactically. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238
  PAForwardTerms238 PAForwardFormula238 PAForwardRename238 PAForwardFormulaBasis238
  PAForwardQuantifier238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  PAForwardTerms238.PAForwardTerms238 PAForwardFormula238.PAForwardFormula238
  PAForwardRename238.PAForwardRename238 PAForwardFormulaBasis238.PAForwardFormulaBasis238
  PAForwardQuantifier238.PAForwardQuantifier238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardND238.
Ltac inherit H :=
  let chi0 := fresh "formula" in let Hchi0 := fresh "Hformula" in
  eapply Weak; [exact H|]; intros chi0 Hchi0; repeat first [exact Hchi0 | right].

Definition pa_derivation_rule (A : list PA238.pa_form) (phi : PA238.pa_form) : Prop :=
  forall G rho,
    G ⊢238 formula_transport_basis ->
    (forall n, G ⊢238 ordinal_representative (rho n)) ->
    (forall psi, List.In psi A -> G ⊢238 pa_formula_value psi rho) ->
    G ⊢238 pa_formula_value phi rho.

Lemma pa_shifted_context_values G (A : list PA238.pa_form) rho x :
  (forall phi, List.In phi A -> G ⊢238 pa_formula_value phi rho) ->
  forall phi, List.In phi (List.map (subst_form ↑) A) ->
    G ⊢238 pa_formula_value phi (x .: rho).
Proof.
  intros HC phi Hphi. apply in_map_iff in Hphi as [psi [<- Hpsi]].
  change (G ⊢238 pa_formula_value (psi[pa_renaming S]) (x .: rho)).
  rewrite pa_formula_value_shift. exact (HC psi Hpsi).
Qed.

Theorem pa_nd_source_transport : forall p (A : list PA238.pa_form) (phi : PA238.pa_form),
  @FullND.prv PA_funcs_signature PA_preds_signature falsity_on p A phi ->
  pa_derivation_rule A phi.
Proof.
  apply (@prv_ind_full PA_funcs_signature PA_preds_signature
    (fun _ A phi => pa_derivation_rule A phi)).
  - intros p A phi psi H IH G rho HB HD HC. apply II, (IH _ rho).
    + inherit HB.
    + intro n. inherit (HD n).
    + intros chi [<-|Hchi]; [apply Ctx; now left|inherit (HC chi Hchi)].
  - intros p A phi psi H1 IH1 H2 IH2 G rho HB HD HC. eapply IE; [exact (IH1 G rho HB HD HC)|exact (IH2 G rho HB HD HC)].
  - intros p A phi H IH G rho HB HD HC. apply interpreted_all_introduce. intro x. apply (IH _ (x .: rho)).
    + inherit HB.
    + intros [|n]; [apply Ctx; now left|inherit (HD n)].
    + apply pa_shifted_context_values. intros chi Hchi. inherit (HC chi Hchi).
  - intros p A t phi H IH G rho HB HD HC. apply (interpreted_all_eliminate G phi t rho); [exact HB|exact HD|exact (IH G rho HB HD HC)].
  - intros p A t phi H IH G rho HB HD HC. apply (interpreted_exists_introduce G phi t rho); [exact HB|exact HD|exact (IH G rho HB HD HC)].
  - intros p A phi psi H1 IH1 H2 IH2 G rho HB HD HC. apply (interpreted_exists_eliminate G phi rho (pa_formula_value psi rho)).
    + exact (IH1 G rho HB HD HC).
    + intro x. rewrite <- (pa_formula_value_shift psi rho x).
      apply (IH2 _ (x .: rho)).
      * inherit HB.
      * intros [|n].
        -- eapply CE1, Ctx. now left.
        -- inherit (HD n).
      * intros chi Hchi. destruct Hchi as [<-|Hchi].
        -- eapply CE2, Ctx. now left.
        -- apply (pa_shifted_context_values _ A rho x).
           ++ intros theta Htheta. inherit (HC theta Htheta).
           ++ exact Hchi.
  - intros p A phi H IH G rho HB HD HC. apply Exp. exact (IH G rho HB HD HC).
  - intros p A phi H G rho HB HD HC. exact (HC phi H).
  - intros p A phi psi H1 IH1 H2 IH2 G rho HB HD HC. apply CI; [exact (IH1 G rho HB HD HC)|exact (IH2 G rho HB HD HC)].
  - intros p A phi psi H IH G rho HB HD HC. exact (CE1 (IH G rho HB HD HC)).
  - intros p A phi psi H IH G rho HB HD HC. exact (CE2 (IH G rho HB HD HC)).
  - intros p A phi psi H IH G rho HB HD HC. apply DI1. exact (IH G rho HB HD HC).
  - intros p A phi psi H IH G rho HB HD HC. apply DI2. exact (IH G rho HB HD HC).
  - intros p A phi psi theta H1 IH1 H2 IH2 H3 IH3 G rho HB HD HC. eapply DE; [exact (IH1 G rho HB HD HC)| |].
    + apply (IH2 _ rho).
      * inherit HB.
      * intro n. inherit (HD n).
      * intros chi [<-|Hchi]; [apply Ctx; now left|inherit (HC chi Hchi)].
    + apply (IH3 _ rho).
      * inherit HB.
      * intro n. inherit (HD n).
      * intros chi [<-|Hchi]; [apply Ctx; now left|inherit (HC chi Hchi)].
  - intros A phi psi G rho HB HD HC. apply Pc.
Qed.

Print Assumptions pa_shifted_context_values.
Print Assumptions pa_nd_source_transport.
End PAForwardND238.
