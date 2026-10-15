(** Finite proof-family assembly for the ordinary PA to S0 endpoint.
    Each axiom family carries its actual finite S0 list. List induction
    combines these lists, and a real ordinal witness supplies the initial
    environment before the retained PA derivation is transported. *)
From Coq Require Import List.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.arith Require Import PAeq238 Compact238 PAinCompact238
  PAForwardTerms238 PAForwardFormula238 PAForwardFormulaBasis238
  PAForwardQuantifier238 PAForwardND238.
Import ListNotations FullSyntax BinSig ZFSignature
  Compact238.Compact238 PAinCompact238.PAinCompact238
  PAForwardTerms238.PAForwardTerms238 PAForwardFormula238.PAForwardFormula238
  PAForwardFormulaBasis238.PAForwardFormulaBasis238 PAForwardQuantifier238.PAForwardQuantifier238
  PAForwardND238.PAForwardND238.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module PAForwardFinite238.
Ltac inherit H :=
  eapply Weak; [exact H|]; intros chi Hchi; repeat first [exact Hchi | right].

Definition pa_axiom_proof_family (phi : PA238.pa_form) : Prop :=
  exists G : list set_form,
    (forall psi, List.In psi G -> finite_set_S0 psi) /\
    forall D rho, List.incl G D ->
      (forall n, D ⊢238 ordinal_representative (rho n)) ->
      D ⊢238 pa_formula_value phi rho.

Lemma pa_axiom_proof_family_all (phi : PA238.pa_form) :
  pa_axiom_proof_family phi -> pa_axiom_proof_family (∀ phi).
Proof.
  intros [G [HG HP]]. exists G. split; [exact HG|]. intros D rho Hinc HD.
  apply interpreted_all_introduce. intro x. apply (HP _ (x .: rho)).
  - intros psi Hpsi. right. exact (Hinc psi Hpsi).
  - intros [|n]; [apply Ctx; now left|apply weaken_one; exact (HD n)].
Qed.

Lemma pa_axiom_proof_family_capture n (phi : PA238.pa_form) :
  pa_axiom_proof_family phi -> pa_axiom_proof_family (@capture PA_funcs_signature PA_preds_signature full_operators falsity_on All n phi).
Proof.
  induction n; intro Hphi.
  - exact Hphi.
  - change (pa_axiom_proof_family (∀ (@capture PA_funcs_signature PA_preds_signature full_operators falsity_on All n phi))).
    apply pa_axiom_proof_family_all, IHn, Hphi.
Qed.

Lemma pa_axiom_proof_family_close (phi : PA238.pa_form) :
  pa_axiom_proof_family phi -> pa_axiom_proof_family (PA238.universal_close phi).
Proof.
  unfold PA238.universal_close, close. apply pa_axiom_proof_family_capture.
Qed.

Lemma pa_finite_axiom_proof_family (A : list PA238.pa_form) :
  (forall phi, List.In phi A -> pa_axiom_proof_family phi) ->
  exists G : list set_form,
    (forall psi, List.In psi G -> finite_set_S0 psi) /\
    forall D rho, List.incl G D ->
      (forall n, D ⊢238 ordinal_representative (rho n)) ->
      forall phi, List.In phi A -> D ⊢238 pa_formula_value phi rho.
Proof.
  induction A as [|phi A IH]; intro HF.
  - exists []. split; [intros psi Hpsi; contradiction|].
    intros D rho Hinc HD psi Hpsi. contradiction.
  - destruct (HF phi ltac:(now left)) as [Gh [HGh HH]].
    destruct (IH ltac:(intros psi Hpsi; apply HF; now right)) as [Gt [HGt HT]].
    set (G := Gh ++ Gt). exists G. split.
    + intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi];
        [now apply HGh|now apply HGt].
    + intros D rho Hinc HD psi Hpsi. destruct Hpsi as [<-|Hpsi].
      * apply (HH D rho); [|exact HD]. intros chi Hchi.
        apply Hinc. unfold G. apply in_or_app. now left.
      * apply (HT D rho); [|exact HD|exact Hpsi]. intros chi Hchi.
        apply Hinc. unfold G. apply in_or_app. now right.
Qed.

(** This assembly lemma does not assert that unspecified PA axioms have
    source proofs: every member's concrete finite proof family is supplied
    explicitly. The PAeq constructor theorem will supply exactly those
    families from the actual arithmetic and induction producers. *)
Theorem finite_pa_refutation_from_proof_families (A : list PA238.pa_form) :
  (forall phi, List.In phi A -> pa_axiom_proof_family phi) ->
  @FullND.prv PA_funcs_signature PA_preds_signature falsity_on class A falsity ->
  derivable finite_set_S0 falsity.
Proof.
  intros HF HP.
  destruct (pa_finite_axiom_proof_family A HF) as [Ga [HGa HA]].
  destruct S0_formula_transport_basis as [Gb [HGb HB]].
  destruct S0_ordinal_domain_inhabited as [Ge [HGe HE]].
  set (G := Ga ++ Gb ++ Ge).
  assert (HB' : G ⊢238 formula_transport_basis).
  { eapply Weak; [exact HB|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. now left. }
  assert (HE' : G ⊢238 ∃ ordinal_representative $0).
  { eapply Weak; [exact HE|]. intros psi Hpsi. unfold G.
    apply in_or_app. right. apply in_or_app. now right. }
  exists G. split.
  - intros psi Hpsi. unfold G in Hpsi. apply in_app_or in Hpsi as [Hpsi|Hpsi].
    + now apply HGa.
    + apply in_app_or in Hpsi as [Hpsi|Hpsi]; [now apply HGb|now apply HGe].
  - eapply ExE_named; [exact HE'|]. intro e. rewrite ordinal_value_subst.
    apply (pa_nd_source_transport class A falsity HP _ (fun _ => e)).
    + inherit HB'.
    + intro n. apply Ctx. now left.
    + apply (HA _ (fun _ => e)).
      * intros psi Hpsi. right. unfold G. apply in_or_app. now left.
      * intro n. apply Ctx. now left.
Qed.

Print Assumptions pa_axiom_proof_family_all.
Print Assumptions pa_axiom_proof_family_capture.
Print Assumptions pa_axiom_proof_family_close.
Print Assumptions pa_finite_axiom_proof_family.
Print Assumptions finite_pa_refutation_from_proof_families.
End PAForwardFinite238.
