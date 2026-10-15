(** Original finite natural-deduction transport into the exact PA238
    numeric calculus. Every rule constructs finite numeric_context proofs
    using actual numeric theorems, MP and hypothesis discharge. Primitive
    bottom maps syntactically to code 1, with the proved R6/K explosion;
    no model, numeric IR premise, or logical completeness supplier occurs. *)
From Coq Require Import Arith List Lia.
From Undecidability.FOL Require Import
  Sets.Signatures Syntax.Facts Deduction.FullNDFacts.
From P238.logic Require Import Codes238 Compiler238 NumericSyntax238
  NumericHilbert238 NumericNamed238 NativeNamed238.
From P238.arith Require Import Compact238.
Import ListNotations FullSyntax BinSig ZFSignature.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Module NativeND238.
Module C := Compact238.Compact238.
Module N := NumericSyntax238.NumericSyntax238.
Module H := NumericHilbert238.NumericHilbert238.
Module T := NativeNamed238.NativeNamed238.

Definition context_codes (G : list C.set_form) rho lo := map (fun phi => T.native_code phi rho lo) G.

Lemma shifted_context_codes G rho lo a :
  context_codes (map (subst_form ↑) G) (T.push_label rho a) lo = context_codes G rho lo.
Proof.
  unfold context_codes; rewrite map_map; apply map_ext; intro phi.
  unfold T.native_code; now rewrite T.native_named_shift.
Qed.

Lemma context_vacuity G rho lo : 0 < lo -> (forall i, rho i < lo) ->
  forall h, In h (context_codes G rho lo) -> Compiler238.derivable (wim h (wal lo h)).
Proof.
  intros Hpos Hr h Hh; apply in_map_iff in Hh as [phi [<- Hphi]].
  apply T.native_vacuity_bound; assumption.
Qed.

Theorem native_numeric_nd : forall p G phi,
  @prv sig_empty ZF_pred_sig falsity_on p G phi -> p = class ->
  forall rho lo, 0 < lo -> (forall i, rho i < lo) ->
  H.numeric_context (context_codes G rho lo) (T.native_code phi rho lo).
Proof.
  apply (prv_ind_full (P := fun p G phi => p = class ->
    forall rho lo, 0 < lo -> (forall i, rho i < lo) ->
    H.numeric_context (context_codes G rho lo) (T.native_code phi rho lo))).
  - intros p G phi psi D IH Hp rho lo Hpos Hr; subst p.
    change (H.numeric_context (context_codes G rho lo)
      (wim (T.native_code phi rho lo) (T.native_code psi rho lo))).
    apply H.numeric_deduction; exact (IH eq_refl rho lo Hpos Hr).
  - intros p G phi psi Dimp IHimp Dphi IHphi Hp rho lo Hpos Hr; subst p.
    apply (H.numeric_context_mp (context_codes G rho lo)
      (T.native_code phi rho lo) (T.native_code psi rho lo)).
    + exact (IHphi eq_refl rho lo Hpos Hr).
    + exact (IHimp eq_refl rho lo Hpos Hr).
  - intros p G phi D IH Hp rho lo Hpos Hr; subst p.
    assert (Hpush : forall i, T.push_label rho lo i < S lo).
    { intros [|i]; cbn [T.push_label]; [lia|specialize (Hr i); lia]. }
    pose proof (IH eq_refl (T.push_label rho lo) (S lo) ltac:(lia) Hpush) as Hbody.
    rewrite shifted_context_codes in Hbody.
    pose proof (T.native_context_lower ([]) G rho lo (S lo) _ Hpos ltac:(lia) Hr Hbody) as Hlower.
    change (H.numeric_context (context_codes G rho lo)
      (wal lo (T.native_code phi (T.push_label rho lo) (S lo)))).
    apply H.numeric_context_generalize; [apply context_vacuity; assumption|exact Hlower].
  - intros p G t phi D IH Hp rho lo Hpos Hr; subst p.
    apply (H.numeric_context_mp (context_codes G rho lo)
      (T.native_code (∀ phi) rho lo) (T.native_code (phi[t..]) rho lo)).
    + exact (IH eq_refl rho lo Hpos Hr).
    + apply H.numeric_theorem, T.native_universal_instance; assumption.
  - intros p G t phi D IH Hp rho lo Hpos Hr; subst p.
    apply (H.numeric_context_mp (context_codes G rho lo)
      (T.native_code (phi[t..]) rho lo) (T.native_code (∃ phi) rho lo)).
    + exact (IH eq_refl rho lo Hpos Hr).
    + apply H.numeric_theorem, T.native_existential_instance; assumption.
  - intros p G phi psi Dexists IHexists Dbody IHbody Hp rho lo Hpos Hr; subst p.
    assert (Hpush : forall i, T.push_label rho lo i < S lo).
    { intros [|i]; cbn [T.push_label]; [lia|specialize (Hr i); lia]. }
    pose proof (IHbody eq_refl (T.push_label rho lo) (S lo) ltac:(lia) Hpush) as Hbody.
    change (H.numeric_context
      (T.native_code phi (T.push_label rho lo) (S lo) ::
       context_codes (map (subst_form ↑) G) (T.push_label rho lo) (S lo))
      (T.native_code (psi[↑]) (T.push_label rho lo) (S lo))) in Hbody.
    rewrite shifted_context_codes in Hbody.
    assert (Epsi : T.native_code (psi[↑]) (T.push_label rho lo) (S lo) = T.native_code psi rho (S lo)).
    { unfold T.native_code; now rewrite T.native_named_shift. }
    rewrite Epsi in Hbody.
    set (a := T.native_code phi (T.push_label rho lo) (S lo)).
    pose proof (T.native_context_lower ([a]) G rho lo (S lo) _ Hpos ltac:(lia) Hr Hbody) as Hlower.
    destruct (T.native_named_reallocate psi rho lo (S lo) Hpos ltac:(lia) Hr) as [_ Hback].
    assert (Hresult : H.numeric_context (a :: context_codes G rho lo) (T.native_code psi rho lo)).
    { apply (H.numeric_context_mp (a :: context_codes G rho lo)
        (T.native_code psi rho (S lo)) (T.native_code psi rho lo));
        [exact Hlower|apply H.numeric_theorem; exact Hback]. }
    pose proof (H.numeric_deduction (context_codes G rho lo) a (T.native_code psi rho lo) Hresult) as Himp.
    assert (Hall : H.numeric_context (context_codes G rho lo) (wal lo (wim a (T.native_code psi rho lo)))).
    { apply H.numeric_context_generalize; [apply context_vacuity; assumption|exact Himp]. }
    apply (H.numeric_existential_elimination (context_codes G rho lo) lo a (T.native_code psi rho lo)).
    + apply T.native_vacuity_bound; assumption.
    + exact Hall.
    + exact (IHexists eq_refl rho lo Hpos Hr).
  - intros p G phi D IH Hp rho lo Hpos Hr; subst p.
    apply H.numeric_context_explosion; exact (IH eq_refl rho lo Hpos Hr).
  - intros p G phi Hphi Hp rho lo Hpos Hr; subst p.
    apply H.numeric_assumption; unfold context_codes.
    exact (@in_map C.set_form nat (fun psi => T.native_code psi rho lo) G phi Hphi).
  - intros p G phi psi Dphi IHphi Dpsi IHpsi Hp rho lo Hpos Hr; subst p.
    change (H.numeric_context (context_codes G rho lo)
      (wa (T.native_code phi rho lo) (T.native_code psi rho lo))).
    apply H.numeric_conjunction_intro.
    + exact (IHphi eq_refl rho lo Hpos Hr).
    + exact (IHpsi eq_refl rho lo Hpos Hr).
  - intros p G phi psi D IH Hp rho lo Hpos Hr; subst p.
    apply H.numeric_conjunction_left with (b := T.native_code psi rho lo).
    exact (IH eq_refl rho lo Hpos Hr).
  - intros p G phi psi D IH Hp rho lo Hpos Hr; subst p.
    apply H.numeric_conjunction_right with (a := T.native_code phi rho lo).
    exact (IH eq_refl rho lo Hpos Hr).
  - intros p G phi psi D IH Hp rho lo Hpos Hr; subst p.
    change (H.numeric_context (context_codes G rho lo)
      (H.disjunction_code (T.native_code phi rho lo) (T.native_code psi rho lo))).
    apply H.numeric_disjunction_left; exact (IH eq_refl rho lo Hpos Hr).
  - intros p G phi psi D IH Hp rho lo Hpos Hr; subst p.
    change (H.numeric_context (context_codes G rho lo)
      (H.disjunction_code (T.native_code phi rho lo) (T.native_code psi rho lo))).
    apply H.numeric_disjunction_right; exact (IH eq_refl rho lo Hpos Hr).
  - intros p G phi psi theta Dsum IHsum Dphi IHphi Dpsi IHpsi Hp rho lo Hpos Hr; subst p.
    apply H.numeric_disjunction_elimination with
      (a := T.native_code phi rho lo) (b := T.native_code psi rho lo).
    + exact (IHsum eq_refl rho lo Hpos Hr).
    + exact (IHphi eq_refl rho lo Hpos Hr).
    + exact (IHpsi eq_refl rho lo Hpos Hr).
  - intros G phi psi Hp rho lo Hpos Hr.
    apply H.numeric_context_peirce.
Qed.

Theorem native_numeric_closed G phi rho lo : 0 < lo -> (forall i, rho i < lo) ->
  (forall psi, In psi G -> Compiler238.derivable (T.native_code psi rho lo)) ->
  @prv sig_empty ZF_pred_sig falsity_on class G phi ->
  Compiler238.derivable (T.native_code phi rho lo).
Proof.
  intros Hpos Hr HG D; apply (H.numeric_context_closed (context_codes G rho lo) _
    (native_numeric_nd class G phi D eq_refl rho lo Hpos Hr)).
  intros h Hh; apply in_map_iff in Hh as [psi [<- Hpsi]]; now apply HG.
Qed.

Print Assumptions native_numeric_nd.
Print Assumptions native_numeric_closed.
End NativeND238.
