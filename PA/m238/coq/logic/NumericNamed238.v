(** Original named PA238 logical basis for the finite forward bridge.
    It reuses the existing named tree and the actual numeric constructors.
    The output-label freshness proofs include inner binder labels; no
    interpreter-level claim that self-membership is falsity is used. *)
From Coq Require Import Arith Bool List.
From P238.logic Require Import Codes238 Compiler238 NumericSyntax238 NumericHilbert238.
Import ListNotations.
Unset Implicit Arguments.

Module NumericNamed238.
Module N := NumericSyntax238.NumericSyntax238.
Module H := NumericHilbert238.NumericHilbert238.

Theorem named_vacuity v phi : N.free_named v phi = false ->
  N.binders_named v phi = false ->
  Compiler238.derivable (wim (N.encode_named phi) (wal v (N.encode_named phi))).
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    intros Hfree Hbind; cbn [N.encode_named].
  - apply H.numeric_context_empty, H.numeric_context_lift, H.numeric_theorem.
    exact (Compiler238.derives_all v 0 Compiler238.derives_truth).
  - cbn [N.free_named] in Hfree; apply Bool.orb_false_iff in Hfree as [Hf1 Hf2].
    cbn [N.binders_named] in Hbind; apply Bool.orb_false_iff in Hbind as [Hb1 Hb2].
    apply H.numeric_implication_vacuity; [apply IHphi|apply IHpsi]; assumption.
  - apply H.numeric_negation_vacuity, IH; assumption.
  - cbn [N.free_named] in Hfree; apply Bool.orb_false_iff in Hfree as [Ha Hb].
    apply Nat.eqb_neq in Ha; apply Nat.eqb_neq in Hb.
    exact (H.numeric_membership_vacuity_code a b v Ha Hb).
  - cbn [N.free_named] in Hfree; apply Bool.orb_false_iff in Hfree as [Ha Hb].
    apply Nat.eqb_neq in Ha; apply Nat.eqb_neq in Hb.
    exact (H.numeric_equality_vacuity_code a b v Ha Hb).
  - cbn [N.binders_named] in Hbind; apply Bool.orb_false_iff in Hbind as [Hva Hb].
    cbn [N.free_named] in Hfree; rewrite Hva in Hfree; cbn in Hfree.
    apply H.numeric_universal_vacuity, IH; assumption.
Qed.

Theorem named_output_vacuity phi :
  Compiler238.derivable (wim (N.encode_named phi)
    (wal (N.encode_named phi) (N.encode_named phi))).
Proof.
  apply named_vacuity; [apply N.encoded_output_free_fresh|apply N.encoded_output_binders_fresh].
Qed.

Theorem named_generalize a phi : Compiler238.derivable (N.encode_named phi) ->
  Compiler238.derivable (N.encode_named (N.NAll a phi)).
Proof. intro Hphi; exact (Compiler238.derives_all a (N.encode_named phi) Hphi). Qed.

Theorem named_finite_generalize G x a :
  (forall phi, In phi G -> N.free_named x phi = false /\ N.binders_named x phi = false) ->
  H.numeric_context (map N.encode_named G) a ->
  H.numeric_context (map N.encode_named G) (wal x a).
Proof.
  intros HG D; apply H.numeric_context_generalize; [|exact D].
  intros h Hh; apply in_map_iff in Hh as [phi [<- Hphi]].
  destruct (HG phi Hphi) as [Hfree Hbind].
  apply named_vacuity; assumption.
Qed.

Definition rename_label x y a := if Nat.eqb a x then y else a.
Fixpoint replace_named x y (phi : N.named_formula) : N.named_formula :=
  match phi with
  | N.NTruth => N.NTruth
  | N.NImp phi psi => N.NImp (replace_named x y phi) (replace_named x y psi)
  | N.NNot phi => N.NNot (replace_named x y phi)
  | N.NMem a b => N.NMem (rename_label x y a) (rename_label x y b)
  | N.NEq a b => N.NEq (rename_label x y a) (rename_label x y b)
  | N.NAll a phi => N.NAll a (replace_named x y phi)
  end.

Lemma replace_named_binders x y v phi :
  N.binders_named v (replace_named x y phi) = N.binders_named v phi.
Proof.
  induction phi; cbn [replace_named N.binders_named]; try reflexivity;
    now rewrite ?IHphi, ?IHphi1, ?IHphi2.
Qed.

Lemma renamed_label_avoids x y a : x <> y -> Nat.eqb x (rename_label x y a) = false.
Proof.
  intro Hxy; unfold rename_label; destruct (Nat.eqb a x) eqn:E.
  - apply Nat.eqb_neq; exact Hxy.
  - apply Nat.eqb_neq; apply Nat.eqb_neq in E; congruence.
Qed.

Lemma replace_named_free x y phi : x <> y -> N.free_named x (replace_named x y phi) = false.
Proof.
  intro Hxy; induction phi; cbn [replace_named N.free_named].
  - reflexivity.
  - now rewrite IHphi1, IHphi2.
  - exact IHphi.
  - now rewrite !renamed_label_avoids by exact Hxy.
  - now rewrite !renamed_label_avoids by exact Hxy.
  - rewrite IHphi; apply Bool.andb_false_r.
Qed.

Lemma rename_label_roundtrip x y a : Nat.eqb y a = false ->
  rename_label y x (rename_label x y a) = a.
Proof.
  intro Hya; unfold rename_label; destruct (Nat.eqb a x) eqn:E.
  - apply Nat.eqb_eq in E; subst a; now rewrite Nat.eqb_refl.
  - apply Nat.eqb_neq in Hya; rewrite (proj2 (Nat.eqb_neq a y) ltac:(congruence)); reflexivity.
Qed.

Lemma replace_named_roundtrip x y phi : N.names_named y phi = false ->
  replace_named y x (replace_named x y phi) = phi.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    intro Hy; cbn [replace_named N.names_named] in *.
  - reflexivity.
  - apply Bool.orb_false_iff in Hy as [Hy1 Hy2]; now rewrite (IHphi Hy1), (IHpsi Hy2).
  - now rewrite (IH Hy).
  - apply Bool.orb_false_iff in Hy as [Hy1 Hy2]; now rewrite !rename_label_roundtrip by assumption.
  - apply Bool.orb_false_iff in Hy as [Hy1 Hy2]; now rewrite !rename_label_roundtrip by assumption.
  - apply Bool.orb_false_iff in Hy as [_ Hy]; now rewrite (IH Hy).
Qed.

Lemma named_names_free v phi : N.names_named v phi = false -> N.free_named v phi = false.
Proof.
  intro H; destruct (N.free_named v phi) eqn:E; [|reflexivity].
  apply N.free_named_in_names in E; rewrite H in E; discriminate.
Qed.
Lemma named_names_binders v phi : N.names_named v phi = false -> N.binders_named v phi = false.
Proof.
  intro H; destruct (N.binders_named v phi) eqn:E; [|reflexivity].
  apply N.binders_named_in_names in E; rewrite H in E; discriminate.
Qed.

Lemma rename_label_equality G x y a : H.numeric_context G (weq x y) ->
  H.numeric_context G (weq a (rename_label x y a)).
Proof.
  intro HE; unfold rename_label; destruct (Nat.eqb a x) eqn:E.
  - apply Nat.eqb_eq in E; subst a; exact HE.
  - apply H.numeric_theorem, H.numeric_equality_reflexive.
Qed.

Lemma rename_membership_forward x y a b : Compiler238.derivable
  (wim (weq x y) (wim (wel a b) (wel (rename_label x y a) (rename_label x y b)))).
Proof.
  apply H.numeric_context_empty, H.numeric_deduction, H.numeric_deduction.
  apply H.numeric_context_membership_congruence with (a := a) (b := b).
  - apply rename_label_equality, H.numeric_assumption; right; now left.
  - apply rename_label_equality, H.numeric_assumption; right; now left.
  - apply H.numeric_assumption; now left.
Qed.
Lemma rename_membership_reverse x y a b : Compiler238.derivable
  (wim (weq x y) (wim (wel (rename_label x y a) (rename_label x y b)) (wel a b))).
Proof.
  apply H.numeric_context_empty, H.numeric_deduction, H.numeric_deduction.
  apply H.numeric_context_membership_congruence with
    (a := rename_label x y a) (b := rename_label x y b).
  - apply H.numeric_context_equality_symmetry, rename_label_equality,
      H.numeric_assumption; right; now left.
  - apply H.numeric_context_equality_symmetry, rename_label_equality,
      H.numeric_assumption; right; now left.
  - apply H.numeric_assumption; now left.
Qed.
Lemma rename_equality_forward x y a b : Compiler238.derivable
  (wim (weq x y) (wim (weq a b) (weq (rename_label x y a) (rename_label x y b)))).
Proof.
  apply H.numeric_context_empty, H.numeric_deduction, H.numeric_deduction.
  apply H.numeric_context_equality_congruence with (a := a) (b := b).
  - apply rename_label_equality, H.numeric_assumption; right; now left.
  - apply rename_label_equality, H.numeric_assumption; right; now left.
  - apply H.numeric_assumption; now left.
Qed.
Lemma rename_equality_reverse x y a b : Compiler238.derivable
  (wim (weq x y) (wim (weq (rename_label x y a) (rename_label x y b)) (weq a b))).
Proof.
  apply H.numeric_context_empty, H.numeric_deduction, H.numeric_deduction.
  apply H.numeric_context_equality_congruence with
    (a := rename_label x y a) (b := rename_label x y b).
  - apply H.numeric_context_equality_symmetry, rename_label_equality,
      H.numeric_assumption; right; now left.
  - apply H.numeric_context_equality_symmetry, rename_label_equality,
      H.numeric_assumption; right; now left.
  - apply H.numeric_assumption; now left.
Qed.

(** Equality transports a capture-safe replacement in both directions.
    The universal branch consumes only actual atom-vacuity and R2 proofs. *)
Theorem named_equality_replace x y phi : N.binders_named x phi = false ->
  N.binders_named y phi = false ->
  Compiler238.derivable (wim (weq x y)
    (wim (N.encode_named phi) (N.encode_named (replace_named x y phi)))) /\
  Compiler238.derivable (wim (weq x y)
    (wim (N.encode_named (replace_named x y phi)) (N.encode_named phi))).
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    intros Hx Hy; cbn [replace_named N.encode_named].
  - split; apply H.numeric_context_empty, H.numeric_deduction,
      H.numeric_theorem, H.numeric_I.
  - cbn [N.binders_named] in Hx, Hy.
    apply Bool.orb_false_iff in Hx as [Hx1 Hx2].
    apply Bool.orb_false_iff in Hy as [Hy1 Hy2].
    destruct (IHphi Hx1 Hy1) as [Hphi Hphi']; destruct (IHpsi Hx2 Hy2) as [Hpsi Hpsi'].
    split; apply H.numeric_conditional_implication_congruence; assumption.
  - destruct (IH Hx Hy) as [Hphi Hphi']; split;
      apply H.numeric_conditional_contrapose; assumption.
  - split; [apply rename_membership_forward|apply rename_membership_reverse].
  - split; [apply rename_equality_forward|apply rename_equality_reverse].
  - cbn [N.binders_named] in Hx, Hy.
    apply Bool.orb_false_iff in Hx as [Hxa Hx].
    apply Bool.orb_false_iff in Hy as [Hya Hy].
    apply Nat.eqb_neq in Hxa; apply Nat.eqb_neq in Hya.
    assert (Hv : Compiler238.derivable (wim (weq x y) (wal a (weq x y)))).
    { apply H.numeric_equality_vacuity_code; congruence. }
    destruct (IH Hx Hy) as [Hphi Hphi']; split;
      apply H.numeric_conditional_universal; assumption.
Qed.

Theorem named_universal_instance x y phi : x <> y ->
  N.binders_named x phi = false -> N.binders_named y phi = false ->
  Compiler238.derivable (wim (wal x (N.encode_named phi))
    (N.encode_named (replace_named x y phi))).
Proof.
  intros Hxy Hx Hy.
  set (p := N.encode_named phi).
  set (r := N.encode_named (replace_named x y phi)).
  assert (Hv : Compiler238.derivable (wim r (wal x r))).
  { unfold r; apply named_vacuity.
    - apply replace_named_free; exact Hxy.
    - rewrite replace_named_binders; exact Hx. }
  destruct (named_equality_replace x y phi Hx Hy) as [Hsub _].
  assert (Hperm : Compiler238.derivable (wim p (wim (weq x y) r))).
  { apply H.numeric_context_empty, H.numeric_deduction, H.numeric_deduction.
    assert (Hpr : H.numeric_context (weq x y :: [p]) (wim p r)).
    { apply (H.numeric_context_mp (weq x y :: [p]) (weq x y) (wim p r)).
      - apply H.numeric_assumption; now left.
      - apply H.numeric_theorem; exact Hsub. }
    apply (H.numeric_context_mp (weq x y :: [p]) p r).
    - apply H.numeric_assumption; right; now left.
    - exact Hpr. }
  apply H.numeric_context_empty, H.numeric_deduction.
  apply (H.numeric_existential_elimination [wal x p] x (weq x y) r Hv).
  - apply (H.numeric_forall_mp [wal x p] x p (wim (weq x y) r)).
    + apply H.numeric_assumption; now left.
    + apply H.numeric_theorem; exact (Compiler238.derives_all x _ Hperm).
  - apply H.numeric_theorem; exact (Compiler238.derives_r1 x y).
Qed.

(** Renaming an outer binder uses actual universal instantiation and finite
    generalization. The two freshness conditions exclude inner capture;
    no semantic equality or alpha-conversion supplier is assumed. *)
Theorem named_universal_alpha x y phi : x <> y ->
  N.binders_named x phi = false -> N.names_named y phi = false ->
  Compiler238.derivable
    (wim (wal x (N.encode_named phi))
         (wal y (N.encode_named (replace_named x y phi)))) /\
  Compiler238.derivable
    (wim (wal y (N.encode_named (replace_named x y phi)))
         (wal x (N.encode_named phi))).
Proof.
  intros Hxy Hx Hy.
  assert (Hyb : N.binders_named y phi = false) by (apply named_names_binders; exact Hy).
  assert (Hyf : N.free_named y phi = false) by (apply named_names_free; exact Hy).
  assert (Hyr : N.binders_named y (replace_named x y phi) = false).
  { rewrite replace_named_binders; exact Hyb. }
  assert (Hxr : N.binders_named x (replace_named x y phi) = false).
  { rewrite replace_named_binders; exact Hx. }
  split.
  - apply H.numeric_context_empty, H.numeric_deduction.
    apply H.numeric_context_generalize.
    + intros h [<-|[]]; apply (named_vacuity y (N.NAll x phi)).
      * cbn [N.free_named]; rewrite Hyf; apply Bool.andb_false_r.
      * cbn [N.binders_named].
        rewrite (proj2 (Nat.eqb_neq y x) ltac:(congruence)), Hyb; reflexivity.
    + apply (H.numeric_context_mp [wal x (N.encode_named phi)]
        (wal x (N.encode_named phi)) (N.encode_named (replace_named x y phi))).
      * apply H.numeric_assumption; now left.
      * apply H.numeric_theorem, named_universal_instance; assumption.
  - assert (Hinst : Compiler238.derivable
      (wim (wal y (N.encode_named (replace_named x y phi))) (N.encode_named phi))).
    { rewrite <- (replace_named_roundtrip x y phi Hy) at 2.
      apply named_universal_instance; congruence. }
    apply H.numeric_context_empty, H.numeric_deduction.
    apply H.numeric_context_generalize.
    + intros h [<-|[]]; apply (named_vacuity x (N.NAll y (replace_named x y phi))).
      * cbn [N.free_named]; rewrite replace_named_free by exact Hxy.
        apply Bool.andb_false_r.
      * cbn [N.binders_named].
        rewrite (proj2 (Nat.eqb_neq x y) Hxy), Hxr; reflexivity.
    + apply (H.numeric_context_mp [wal y (N.encode_named (replace_named x y phi))]
        (wal y (N.encode_named (replace_named x y phi))) (N.encode_named phi)).
      * apply H.numeric_assumption; now left.
      * apply H.numeric_theorem; exact Hinst.
Qed.

Theorem named_existential_alpha x y phi : x <> y ->
  N.binders_named x phi = false -> N.names_named y phi = false ->
  Compiler238.derivable
    (wim (wex x (N.encode_named phi))
         (wex y (N.encode_named (replace_named x y phi)))) /\
  Compiler238.derivable
    (wim (wex y (N.encode_named (replace_named x y phi)))
         (wex x (N.encode_named phi))).
Proof.
  intros Hxy Hx Hy.
  destruct (named_universal_alpha x y (N.NNot phi) Hxy Hx Hy) as [Hf Hb].
  cbn [replace_named N.encode_named] in Hf, Hb.
  unfold wex; split; apply H.numeric_contrapose; assumption.
Qed.

Lemma rename_label_free_outside x y v a : v <> x -> v <> y ->
  Nat.eqb v (rename_label x y a) = Nat.eqb v a.
Proof.
  intros Hvx Hvy; unfold rename_label; destruct (Nat.eqb a x) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E; subst a.
  now rewrite (proj2 (Nat.eqb_neq v y) Hvy), (proj2 (Nat.eqb_neq v x) Hvx).
Qed.

Lemma replace_named_free_outside x y v phi : v <> x -> v <> y ->
  N.free_named v (replace_named x y phi) = N.free_named v phi.
Proof.
  intros Hvx Hvy; induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    cbn [replace_named N.free_named].
  - reflexivity.
  - now rewrite IHphi, IHpsi.
  - exact IH.
  - now rewrite !rename_label_free_outside by assumption.
  - now rewrite !rename_label_free_outside by assumption.
  - now rewrite IH.
Qed.

Lemma named_names_split v phi :
  N.names_named v phi = N.free_named v phi || N.binders_named v phi.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    cbn [N.names_named N.free_named N.binders_named].
  - reflexivity.
  - rewrite IHphi, IHpsi.
    destruct (N.free_named v phi), (N.free_named v psi),
      (N.binders_named v phi), (N.binders_named v psi); reflexivity.
  - exact IH.
  - now rewrite Bool.orb_false_r.
  - now rewrite Bool.orb_false_r.
  - rewrite IH.
    destruct (Nat.eqb v a), (N.free_named v phi), (N.binders_named v phi); reflexivity.
Qed.

Lemma replace_named_unchanged x y phi : N.names_named x phi = false ->
  replace_named x y phi = phi.
Proof.
  induction phi as [|phi IHphi psi IHpsi|phi IH|a b|a b|a phi IH];
    intro Hx; cbn [N.names_named replace_named] in *.
  - reflexivity.
  - apply Bool.orb_false_iff in Hx as [Hx1 Hx2]; now rewrite (IHphi Hx1), (IHpsi Hx2).
  - now rewrite (IH Hx).
  - apply Bool.orb_false_iff in Hx as [Ha Hb]; apply Nat.eqb_neq in Ha, Hb.
    unfold rename_label; rewrite (proj2 (Nat.eqb_neq a x) ltac:(congruence)),
      (proj2 (Nat.eqb_neq b x) ltac:(congruence)); reflexivity.
  - apply Bool.orb_false_iff in Hx as [Ha Hb]; apply Nat.eqb_neq in Ha, Hb.
    unfold rename_label; rewrite (proj2 (Nat.eqb_neq a x) ltac:(congruence)),
      (proj2 (Nat.eqb_neq b x) ltac:(congruence)); reflexivity.
  - apply Bool.orb_false_iff in Hx as [_ Hx]; now rewrite (IH Hx).
Qed.

Print Assumptions named_vacuity.
Print Assumptions named_output_vacuity.
Print Assumptions named_finite_generalize.
Print Assumptions named_equality_replace.
Print Assumptions named_universal_instance.
Print Assumptions named_universal_alpha.
Print Assumptions named_existential_alpha.
End NumericNamed238.
