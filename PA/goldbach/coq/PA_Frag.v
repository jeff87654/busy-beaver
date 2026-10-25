(** * PA_Frag: classical translation of the full syntax into the {→, ⊥, ∀} fragment, which is the image
    of the named calculus:  A ∧ B ↦ ¬(A → ¬B),  A ∨ B ↦ ¬A → B,  ∃A ↦ ¬∀¬A.
    [to_frag_iff]: a formula and its translation are interderivable (classical ND, any context). *)
From Coq Require Import Arith Lia List.
From Undecidability.FOL Require Import PA.
Import ListNotations.
Unset Implicit Arguments.

Local Notation "A ⊢C phi" := (@prv _ _ falsity_on class A phi) (at level 55).

Fixpoint to_frag {ff : falsity_flag} (phi : @Core.form _ _ _ ff)
  : @Core.form PA_funcs_signature PA_preds_signature full_operators falsity_on :=
  match phi in Core.form _ _ _ b return @Core.form PA_funcs_signature PA_preds_signature full_operators falsity_on with
  | falsity => falsity
  | atom P v => @atom _ _ _ falsity_on P v
  | bin Conj a b => ¬ (to_frag a → ¬ to_frag b)
  | bin Disj a b => ¬ to_frag a → to_frag b
  | bin Impl a b => to_frag a → to_frag b
  | quant All a => ∀ to_frag a
  | quant Ex a => ¬ ∀ ¬ to_frag a
  end.

Lemma to_frag_subst {ff : falsity_flag} (phi : @Core.form _ _ _ ff) sg : (to_frag phi)[sg] = to_frag (phi[sg]).
Proof.
  revert sg; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intro sg; cbn; try reflexivity.
  - destruct op; cbn; now rewrite IHa, IHb.
  - destruct q; cbn; now rewrite IHa.
Qed.

Lemma up_shift_inst (phi : form) : phi[up ↑][$0..] = phi.
Proof.
  rewrite subst_comp. apply subst_id. intros [|n]; reflexivity.
Qed.

Ltac ctx := apply Ctx; simpl; tauto.

Lemma prv_shift A phi : A ⊢C phi -> map (subst_form ↑) A ⊢C phi[↑].
Proof. apply subst_Weak. Qed.

Definition FI {ff : falsity_flag} : @Core.form _ _ _ ff -> Prop :=
  match ff with
  | falsity_on => fun phi => forall A, (A ⊢C phi -> A ⊢C to_frag phi) /\ (A ⊢C to_frag phi -> A ⊢C phi)
  | falsity_off => fun _ => True
  end.

Lemma to_frag_FI {ff : falsity_flag} (phi : @Core.form _ _ _ ff) : FI phi.
Proof.
  induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; [cbn; tauto | destruct ff; cbn; tauto | |].
  - destruct ff; [exact I|]. cbn in IHa, IHb |- *. intro A. destruct op; cbn.
    + split; intro H.
      * apply II. eapply IE.
        -- eapply IE; [ctx|]. apply (proj1 (IHa _)). eapply CE1, Weak; [exact H | intros ? ?; now right].
        -- apply (proj1 (IHb _)). eapply CE2, Weak; [exact H | intros ? ?; now right].
      * apply CI.
        -- apply (proj2 (IHa _)). apply DN. apply II. eapply IE; [eapply Weak; [exact H | intros ? ?; now right]|].
           apply II. apply Exp. eapply IE; [apply Ctx; right; now left | ctx].
        -- apply (proj2 (IHb _)). apply DN. apply II. eapply IE; [eapply Weak; [exact H | intros ? ?; now right]|].
           apply II. ctx.
    + split; intro H.
      * apply II. eapply DE; [eapply Weak; [exact H | intros ? ?; now right] | |].
        -- apply Exp. eapply IE; [apply Ctx; right; now left|]. apply (proj1 (IHa _)). ctx.
        -- apply (proj1 (IHb _)). ctx.
      * eapply IE; [|apply (XM _ (to_frag a))]. apply II. eapply DE; [ctx| |].
        -- apply DI1. apply (proj2 (IHa _)). ctx.
        -- apply DI2. apply (proj2 (IHb _)). eapply IE; [eapply Weak; [exact H | intros ? ?; right; now right] | ctx].
    + split; intro H.
      * apply II. apply (proj1 (IHb _)). eapply IE; [eapply Weak; [exact H | intros ? ?; now right]|].
        apply (proj2 (IHa _)). ctx.
      * apply II. apply (proj2 (IHb _)). eapply IE; [eapply Weak; [exact H | intros ? ?; now right]|].
        apply (proj1 (IHa _)). ctx.
  - destruct ff; [exact I|]. cbn in IHa |- *. intro A. destruct q; cbn.
    + split; intro H; apply AllI.
      * apply (proj1 (IHa _)). apply prv_shift in H. cbn in H. apply (AllE ($0)) in H.
        now rewrite up_shift_inst in H.
      * apply (proj2 (IHa _)). apply prv_shift in H. cbn in H. apply (AllE ($0)) in H.
        now rewrite up_shift_inst in H.
    + split; intro H.
      * apply II. eapply ExE; [eapply Weak; [exact H | intros ? ?; now right]|].
        cbn. match goal with |- prv ?G _ =>
          assert (Hn : G ⊢C (¬ (to_frag a)[up ↑])[$0..]) by (apply AllE; apply Ctx; right; now left) end.
        cbn in Hn. rewrite up_shift_inst in Hn. eapply IE; [exact Hn|]. apply (proj1 (IHa _)). ctx.
      * apply DN. apply II. eapply IE; [eapply Weak; [exact H | intros ? ?; now right]|].
        apply AllI. apply II. cbn. eapply IE; [apply Ctx; right; now left|].
        apply (ExI ($0)). rewrite up_shift_inst. apply (proj2 (IHa _)). ctx.
Qed.

Lemma to_frag_l A (phi : form) : A ⊢C phi -> A ⊢C to_frag phi.
Proof. apply (to_frag_FI phi). Qed.

Lemma to_frag_r A (phi : form) : A ⊢C to_frag phi -> A ⊢C phi.
Proof. apply (to_frag_FI phi). Qed.
