(** * PA_F: soundness of the reference calculus for the library's PAeq.
    [Fvalid a]: one fixed list of PAeq axioms proves [dB rho a] for every environment [rho]
    (classical natural deduction).  Main result:
      pprov X a -> Fvalid a,   provided every extra axiom in X is Fvalid. *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import PA.
From Undecidability.FOL.Arithmetics Require Import DeductionFacts.
From PAGB Require Import PALogic PA_dB PA_LMeta.
Import ListNotations.
Unset Implicit Arguments.

Local Notation "A ⊢C phi" := (@prv _ _ falsity_on class A phi) (at level 55).

Ltac ctx := apply Ctx; simpl; tauto.

Lemma mp_weak A phi psi : [] ⊢C phi → psi -> A ⊢C phi -> A ⊢C psi.
Proof. intros H1 H2. eapply IE; [eapply Weak; [exact H1 | intros ? []] | exact H2]. Qed.

Lemma prv_dB_ext A r r' a : (forall v, r v = r' v) -> A ⊢C dB r a -> A ⊢C dB r' a.
Proof. intros E H. now rewrite <- (dB_ext r r' a E). Qed.

Lemma prv_dB_subst2 A r sg tau a :
  A ⊢C (dB r a)[sg][tau] -> A ⊢C dB ((r >> subst_term sg) >> subst_term tau) a.
Proof. intro H. now rewrite !dB_subst in H. Qed.

Ltac env_solve :=
  let v := fresh "v" in
  intros v; unfold shift_env, upd, funcomp;
  repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b) end;
  try subst; cbn; try reflexivity; try (exfalso; congruence);
  rewrite ?subst_term_comp;
  first [ reflexivity
        | apply subst_term_id; intros [|?]; reflexivity
        | symmetry; apply subst_term_id; intros [|?]; reflexivity
        | apply subst_term_ext; intros [|?]; reflexivity ].

(** ** Logical axioms *)
Section LogicAx.
Variable rho : nat -> term.

Lemma nd_B1 a b c : [] ⊢C dB rho (Wim (Wim a b) (Wim (Wim b c) (Wim a c))).
Proof. cbn. apply II, II, II. eapply IE; [ctx|]. eapply IE; [ctx | ctx]. Qed.

Lemma nd_B2 a : [] ⊢C dB rho (Wim (Wim (Wn a) a) a).
Proof. cbn. apply II. apply DN. apply II. eapply IE; [ctx|]. eapply IE; [ctx|]. ctx. Qed.

Lemma nd_B3 a b : [] ⊢C dB rho (Wim a (Wim (Wn a) b)).
Proof. cbn. apply II, II. apply Exp. eapply IE; ctx. Qed.

Lemma nd_B4 x a b : [] ⊢C dB rho (Wim (Wal x (Wim a b)) (Wim (Wal x a) (Wal x b))).
Proof.
  cbn. apply II, II. apply AllI_named. intro t. rewrite dB_inst.
  assert (H1 : [∀ dB (shift_env x rho) a; ∀ (dB (shift_env x rho) a → dB (shift_env x rho) b)]
            ⊢C (dB (shift_env x rho) a → dB (shift_env x rho) b)[t..]) by (apply AllE; ctx).
  assert (H2 : [∀ dB (shift_env x rho) a; ∀ (dB (shift_env x rho) a → dB (shift_env x rho) b)]
            ⊢C (dB (shift_env x rho) a)[t..]) by (apply AllE; ctx).
  cbn in H1. rewrite !dB_inst in H1. rewrite dB_inst in H2.
  eapply IE; eassumption.
Qed.

Lemma nd_B6a z t s : tocc z t = false -> tocc z s = false ->
  [] ⊢C dB rho (Wim (Weq t s) (Wal z (Weq t s))).
Proof.
  intros Ht Hs. cbn [dB]. rewrite !dBt_shift_nocc by assumption.
  apply II, AllI. apply Ctx. cbn. now left.
Qed.

Lemma nd_B6b x y a : [] ⊢C dB rho (Wim (Wal x (Wal y a)) (Wal y (Wal x a))).
Proof.
  cbn [dB]. apply II. apply AllI_named. intro t. cbn. apply AllI_named. intro s.
  rewrite !dB_subst.
  destruct (Nat.eqb_spec x y) as [<-|Hxy].
  - assert (H : [∀ ∀ dB (shift_env x (shift_env x rho)) a]
                ⊢C (∀ dB (shift_env x (shift_env x rho)) a)[t..]) by (apply AllE; ctx).
    cbn in H. apply (AllE s) in H. rewrite !dB_subst in H.
    refine (prv_dB_ext _ _ _ _ _ H). env_solve.
  - assert (H : [∀ ∀ dB (shift_env y (shift_env x rho)) a]
                ⊢C (∀ dB (shift_env y (shift_env x rho)) a)[s..]) by (apply AllE; ctx).
    cbn in H. apply (AllE t) in H. rewrite !dB_subst in H.
    refine (prv_dB_ext _ _ _ _ _ H). env_solve.
Qed.

Lemma nd_B6c x a : [] ⊢C dB rho (Wim (Wex x (Wal x a)) a).
Proof.
  cbn [dB Wex]. apply II. apply DN. apply II.
  eapply IE; [apply Ctx; simpl; right; left; reflexivity|].
  apply AllI_named. intro t. cbn. apply II.
  eapply IE; [apply Ctx; simpl; right; left; reflexivity|].
  match goal with |- prv ?G _ =>
    assert (H : G ⊢C (dB (shift_env x (shift_env x rho)) a)[up (t..)][(rho x)..])
      by (apply AllE; apply Ctx; left; reflexivity) end.
  apply prv_dB_subst2 in H. refine (prv_dB_ext _ _ _ _ _ H). env_solve.
Qed.
End LogicAx.

(** ** Equality and arithmetic, from FAeq *)
Section Eq.
Variable rho : nat -> term.

Lemma FAeq_incl : incl FAeq FAeq.
Proof. apply incl_refl. Qed.

Lemma ctx_incl (B : list form) : incl FAeq (B ++ FAeq).
Proof. apply incl_appr, incl_refl. Qed.

Lemma nd_B7 x t : tocc x t = false -> FAeq ⊢C dB rho (Wex x (Weq (TV x) t)).
Proof.
  intro Ht. cbn [dB Wex dBt]. rewrite dBt_shift_nocc by exact Ht. rewrite shift_env_eq.
  apply II.
  assert (H : ((∀ ($0 == (dBt rho t)`[↑] → ⊥)) :: FAeq) ⊢C ($0 == (dBt rho t)`[↑] → ⊥)[(dBt rho t)..])
    by (apply AllE; ctx).
  cbn in H. rewrite subst_term_shift in H. eapply IE; [exact H|].
  apply (reflexivity class). intros ? ?; simpl; tauto.
Qed.

Lemma nd_E8 t s r : FAeq ⊢C dB rho (Wim (Weq t s) (Wim (Weq t r) (Weq s r))).
Proof.
  cbn [dB]. apply II, II.
  assert (G : incl FAeq (dB rho (Weq t r) :: dB rho (Weq t s) :: FAeq)) by (intros ? ?; simpl; tauto).
  cbn [dB]. eapply (transitivity G).
  - apply (symmetry G). ctx.
  - ctx.
Qed.

Lemma nd_ES t s : FAeq ⊢C dB rho (Wim (Weq t s) (Weq (TS t) (TS s))).
Proof.
  cbn [dB dBt]. apply II.
  assert (G : incl FAeq (dB rho (Weq t s) :: FAeq)) by (intros ? ?; simpl; tauto).
  apply (eq_succ G). ctx.
Qed.

Lemma nd_EPl t s r : FAeq ⊢C dB rho (Wim (Weq t s) (Weq (TP t r) (TP s r))).
Proof.
  cbn [dB dBt]. apply II.
  assert (G : incl FAeq (dB rho (Weq t s) :: FAeq)) by (intros ? ?; simpl; tauto).
  apply (eq_add G); [ctx | apply (reflexivity class G)].
Qed.

Lemma nd_EPr t s r : FAeq ⊢C dB rho (Wim (Weq t s) (Weq (TP r t) (TP r s))).
Proof.
  cbn [dB dBt]. apply II.
  assert (G : incl FAeq (dB rho (Weq t s) :: FAeq)) by (intros ? ?; simpl; tauto).
  apply (eq_add G); [apply (reflexivity class G) | ctx].
Qed.

Lemma nd_EMl t s r : FAeq ⊢C dB rho (Wim (Weq t s) (Weq (TM t r) (TM s r))).
Proof.
  cbn [dB dBt]. apply II.
  assert (G : incl FAeq (dB rho (Weq t s) :: FAeq)) by (intros ? ?; simpl; tauto).
  apply (eq_mult G); [ctx | apply (reflexivity class G)].
Qed.

Lemma nd_EMr t s r : FAeq ⊢C dB rho (Wim (Weq t s) (Weq (TM r t) (TM r s))).
Proof.
  cbn [dB dBt]. apply II.
  assert (G : incl FAeq (dB rho (Weq t s) :: FAeq)) by (intros ? ?; simpl; tauto).
  apply (eq_mult G); [apply (reflexivity class G) | ctx].
Qed.

Lemma nd_QA0 : FAeq ⊢C dB rho QA0.
Proof.
  cbn. change (FAeq ⊢C (zero ⊕ $0 == $0)[(rho 0)..]). apply AllE. ctx.
Qed.

Lemma nd_QAS : FAeq ⊢C dB rho QAS.
Proof. cbn. apply (Add_rec class (incl_refl _)). Qed.

Lemma nd_QM0 : FAeq ⊢C dB rho QM0.
Proof.
  cbn. change (FAeq ⊢C (zero ⊗ $0 == zero)[(rho 0)..]). apply AllE. ctx.
Qed.

Lemma nd_QMS : FAeq ⊢C dB rho QMS.
Proof. cbn. apply (Mult_rec class (incl_refl _)). Qed.

Lemma nd_QZS : [ax_zero_succ] ⊢C dB rho QZS.
Proof.
  cbn. change ([ax_zero_succ] ⊢C (zero == σ $0 → ⊥)[(rho 0)..]). apply AllE. ctx.
Qed.

Lemma nd_QSI : [ax_succ_inj] ⊢C dB rho QSI.
Proof.
  cbn. assert (H : [ax_succ_inj] ⊢C ax_succ_inj) by ctx.
  apply (AllE (rho 0)) in H. apply (AllE (rho 1)) in H. cbn in H.
  rewrite !subst_term_shift in H. exact H.
Qed.
End Eq.

(** ** Induction *)
Section Ind.
Variable rho : nat -> term.

Lemma dB_Wim r a b : dB r (Wim a b) = (dB r a → dB r b). Proof. reflexivity. Qed.
Lemma dB_Wal r x a : dB r (Wal x a) = ∀ dB (shift_env x r) a. Proof. reflexivity. Qed.
Lemma dB_Weq r t s : dB r (Weq t s) = (dBt r t == dBt r s). Proof. reflexivity. Qed.

Definition ind_step (x c : nat) (a : wff) : wff :=
  Wim a (Wal c (Wim (Weq (TV c) (TS (TV x))) (Wal x (Wim (Weq (TV x) (TV c)) a)))).

Lemma IND_unfold x c a :
  dB rho (IND x c a) = ((∀ dB (shift_env x rho) (Wim (Weq (TV x) TZ) a)) →
                        (∀ dB (shift_env x rho) (ind_step x c a)) → ∀ dB (shift_env x rho) a).
Proof. reflexivity. Qed.

Lemma nd_base B x a : incl FAeq B ->
  B ⊢C ∀ dB (shift_env x rho) (Wim (Weq (TV x) TZ) a) -> B ⊢C (dB (shift_env x rho) a)[zero..].
Proof.
  intros GB H. apply (AllE zero) in H. rewrite dB_inst in H. rewrite dB_Wim, dB_Weq in H. cbn [dBt] in H. rewrite upd_eq in H.
  rewrite dB_inst. eapply IE; [exact H | exact (reflexivity class GB zero)].
Qed.

Lemma nd_step B x c a : c <> x -> occ c a = false -> incl FAeq B ->
  B ⊢C ∀ dB (shift_env x rho) (ind_step x c a) ->
  B ⊢C ∀ (dB (shift_env x rho) a → (dB (shift_env x rho) a)[σ $0 .: ↑]).
Proof.
  intros Hcx Hc GB H. apply AllI_named. intro t.
  apply (AllE t) in H. rewrite dB_inst in H. unfold ind_step in H. rewrite dB_Wim, dB_Wal in H.
  change ((dB (shift_env x rho) a → (dB (shift_env x rho) a)[σ $0 .: ↑])[t..])
    with ((dB (shift_env x rho) a)[t..] → (dB (shift_env x rho) a)[σ $0 .: ↑][t..]).
  rewrite dB_inst. apply II.
  assert (GB' : incl FAeq (dB (upd rho x t) a :: B)) by (intros ? ?; right; auto).
  assert (H1 : (dB (upd rho x t) a :: B) ⊢C
               ∀ dB (shift_env c (upd rho x t))
                   (Wim (Weq (TV c) (TS (TV x))) (Wal x (Wim (Weq (TV x) (TV c)) a)))).
  { eapply IE; [eapply Weak; [exact H | intros ? ?; right; auto] | ctx]. }
  apply (AllE (σ t)) in H1. rewrite dB_inst in H1. rewrite dB_Wim, dB_Weq, dB_Wal in H1. cbn [dBt] in H1.
  rewrite upd_eq, (upd_neq _ c _ x) in H1 by congruence. rewrite upd_eq in H1.
  apply (fun h => IE h (reflexivity class GB' (σ t))) in H1.
  apply (AllE (σ t)) in H1. rewrite dB_inst in H1. rewrite dB_Wim, dB_Weq in H1. cbn [dBt] in H1.
  rewrite upd_eq, (upd_neq _ x _ c) in H1 by congruence. rewrite upd_eq in H1.
  apply (fun h => IE h (reflexivity class GB' (σ t))) in H1.
  rewrite !dB_subst.
  assert (E : dB (upd (upd (upd rho x t) c (σ t)) x (σ t)) a =
              dB ((shift_env x rho >> subst_term (σ $0 .: ↑)) >> subst_term (t..)) a).
  { apply dB_ext_occ. intros v Hv. assert (v <> c) by (intros ->; congruence).
    unfold shift_env, upd, funcomp.
    destruct (Nat.eqb_spec v x); [subst; cbn; reflexivity|].
    apply Nat.eqb_neq in H0. rewrite H0. cbn. rewrite !subst_term_comp. symmetry. apply subst_term_id. reflexivity. }
  rewrite E in H1. exact H1.
Qed.

Lemma nd_IND x c a : c <> x -> occ c a = false ->
  (ax_induction (dB (shift_env x rho) a) :: FAeq) ⊢C dB rho (IND x c a).
Proof.
  intros Hcx Hc. rewrite IND_unfold. apply II, II.
  set (B := _ :: _ :: ax_induction (dB (shift_env x rho) a) :: FAeq).
  assert (GB : incl FAeq B) by (intros ? ?; unfold B; simpl; tauto).
  assert (HI : B ⊢C ax_induction (dB (shift_env x rho) a)) by (unfold B; ctx).
  unfold ax_induction in HI. eapply IE; [eapply IE; [exact HI|] |].
  - apply (nd_base B x a GB). unfold B; ctx.
  - apply (nd_step B x c a Hcx Hc GB). unfold B; ctx.
Qed.
End Ind.

Lemma nd_AllE_dB A e x a t : A ⊢C dB e (Wal x a) -> A ⊢C dB (upd e x t) a.
Proof. intro H. rewrite <- dB_inst. exact (AllE t H). Qed.

(** ** Iterated quantifiers in ND *)
Lemma nd_galls_E A ps a e e' : A ⊢C dB e (galls ps a) -> (forall v, ~ In v ps -> e' v = e v) -> A ⊢C dB e' a.
Proof.
  revert e; induction ps as [|p ps IH]; intros e H He; cbn [galls] in H.
  - erewrite dB_ext; [exact H|]. intro v. apply He. intros [].
  - rewrite dB_Wal in H. apply (AllE (e' p)) in H. rewrite dB_inst in H. apply (IH _ H).
    intros v Hv. unfold upd. destruct (Nat.eqb_spec v p); [now subst|]. apply He. intros [->|]; tauto.
Qed.

Lemma nd_galls_I A ps a e : (forall e', (forall v, ~ In v ps -> e' v = e v) -> A ⊢C dB e' a) ->
  A ⊢C dB e (galls ps a).
Proof.
  revert e; induction ps as [|p ps IH]; intros e H; cbn [galls].
  - apply H. reflexivity.
  - rewrite dB_Wal. apply AllI_named. intro t. rewrite dB_inst. apply IH.
    intros e' He'. apply H. intros v Hv. rewrite He' by (intro; apply Hv; now right).
    apply upd_neq. intros ->. apply Hv. now left.
Qed.

(** ** Induction with parameters, from one parameter-free instance *)
Section IndClosed.
Variables (x c : nat) (a : wff).
Hypothesis Hcx : c <> x.
Hypothesis Hc : occ c a = false.

Definition ind_body : wff := Wim (Wal x (Wim (Weq (TV x) TZ) a)) (Wim (Wal x (ind_step x c a)) a).
Definition ind_ps : list nat := filter (fun v => negb (Nat.eqb v x)) (seq 0 (S (maxv ind_body))).
Definition ind_theta : wff := galls ind_ps ind_body.
Definition ind_psi : form := dB (shift_env x var) ind_theta.

Lemma ind_theta_fr v : fr v ind_theta = true -> v = x.
Proof.
  intro H. apply fr_galls in H as [H1 H2]. destruct (Nat.eqb_spec v x) as [|Hv]; [assumption|].
  exfalso. apply H1. unfold ind_ps. apply filter_In. split.
  - apply in_seq. apply fr_occ, occ_maxv in H2. lia.
  - now apply negb_true_iff, Nat.eqb_neq.
Qed.

Lemma ind_psi_env rho : dB (shift_env x rho) ind_theta = ind_psi.
Proof.
  unfold ind_psi. apply dB_ext_fr. intros v Hv. apply ind_theta_fr in Hv as ->.
  now rewrite !shift_env_eq.
Qed.

Lemma x_notin_ps : ~ In x ind_ps.
Proof. unfold ind_ps. intros [_ H]%filter_In. rewrite Nat.eqb_refl in H. discriminate. Qed.

(** from a(u), the step hypothesis gives a(S u) *)
Lemma nd_step_inst B e u : incl FAeq B ->
  B ⊢C dB e (Wal x (ind_step x c a)) -> B ⊢C dB (upd e x u) a -> B ⊢C dB (upd e x (σ u)) a.
Proof.
  intros GB H Ha. rewrite dB_Wal in H. apply (AllE u) in H. rewrite dB_inst in H.
  unfold ind_step in H. rewrite dB_Wim, dB_Wal in H. apply (fun h => IE h Ha) in H.
  apply (AllE (σ u)) in H. rewrite dB_inst in H. rewrite dB_Wim, dB_Weq, dB_Wal in H. cbn [dBt] in H.
  rewrite upd_eq, (upd_neq _ c _ x) in H by congruence. rewrite upd_eq in H.
  apply (fun h => IE h (reflexivity class GB (σ u))) in H.
  apply (AllE (σ u)) in H. rewrite dB_inst in H. rewrite dB_Wim, dB_Weq in H. cbn [dBt] in H.
  rewrite upd_eq, (upd_neq _ x _ c) in H by congruence. rewrite upd_eq in H.
  apply (fun h => IE h (reflexivity class GB (σ u))) in H.
  erewrite dB_ext_occ; [exact H|]. intros v Hv. assert (v <> c) by (intros ->; congruence).
  unfold upd. destruct (Nat.eqb_spec v x); [reflexivity|]. apply Nat.eqb_neq in H0. now rewrite H0.
Qed.

Lemma nd_IND_closed rho : (ax_induction ind_psi :: FAeq) ⊢C dB rho (IND x c a).
Proof.
  rewrite IND_unfold. apply II, II.
  set (B := _ :: _ :: ax_induction ind_psi :: FAeq).
  assert (GB : incl FAeq B) by (intros ? ?; unfold B; simpl; tauto).
  assert (H1 : B ⊢C dB rho (Wal x (Wim (Weq (TV x) TZ) a))) by (unfold B; ctx).
  assert (H2 : B ⊢C dB rho (Wal x (ind_step x c a))) by (unfold B; ctx).
  assert (HI : B ⊢C ax_induction ind_psi) by (unfold B; ctx).
  rewrite <- (ind_psi_env rho) in HI. unfold ax_induction in HI.
  apply AllI_named. intro t. rewrite dB_inst.
  assert (HA : B ⊢C ∀ dB (shift_env x rho) ind_theta).
  { eapply IE; [eapply IE; [exact HI|] |].
    - (* base *)
      rewrite dB_inst. apply nd_galls_I. intros e' He'.
      assert (Ex : e' x = zero) by (rewrite He' by apply x_notin_ps; apply upd_eq).
      unfold ind_body. rewrite !dB_Wim. apply II, II.
      assert (H : (dB e' (Wal x (ind_step x c a)) :: dB e' (Wal x (Wim (Weq (TV x) TZ) a)) :: B)
                  ⊢C dB e' (Wal x (Wim (Weq (TV x) TZ) a))) by ctx.
      apply (nd_AllE_dB _ _ _ _ zero) in H. rewrite dB_Wim, dB_Weq in H. cbn [dBt] in H.
      rewrite upd_eq in H. apply (fun h => IE h (reflexivity class (incl_tl _ (incl_tl _ GB)) zero)) in H.
      refine (prv_dB_ext _ _ _ _ _ H). intro v. unfold upd. destruct (Nat.eqb_spec v x); [subst; now rewrite Ex|reflexivity].
    - (* step *)
      apply AllI_named. intro u.
      change ((dB (shift_env x rho) ind_theta → (dB (shift_env x rho) ind_theta)[σ $0 .: ↑])[u..])
        with ((dB (shift_env x rho) ind_theta)[u..] → (dB (shift_env x rho) ind_theta)[σ $0 .: ↑][u..]).
      rewrite dB_inst, !dB_subst. apply II.
      assert (Env : forall v, ((shift_env x rho >> subst_term (σ $0 .: ↑)) >> subst_term (u..)) v
                              = upd rho x (σ u) v).
      { intro v. unfold shift_env, upd, funcomp. destruct (Nat.eqb v x); cbn; [reflexivity|].
        rewrite !subst_term_comp. apply subst_term_id. reflexivity. }
      rewrite (dB_ext _ _ _ Env). apply nd_galls_I. intros e' He'.
      assert (Ex : e' x = σ u) by (rewrite He' by apply x_notin_ps; apply upd_eq).
      set (B' := dB (upd rho x u) ind_theta :: B).
      assert (GB' : incl FAeq B') by (intros ? ?; right; auto).
      assert (IH : B' ⊢C dB (upd e' x u) ind_body).
      { apply (nd_galls_E _ ind_ps _ (upd rho x u)); [unfold B'; ctx|].
        intros v Hv. unfold upd. destruct (Nat.eqb_spec v x); [reflexivity|]. rewrite He' by exact Hv.
        apply upd_neq, n. }
      unfold ind_body in IH |- *. rewrite !dB_Wim in IH |- *. rewrite !dB_Wal_upd_same in IH.
      apply II, II.
      set (B2 := _ :: _ :: B').
      assert (GB2 : incl FAeq B2) by (intros ? ?; right; right; auto).
      assert (Hu : B2 ⊢C dB (upd e' x u) a).
      { eapply IE; [eapply IE; [eapply Weak; [exact IH | intros ? ?; right; right; auto] |] |];
          unfold B2; ctx. }
      apply (nd_step_inst B2 e' u GB2) in Hu; [|unfold B2; ctx].
      refine (prv_dB_ext _ _ _ _ _ Hu). intro v. unfold upd. destruct (Nat.eqb_spec v x); [subst; now rewrite Ex|reflexivity]. }
  apply (AllE t) in HA. rewrite dB_inst in HA.
  apply (nd_galls_E _ ind_ps _ _ (upd rho x t)) in HA; [|reflexivity].
  unfold ind_body in HA. rewrite !dB_Wim, !dB_Wal_upd_same in HA.
  eapply IE; [eapply IE; [exact HA | exact H1] | exact H2].
Qed.
End IndClosed.

(** ** Validity in a theory T containing PAeq *)
Section Th.
Variable T : form -> Prop.
Hypothesis HT : forall psi, PAeq psi -> T psi.

Definition good_list (A : list form) : Prop := forall psi, In psi A -> T psi.

Definition Fvalid (a : wff) : Prop := exists A, good_list A /\ forall rho, A ⊢C dB rho a.

Lemma good_FAeq : good_list FAeq.
Proof. intros psi H. now apply HT, PAeq_FA. Qed.

Lemma Fvalid_of A (a : wff) : good_list A -> (forall rho, A ⊢C dB rho a) -> Fvalid a.
Proof. intros G H. now exists A. Qed.

Lemma Fvalid_FAeq (a : wff) : (forall rho, FAeq ⊢C dB rho a) -> Fvalid a.
Proof. apply Fvalid_of, good_FAeq. Qed.

Lemma Fvalid_nil (a : wff) : (forall rho, [] ⊢C dB rho a) -> Fvalid a.
Proof. intro H. apply Fvalid_FAeq. intro rho. eapply Weak; [apply H | intros ? []]. Qed.

Lemma Fvalid_mp a b : Fvalid (Wim a b) -> Fvalid a -> Fvalid b.
Proof.
  intros [A1 [G1 H1]] [A2 [G2 H2]]. exists (A1 ++ A2). split.
  - intros psi [Hp|Hp]%in_app_iff; auto.
  - intro rho. eapply IE.
    + eapply Weak; [apply (H1 rho) | apply incl_appl, incl_refl].
    + eapply Weak; [apply (H2 rho) | apply incl_appr, incl_refl].
Qed.

Lemma Fvalid_gen x a : Fvalid a -> Fvalid (Wal x a).
Proof.
  intros [A [G H]]. exists A. split; [exact G|]. intro rho. rewrite dB_Wal.
  apply AllI_named. intro t. rewrite dB_inst. apply H.
Qed.

End Th.

(** ** Soundness *)
Section Sound.
Variable T : form -> Prop.
Hypothesis HT : forall psi, PAeq psi -> T psi.
Variable X : wff -> Prop.
Hypothesis HX : forall b, X b -> Fvalid T b.

Theorem pprov_Fvalid a : pprov X a -> Fvalid T a.
Proof.
  induction 1.
  - now apply HX.
  - eapply (Fvalid_mp T); eassumption.
  - now apply (Fvalid_gen T).
  - apply Fvalid_nil; [exact HT|]. intro; apply nd_B1.
  - apply Fvalid_nil; [exact HT|]. intro; apply nd_B2.
  - apply Fvalid_nil; [exact HT|]. intro; apply nd_B3.
  - apply Fvalid_nil; [exact HT|]. intro; apply nd_B4.
  - apply Fvalid_nil; [exact HT|]. intro; now apply nd_B6a.
  - apply Fvalid_nil; [exact HT|]. intro; apply nd_B6b.
  - apply Fvalid_nil; [exact HT|]. intro; apply nd_B6c.
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_B7. cbn. apply Nat.eqb_neq. congruence.
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_B7, tcode_nocc.
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_E8.
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_ES.
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_EPl.
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_EPr.
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_EMl.
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_EMr.
  - apply (Fvalid_of T (ax_zero_succ :: nil)); [intros ? [<-|[]]; apply HT, PAeq_discr | intro; apply nd_QZS].
  - apply (Fvalid_of T (ax_succ_inj :: nil)); [intros ? [<-|[]]; apply HT, PAeq_inj | intro; apply nd_QSI].
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_QA0.
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_QAS.
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_QM0.
  - apply Fvalid_FAeq; [exact HT|]. intro; apply nd_QMS.
  - rename x into x0. rename a into a0.
    apply (Fvalid_of T (ax_induction (ind_psi x0 (fcode a0) a0) :: FAeq)).
    + intros psi [<-|Hp]; [apply HT, PAeq_induction | now apply (good_FAeq T HT)].
    + intro rho. apply nd_IND_closed; [lia | apply fcode_nocc].
Qed.
End Sound.

Print Assumptions pprov_Fvalid.
