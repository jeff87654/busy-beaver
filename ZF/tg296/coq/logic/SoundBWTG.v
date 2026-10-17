(** * SoundBWTG: the m254tg bundle wffs are valid in SUIR (port of ZF/m254/coq/logic/SoundBW254.v).

    [V a] := Fvalid SUIR a  (one fixed list of SUIR axioms proves dB rho a for every environment rho).
    Main lemma:  c <> a -> c <> b -> fr c phi = false -> fr (S c) phi = false -> V (BW a b c phi).
    The universe w (and T, Q, p∈w) always comes from the closed UG' instance for the matrix
    thetaW3 a b phi; the collision cases (design/machine.md section 3):
      b = S c : the top guard is x∈x, refuted by IR;
      a = b   : C := an empty set (nx clause of UG'(⊥)), U := p, cl1's guard a∈a refuted by IR;
      a = S c : H' (y∈a) gives the instance's hypothesis (y∈w) by transitivity of w;
      0 ∈ {a,b} or c = 0 : the f binder is shadowed / unused (handled by sab3 and theta_inst3). *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_F Std_tr Std_H Std_alpha Std_gen
  Std_iface Std_iface2 Std_setnd Std_setbase Std_glue Std_breq Std_brnd Std_brrep.
From M254S Require Import S_def.
From M254TG Require Import SU_def.
From M254TGL Require Import BundleTG.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Lemma SUIR_EqAx psi : In psi EqAx -> SUIR psi.
Proof. intros H. left. apply SU0_base. rewrite SUbase_EqAx. exact H. Qed.

Lemma SUIR_ug n th : closedf (forall_times n (ug th)) -> SUIR (forall_times n (ug th)).
Proof. intros H. left. now apply SU0_ug. Qed.

Definition V (a : wff) : Prop := Fvalid SUIR a.

Lemma V_mp a b : V (Wim a b) -> V a -> V b.
Proof.
  intros [A1 [G1 H1]] [A2 [G2 H2]]. exists (A1 ++ A2). split.
  - intros psi [Hp|Hp]%in_app_iff; auto.
  - intro rho. eapply IE.
    + eapply Weak; [apply (H1 rho) | apply incl_appl, incl_refl].
    + eapply Weak; [apply (H2 rho) | apply incl_appr, incl_refl].
Qed.

Lemma V_gen x a : V a -> V (Wal x a).
Proof.
  intros [A [G H]]. exists A. split; [exact G|]. intro rho. cbn [dB]. apply AllI_named. intro t.
  rewrite dB_inst. apply H.
Qed.

Lemma V_lprov a : lprov a -> V a.
Proof.
  induction 1 as [a b _ IH1 _ IH2 | x a _ IH | a b c | a | a b | x a b | x y z Hxz Hyz
                  | x y a | x a | x y | x y z | x y z | x y z].
  - exact (V_mp _ _ IH1 IH2).
  - now apply V_gen.
  - apply (@Fvalid_nil SUIR SUIR_EqAx). intro; apply nd_B1.
  - apply (@Fvalid_nil SUIR SUIR_EqAx). intro; apply nd_B2.
  - apply (@Fvalid_nil SUIR SUIR_EqAx). intro; apply nd_B3.
  - apply (@Fvalid_nil SUIR SUIR_EqAx). intro; apply nd_B4.
  - apply (@Fvalid_nil SUIR SUIR_EqAx). intro; now apply nd_B6a.
  - apply (@Fvalid_nil SUIR SUIR_EqAx). intro; apply nd_B6b.
  - apply (@Fvalid_nil SUIR SUIR_EqAx). intro; apply nd_B6c.
  - apply (@Fvalid_EqAx SUIR SUIR_EqAx). intro; apply nd_B7.
  - apply (@Fvalid_EqAx SUIR SUIR_EqAx). intro; apply nd_B8a.
  - apply (@Fvalid_EqAx SUIR SUIR_EqAx). intro; apply nd_B8b.
  - apply (@Fvalid_EqAx SUIR SUIR_EqAx). intro; apply nd_B8c.
Qed.

Lemma V_ir : V (Wal 1 (Wn (Wel 1 1))).
Proof.
  exists [ax_ir]. split; [intros psi [<-|[]]; now right|].
  intro rho. apply Ctx. left. reflexivity.
Qed.

(** ** Helpers (local: Comp_BundleTG has its own copies) *)
Local Lemma sb_dB_el (rho : nat -> term) x y : dB rho (Wel x y) = rho x ∈' rho y.
Proof. reflexivity. Qed.
Local Lemma sb_dB_eqq (rho : nat -> term) x y : dB rho (Weq x y) = rho x ≡' rho y.
Proof. reflexivity. Qed.

Local Ltac envs := repeat first [ rewrite upd_eq | rewrite upd_neq by lia ].
Local Ltac envs_in H := repeat first [ rewrite upd_eq in H | rewrite upd_neq in H by lia ].

(** ** Atomic vacuity (V= /\ V-in) *)
Lemma VBVt a b c rho : c <> a -> c <> b -> [] ⊢C dB rho (BVt a b c).
Proof.
  intros H1 H2. unfold BVt. apply dB_andI.
  - apply dB_impI. ctx_push H. apply dB_allI. intros t. rewrite sb_dB_eqq in *. envs. exact H.
  - apply dB_impI. ctx_push H. apply dB_allI. intros t. rewrite sb_dB_el in *. envs. exact H.
Qed.

Local Lemma sb_ir_inst G x : In ax_ir G -> G ⊢C ¬ x ∈' x.
Proof. intros H. exact (AllE x (Ctx H)). Qed.

(** ** The matrix of the UG' instance: a -> $0 (input), b -> $1 (output), 0 -> $2 (f), v -> $(3+v) *)
Definition sab3 (a b : nat) (v : nat) : term :=
  if Nat.eqb v a then $0 else if Nat.eqb v b then $1 else if Nat.eqb v 0 then $2 else $(3 + v).
Definition thetaW3 (a b : nat) (phi : wff) : form := dB (sab3 a b) phi.

Lemma fb_theta3 a b phi : fb (maxfr phi + 4) (thetaW3 a b phi).
Proof.
  apply fb_dB. intros v Hv. apply fr_maxfr in Hv. unfold sab3.
  destruct (Nat.eqb v a); [cbn; lia|]. destruct (Nat.eqb v b); [cbn; lia|].
  destruct (Nat.eqb v 0); cbn; lia.
Qed.

Lemma theta_inst3 a b phi (tau e : nat -> term) : a <> b ->
  tau 0 = e a -> tau 1 = e b -> (fr 0 phi = true -> 0 <> a -> 0 <> b -> tau 2 = e 0) ->
  (forall v, fr v phi = true -> v <> a -> v <> b -> v <> 0 -> tau (3 + v) = e v) ->
  (thetaW3 a b phi)[tau] = dB e phi.
Proof.
  intros Hab E0 E1 E2 Ev. unfold thetaW3. rewrite dB_subst. apply dB_ext_fr. intros v Hv.
  unfold sab3, funcomp. destruct (Nat.eqb_spec v a) as [->|Ha]; [exact E0|].
  destruct (Nat.eqb_spec v b) as [->|Hb]; [exact E1|].
  destruct (Nat.eqb_spec v 0) as [->|H0]; cbn; [now apply E2 | now apply Ev].
Qed.

Local Ltac tcase := repeat match goal with |- context [?t`[_]] => is_var t; destruct t as [?|[]] end.

(* normalize a stacked substitution instance of thetaW3 to dB e phi *)
Local Ltac thw3 Hab c Hfr Hfr' rho := rewrite ?subst_comp; apply theta_inst3; [exact Hab | | | |];
  [ unfold funcomp; cbn; envs; tcase; cbn; reflexivity
  | unfold funcomp; cbn; envs; tcase; cbn; reflexivity
  | let Hf0 := fresh in let H0a := fresh in let H0b := fresh in intros Hf0 H0a H0b;
    assert (c <> 0) by (intros ->; rewrite Hfr in Hf0; discriminate);
    unfold funcomp; cbn; envs; tcase; cbn; reflexivity
  | let v := fresh "v" in let Hv := fresh "Hv" in let H1 := fresh in let H2 := fresh in
    let H3 := fresh in
    intros v Hv H1 H2 H3;
    assert (v <> c) by (intros ->; rewrite Hfr in Hv; discriminate);
    assert (v <> S c) by (intros ->; rewrite Hfr' in Hv; discriminate);
    unfold funcomp; cbn; envs; unfold funcomp; destruct (rho v) as [?|[]]; cbn; reflexivity ].

Lemma closed_ug_theta3 a b phi : closedf (forall_times (maxfr phi + 1) (ug (thetaW3 a b phi))).
Proof. apply ug_closed. replace (S (S (S (maxfr phi + 1)))) with (maxfr phi + 4) by lia. apply fb_theta3. Qed.

Lemma closed_ug_false : closedf (forall_times 0 (ug falsity)).
Proof. apply ug_closed. exact I. Qed.

(** an empty set (from the nx clause of UG'(⊥) at the point B := t) *)
Lemma sb_empty G (t : term) : In (forall_times 0 (ug falsity)) G ->
  G ⊢C ∃ (∀ ($0 ∈' $1 → ⊥)).
Proof.
  intros Hin. pose proof (closed_inst G _ _ var closed_ug_false (Ctx Hin)) as H.
  unfold ug in H. cbn in H. finst H t. fex H w Hw. fdestr Hw H1 H2. fdestr H1 Hp Hx.
  finst H2 t t. fmp H2 Hp. fex H2 C HC. fdestr HC HC12 Hb. fdestr HC12 Hc Hnx.
  fexists C. fall y. apply II. ctx_push Hy. simp_in Hy. finst Hnx y. fmp Hnx Hy. fex Hnx z Hz. exact Hz.
Qed.

(** ** The bundle wffs are valid in SUIR *)
Theorem V_BW a b c phi : c <> a -> c <> b -> fr c phi = false -> fr (S c) phi = false -> V (BW a b c phi).
Proof.
  intros Hca Hcb Hfr Hfr'.
  set (n := maxfr phi + 1).
  set (thU := forall_times n (ug (thetaW3 a b phi))).
  set (th0 := forall_times 0 (ug falsity)).
  pose (A := [ax_ir; th0; thU]).
  exists A. split.
  { intros psi [<-|[<-|[<-|[]]]]; [now right | exact (SUIR_ug _ _ closed_ug_false)
                                   | exact (SUIR_ug _ _ (closed_ug_theta3 a b phi))]. }
  intros rho. unfold BW. apply dB_andI; [|eapply Weak; [apply (VBVt a b c rho Hca Hcb) | intros ? []]].
  assert (HI : In ax_ir A) by (unfold A; simpl; tauto).
  assert (H0 : In th0 A) by (unfold A; simpl; tauto).
  assert (HU : In thU A) by (unfold A; simpl; tauto).
  clearbody A. rename A into G.
  pose proof (closed_inst G _ _ rho (closed_ug_theta3 a b phi) (Ctx HU)) as H.
  unfold ug in H. cbn in H. finst H (rho c). fex H w Hw. fdestr Hw H1 H2. fdestr H1 Hp HT.
  unfold UGW. apply (dB_exI _ _ _ w). apply dB_andI;
    [|rewrite sb_dB_el; envs; exact Hp].
  apply dB_allI. intros f. apply dB_allI. intros x. apply dB_impI. ctx_push Hx.
  rewrite sb_dB_el in Hx.
  destruct (Nat.eq_dec b (S c)) as [Eb|Eb].
  { (* b = S c: the guard is x ∈ x *)
    subst b. envs_in Hx. fabsurd. exact (IE (sb_ir_inst _ x HI) Hx). }
  envs_in Hx.
  pose proof HT as HT0.
  apply dB_andI.
  2:{ (* T /\ Q *)
    finst HT x. fmp HT Hx. fdestr HT HTt HTq. apply dB_andI.
    - unfold WT. apply dB_allI. intros u. apply dB_impI. ctx_push Hu. rewrite sb_dB_el in *.
      envs_in Hu. envs. finst HTt u. exact (IE HTt Hu).
    - unfold WQ. fex HTq W HW. fdestr HW HWw HWz. apply (dB_exI _ _ _ W). apply dB_andI.
      + apply dB_allI. intros z. apply dB_impI. ctx_push Hs. rewrite sb_dB_el. envs.
        finst HWz z. apply (IE HWz). fall u. apply II. ctx_push Hu. simp_in Hu.
        apply (dB_allE _ _ _ u) in Hs. cbn [dB] in Hs. envs_in Hs. exact (IE Hs Hu).
      + rewrite sb_dB_el. envs. exact HWw. }
  unfold WY.
  destruct (Nat.eq_dec a b) as [Eab|Hab].
  { (* a = b: C := empty, U := p *)
    subst b. fobtain (sb_empty _ (rho c) H0) as C HC.
    apply (dB_exI _ _ _ C). apply dB_andI; [apply dB_andI|].
    - unfold Wcl2. apply dB_allI. intros y. apply dB_impI. ctx_push Hy. rewrite sb_dB_el in Hy.
      envs_in Hy. fabsurd. finst HC y. exact (IE HC Hy).
    - apply dB_impI. ctx_push HH. clear HH. unfold WU. apply (dB_exI _ _ _ (rho c)). apply dB_andI.
      + rewrite sb_dB_el. envs. exact Hp.
      + apply dB_allI. intros y. apply dB_impI. ctx_push Hy. rewrite sb_dB_el in Hy. envs_in Hy.
        fabsurd. finst HC y. exact (IE HC Hy).
    - unfold Wcl1. apply dB_allI. intros t. apply dB_impI. ctx_push Ht. rewrite sb_dB_el in Ht.
      envs_in Ht. fabsurd. exact (IE (sb_ir_inst _ t HI) Ht). }
  (* distinct names: the UG' instance for thetaW3 a b phi *)
  finst H2 f x. fmp H2 Hx. fex H2 C HC. fdestr HC HC12 HC3. fdestr HC12 Hcov Hnx.
  apply (dB_exI _ _ _ C). apply dB_andI; [apply dB_andI|].
  - (* cl2 *)
    unfold Wcl2. apply dB_allI. intros y. apply dB_impI. ctx_push Hy. rewrite sb_dB_el in Hy.
    envs_in Hy. finst Hnx y. fmp Hnx Hy. fex Hnx x' Hx'. apply (dB_exI _ _ _ x').
    match type of Hx' with _ ⊢C ?A =>
      assert (E : A = dB (upd (upd (upd (upd (upd (upd rho (S c) w) 0 f) b x) c C) b y) a x') phi)
        by (thw3 Hab c Hfr Hfr' rho) end.
    rewrite E in Hx'. exact Hx'.
  - (* H -> U *)
    apply dB_impI. ctx_push HH.
    match type of HC3 with ?G ⊢C ?A → _ => assert (Htot : G ⊢C A) end.
    { fall a'. apply II. ctx_push Ha. simp_in Ha. unfold WH in HH. apply (dB_allE _ _ _ a') in HH.
      fassert Ha' : (dB (upd (upd (upd (upd (upd rho (S c) w) 0 f) b x) c C) a a') (Wel a b));
        [rewrite sb_dB_el; envs; exact Ha|].
      pose proof (dB_imp _ _ _ HH Ha') as H3. clear Ha' HH.
      apply (dB_exE _ _ _ _ H3). intros y. apply II. ctx_push Hy.
      pose proof (dB_andE1 _ _ _ Hy) as Hyw. pose proof (dB_andE2 _ _ _ Hy) as Hyp. clear Hy.
      rewrite sb_dB_el in Hyw.
      fexists y. fsplit.
      - destruct (Nat.eq_dec a (S c)) as [Ea|Ea].
        + (* a = S c: y ∈ a', a' ∈ x, x ∈ w; transitivity of w twice *)
          subst a. envs_in Hyw.
          pose proof HT0 as HT1. finst HT0 x. fmp HT0 Hx. fdestr HT0 HTx HTq0.
          finst HTx a'. fmp HTx Ha.
          finst HT1 a'. fmp HT1 HTx. fdestr HT1 HTa HTq1. finst HTa y. exact (IE HTa Hyw).
        + envs_in Hyw. exact Hyw.
      - match goal with |- _ ⊢C ?A =>
          assert (E : A = dB (upd (upd (upd (upd (upd (upd rho (S c) w) 0 f) b x) c C) a a') b y) phi)
            by (thw3 Hab c Hfr Hfr' rho) end.
        rewrite E. exact Hyp. }
    fmp HC3 Htot. fex HC3 U HUU. fdestr HUU HUw HUb.
    unfold WU. apply (dB_exI _ _ _ U). apply dB_andI.
    + rewrite sb_dB_el. envs. exact HUw.
    + apply dB_allI. intros y. apply dB_impI. ctx_push Hy. rewrite sb_dB_el in Hy. envs_in Hy.
      apply dB_allI. intros z. apply dB_impI. ctx_push Hz. rewrite sb_dB_el in Hz. envs_in Hz.
      rewrite sb_dB_el. envs. finst HUb y. fmp HUb Hy. finst HUb z. exact (IE HUb Hz).
  - (* cl1 *)
    unfold Wcl1. apply dB_allI. intros a'. apply dB_impI. ctx_push Ha. rewrite sb_dB_el in Ha.
    envs_in Ha. finst Hcov a'. fmp Hcov Ha.
    apply dB_allI. intros y. apply dB_impI. ctx_push Hy. finst Hcov y.
    match type of Hcov with _ ⊢C ?A → _ =>
      assert (E : A = dB (upd (upd (upd (upd (upd (upd rho (S c) w) 0 f) b x) c C) a a') b y) phi)
        by (thw3 Hab c Hfr Hfr' rho) end.
    rewrite E in Hcov. clear E. fmp Hcov Hy. fex Hcov y' Hy'. fdestr Hy' Hyp Hym.
    apply (dB_exI _ _ _ y'). apply dB_andI.
    + rewrite sb_dB_el. envs. exact Hym.
    + match type of Hyp with _ ⊢C ?A =>
        assert (E : A = dB (upd (upd (upd (upd (upd (upd (upd rho (S c) w) 0 f) b x) c C) a a') b y) b y') phi)
          by (thw3 Hab c Hfr Hfr' rho) end.
      rewrite E in Hyp. exact Hyp.
Qed.
