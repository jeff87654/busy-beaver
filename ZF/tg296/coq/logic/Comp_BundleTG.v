(** * Comp_BundleTG: SUIR inconsistent -> thm_tg 1  (ported from ZF/m254/coq/logic/Comp_Bundle254.v).

    TB = the universal closures [Lib n a] of the named wffs a with thm_tg (tau a).
      (1) TB ⊢ ⊥ -> thm_tg 1    (ND soundness for S2 [nd_sound], as Std_glue.TPset_to_prov)
      (2) every SUIR axiom is derivable from TB:
          equality axioms and IR are closures of tau-theorems; every closed UG' instance follows from
          the closure of a bundle wff  BW 1 3 c phi  (BundleTG) with phi = Wal q (tr eta th),
          eta: $0 -> 1 (input a), $1 -> 3 (output b), $2 -> 0 (f), $(k+3) -> 2k+5, c = tau phi. *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import Sets.minZF Deduction.FullNDFacts.
From ZF Require Import Logic L1_LDef L1_LProp L1_LMeta Std_dB Std_F Std_tr Std_H Std_alpha Std_gen
  Std_iface Std_iface2 Std_setnd Std_setbase Std_glue Std_breq Std_brnd Std_brrep.
From M254S Require Import S_def.
From M254TG Require Import SU_def.
From M254L Require Import Wff254.
From M254TGL Require Import CodesTG ThmTG CDTG Comp_PropTG BundleTG.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

Definition Q (a : wff) : Prop := thm_tg (tau a).

Lemma Q_lprov a b : lprov (Wim a b) -> Q a -> Q b.
Proof. intros H Ha. pose proof (lprov_thm _ H) as H'. cbn [tau] in H'. exact (T_mp _ _ Ha H'). Qed.

Lemma Q_of_lprov a : lprov a -> Q a.
Proof. apply lprov_thm. Qed.

Lemma Q_genall n a : Q a -> Q (genall n a).
Proof. induction n; cbn; [auto|]. intro H. apply T_gen, IHn, H. Qed.

Lemma Q_tr_cl eta n a : Q a -> maxfr a < n -> Q (tr eta (dB var (genall n a))).
Proof.
  intros Ha Hn. set (th := dB var (genall n a)).
  assert (Hfb : fb 0 th) by now apply fb_cl.
  assert (E : dB var (tr eta th) = dB var (genall n a)).
  { rewrite (dB_tr th 0 eta var (frag_dB _ _) Hfb) by (intros; lia).
    rewrite (subst_ext_fb _ 0 _ var Hfb) by (intros; lia). apply subst_var. }
  destruct (alpha_dB _ _ var injective_var E) as [_ H2].
  exact (Q_lprov _ _ H2 (Q_genall n a Ha)).
Qed.

Lemma Q_discharge G c : lprov (foldi G c) -> (forall h, In h G -> Q h) -> Q c.
Proof.
  intros H HG. revert c H; induction G as [|h G IH]; intros c H; [exact (Q_of_lprov _ H)|].
  cbn [foldi fold_left] in H. specialize (IH (fun h' Hh' => HG h' (or_intror Hh')) _ H).
  unfold Q in IH. cbn [tau] in IH. exact (T_mp _ _ (HG h (or_introl eq_refl)) IH).
Qed.

Definition TB (th : form) : Prop := exists a n, Q a /\ maxfr a < n /\ th = Lib n a.

Lemma TB_Lib a n : Q a -> maxfr a < n -> TB (Lib n a).
Proof. intros H1 H2. now exists a, n. Qed.

Theorem TB_to_thm : thm TB falsity -> thm_tg 1.
Proof.
  intros [C [HC Dv]].
  pose proof (nd_sound C falsity Dv eta0 oddenv_eta0) as S. cbn [tr] in S.
  apply der_foldi in S.
  assert (Hb : Q botw).
  { apply (Q_discharge _ _ S). intros h Hh. apply in_map_iff in Hh as [th [<- Hth]].
    destruct (HC th Hth) as (a & n & Ha & Hn & ->). exact (Q_tr_cl eta0 n a Ha Hn). }
  assert (H0 : Q (Wal 0 (Weq 0 0))) by (apply Q_of_lprov, LGEN, leq_refl).
  unfold Q in Hb, H0. cbn [tau botw] in Hb, H0. exact (T_mp _ _ H0 Hb).
Qed.

(** ** Equality axioms and IR *)
Lemma Lib_eq_thm a n psi : Q a -> maxfr a < n -> Lib n a = psi -> thm TB psi.
Proof. intros H1 H2 <-. apply thm_ax. now apply TB_Lib. Qed.

Lemma lprov_trans_eq : lprov (Wim (Weq 2 1) (Wim (Weq 1 0) (Weq 2 0))).
Proof.
  apply der_lprov. do 2 apply L1_LMeta.ded.
  apply (L1_LMeta.dmp _ (Weq 1 0)); [|apply L1_LMeta.dhyp; simpl; tauto].
  apply (L1_LMeta.dmp _ (Weq 1 2)); [apply L1_LMeta.dthm, LB8a|].
  apply (L1_LMeta.dmp _ (Weq 2 1)); [apply L1_LMeta.dthm, leq_sym | apply L1_LMeta.dhyp; simpl; tauto].
Qed.

Lemma TB_EqAx_mem psi : In psi EqAx -> TB psi.
Proof.
  intros H. repeat destruct H as [<-|H]; [| | | | destruct H].
  - exists (Weq 0 0), 1. repeat split; [apply Q_of_lprov, leq_refl | cbv; lia].
  - exists (Wim (Weq 1 0) (Weq 0 1)), 2. repeat split; [apply Q_of_lprov, leq_sym | cbv; lia].
  - exists (Wim (Weq 2 1) (Wim (Weq 1 0) (Weq 2 0))), 3. repeat split; [apply Q_of_lprov, lprov_trans_eq | cbv; lia].
  - exists (Wim (Weq 3 1) (Wim (Weq 2 0) (Wim (Wel 3 2) (Wel 1 0)))), 4.
    repeat split; [apply Q_of_lprov, leq_tr_el | cbv; lia].
Qed.

Lemma TB_EqAx psi : In psi EqAx -> thm TB psi.
Proof. intro H. apply thm_ax. now apply TB_EqAx_mem. Qed.

(** IR is the closure of  -. v0 e. v0, whose code is F -> F *)
Lemma TB_IR : thm TB ax_ir.
Proof.
  apply (Lib_eq_thm (Wn (Wel 0 0)) 1); [unfold Q; cbn [tau]; apply thm_I | cbv; lia | reflexivity].
Qed.

(** ** UG' instances from bundle closures *)
Lemma occ_tau v a : occ v a = true -> v < tau a.
Proof.
  induction a as [x y|x y|a IHa b IHb|a IHa|x a IHa]; cbn [occ tau]; intro H.
  - apply orb_true_iff in H as [H|H]; apply Nat.eqb_eq in H; subst; unfold weq;
      [pose proof (P_ge_l v y) | pose proof (P_ge_r x v)]; lia.
  - apply orb_true_iff in H as [H|H]; apply Nat.eqb_eq in H; subst; unfold wel;
      [pose proof (P_ge_l v y) | pose proof (P_ge_r x v)]; lia.
  - unfold wim. apply orb_true_iff in H as [H|H];
      [specialize (IHa H); pose proof (P_ge_l (tau a) (tau b)) | specialize (IHb H); pose proof (P_ge_r (tau a) (tau b))]; lia.
  - unfold wim. specialize (IHa H). pose proof (P_ge_l (tau a) 1). lia.
  - unfold wal. apply orb_true_iff in H as [H|H].
    + apply Nat.eqb_eq in H; subst. pose proof (P_ge_l v (tau a)). lia.
    + specialize (IHa H). pose proof (P_ge_r x (tau a)). lia.
Qed.

Local Opaque wim wel wal weq P.

Lemma tau_BW a b phi : tau (BW a b (tau phi) phi) = bundle_tg a b (tau phi).
Proof. reflexivity. Qed.

Lemma dB_el (rho : nat -> term) x y : dB rho (Wel x y) = rho x ∈' rho y.
Proof. reflexivity. Qed.

Ltac envs := repeat first [ rewrite upd_eq | rewrite upd_neq by lia ].
Ltac envs_in H := repeat first [ rewrite upd_eq in H | rewrite upd_neq in H by lia ].

Lemma Q_BW a b phi : tau phi <> a -> tau phi <> b -> Q (BW a b (tau phi) phi).
Proof. intros H1 H2. unfold Q. rewrite tau_BW. now apply T_bundle. Qed.

(** the label map of the named matrix: $0 -> 1 (input), $1 -> 3 (output), $2 -> 0 (f), $(k+3) -> 2k+5 *)
Definition etaU (k : nat) : nat :=
  match k with 0 => 1 | 1 => 3 | 2 => 0 | S (S (S k)) => 2 * k + 5 end.

Lemma etaU_bname n k : etaU n <> bname k.
Proof. unfold bname. destruct n as [|[|[|n]]]; cbn; lia. Qed.

Lemma etaU_lt n N : n < N -> etaU n < 2 * N + 5.
Proof. destruct n as [|[|[|n]]]; cbn; lia. Qed.

Lemma phi_eqv3 (th : form) N (HN : fb N th) q (Hq : occ q (tr etaU th) = false)
  (G : list form) (HE : incl EqAx G) (e : nat -> term) (x y f : term) (sg : nat -> term) :
  (forall k, k < N -> etaU k <> q) ->
  e 1 = x -> e 3 = y -> e 0 = f -> (forall k, k + 3 < N -> e (2 * k + 5) = sg k) ->
  G ⊢C dB e (Wal q (tr etaU th)) ↔ th[x .: y .: f .: sg].
Proof.
  intros Hnq E1 E3 E0 Ek.
  assert (Hfr : forall t, dB (upd e q t) (tr etaU th) = dB e (tr etaU th)).
  { intros t. apply dB_ext_fr. intros v Hv. apply upd_neq. intros ->. rewrite fr_occ in Hv; [discriminate | exact Hq]. }
  assert (Hb : forall n k, n < N -> k < qd th -> etaU n <> bname k) by (intros; apply etaU_bname).
  pose proof (tr_equiv th N etaU e G HE HN Hb) as T. cbv beta in T.
  assert (Es : th[fun n => e (etaU n)] = th[x .: y .: f .: sg]).
  { apply (subst_ext_fb _ N); [exact HN|]. intros [|[|[|k]]] Hk; cbn - [Nat.mul].
    - exact E1.
    - exact E3.
    - exact E0.
    - apply Ek. lia. }
  rewrite Es in T. fsplit.
  - fintro H. apply (iff_l _ _ _ T). apply (dB_allE _ _ _ $0) in H. rewrite Hfr in H. exact H.
  - fintro H. apply dB_allI. intros t. rewrite Hfr. apply (iff_r _ _ _ T). exact H.
Qed.

Ltac tcase := repeat match goal with |- context [?t`[_]] => is_var t; destruct t as [?|[]] end.

Lemma half k : (2 * k + 5 - 5) / 2 = k.
Proof. replace (2 * k + 5 - 5) with (k * 2) by lia. apply Nat.div_mul. lia. Qed.

Local Opaque Lib EqAx.

Ltac thnorm3 HN sg :=
  rewrite ?subst_comp; apply (subst_ext_fb _ _ _ _ HN);
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros [|[|[|k]]] Hk; unfold funcomp; cbn; unfold funcomp;
  try (destruct (sg k) as [?|[]]); cbn; tcase; cbn; reflexivity.
Ltac thnorm3_in H th HN sg x y f :=
  match type of H with _ ⊢C ?g =>
    let E := fresh "E" in assert (E : g = th[x .: y .: f .: sg]) by thnorm3 HN sg; rewrite E in H; clear E end.
Ltac thnorm3_goal th HN sg x y f :=
  match goal with |- _ ⊢C ?g =>
    let E := fresh "E" in assert (E : g = th[x .: y .: f .: sg]) by thnorm3 HN sg; rewrite E; clear E end.
(** every UG' instance (closed or not) is derivable from TB *)
Lemma TB_ug (th : form) n : thm TB (forall_times n (ug th)).
Proof.
  destruct (fb_exists th) as [N HN].
  set (q := 2 * N + 5).
  set (phi0 := tr etaU th). set (phi := Wal q phi0). set (c := tau phi).
  assert (Hnq : forall k, k < N -> etaU k <> q) by (intros k Hk; pose proof (etaU_lt k N Hk); unfold q; lia).
  assert (Hq : occ q phi0 = false).
  { eapply occ_tr; [exact HN | exact Hnq | apply notbinder_odd; unfold q;
      rewrite Nat.odd_add, Nat.odd_mul; reflexivity]. }
  assert (Hqc : q < c) by (apply occ_tau; cbn [occ phi]; now rewrite Nat.eqb_refl).
  pose proof (Q_BW 1 3 phi) as HQ. fold c in HQ. specialize (HQ ltac:(unfold q in Hqc; lia) ltac:(unfold q in Hqc; lia)).
  clearbody c.
  set (W := BW 1 3 c phi) in *.
  set (m := S (maxfr W)). assert (Hm : maxfr W < m) by (unfold m; lia). clearbody m.
  exists (Lib m W :: EqAx). split.
  { intros psi [<-|H]; [apply TB_Lib; [exact HQ | exact Hm] | now apply TB_EqAx_mem]. }
  assert (HL : (Lib m W :: EqAx) ⊢C Lib m W) by (apply Ctx; now left).
  assert (HE : incl EqAx (Lib m W :: EqAx)) by (intros x Hx; now right).
  apply ft_intro. intros sg. unfold ug. cbn. apply AllI_named. intros p.
  set (rho := fun v => if Nat.eqb v c then p else sg ((v - 5) / 2)).
  assert (Rc : rho c = p) by (unfold rho; now rewrite Nat.eqb_refl).
  assert (Rk : forall k, 2 * k + 5 < c -> rho (2 * k + 5) = sg k).
  { intros k Hk. unfold rho. replace (Nat.eqb (2 * k + 5) c) with false by (symmetry; apply Nat.eqb_neq; lia).
    now rewrite half. }
  pose proof (Lib_inst _ _ _ rho Hm HL) as H.
  change (dB rho W) with (dB rho (BW 1 3 c phi)) in H. unfold BW in H. apply dB_andE1 in H. unfold UGW in H.
  apply (dB_exE _ _ _ _ H). intros w. apply II. ctx_push Hw.
  apply (ExI w). simp.
  fsplit; [fsplit|].
  - pose proof (dB_andE2 _ _ _ Hw) as H1. rewrite dB_el in H1. envs_in H1. rewrite Rc in H1. exact H1.
  - fall x. apply II. ctx_push Hx. simp_in Hx.
    pose proof (dB_andE1 _ _ _ Hw) as H1. apply (dB_allE _ _ _ x) in H1. apply (dB_allE _ _ _ x) in H1.
    fassert Hx' : (dB (upd (upd (upd rho (S c) w) 0 x) 3 x) (Wel 3 (S c))); [rewrite dB_el; envs; exact Hx|].
    pose proof (dB_imp _ _ _ H1 Hx') as H2. clear H1 Hx'. apply dB_andE2 in H2.
    fsplit.
    + pose proof (dB_andE1 _ _ _ H2) as H3. unfold WT in H3. fall u. apply II. ctx_push Hu. simp_in Hu.
      apply (dB_allE _ _ _ u) in H3.
      fassert Hu' : (dB (upd (upd (upd (upd rho (S c) w) 0 x) 3 x) c u) (Wel c 3)); [rewrite dB_el; envs; exact Hu|].
      pose proof (dB_imp _ _ _ H3 Hu') as H4. rewrite dB_el in H4. envs_in H4. exact H4.
    + pose proof (dB_andE2 _ _ _ H2) as H3. unfold WQ in H3. apply (dB_exE _ _ _ _ H3). intros W'. apply II. ctx_push HW.
      apply (ExI W'). simp. fsplit.
      * pose proof (dB_andE2 _ _ _ HW) as H4. rewrite dB_el in H4. envs_in H4. exact H4.
      * fall z. apply II. ctx_push Hs. simp_in Hs.
        pose proof (dB_andE1 _ _ _ HW) as H4. apply (dB_allE _ _ _ z) in H4.
        fassert Hs' : (dB (upd (upd (upd (upd (upd rho (S c) w) 0 x) 3 x) c W') (S c) z) (Wal c (Wim (Wel c (S c)) (Wel c 3)))).
        { apply dB_allI. intros u. cbn [dB]. envs. apply (AllE u) in Hs. simp_in Hs. exact Hs. }
        pose proof (dB_imp _ _ _ H4 Hs') as H5. rewrite dB_el in H5. envs_in H5. exact H5.
  - fall f. fall B. apply II. ctx_push HB. simp_in HB.
    assert (Hc5 : 5 < c) by (unfold q in Hqc; lia).
    pose proof (dB_andE1 _ _ _ Hw) as H1. apply (dB_allE _ _ _ f) in H1. apply (dB_allE _ _ _ B) in H1.
    fassert HB' : (dB (upd (upd (upd rho (S c) w) 0 f) 3 B) (Wel 3 (S c))); [rewrite dB_el; envs; exact HB|].
    pose proof (dB_imp _ _ _ H1 HB') as H2. clear H1 HB'. apply dB_andE1 in H2. unfold WY in H2.
    apply (dB_exE _ _ _ _ H2). intros C. apply II. ctx_push HC.
    apply (ExI C). simp.
    set (e1 := upd (upd (upd (upd rho (S c) w) 0 f) 3 B) c C) in *.
    assert (Ek1 : forall k, k + 3 < N -> e1 (2 * k + 5) = sg k).
    { intros k Hk. unfold e1. unfold q in Hqc. envs. apply Rk. lia. }
    assert (E10 : e1 0 = f) by (unfold e1; envs; reflexivity).
    pose proof (dB_andE2 _ _ _ HC) as Hcl1. pose proof (dB_andE1 _ _ _ HC) as Hc23.
    pose proof (dB_andE1 _ _ _ Hc23) as Hcl2. pose proof (dB_andE2 _ _ _ Hc23) as Hcl3.
    fsplit; [fsplit|].
    + apply AllI_named. intros a. simp. apply II. ctx_push Ha. simp_in Ha.
      apply AllI_named. intros y. simp. apply II. ctx_push Hy. simp_in Hy.
      thnorm3_in Hy th HN sg a y f.
      unfold Wcl1 in Hcl1. apply (dB_allE _ _ _ a) in Hcl1.
      fassert Ha' : (dB (upd e1 1 a) (Wel 1 3)); [rewrite dB_el; unfold e1; envs; exact Ha|].
      pose proof (dB_imp _ _ _ Hcl1 Ha') as H3. clear Ha'. apply (dB_allE _ _ _ y) in H3.
      set (e2 := upd (upd e1 1 a) 3 y) in *.
      assert (Ek2 : forall k, k + 3 < N -> e2 (2 * k + 5) = sg k) by (intros k Hk; unfold e2; envs; apply Ek1; lia).
      fassert Hp : (dB e2 phi);
        [apply (iff_r _ _ _ (phi_eqv3 th N HN q Hq _ HE e2 a y f sg Hnq ltac:(unfold e2; envs; reflexivity)
                                ltac:(unfold e2; envs; reflexivity) ltac:(unfold e2; envs; exact E10) Ek2)); exact Hy|].
      pose proof (dB_imp _ _ _ H3 Hp) as H4. clear H3 Hp.
      apply (dB_exE _ _ _ _ H4). intros y'. apply II. ctx_push Hy'.
      apply (ExI y'). simp. fsplit.
      * thnorm3_goal th HN sg a y' f.
        apply (iff_l _ _ _ (phi_eqv3 th N HN q Hq _ HE (upd e2 3 y') a y' f sg Hnq
                               ltac:(unfold e2; envs; reflexivity) ltac:(envs; reflexivity)
                               ltac:(unfold e2; envs; exact E10) ltac:(intros k Hk; envs; apply Ek2; lia))).
        exact (dB_andE2 _ _ _ Hy').
      * pose proof (dB_andE1 _ _ _ Hy') as H5. rewrite dB_el in H5. unfold e2 in H5. envs_in H5.
        unfold e1 in H5. envs_in H5. exact H5.
    + apply AllI_named. intros y. simp. apply II. ctx_push Hy. simp_in Hy.
      unfold Wcl2 in Hcl2. apply (dB_allE _ _ _ y) in Hcl2.
      fassert Hy2 : (dB (upd e1 3 y) (Wel 3 c)); [rewrite dB_el; envs; unfold e1; envs; exact Hy|].
      pose proof (dB_imp _ _ _ Hcl2 Hy2) as H3. clear Hy2.
      apply (dB_exE _ _ _ _ H3). intros x. apply II. ctx_push Hx.
      apply (ExI x). thnorm3_goal th HN sg x y f.
      apply (iff_l _ _ _ (phi_eqv3 th N HN q Hq _ HE (upd (upd e1 3 y) 1 x) x y f sg Hnq
                             ltac:(envs; reflexivity) ltac:(envs; reflexivity) ltac:(envs; exact E10)
                             ltac:(intros k Hk; envs; apply Ek1; lia))).
      exact Hx.
    + apply II. ctx_push Ht. simp_in Ht.
      fassert HH : (dB e1 (WH 1 3 c phi)).
      { unfold WH. apply dB_allI. intros a. apply dB_impI. ctx_push Ha. rewrite dB_el in Ha. envs_in Ha.
        unfold e1 in Ha. envs_in Ha.
        finst Ht a. fmp Ht Ha. fex Ht y Hy. fdestr Hy Hyw Hyp.
        apply (dB_exI _ _ _ y). apply dB_andI.
        - rewrite dB_el. envs. unfold e1. envs. exact Hyw.
        - thnorm3_in Hyp th HN sg a y f.
          apply (iff_r _ _ _ (phi_eqv3 th N HN q Hq _ HE (upd (upd e1 1 a) 3 y) a y f sg Hnq
                                 ltac:(envs; reflexivity) ltac:(envs; reflexivity) ltac:(envs; exact E10)
                                 ltac:(intros k Hk; envs; apply Ek1; lia))).
          exact Hyp. }
      pose proof (dB_imp _ _ _ Hcl3 HH) as HU. clear HH. unfold WU in HU.
      apply (dB_exE _ _ _ _ HU). intros U. apply II. ctx_push HU'.
      apply (ExI U). simp. fsplit.
      * pose proof (dB_andE1 _ _ _ HU') as H5. rewrite dB_el in H5. envs_in H5. unfold e1 in H5. envs_in H5. exact H5.
      * fall y. apply II. ctx_push Hy. simp_in Hy. fall z. apply II. ctx_push Hz. simp_in Hz.
        pose proof (dB_andE2 _ _ _ HU') as H5. apply (dB_allE _ _ _ y) in H5.
        fassert Hy' : (dB (upd (upd e1 3 U) (S c) y) (Wel (S c) c)); [rewrite dB_el; envs; unfold e1; envs; exact Hy|].
        pose proof (dB_imp _ _ _ H5 Hy') as H6. apply (dB_allE _ _ _ z) in H6.
        fassert Hz' : (dB (upd (upd (upd e1 3 U) (S c) y) c z) (Wel c (S c))); [rewrite dB_el; envs; exact Hz|].
        pose proof (dB_imp _ _ _ H6 Hz') as H7. rewrite dB_el in H7. envs_in H7. exact H7.
Qed.

(** ** SUIR from TB *)
Local Transparent EqAx Lib.

Lemma SUIR_TB psi : SUIR psi -> thm TB psi.
Proof.
  intros [[phi Hb | phi n Hc] | ->].
  - apply TB_EqAx. rewrite <- SUbase_EqAx. exact Hb.
  - apply TB_ug.
  - exact TB_IR.
Qed.

Theorem SUIR_to_thm : @tprv _ _ falsity_on class SUIR falsity -> thm_tg 1.
Proof. intro H. apply TB_to_thm. exact (thm_trans _ _ _ H SUIR_TB). Qed.

Print Assumptions SUIR_to_thm.
