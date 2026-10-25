(** * PA_Comp: completeness of the reference calculus for PAeq + NG:
      PAeq ⋄ ¬GC_form ⊢TC ⊥   ->   pprov X botw      whenever X contains NGw.
    Every PAeq axiom's translation [tr eta] is derivable in [pprov X]; the induction instances use
    the substitution-free schema IND with a fresh variable c (term Leibniz, PA_LMeta). *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import PA Syntax.Theories.
From PAGB Require Import Spec PALogic PA_dB PA_LProp PA_LMeta PA_tr PA_H PA_ND PA_F PA_Sound PA_Ind.
Import ListNotations.
Unset Implicit Arguments.

Local Notation "A ⊢C phi" := (@prv _ _ falsity_on class A phi) (at level 55).

Section Comp.
Variable X : wff -> Prop.
Hypothesis HNG : X NGw.
Local Notation lprov := (pprov X).
Local Notation der := (der X).
Let LDET := DET X.
Let LGEN := GEN X.
Let LB4 := B4 X.

Ltac dh := apply dhyp; simpl; tauto.
Ltac dt H := apply dthm; exact H.
Ltac mp a := apply (dmp _ _ a).

Lemma der_cut G a : der G a -> (forall h, In h G -> lprov h) -> lprov a.
Proof. induction 1; intro HG; [now apply HG | assumption | exact (LDET _ _ (IHder1 HG) (IHder2 HG))]. Qed.

Lemma p_inst x y a : lprov a -> x <> y -> bnd x a = false -> bnd y a = false -> lprov (sb x (TV y) a).
Proof.
  intros H Hxy Hx Hy. refine (LDET _ _ (lspec X x (TV y) a _ Hx _) (LGEN x _ H)).
  - cbn. apply Nat.eqb_neq. congruence.
  - intros v Hv. cbn in Hv. apply Nat.eqb_eq in Hv. now subst.
Qed.

(** ** The arithmetic and equality axioms *)
Lemma c_FA eta psi : In psi FAeq -> lprov (tr eta psi).
Proof.
  intro H. repeat (destruct H as [<-|H]); [| | | | | | | | | | destruct H]; cbn; repeat apply LGEN.
  - apply leq_refl.
  - apply leq_sym.
  - apply leq_trans.
  - apply ES.
  - apply der_lprov, ded, ded.
    mp (Weq (TP (TV 4) (TV 6)) (TP (TV 4) (TV 8))).
    + mp (Weq (TP (TV 2) (TV 6)) (TP (TV 4) (TV 6))); [dt (leq_trans X (TP (TV 2) (TV 6)) (TP (TV 4) (TV 6)) (TP (TV 4) (TV 8)))|].
      mp (Weq (TV 2) (TV 4)); [dt (EPl X (TV 2) (TV 4) (TV 6)) | dh].
    + mp (Weq (TV 6) (TV 8)); [dt (EPr X (TV 6) (TV 8) (TV 4)) | dh].
  - apply der_lprov, ded, ded.
    mp (Weq (TM (TV 4) (TV 6)) (TM (TV 4) (TV 8))).
    + mp (Weq (TM (TV 2) (TV 6)) (TM (TV 4) (TV 6))); [dt (leq_trans X (TM (TV 2) (TV 6)) (TM (TV 4) (TV 6)) (TM (TV 4) (TV 8)))|].
      mp (Weq (TV 2) (TV 4)); [dt (EMl X (TV 2) (TV 4) (TV 6)) | dh].
    + mp (Weq (TV 6) (TV 8)); [dt (EMr X (TV 6) (TV 8) (TV 4)) | dh].
  - exact (p_inst 0 2 _ (AA0 X) ltac:(lia) eq_refl eq_refl).
  - exact (p_inst 1 4 _ (p_inst 0 2 _ (AAS X) ltac:(lia) eq_refl eq_refl) ltac:(lia) eq_refl eq_refl).
  - exact (p_inst 0 2 _ (AM0 X) ltac:(lia) eq_refl eq_refl).
  - exact (p_inst 1 2 _ (p_inst 0 4 _ (AMS X) ltac:(lia) eq_refl eq_refl) ltac:(lia) eq_refl eq_refl).
Qed.

Lemma c_zero_succ eta : lprov (tr eta ax_zero_succ).
Proof. cbn. apply LGEN. exact (p_inst 0 2 _ (AZS X) ltac:(lia) eq_refl eq_refl). Qed.

Lemma c_succ_inj eta : lprov (tr eta ax_succ_inj).
Proof.
  cbn. apply LGEN, LGEN. exact (p_inst 1 2 _ (p_inst 0 4 _ (ASI X) ltac:(lia) eq_refl eq_refl) ltac:(lia) eq_refl eq_refl).
Qed.
(** ** Induction *)
Lemma sbt_fresh_comp c B s t : tocc c t = false -> sbt c s (sbt B (TV c) t) = sbt B s t.
Proof.
  induction t; cbn; intro H; try reflexivity.
  - destruct (Nat.eqb_spec n B); cbn; [now rewrite Nat.eqb_refl|]. now rewrite H.
  - now rewrite IHt.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IHt1, IHt2.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IHt1, IHt2.
Qed.

Lemma sb_fresh_comp c B s a : occ c a = false -> sb c s (sb B (TV c) a) = sb B s a.
Proof.
  induction a as [t r|a1 IH1 a2 IH2|a1 IH|z a1 IH]; cbn; intro H.
  - apply orb_false_iff in H as [H1 H2]. now rewrite !sbt_fresh_comp.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IH1, IH2.
  - now rewrite IH.
  - apply orb_false_iff in H as [H1 H2]. destruct (Nat.eqb_spec z B) as [->|].
    + cbn. rewrite H1. now rewrite sb_noocc.
    + cbn. rewrite H1. now rewrite IH.
Qed.

Lemma tocc_sbt_other c B s t : tocc c t = false -> tocc c s = false -> tocc c (sbt B s t) = false.
Proof.
  intros H Hs. induction t; cbn in *; auto.
  - destruct (Nat.eqb n B); cbn; auto.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IHt1, IHt2.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IHt1, IHt2.
Qed.

Lemma occ_sb_other c B s a : occ c a = false -> tocc c s = false -> occ c (sb B s a) = false.
Proof.
  intros H Hs. induction a as [t r|a1 IH1 a2 IH2|a1 IH|z a1 IH]; cbn in *.
  - apply orb_false_iff in H as [H1 H2]. now rewrite !tocc_sbt_other.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IH1, IH2.
  - now apply IH.
  - apply orb_false_iff in H as [H1 H2]. destruct (Nat.eqb z B); cbn; rewrite H1; cbn; auto.
Qed.

Lemma ind_core B a : bnd B a = false ->
  lprov (Wim (sb B TZ a) (Wim (Wal B (Wim a (sb B (TS (TV B)) a))) (Wal B a))).
Proof.
  intro Hb. set (c := S (maxv a + B)).
  assert (Hc : occ c a = false).
  { destruct (occ c a) eqn:E; [|reflexivity]. apply occ_maxv in E. unfold c in E. lia. }
  assert (HcB : c <> B) by (unfold c; lia).
  assert (HcBb : Nat.eqb c B = false) by now apply Nat.eqb_neq.
  assert (HBcb : Nat.eqb B c = false) by (apply Nat.eqb_neq; congruence).
  (* (i) base *)
  assert (P0 : lprov (Wim (sb B TZ a) (Wal B (Wim (Weq (TV B) TZ) a)))).
  { destruct (leib X B TZ a Hb ltac:(intros v Hv; discriminate)) as [_ L].
    pose proof (LDET _ _ (lpc_C X _ _ _) L) as L'.
    refine (lsyl X _ _ _ (lvac X B _ _) (lal X B _ _ L')).
    apply occ_sb_self; [reflexivity | exact Hb]. }
  (* (ii) a(S B) -> A.c (c = S B -> A.B (B = c -> a)) *)
  set (ac := sb B (TV c) a).
  assert (Q1 : lprov (Wim ac (Wal B (Wim (Weq (TV B) (TV c)) a)))).
  { assert (Hs : sfree (TV c) a).
    { intros v Hv. change (Nat.eqb c v = true) in Hv. apply Nat.eqb_eq in Hv. subst v. now apply occ_bnd. }
    destruct (leib X B (TV c) a Hb Hs) as [_ L].
    pose proof (LDET _ _ (lpc_C X _ _ _) L) as L'.
    refine (lsyl X _ _ _ (lvac X B _ _) (lal X B _ _ L')).
    apply occ_sb_self; [cbn; exact HcBb | exact Hb]. }
  assert (Q2 : lprov (Wim (Weq (TV c) (TS (TV B))) (Wim (sb B (TS (TV B)) a) ac))).
  { assert (Hbc : bnd c ac = false) by (unfold ac; rewrite bnd_sb; now apply occ_bnd).
    assert (Hs : sfree (TS (TV B)) ac).
    { intros v Hv. change (Nat.eqb B v = true) in Hv. apply Nat.eqb_eq in Hv. subst v. unfold ac. now rewrite bnd_sb. }
    destruct (leib X c (TS (TV B)) ac Hbc Hs) as [_ L].
    unfold ac in L at 1. rewrite sb_fresh_comp in L by exact Hc. exact L. }
  assert (P1 : lprov (Wim (sb B (TS (TV B)) a)
                          (Wal c (Wim (Weq (TV c) (TS (TV B))) (Wal B (Wim (Weq (TV B) (TV c)) a)))))).
  { assert (I : lprov (Wim (sb B (TS (TV B)) a) (Wim (Weq (TV c) (TS (TV B))) (Wal B (Wim (Weq (TV B) (TV c)) a))))).
    { apply der_lprov, ded, ded. mp ac; [dt Q1|].
      mp (sb B (TS (TV B)) a); [mp (Weq (TV c) (TS (TV B))); [dt Q2 | dh] | dh]. }
    refine (lsyl X _ _ _ (lvac X c _ _) (lal X c _ _ I)).
    apply occ_sb_other; [exact Hc | cbn; exact HBcb]. }
  (* (iii) the step hypothesis *)
  assert (P2 : lprov (Wim (Wal B (Wim a (sb B (TS (TV B)) a))) (Wal B (ind_step B c a)))).
  { apply lal. unfold ind_step. apply der_lprov, ded, ded.
    mp (sb B (TS (TV B)) a); [dt P1|]. mp a; dh. }
  (* (iv) induction *)
  pose proof (lind X B c a HcB Hc) as HI. unfold IND in HI.
  apply der_lprov, ded, ded.
  mp (Wal B (ind_step B c a)); [mp (Wal B (Wim (Weq (TV B) TZ) a)); [dt HI|] |].
  - mp (sb B TZ a); [dt P0 | dh].
  - mp (Wal B (Wim a (sb B (TS (TV B)) a))); [dt P2 | dh].
Qed.

Lemma tr_ind_unfold eta (phi : form) :
  tr eta (ax_induction phi) =
  Wim (tr eta (phi[zero..]))
      (Wim (Wal (bname (Nat.max (qd phi) (qd (phi[σ $0 .: S >> var]))))
                (tr (scons (TV (bname (Nat.max (qd phi) (qd (phi[σ $0 .: S >> var]))))) eta)
                    (phi → phi[σ $0 .: S >> var])))
           (Wal (bname (qd phi)) (tr (scons (TV (bname (qd phi))) eta) phi))).
Proof. reflexivity. Qed.

Lemma c_induction eta phi : oddenv eta -> lprov (tr eta (ax_induction phi)).
Proof.
  intro He. rewrite tr_ind_unfold, qd_subst, Nat.max_id.
  set (B := bname (qd phi)). set (a := tr (scons (TV B) eta) phi).
  assert (Hb : bnd B a = false) by apply bnd_tr, notbinder_bname.
  assert (E0 : tr eta (phi[zero..]) = sb B TZ a).
  { rewrite tr_inst. unfold a. rewrite sb_tr by apply notbinder_bname. apply tr_ext.
    intros [|n]; cbn; [unfold B; now rewrite Nat.eqb_refl | symmetry; apply sbt_noocc, oddenv_bname, He]. }
  assert (E1 : tr (scons (TV B) eta) (phi[σ $0 .: S >> var]) = sb B (TS (TV B)) a).
  { rewrite tr_subst. unfold a. rewrite sb_tr by apply notbinder_bname. apply tr_ext.
    intros [|n]; cbn; [unfold B; now rewrite Nat.eqb_refl | symmetry; apply sbt_noocc, oddenv_bname, He]. }
  rewrite E0.
  destruct (tr_imp_equiv X (scons (TV B) eta) phi (phi[σ $0 .: S >> var])) as [T1 _].
  rewrite E1 in T1. fold a in T1.
  pose proof (ind_core B a Hb) as C.
  apply der_lprov, ded, ded.
  mp (Wal B (Wim a (sb B (TS (TV B)) a))); [mp (sb B TZ a); [dt C | dh] |].
  mp (Wal B (tr (scons (TV B) eta) (phi → phi[σ $0 .: S >> var]))); [dt (lal X B _ _ T1) | dh].
Qed.

(** ** Completeness *)
Definition eta1 : nat -> tm := fun _ => TV 1.

Lemma oddenv_eta1 : oddenv eta1.
Proof. intros n v Hv. change (Nat.eqb 1 v = true) in Hv. apply Nat.eqb_eq in Hv. now subst. Qed.

Theorem pprov_complete : PA_NG_inconsistent -> lprov botw.
Proof.
  intros [A [HA D]]. pose proof (nd_sound X A falsity D eta1 oddenv_eta1) as H. cbn [tr] in H.
  apply (der_cut _ _ H). intros h Hh. apply in_map_iff in Hh as [psi [<- Hpsi]].
  destruct (HA psi Hpsi) as [HP | ->].
  - destruct HP as [phi Hphi | | | phi].
    + now apply c_FA.
    + apply c_zero_succ.
    + apply c_succ_inj.
    + apply c_induction, oddenv_eta1.
  - apply HYP. exact HNG.
Qed.
End Comp.

(** ** The reference calculus with NG decides exactly PA ⊢ GC *)
Theorem pprov_NG_iff_PA_GC : pprov (eq NGw) Fw <-> PA_proves_GC.
Proof.
  split; [apply pprov_NG_GC|].
  intro H. apply PA_GC_refutation in H. exact (pprov_complete (eq NGw) eq_refl H).
Qed.

Print Assumptions pprov_NG_iff_PA_GC.
