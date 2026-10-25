(** * PA_ND: the main theorem of the completeness direction's logic part:
      A ⊢C phi  ->  der (map (tr eta) A) (tr eta phi)      (in pprov X, any X)
    for every environment [eta] whose terms use only odd variables ([oddenv]).
    Ported from zf/stdzf/coq/Std_H.v ([nd_sound]); AllE/ExI now instantiate with arbitrary terms. *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import PA.
From PAGB Require Import PALogic PA_dB PA_LProp PA_LMeta PA_tr PA_H.
Import ListNotations.
Unset Implicit Arguments.

Local Notation "A ⊢C phi" := (@prv _ _ falsity_on class A phi) (at level 55).

(** ** Environments and fresh names *)
Definition oddenv (eta : nat -> tm) : Prop := forall n v, tocc v (eta n) = true -> Nat.odd v = true.

Fixpoint sumenv (eta : nat -> tm) (N : nat) : nat :=
  match N with 0 => 0 | S N => tmaxv (eta N) + sumenv eta N end.

Lemma sumenv_ge eta N n : n < N -> tmaxv (eta n) <= sumenv eta N.
Proof. induction N; intros H; cbn; [lia|]. destruct (Nat.eq_dec n N); [subst; lia | specialize (IHN ltac:(lia)); lia]. Qed.

Definition fresh (eta : nat -> tm) (N : nat) : nat := 2 * sumenv eta N + 1.

Lemma fresh_odd eta N : Nat.odd (fresh eta N) = true.
Proof. unfold fresh. rewrite Nat.odd_add, Nat.odd_mul. reflexivity. Qed.

Lemma fresh_nocc eta N n : n < N -> tocc (fresh eta N) (eta n) = false.
Proof.
  intros H. pose proof (sumenv_ge eta N n H). destruct (tocc (fresh eta N) (eta n)) eqn:E; [|reflexivity].
  apply tocc_tmaxv in E. unfold fresh in E. lia.
Qed.

Lemma odd_neq_bname y k : Nat.odd y = true -> y <> bname k.
Proof. intros H ->. unfold bname in H. rewrite Nat.odd_add, Nat.odd_mul in H. discriminate. Qed.

Lemma oddenv_cons y eta : Nat.odd y = true -> oddenv eta -> oddenv (scons (TV y) eta).
Proof.
  intros Hy He [|n] v Hv; cbn in Hv; [apply Nat.eqb_eq in Hv; now subst | exact (He n v Hv)].
Qed.

Lemma oddenv_bname eta n k : oddenv eta -> tocc (bname k) (eta n) = false.
Proof.
  intro He. destruct (tocc (bname k) (eta n)) eqn:E; [|reflexivity].
  apply He in E. exfalso. exact (odd_neq_bname _ k E eq_refl).
Qed.

Lemma oddenv_trt_bname eta k t : oddenv eta -> tocc (bname k) (trt eta t) = false.
Proof.
  intro He. destruct (tocc (bname k) (trt eta t)) eqn:E; [|reflexivity].
  apply tocc_tsub in E as [n [_ E]]. now rewrite oddenv_bname in E.
Qed.

Lemma tr_shift eta y (psi : form) : tr (scons y eta) (psi[↑]) = tr eta psi.
Proof. rewrite tr_subst. apply tr_ext. intro n. reflexivity. Qed.

Lemma tr_inst eta t (phi : form) : tr eta (phi[t..]) = tr (scons (trt eta t) eta) phi.
Proof. rewrite tr_subst. apply tr_ext. intros []; reflexivity. Qed.

Lemma tr_ext_fb (phi : form) N eta eta' : fb N phi -> (forall n, n < N -> eta n = eta' n) -> tr eta phi = tr eta' phi.
Proof.
  enough (G : forall ff (phi : @Core.form _ _ _ ff) N eta eta',
             fb N phi -> (forall n, n < N -> eta n = eta' n) -> tr eta phi = tr eta' phi) by apply G.
  clear. intros ff phi; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros N eta eta' Hfb H; cbn in *.
  - reflexivity.
  - destruct P; cbn in *. destruct Hfb as [H1 H2]. unfold trt.
    rewrite (tsub_ext eta eta' (tl (Vector.hd v))), (tsub_ext eta eta' (tl (Vector.hd (Vector.tl v))));
      [reflexivity | |]; intros n Hn; apply H; auto.
  - destruct Hfb as [Ha Hb]. rewrite (IHa N eta eta' Ha H).
    destruct op; [now rewrite (IHb N eta eta' Hb H) | now rewrite (IHb N eta eta' Hb H) |].
    destruct b; try reflexivity; now rewrite (IHb N eta eta' Hb H).
  - destruct q; [apply (f_equal (Wal _)) | apply (f_equal (Wex _))];
      apply (IHa (S N)); auto; intros [|n] Hn; cbn; auto; apply H; lia.
Qed.

Lemma notbinder_bname (phi : form) : notbinder (bname (qd phi)) phi.
Proof. intros k Hk E. unfold bname in E. lia. Qed.

Lemma sfree_odd s (phi : form) eta : (forall v, tocc v s = true -> Nat.odd v = true) -> sfree s (tr eta phi).
Proof. intros H v Hv. apply bnd_tr, notbinder_odd, H, Hv. Qed.

(** The binder of [quant q phi] vs. a fresh odd name [y]: alpha-conversion. *)
Lemma alpha_tr eta y N (phi : form) :
  oddenv eta -> Nat.odd y = true -> fb (S N) phi -> (forall n, n < N -> tocc y (eta n) = false) ->
  let B := bname (qd phi) in
  y <> B /\ bnd y (tr (scons (TV y) eta) phi) = false /\ occ B (tr (scons (TV y) eta) phi) = false /\
  sb y (TV B) (tr (scons (TV y) eta) phi) = tr (scons (TV B) eta) phi.
Proof.
  intros He Hy Hfb Hn B.
  assert (HyB : y <> B) by (apply odd_neq_bname; exact Hy).
  split; [exact HyB|]. split; [apply bnd_tr, notbinder_odd, Hy|]. split.
  - apply (occ_tr phi (S N) (scons (TV y) eta) B); [exact Hfb | | apply notbinder_bname].
    intros [|n] _; cbn; [apply Nat.eqb_neq; congruence | apply oddenv_bname, He].
  - rewrite sb_tr by apply notbinder_odd, Hy. apply (tr_ext_fb _ (S N)); [exact Hfb|].
    intros [|n] Hlt; cbn; [now rewrite Nat.eqb_refl|]. apply sbt_noocc, Hn. lia.
Qed.

(** instantiation of the binder of [quant q phi] by the term [s] (odd variables only) *)
Lemma inst_tr eta s (phi : form) : oddenv eta -> (forall v, tocc v s = true -> Nat.odd v = true) ->
  let B := bname (qd phi) in
  tocc B s = false /\ bnd B (tr (scons (TV B) eta) phi) = false /\ sfree s (tr (scons (TV B) eta) phi) /\
  sb B s (tr (scons (TV B) eta) phi) = tr (scons s eta) phi.
Proof.
  intros He Hs B.
  split; [destruct (tocc B s) eqn:E; [exfalso; apply Hs in E; exact (odd_neq_bname _ _ E eq_refl) | reflexivity]|].
  split; [apply bnd_tr, notbinder_bname|].
  split; [apply sfree_odd, Hs|].
  rewrite sb_tr by apply notbinder_bname.
  apply tr_ext. intros [|n]; cbn; [now rewrite Nat.eqb_refl|]. apply sbt_noocc, oddenv_bname, He.
Qed.

Lemma trt_odd eta t : oddenv eta -> forall v, tocc v (trt eta t) = true -> Nat.odd v = true.
Proof. intros He v Hv. apply tocc_tsub in Hv as [n [_ Hv]]. exact (He n v Hv). Qed.

Lemma map_tr_shift eta y (A : list form) : map (tr (scons y eta)) (map (subst_form ↑) A) = map (tr eta) A.
Proof. rewrite map_map. apply map_ext. intro. apply tr_shift. Qed.

Lemma fresh_not_occ eta N (A : list form) : (forall psi, In psi A -> fb N psi) ->
  forall h, In h (map (tr eta) A) -> occ (fresh eta N) h = false.
Proof.
  intros HA h Hh. apply in_map_iff in Hh as [psi [<- Hpsi]].
  apply (occ_tr psi N eta); [apply HA, Hpsi | intros n Hn; apply fresh_nocc, Hn | apply notbinder_odd, fresh_odd].
Qed.

Section ND.
Variable X : wff -> Prop.
Local Notation lprov := (pprov X).
Local Notation der := (der X).

Theorem nd_sound (A : list form) (phi : form) :
  A ⊢C phi -> forall eta, oddenv eta -> der (map (tr eta) A) (tr eta phi).
Proof.
  intro D.
  pattern class, A, phi. revert D. generalize class. intros p D. pattern p, A, phi.
  revert p A phi D. apply prv_ind_full.
  - (* II *) intros p A phi psi _ IH eta He. specialize (IH eta He). cbn [map] in IH.
    apply (der_leqv X _ _ _ (leqv_sym X _ _ (tr_imp_equiv X eta phi psi))). now apply ded.
  - (* IE *) intros p A phi psi _ IH1 _ IH2 eta He.
    specialize (IH1 eta He). apply (der_leqv X _ _ _ (tr_imp_equiv X eta phi psi)) in IH1.
    exact (dmp _ _ _ _ IH1 (IH2 eta He)).
  - (* AllI *) intros p A phi _ IH eta He.
    destruct (fb_exists_L A) as [N1 HN1]. destruct (fb_exists phi) as [N2 HN2].
    set (N := N1 + N2). set (y := fresh eta N).
    assert (HA : forall psi, In psi A -> fb N psi) by (intros; eapply fb_mono; eauto; lia).
    assert (Hphi : fb (S N) phi) by (eapply fb_mono; eauto; lia).
    specialize (IH (scons (TV y) eta) (oddenv_cons _ _ (fresh_odd eta N) He)).
    rewrite map_tr_shift in IH.
    apply (der_gen X _ y) in IH; [| apply fresh_not_occ, HA].
    destruct (alpha_tr eta y N phi He (fresh_odd eta N) Hphi (fun n Hn => fresh_nocc eta N n Hn))
      as (Hne & Hbnd & Hocc & Hren).
    pose proof (lalpha X y _ _ Hne Hbnd Hocc) as Hal. rewrite Hren in Hal.
    exact (dmp _ _ _ _ (dthm _ _ _ Hal) IH).
  - (* AllE *) intros p A t phi _ IH eta He.
    rewrite tr_inst. specialize (IH eta He). cbn [tr] in IH.
    destruct (inst_tr eta (trt eta t) phi He (trt_odd eta t He)) as (Hne & Hb1 & Hb2 & Hren).
    pose proof (lspec X _ _ _ Hne Hb1 Hb2) as Hs. rewrite Hren in Hs.
    exact (dmp _ _ _ _ (dthm _ _ _ Hs) IH).
  - (* ExI *) intros p A t phi _ IH eta He.
    specialize (IH eta He). rewrite tr_inst in IH. cbn [tr].
    destruct (inst_tr eta (trt eta t) phi He (trt_odd eta t He)) as (Hne & Hb1 & Hb2 & Hren).
    pose proof (lexi X _ _ _ Hne Hb1 Hb2) as Hs. rewrite Hren in Hs.
    exact (dmp _ _ _ _ (dthm _ _ _ Hs) IH).
  - (* ExE *) intros p A phi psi _ IH1 _ IH2 eta He.
    destruct (fb_exists_L A) as [N1 HN1]. destruct (fb_exists phi) as [N2 HN2].
    destruct (fb_exists psi) as [N3 HN3].
    set (N := N1 + N2 + N3). set (y := fresh eta N).
    assert (HA : forall chi, In chi A -> fb N chi) by (intros; eapply fb_mono; eauto; lia).
    assert (Hphi : fb (S N) phi) by (eapply fb_mono; eauto; lia).
    assert (Hpsi : fb N psi) by (eapply fb_mono; eauto; lia).
    specialize (IH2 (scons (TV y) eta) (oddenv_cons _ _ (fresh_odd eta N) He)).
    cbn [map] in IH2. rewrite map_tr_shift, tr_shift in IH2.
    apply ded in IH2. apply (der_gen X _ y) in IH2; [| apply fresh_not_occ, HA].
    assert (Hy : occ y (tr eta psi) = false).
    { apply (occ_tr psi N eta); [exact Hpsi | intros n Hn; apply fresh_nocc, Hn | apply notbinder_odd, fresh_odd]. }
    pose proof (dmp _ _ _ _ (dthm _ _ _ (l_ex_elim X _ _ _ Hy)) IH2) as Hel.
    refine (dmp _ _ _ _ Hel _). specialize (IH1 eta He). cbn [tr] in IH1.
    destruct (alpha_tr eta y N phi He (fresh_odd eta N) Hphi (fun n Hn => fresh_nocc eta N n Hn))
      as (Hne & Hbnd & Hocc & Hren).
    (* E. B a  ->  E. y a[y/B]: alpha back from the fresh name *)
    assert (HyB : bname (qd phi) <> y) by (intro E0; apply Hne; symmetry; exact E0).
    assert (Hb' : bnd (bname (qd phi)) (tr (scons (TV (bname (qd phi))) eta) phi) = false)
      by apply bnd_tr, notbinder_bname.
    assert (Ho' : occ y (tr (scons (TV (bname (qd phi))) eta) phi) = false).
    { apply (occ_tr phi (S N) _ y); [exact Hphi | | apply notbinder_odd, fresh_odd].
      intros [|n] Hn; cbn; [apply Nat.eqb_neq; exact HyB | apply fresh_nocc; lia]. }
    pose proof (lalpha_ex X _ _ _ HyB Hb' Ho') as Hal.
    rewrite sb_tr in Hal by apply notbinder_bname.
    assert (E : tr (fun n => sbt (bname (qd phi)) (TV y) (scons (TV (bname (qd phi))) eta n)) phi
                = tr (scons (TV y) eta) phi).
    { apply tr_ext. intros [|n]; cbn; [now rewrite Nat.eqb_refl|]. apply sbt_noocc, oddenv_bname, He. }
    rewrite E in Hal. exact (dmp _ _ _ _ (dthm _ _ _ Hal) IH1).
  - (* Exp *) intros p A phi _ IH eta He. exact (dmp _ _ _ _ (dthm _ _ _ (l_botw_elim X _)) (IH eta He)).
  - (* Ctx *) intros p A phi H eta He. apply dhyp. now apply in_map.
  - (* CI *) intros p A phi psi _ IH1 _ IH2 eta He. cbn [tr].
    exact (dmp _ _ _ _ (dmp _ _ _ _ (dthm _ _ _ (lpc_andi X _ _)) (IH1 eta He)) (IH2 eta He)).
  - (* CE1 *) intros p A phi psi _ IH eta He. exact (dmp _ _ _ _ (dthm _ _ _ (lpc_andl X _ _)) (IH eta He)).
  - (* CE2 *) intros p A phi psi _ IH eta He. exact (dmp _ _ _ _ (dthm _ _ _ (lpc_andr X _ _)) (IH eta He)).
  - (* DI1 *) intros p A phi psi _ IH eta He. cbn [tr].
    exact (dmp _ _ _ _ (dthm _ _ _ (B3 X _ _)) (IH eta He)).
  - (* DI2 *) intros p A phi psi _ IH eta He. cbn [tr].
    exact (dmp _ _ _ _ (dthm _ _ _ (lpc_K X _ _)) (IH eta He)).
  - (* DE *) intros p A phi psi theta _ IH1 _ IH2 _ IH3 eta He.
    specialize (IH1 eta He). specialize (IH2 eta He). specialize (IH3 eta He). cbn [map tr] in *.
    apply ded in IH2. apply ded in IH3.
    exact (dmp _ _ _ _ (dmp _ _ _ _ (dmp _ _ _ _ (dthm _ _ _ (l_case X _ _ _)) IH1) IH2) IH3).
  - (* Pc *) intros A phi psi eta He. apply dthm.
    refine (lprov_leqv X _ _ _ (l_peirce X (tr eta phi) (tr eta psi))).
    apply leqv_sym. eapply leqv_trans; [apply tr_imp_equiv|]. apply leqv_im; [|apply leqv_refl].
    eapply leqv_trans; [apply tr_imp_equiv|]. apply leqv_im; [apply tr_imp_equiv | apply leqv_refl].
Qed.
End ND.

Print Assumptions nd_sound.
