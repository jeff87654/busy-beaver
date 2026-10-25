(** * PA_tr: library PA formulas -> named wffs (PALogic), the inverse direction of PA_dB.

    [tr eta phi]: [eta] maps de Bruijn indices to named terms.  As in zf/stdzf/coq/Std_tr.v, a
    quantifier over [phi] binds the name [bname (qd phi)] (even, >= 2; [qd] = quantifier depth),
    so binder names do not depend on the context and translation commutes EXACTLY with every
    substitution ([tr_subst]).  Free variables get odd names from the caller.
    [falsity] becomes the closed refutable wff [botw] := -. 0 = 0;  [phi -> falsity] becomes a
    negation.  Library terms are first converted to [tm] with de Bruijn indices as variables ([tl]). *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import PA.
From PAGB Require Import PALogic PA_dB PA_LProp PA_LMeta.
Import ListNotations.
Unset Implicit Arguments.

(** ** Terms *)
Fixpoint tsub (e : nat -> tm) (t : tm) : tm :=
  match t with
  | TV n => e n
  | TZ => TZ
  | TS t => TS (tsub e t)
  | TP t s => TP (tsub e t) (tsub e s)
  | TM t s => TM (tsub e t) (tsub e s)
  end.

Lemma tsub_comp e e' t : tsub e (tsub e' t) = tsub (fun n => tsub e (e' n)) t.
Proof. induction t; cbn; congruence. Qed.

Lemma tsub_ext e e' t : (forall n, tocc n t = true -> e n = e' n) -> tsub e t = tsub e' t.
Proof.
  induction t; cbn; intro H.
  - apply H. apply Nat.eqb_refl.
  - reflexivity.
  - now rewrite IHt.
  - rewrite IHt1, IHt2; [reflexivity | |]; intros n Hn; apply H; now rewrite Hn, ?orb_true_r.
  - rewrite IHt1, IHt2; [reflexivity | |]; intros n Hn; apply H; now rewrite Hn, ?orb_true_r.
Qed.

Lemma tsub_id t : tsub TV t = t.
Proof. induction t; cbn; congruence. Qed.

Lemma tocc_tsub v e t : tocc v (tsub e t) = true -> exists n, tocc n t = true /\ tocc v (e n) = true.
Proof.
  induction t; cbn; intro H; try discriminate.
  - exists n. now rewrite Nat.eqb_refl.
  - auto.
  - apply orb_true_iff in H as [H|H]; [destruct (IHt1 H) as [n [H1 H2]] | destruct (IHt2 H) as [n [H1 H2]]];
      exists n; now rewrite H1, ?orb_true_r.
  - apply orb_true_iff in H as [H|H]; [destruct (IHt1 H) as [n [H1 H2]] | destruct (IHt2 H) as [n [H1 H2]]];
      exists n; now rewrite H1, ?orb_true_r.
Qed.

Lemma sbt_tsub x s e t : sbt x s (tsub e t) = tsub (fun n => sbt x s (e n)) t.
Proof. induction t; cbn; congruence. Qed.

Definition mk (f : PA_funcs) : Vector.t tm (PA_funcs_ar f) -> tm :=
  match f with
  | Zero => fun _ => TZ
  | Succ => fun w => TS (Vector.hd w)
  | Plus => fun w => TP (Vector.hd w) (Vector.hd (Vector.tl w))
  | Mult => fun w => TM (Vector.hd w) (Vector.hd (Vector.tl w))
  end.

Fixpoint tl (t : term) : tm :=
  match t with
  | var n => TV n
  | func f v => mk f (Vector.map tl v)
  end.

Lemma vec0 {A} (v : Vector.t A 0) : v = Vector.nil _.
Proof. apply (Vector.case0 (fun u => u = Vector.nil _)). reflexivity. Qed.

Lemma vec1 {A} (v : Vector.t A 1) : v = Vector.cons _ (Vector.hd v) _ (Vector.nil _).
Proof. rewrite (Vector.eta v) at 1. f_equal. apply vec0. Qed.

Lemma vec2 {A} (v : Vector.t A 2) :
  v = Vector.cons _ (Vector.hd v) _ (Vector.cons _ (Vector.hd (Vector.tl v)) _ (Vector.nil _)).
Proof. rewrite (Vector.eta v) at 1. f_equal. apply vec1. Qed.

Lemma tl_subst (t : term) sg : tl (t`[sg]) = tsub (fun n => tl (sg n)) (tl t).
Proof.
  induction t as [n|f v IH] using term_ind; [reflexivity|].
  destruct f; cbn in v |- *.
  - reflexivity.
  - rewrite (vec1 v) in IH |- *. cbn. f_equal. apply IH. now left.
  - rewrite (vec2 v) in IH |- *. cbn. f_equal; apply IH; [now left | right; now left].
  - rewrite (vec2 v) in IH |- *. cbn. f_equal; apply IH; [now left | right; now left].
Qed.

Definition trt (eta : nat -> tm) (t : term) : tm := tsub eta (tl t).

Lemma trt_subst eta (t : term) sg : trt eta (t`[sg]) = trt (fun n => trt eta (sg n)) t.
Proof. unfold trt. rewrite tl_subst, tsub_comp. reflexivity. Qed.

(** ** The translation *)
Definition botw : wff := Wn (Weq TZ TZ).
Definition bname (k : nat) : nat := 2 * k + 2.
Arguments bname : simpl never.

Fixpoint qd {ff} (phi : @Core.form _ _ _ ff) : nat :=
  match phi with
  | falsity => 0
  | atom _ _ => 0
  | bin _ a b => Nat.max (qd a) (qd b)
  | quant _ a => S (qd a)
  end.

Definition tatom (eta : nat -> tm) (P : PA_preds) : Vector.t term (PA_preds_ar P) -> wff :=
  match P with
  | Eq => fun v => Weq (trt eta (Vector.hd v)) (trt eta (Vector.hd (Vector.tl v)))
  end.

Fixpoint tr {ff} (eta : nat -> tm) (phi : @Core.form _ _ _ ff) : wff :=
  match phi with
  | falsity => botw
  | atom P v => tatom eta P v
  | bin Conj a b => Wa (tr eta a) (tr eta b)
  | bin Disj a b => Wim (Wn (tr eta a)) (tr eta b)
  | bin Impl a b =>
      match b with
      | falsity => Wn (tr eta a)
      | _ => Wim (tr eta a) (tr eta b)
      end
  | quant All a => Wal (bname (qd a)) (tr (scons (TV (bname (qd a))) eta) a)
  | quant Ex a => Wex (bname (qd a)) (tr (scons (TV (bname (qd a))) eta) a)
  end.

Lemma tr_ext {ff} (phi : @Core.form _ _ _ ff) eta eta' :
  (forall n, eta n = eta' n) -> tr eta phi = tr eta' phi.
Proof.
  revert eta eta'; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros eta eta' H; cbn.
  - reflexivity.
  - destruct P; cbn; unfold trt; now rewrite !(tsub_ext eta eta') by auto.
  - destruct op.
    + now rewrite (IHa eta eta'), (IHb eta eta').
    + now rewrite (IHa eta eta'), (IHb eta eta').
    + destruct b; try now rewrite (IHa eta eta').
      all: now rewrite (IHa eta eta'), (IHb eta eta').
  - destruct q; f_equal; apply IHa; intros []; cbn; auto.
Qed.

Lemma qd_subst {ff} (phi : @Core.form _ _ _ ff) sigma : qd (phi[sigma]) = qd phi.
Proof.
  revert sigma; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros sigma; cbn; auto.
Qed.

Lemma tr_subst {ff} (phi : @Core.form _ _ _ ff) eta sigma :
  tr eta (phi[sigma]) = tr (fun n => trt eta (sigma n)) phi.
Proof.
  revert eta sigma; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros eta sigma; cbn.
  - reflexivity.
  - destruct P; cbn in v |- *. rewrite (vec2 v). cbn. rewrite !tl_subst, !tsub_comp. reflexivity.
  - destruct op.
    + now rewrite (IHa eta sigma), (IHb eta sigma).
    + now rewrite (IHa eta sigma), (IHb eta sigma).
    + destruct b; cbn; try now rewrite (IHa eta sigma).
      all: rewrite (IHa eta sigma); f_equal; exact (IHb eta sigma).
  - rewrite qd_subst. destruct q; f_equal; rewrite IHa; apply tr_ext; intros [|n]; cbn; [reflexivity| | reflexivity|];
      unfold funcomp, trt; rewrite tl_subst, tsub_comp; apply tsub_ext; intros; reflexivity.
Qed.

(** ** Free indices, occurrence, binders, substitution *)
Definition tb (N : nat) (t : term) : Prop := forall n, tocc n (tl t) = true -> n < N.

Fixpoint fb {ff} (N : nat) (phi : @Core.form _ _ _ ff) : Prop :=
  match phi with
  | falsity => True
  | atom P v =>
      match P return Vector.t term (PA_preds_ar P) -> Prop with
      | Eq => fun v => tb N (Vector.hd v) /\ tb N (Vector.hd (Vector.tl v))
      end v
  | bin _ a b => fb N a /\ fb N b
  | quant _ a => fb (S N) a
  end.

Lemma tb_mono N M t : tb N t -> N <= M -> tb M t.
Proof. intros H HM n Hn. specialize (H n Hn). lia. Qed.

Lemma tb_exists t : exists N, tb N t.
Proof. exists (S (tmaxv (tl t))). intros n Hn. apply tocc_tmaxv in Hn. lia. Qed.

Lemma fb_mono {ff} (phi : @Core.form _ _ _ ff) N M : fb N phi -> N <= M -> fb M phi.
Proof.
  revert N M; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros N M H HM; cbn in *.
  - exact I.
  - destruct P; cbn in *. destruct H; split; eapply tb_mono; eauto.
  - destruct H; split; eauto.
  - apply (IHa (S N)); [exact H | lia].
Qed.

Lemma fb_exists {ff} (phi : @Core.form _ _ _ ff) : exists N, fb N phi.
Proof.
  induction phi as [|ff P v|ff op a [N HN] b [M HM]|ff q a [N HN]].
  - exists 0. exact I.
  - destruct P; cbn. destruct (tb_exists (Vector.hd v)) as [N HN].
    destruct (tb_exists (Vector.hd (Vector.tl v))) as [M HM].
    exists (N + M). split; eapply tb_mono; eauto; lia.
  - exists (N + M). split; eapply fb_mono; eauto; lia.
  - exists N. cbn. eapply fb_mono; eauto.
Qed.

Lemma fb_exists_L (A : list form) : exists N, forall phi, In phi A -> fb N phi.
Proof.
  induction A as [|a A [N HN]].
  - exists 0. intros _ [].
  - destruct (fb_exists a) as [M HM]. exists (N + M). intros phi [<-|H].
    + eapply fb_mono; eauto; lia.
    + eapply fb_mono; eauto; lia.
Qed.

Definition notbinder {ff} (y : nat) (phi : @Core.form _ _ _ ff) : Prop :=
  forall k, k < qd phi -> y <> bname k.

Lemma notbinder_odd {ff} y (phi : @Core.form _ _ _ ff) : Nat.odd y = true -> notbinder y phi.
Proof.
  intros H k _ ->. unfold bname in H. rewrite Nat.odd_add, Nat.odd_mul in H. discriminate.
Qed.

Lemma notbinder_bin_l {ff} y op (a b : @Core.form _ _ _ ff) : notbinder y (bin op a b) -> notbinder y a.
Proof. intros H k Hk. apply H. cbn. lia. Qed.

Lemma notbinder_bin_r {ff} y op (a b : @Core.form _ _ _ ff) : notbinder y (bin op a b) -> notbinder y b.
Proof. intros H k Hk. apply H. cbn. lia. Qed.

Lemma notbinder_quant {ff} y q (a : @Core.form _ _ _ ff) :
  notbinder y (quant q a) -> notbinder y a /\ y <> bname (qd a).
Proof. intros H. split; [intros k Hk|]; apply H; cbn; lia. Qed.

Lemma tocc_trt y eta N t : tb N t -> (forall n, n < N -> tocc y (eta n) = false) -> tocc y (trt eta t) = false.
Proof.
  intros Ht He. destruct (tocc y (trt eta t)) eqn:E; [|reflexivity].
  apply tocc_tsub in E as [n [H1 H2]]. rewrite He in H2; [discriminate | now apply Ht].
Qed.

Lemma occ_tr {ff} (phi : @Core.form _ _ _ ff) N eta y :
  fb N phi -> (forall n, n < N -> tocc y (eta n) = false) -> notbinder y phi -> occ y (tr eta phi) = false.
Proof.
  revert N eta; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros N eta Hfb Heta Hnb; cbn in *.
  - reflexivity.
  - destruct P; cbn in *. destruct Hfb as [H1 H2].
    now rewrite (tocc_trt y eta N _ H1 Heta), (tocc_trt y eta N _ H2 Heta).
  - destruct Hfb as [Ha Hb].
    assert (Ea : occ y (tr eta a) = false) by (eapply IHa; eauto using notbinder_bin_l).
    destruct op; cbn.
    + now rewrite Ea, (IHb N eta Hb Heta (notbinder_bin_r _ _ _ _ Hnb)).
    + now rewrite Ea, (IHb N eta Hb Heta (notbinder_bin_r _ _ _ _ Hnb)).
    + destruct b; cbn; try exact Ea.
      all: rewrite Ea; exact (IHb N eta Hb Heta (notbinder_bin_r _ _ _ _ Hnb)).
  - destruct (notbinder_quant _ _ _ Hnb) as [Hnb' HB].
    assert (E : occ y (tr (scons (TV (bname (qd a))) eta) a) = false).
    { apply (IHa (S N)); [exact Hfb | | exact Hnb']. intros [|n] Hn; cbn; [apply Nat.eqb_neq; congruence | apply Heta; lia]. }
    assert (HB' : Nat.eqb (bname (qd a)) y = false) by (apply Nat.eqb_neq; congruence).
    destruct q; cbn [tr occ Wex]; rewrite HB', E; reflexivity.
Qed.

Lemma bnd_tr {ff} (phi : @Core.form _ _ _ ff) eta z : notbinder z phi -> bnd z (tr eta phi) = false.
Proof.
  revert eta; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros eta Hnb; cbn in *.
  - reflexivity.
  - destruct P; reflexivity.
  - assert (Ea : bnd z (tr eta a) = false) by (eapply IHa; eauto using notbinder_bin_l).
    destruct op; cbn.
    + now rewrite Ea, (IHb eta (notbinder_bin_r _ _ _ _ Hnb)).
    + now rewrite Ea, (IHb eta (notbinder_bin_r _ _ _ _ Hnb)).
    + destruct b; cbn; try exact Ea.
      all: rewrite Ea; exact (IHb eta (notbinder_bin_r _ _ _ _ Hnb)).
  - destruct (notbinder_quant _ _ _ Hnb) as [Hnb' HB].
    assert (HB' : Nat.eqb (bname (qd a)) z = false) by (apply Nat.eqb_neq; congruence).
    destruct q; cbn [tr bnd Wex]; rewrite HB', IHa by exact Hnb'; reflexivity.
Qed.

Lemma sb_tr {ff} (phi : @Core.form _ _ _ ff) eta x s :
  notbinder x phi -> sb x s (tr eta phi) = tr (fun n => sbt x s (eta n)) phi.
Proof.
  revert eta; induction phi as [|ff P v|ff op a IHa b IHb|ff q a IHa]; intros eta Hx; cbn in *.
  - reflexivity.
  - destruct P; cbn. unfold trt. now rewrite !sbt_tsub.
  - assert (Ea : sb x s (tr eta a) = tr (fun n => sbt x s (eta n)) a)
      by (apply IHa; eauto using notbinder_bin_l).
    destruct op; cbn.
    + now rewrite Ea, (IHb eta (notbinder_bin_r _ _ _ _ Hx)).
    + now rewrite Ea, (IHb eta (notbinder_bin_r _ _ _ _ Hx)).
    + destruct b; cbn; try now rewrite Ea.
      all: rewrite Ea; f_equal; exact (IHb eta (notbinder_bin_r _ _ _ _ Hx)).
  - destruct (notbinder_quant _ _ _ Hx) as [Hx' HBx].
    assert (Hr : Nat.eqb (bname (qd a)) x = false) by (apply Nat.eqb_neq; congruence).
    destruct q; cbn [tr]; unfold Wex; cbn [sb]; rewrite Hr, IHa by assumption;
      [f_equal | do 3 f_equal]; apply tr_ext; intros []; cbn; [now rewrite Hr | reflexivity | now rewrite Hr | reflexivity].
Qed.
