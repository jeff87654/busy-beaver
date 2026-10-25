(** * PA_dB: named PA wffs (PALogic) -> de Bruijn formulas of the library's PA signature.
    [dB rho a]: [rho] maps named variables to library terms. *)
From Coq Require Import Arith Lia List Bool.
From Undecidability.FOL Require Import PA.
From PAGB Require Import PALogic.
Import ListNotations.
Unset Implicit Arguments.

Fixpoint dBt (rho : nat -> term) (t : tm) : term :=
  match t with
  | TV n => rho n
  | TZ => zero
  | TS t => σ (dBt rho t)
  | TP t s => dBt rho t ⊕ dBt rho s
  | TM t s => dBt rho t ⊗ dBt rho s
  end.

Definition shift_env (x : nat) (rho : nat -> term) : nat -> term :=
  fun v => if Nat.eqb v x then var 0 else (rho v)`[↑].

Arguments shift_env : simpl never.

Fixpoint dB (rho : nat -> term) (a : wff) : form :=
  match a with
  | Weq t s => dBt rho t == dBt rho s
  | Wim a b => dB rho a → dB rho b
  | Wn a => dB rho a → ⊥
  | Wal x a => ∀ dB (shift_env x rho) a
  end.

Definition upd (rho : nat -> term) (x : nat) (t : term) : nat -> term :=
  fun v => if Nat.eqb v x then t else rho v.

(** ** Extensionality and substitution *)
Lemma dBt_ext_occ rho rho' t : (forall v, tocc v t = true -> rho v = rho' v) -> dBt rho t = dBt rho' t.
Proof.
  induction t; cbn; intro H.
  - apply H. apply Nat.eqb_refl.
  - reflexivity.
  - now rewrite IHt.
  - rewrite IHt1, IHt2; [reflexivity | |]; intros v Hv; apply H; now rewrite Hv, ?orb_true_r.
  - rewrite IHt1, IHt2; [reflexivity | |]; intros v Hv; apply H; now rewrite Hv, ?orb_true_r.
Qed.

Lemma dBt_ext rho rho' t : (forall v, rho v = rho' v) -> dBt rho t = dBt rho' t.
Proof. intro H. apply dBt_ext_occ. intros v _. apply H. Qed.

Lemma dBt_subst rho sg t : (dBt rho t)`[sg] = dBt (rho >> subst_term sg) t.
Proof. induction t; cbn; try reflexivity; now rewrite ?IHt, ?IHt1, ?IHt2. Qed.

Lemma dB_ext_occ rho rho' a : (forall v, occ v a = true -> rho v = rho' v) -> dB rho a = dB rho' a.
Proof.
  revert rho rho'; induction a as [t s | a IHa b IHb | a IHa | x a IHa]; intros rho rho' H; cbn.
  - cbn in H. rewrite (dBt_ext_occ rho rho' t), (dBt_ext_occ rho rho' s); [reflexivity | |];
      intros v Hv; apply H; now rewrite Hv, ?orb_true_r.
  - rewrite (IHa rho rho'), (IHb rho rho'); [reflexivity | |]; intros v Hv; apply H; cbn; now rewrite Hv, ?orb_true_r.
  - now rewrite (IHa rho rho').
  - f_equal. apply IHa. intros v Hv. unfold shift_env. destruct (Nat.eqb_spec v x); [reflexivity|].
    rewrite H; [reflexivity|]. cbn. now rewrite Hv, orb_true_r.
Qed.

Lemma dB_ext rho rho' a : (forall v, rho v = rho' v) -> dB rho a = dB rho' a.
Proof. intro H. apply dB_ext_occ. intros v _. apply H. Qed.

Lemma dB_subst rho sg a : (dB rho a)[sg] = dB (rho >> subst_term sg) a.
Proof.
  revert rho sg; induction a as [t s | a IHa b IHb | a IHa | x a IHa]; intros rho sg; cbn.
  - now rewrite !dBt_subst.
  - now rewrite IHa, IHb.
  - now rewrite IHa.
  - f_equal. rewrite IHa. apply dB_ext. intros v. unfold shift_env, funcomp.
    destruct (Nat.eqb v x); cbn; [reflexivity|]. apply up_term.
Qed.

Lemma shift_env_inst x rho t v : (shift_env x rho >> subst_term (t..)) v = upd rho x t v.
Proof. unfold shift_env, upd, funcomp. destruct (Nat.eqb v x); cbn; [reflexivity | apply subst_term_shift]. Qed.

Lemma dB_inst x rho t a : (dB (shift_env x rho) a)[t..] = dB (upd rho x t) a.
Proof. rewrite dB_subst. apply dB_ext. apply shift_env_inst. Qed.

Lemma shift_env_neq x rho v : v <> x -> shift_env x rho v = (rho v)`[↑].
Proof. intro H. unfold shift_env. apply Nat.eqb_neq in H. now rewrite H. Qed.

Lemma shift_env_eq x rho : shift_env x rho x = var 0.
Proof. unfold shift_env. now rewrite Nat.eqb_refl. Qed.

Lemma upd_eq rho x t : upd rho x t x = t.
Proof. unfold upd. now rewrite Nat.eqb_refl. Qed.

Lemma upd_neq rho x t v : v <> x -> upd rho x t v = rho v.
Proof. intro H. unfold upd. apply Nat.eqb_neq in H. now rewrite H. Qed.

(** a variable not occurring in [t]: shifting the environment at it shifts the term *)
Lemma dBt_shift_nocc x rho t : tocc x t = false -> dBt (shift_env x rho) t = (dBt rho t)`[↑].
Proof.
  intro H. rewrite dBt_subst. apply dBt_ext_occ. intros v Hv.
  apply shift_env_neq. intros ->. congruence.
Qed.

Lemma dBt_upd_nocc x rho s t : tocc x t = false -> dBt (upd rho x s) t = dBt rho t.
Proof.
  intro H. apply dBt_ext_occ. intros v Hv. apply upd_neq. intros ->. congruence.
Qed.

Lemma dB_upd_nocc x rho s a : occ x a = false -> dB (upd rho x s) a = dB rho a.
Proof.
  intro H. apply dB_ext_occ. intros v Hv. apply upd_neq. intros ->. congruence.
Qed.

(** ** Free variables, iterated quantifiers, a bound on the variables *)
Fixpoint fr (v : nat) (a : wff) : bool :=
  match a with
  | Weq t s => tocc v t || tocc v s
  | Wim a b => fr v a || fr v b
  | Wn a => fr v a
  | Wal y a => negb (Nat.eqb y v) && fr v a
  end.

Lemma fr_occ v a : fr v a = true -> occ v a = true.
Proof.
  induction a; cbn; auto.
  - intro H. apply orb_true_iff in H as [H|H]; [rewrite IHa1 | rewrite IHa2]; auto using orb_true_r.
  - intro H. apply andb_true_iff in H as [_ H]. rewrite IHa; auto using orb_true_r.
Qed.

Lemma dB_ext_fr rho rho' a : (forall v, fr v a = true -> rho v = rho' v) -> dB rho a = dB rho' a.
Proof.
  revert rho rho'; induction a as [t s | a IHa b IHb | a IHa | x a IHa]; intros rho rho' H; cbn.
  - cbn in H. rewrite (dBt_ext_occ rho rho' t), (dBt_ext_occ rho rho' s); [reflexivity | |];
      intros v Hv; apply H; now rewrite Hv, ?orb_true_r.
  - rewrite (IHa rho rho'), (IHb rho rho'); [reflexivity | |]; intros v Hv; apply H; cbn; now rewrite Hv, ?orb_true_r.
  - now rewrite (IHa rho rho').
  - f_equal. apply IHa. intros v Hv. unfold shift_env. destruct (Nat.eqb_spec v x); [reflexivity|].
    rewrite H; [reflexivity|]. cbn. rewrite Hv, andb_true_r. apply negb_true_iff, Nat.eqb_neq. congruence.
Qed.

Fixpoint galls (ps : list nat) (a : wff) : wff :=
  match ps with [] => a | p :: ps => Wal p (galls ps a) end.

Lemma fr_galls v ps a : fr v (galls ps a) = true -> ~ In v ps /\ fr v a = true.
Proof.
  induction ps as [|p ps IH]; cbn; [tauto|]. intro H. apply andb_true_iff in H as [H1 H2].
  apply IH in H2 as [H2 H3]. split; [|exact H3]. intros [->|Hv]; [|tauto].
  rewrite Nat.eqb_refl in H1. discriminate.
Qed.

Fixpoint tmaxv (t : tm) : nat :=
  match t with TV n => n | TZ => 0 | TS t => tmaxv t | TP t s | TM t s => Nat.max (tmaxv t) (tmaxv s) end.

Fixpoint maxv (a : wff) : nat :=
  match a with
  | Weq t s => Nat.max (tmaxv t) (tmaxv s)
  | Wim a b => Nat.max (maxv a) (maxv b)
  | Wn a => maxv a
  | Wal x a => Nat.max x (maxv a)
  end.

Lemma tocc_tmaxv v t : tocc v t = true -> v <= tmaxv t.
Proof.
  induction t; cbn; intro H; try discriminate.
  - apply Nat.eqb_eq in H. lia.
  - auto.
  - apply orb_true_iff in H as [H|H]; [specialize (IHt1 H) | specialize (IHt2 H)]; lia.
  - apply orb_true_iff in H as [H|H]; [specialize (IHt1 H) | specialize (IHt2 H)]; lia.
Qed.

Lemma occ_maxv v a : occ v a = true -> v <= maxv a.
Proof.
  induction a; cbn; intro H.
  - apply orb_true_iff in H as [H|H]; apply tocc_tmaxv in H; lia.
  - apply orb_true_iff in H as [H|H]; [specialize (IHa1 H) | specialize (IHa2 H)]; lia.
  - auto.
  - apply orb_true_iff in H as [H|H]; [apply Nat.eqb_eq in H; lia | specialize (IHa H); lia].
Qed.

Lemma shift_env_upd_same x e u v : shift_env x (upd e x u) v = shift_env x e v.
Proof.
  unfold shift_env, upd. destruct (Nat.eqb_spec v x); reflexivity.
Qed.

Lemma dB_Wal_upd_same x e u a : dB (upd e x u) (Wal x a) = dB e (Wal x a).
Proof. cbn [dB]. f_equal. apply dB_ext. apply shift_env_upd_same. Qed.
