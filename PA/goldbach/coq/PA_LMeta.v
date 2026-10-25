(** * PA_LMeta: metatheory of [pprov X] (any extra axioms X): deduction theorem, equality and term
    congruence, vacuous generalization, Leibniz substitution of a term for a variable,
    specialization to a term and alphabetic variance.
    Ported from zf/stdzf/coq/L1_LMeta.v (variables only) and extended to terms. *)
From Coq Require Import Arith.Arith Lia Lists.List Bool.Bool.
From PAGB Require Import PA_Pair PALogic PA_LProp PA_dB.
Import ListNotations.
Unset Implicit Arguments.

Section LMeta.
Variable X : wff -> Prop.
Local Notation lprov := (pprov X).
Let LDET := DET X.
Let LGEN := GEN X.
Let LB1 := B1 X.
Let LB2 := B2 X.
Let LB3 := B3 X.
Let LB4 := B4 X.
Let LB6a := B6a X.
Let LB6b := B6b X.
Let LB6c := B6c X.

(** ** Derived rules *)
Lemma lsyl a b c : lprov (Wim a b) -> lprov (Wim b c) -> lprov (Wim a c).
Proof. intros H1 H2. exact (LDET _ _ (LDET _ _ (LB1 a b c) H1) H2). Qed.

Lemma lcontra a b : lprov (Wim a b) -> lprov (Wim (Wn b) (Wn a)).
Proof. intro H. exact (LDET _ _ (lpc_contra X a b) H). Qed.

Lemma lal x a b : lprov (Wim a b) -> lprov (Wim (Wal x a) (Wal x b)).
Proof. intro H. exact (LDET _ _ (LB4 x a b) (LGEN x _ H)). Qed.

Lemma lex x a b : lprov (Wim a b) -> lprov (Wim (Wex x a) (Wex x b)).
Proof. intro H. unfold Wex. apply lcontra, lal, lcontra, H. Qed.

(** ** Deduction theorem (propositional, no GEN under hypotheses) *)
Inductive der (G : list wff) : wff -> Prop :=
  | dhyp a : In a G -> der G a
  | dthm a : lprov a -> der G a
  | dmp a b : der G (Wim a b) -> der G a -> der G b.

Lemma ruleS G h a b : der G (Wim h (Wim a b)) -> der G (Wim h a) -> der G (Wim h b).
Proof.
  intros H1 H2.
  assert (H3 : der G (Wim a (Wim h b))) by exact (dmp _ _ _ (dthm _ _ (lpc_C X h a b)) H1).
  assert (H4 : der G (Wim h (Wim h b))).
  { exact (dmp _ _ _ (dmp _ _ _ (dthm _ _ (LB1 h a (Wim h b))) H2) H3). }
  exact (dmp _ _ _ (dthm _ _ (lpc_W X h b)) H4).
Qed.

Lemma ded G h a : der (h :: G) a -> der G (Wim h a).
Proof.
  induction 1 as [a [<-|Ha] | a Ha | a b _ IH1 _ IH2].
  - apply dthm, lpc_id.
  - exact (dmp _ _ _ (dthm _ _ (lpc_K X a h)) (dhyp _ _ Ha)).
  - exact (dmp _ _ _ (dthm _ _ (lpc_K X a h)) (dthm _ _ Ha)).
  - exact (ruleS _ _ _ _ IH1 IH2).
Qed.

Lemma der_lprov a : der [] a -> lprov a.
Proof. induction 1 as [a []| |]; [assumption | exact (LDET _ _ IHder1 IHder2)]. Qed.

Lemma der_weak G G' a : der G a -> incl G G' -> der G' a.
Proof. induction 1; intros HG; [apply dhyp; auto | apply dthm; auto | eapply dmp; eauto]. Qed.

Ltac dh := apply dhyp; simpl; tauto.
Ltac dt H := apply dthm; exact H.
Ltac mp a := apply (dmp _ a).

(** ** Syntax: substitution of a term for a variable, binders *)
Fixpoint sbt (x : nat) (s : tm) (t : tm) : tm :=
  match t with
  | TV n => if Nat.eqb n x then s else TV n
  | TZ => TZ
  | TS t => TS (sbt x s t)
  | TP t r => TP (sbt x s t) (sbt x s r)
  | TM t r => TM (sbt x s t) (sbt x s r)
  end.

Fixpoint sb (x : nat) (s : tm) (a : wff) : wff :=
  match a with
  | Weq t r => Weq (sbt x s t) (sbt x s r)
  | Wim a b => Wim (sb x s a) (sb x s b)
  | Wn a => Wn (sb x s a)
  | Wal z a => if Nat.eqb z x then Wal z a else Wal z (sb x s a)
  end.

Fixpoint bnd (y : nat) (a : wff) : bool :=
  match a with
  | Weq _ _ => false
  | Wim a b => bnd y a || bnd y b
  | Wn a => bnd y a
  | Wal z a => Nat.eqb z y || bnd y a
  end.

(** no variable of [s] is bound in [a] *)
Definition sfree (s : tm) (a : wff) : Prop := forall v, tocc v s = true -> bnd v a = false.

Lemma occ_bnd y a : occ y a = false -> bnd y a = false.
Proof. induction a; simpl; intros; rewrite ?orb_false_iff in *; intuition. Qed.

Lemma tocc_sbt_self x s t : tocc x s = false -> tocc x (sbt x s t) = false.
Proof.
  intro H. induction t; cbn; auto.
  - destruct (Nat.eqb_spec n x); [exact H|]. cbn. now apply Nat.eqb_neq.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
Qed.

Lemma occ_sb_self x s a : tocc x s = false -> bnd x a = false -> occ x (sb x s a) = false.
Proof.
  intros Hs. induction a; cbn; intro H.
  - now rewrite !tocc_sbt_self.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IHa1, IHa2.
  - now apply IHa.
  - apply orb_false_iff in H as [H1 H2]. rewrite H1. cbn. rewrite H1. now apply IHa.
Qed.

Lemma sfree_im_l s a b : sfree s (Wim a b) -> sfree s a.
Proof. intros H v Hv. specialize (H v Hv). cbn in H. now apply orb_false_iff in H. Qed.
Lemma sfree_im_r s a b : sfree s (Wim a b) -> sfree s b.
Proof. intros H v Hv. specialize (H v Hv). cbn in H. now apply orb_false_iff in H. Qed.
Lemma sfree_n s a : sfree s (Wn a) -> sfree s a.
Proof. intros H v Hv. exact (H v Hv). Qed.
Lemma sfree_al s z a : sfree s (Wal z a) -> sfree s a /\ tocc z s = false.
Proof.
  intro H. split.
  - intros v Hv. specialize (H v Hv). cbn in H. now apply orb_false_iff in H.
  - destruct (tocc z s) eqn:E; [|reflexivity]. specialize (H z E). cbn in H.
    rewrite Nat.eqb_refl in H. discriminate.
Qed.

(** ** Vacuous generalization *)
Lemma lneg_vac y a : lprov (Wim a (Wal y a)) -> lprov (Wim (Wn a) (Wal y (Wn a))).
Proof.
  intro H.
  pose proof (lcontra _ _ (LB6c y a)) as H1.
  pose proof (lsyl _ _ _ H1 (lpc_nn_elim X _)) as H2.
  exact (lsyl _ _ _ H2 (lal y _ _ (lcontra _ _ H))).
Qed.

Lemma lvac y a : occ y a = false -> lprov (Wim a (Wal y a)).
Proof.
  induction a as [u v|a IHa b IHb|a IHa|z a IHa]; simpl; intro H;
    try (apply orb_false_iff in H as [H0 H0']).
  - exact (LB6a y u v H0 H0').
  - set (Y := Wal y (Wim a b)).
    assert (H1 : lprov (Wim (Wn a) Y)).
    { pose proof (lneg_vac y a (IHa ltac:(assumption))) as N.
      refine (lsyl _ _ _ N (lal y _ _ _)).
      exact (LDET _ _ (lpc_C X _ _ _) (LB3 a b)). }
    assert (H2 : lprov (Wim b Y)).
    { exact (lsyl _ _ _ (IHb ltac:(assumption)) (lal y _ _ (lpc_K X b a))). }
    apply der_lprov, ded. mp (Wim (Wn Y) Y); [dt (LB2 Y)|]. apply ded.
    mp (Wn a); [dt H1|]. mp (Wn b).
    + mp (Wim a b); [dt (lpc_contra X a b) | dh].
    + mp (Wn Y); [dt (lcontra _ _ H2) | dh].
  - exact (lneg_vac y a (IHa H)).
  - pose proof (lal z _ _ (IHa ltac:(assumption))) as H1.
    exact (lsyl _ _ _ H1 (LB6b z y a)).
Qed.

(** ** Specialization helpers *)
Lemma lall_ex x p q : lprov (Wim (Wal x (Wim p q)) (Wim (Wex x p) (Wex x q))).
Proof.
  unfold Wex.
  pose proof (LDET _ _ (LB4 x (Wim p q) (Wim (Wn q) (Wn p))) (LGEN x _ (lpc_contra X p q))) as H1.
  apply der_lprov, ded.
  mp (Wim (Wal x (Wn q)) (Wal x (Wn p))); [dt (lpc_contra X (Wal x (Wn q)) (Wal x (Wn p)))|].
  mp (Wal x (Wim (Wn q) (Wn p))); [dt (LB4 x (Wn q) (Wn p))|].
  mp (Wal x (Wim p q)); [dt H1 | dh].
Qed.

(** ** Term existence in general, from the two primitive forms *)
Lemma lex_elim y p c : occ y c = false -> lprov (Wim (Wal y (Wim p c)) (Wim (Wex y p) c)).
Proof.
  intro Hy. apply der_lprov, ded, ded.
  apply (dmp _ (Wex y (Wal y c))); [apply dthm, (LB6c y c)|].
  apply (dmp _ (Wex y c)); [apply dthm, (lex y _ _ (lvac y c Hy))|].
  apply (dmp _ (Wex y p)); [| apply dhyp; simpl; auto].
  apply (dmp _ (Wal y (Wim p c))); [apply dthm, lall_ex | apply dhyp; simpl; auto].
Qed.

Lemma tcode_fresh v t : tocc v t = true -> v < tcode t.
Proof.
  induction t; cbn; intro H; try discriminate.
  - apply Nat.eqb_eq in H. subst. pose proof (P_ge_l v 0). lia.
  - specialize (IHt H). pose proof (P_ge_l (tcode t) 1). lia.
  - apply orb_true_iff in H as [H|H]; [specialize (IHt1 H) | specialize (IHt2 H)];
      pose proof (P_ge_l (tcode t1) (tcode t2)); pose proof (P_ge_r (tcode t1) (tcode t2)); lia.
  - apply orb_true_iff in H as [H|H]; [specialize (IHt1 H) | specialize (IHt2 H)];
      pose proof (P_ge_l (tcode t1) (tcode t2)); pose proof (P_ge_r (tcode t1) (tcode t2)); lia.
Qed.

Lemma fcode_pos a : 0 < fcode a.
Proof.
  induction a; cbn; try lia.
  - pose proof (P_ge_l (fcode a1) (fcode a2)). lia.
  - pose proof (P_ge_l (fcode a) 1). lia.
Qed.

Lemma fcode_fresh v a : occ v a = true -> v < fcode a.
Proof.
  induction a as [t r|a1 IHa1 a2 IHa2|a IHa|n a IHa]; cbn; intro H.
  - apply orb_true_iff in H as [H|H]; apply tcode_fresh in H;
      pose proof (P_ge_l (tcode t) (tcode r)); pose proof (P_ge_r (tcode t) (tcode r)); lia.
  - pose proof (fcode_pos a1). pose proof (fcode_pos a2).
    pose proof (P_ge_l (fcode a1) (fcode a2)); pose proof (P_ge_r (fcode a1) (fcode a2)).
    apply orb_true_iff in H as [H|H]; [specialize (IHa1 H) | specialize (IHa2 H)]; lia.
  - specialize (IHa H). pose proof (P_ge_l (fcode a) 1). lia.
  - pose proof (P_ge_l n (fcode a)); pose proof (P_ge_r n (fcode a)).
    apply orb_true_iff in H as [H|H]; [apply Nat.eqb_eq in H; lia | specialize (IHa H); lia].
Qed.

Lemma fcode_nocc a : occ (fcode a) a = false.
Proof. destruct (occ (fcode a) a) eqn:E; [|reflexivity]. apply fcode_fresh in E. lia. Qed.

Lemma tcode_nocc t : tocc (S (tcode t)) t = false.
Proof. destruct (tocc (S (tcode t)) t) eqn:E; [|reflexivity]. apply tcode_fresh in E. lia. Qed.

Lemma lrefl_var x : lprov (Weq (TV x) (TV x)).
Proof.
  set (z := S x). assert (Hzx : z <> x) by (unfold z; lia).
  assert (H1 : lprov (Wim (Weq (TV z) (TV x)) (Weq (TV x) (TV x))))
    by exact (LDET _ _ (lpc_W X _ _) (E8 X (TV z) (TV x) (TV x))).
  refine (LDET _ _ (LDET _ _ (lex_elim z (Weq (TV z) (TV x)) (Weq (TV x) (TV x)) _) (LGEN z _ H1)) (B7v X z x Hzx)).
  cbn [occ tocc]. apply orb_false_iff; split; apply Nat.eqb_neq; congruence.
Qed.

Theorem lb7 x t : tocc x t = false -> lprov (Wex x (Weq (TV x) t)).
Proof.
  intro Hx. set (x0 := S (tcode t)).
  destruct (Nat.eq_dec x x0) as [->|Hne]; [exact (B7c X t)|].
  assert (Hx0 : tocc x0 t = false) by apply tcode_nocc.
  (* x0 = t -> E. x x = t *)
  assert (I : lprov (Wim (Weq (TV x0) t) (Wex x (Weq (TV x) t)))).
  { assert (Q : lprov (Wim (Weq (TV x0) t) (Wim (Weq (TV x) (TV x0)) (Weq (TV x) t)))).
    { apply der_lprov, ded, ded.
      apply (dmp _ (Weq (TV x0) t)); [| apply dhyp; simpl; auto].
      apply (dmp _ (Weq (TV x0) (TV x))).
      - apply dthm, (E8 X (TV x0) (TV x) t).
      - apply (dmp _ (Weq (TV x) (TV x))); [| apply dthm, lrefl_var].
        apply (dmp _ (Weq (TV x) (TV x0))); [apply dthm, (E8 X (TV x) (TV x0) (TV x)) | apply dhyp; simpl; auto]. }
    assert (V : lprov (Wim (Weq (TV x0) t) (Wal x (Weq (TV x0) t)))).
    { apply lvac. cbn [occ tocc]. rewrite Hx, orb_false_r. apply Nat.eqb_neq. congruence. }
    apply der_lprov, ded.
    apply (dmp _ (Wex x (Weq (TV x) (TV x0)))); [| apply dthm, B7v; exact Hne].
    apply (dmp _ (Wal x (Wim (Weq (TV x) (TV x0)) (Weq (TV x) t)))); [apply dthm, lall_ex|].
    apply (dmp _ (Wal x (Weq (TV x0) t))); [| apply (dmp _ (Weq (TV x0) t)); [apply dthm, V | apply dhyp; simpl; auto]].
    apply dthm. exact (LDET _ _ (LB4 x _ _) (LGEN x _ Q)). }
  refine (LDET _ _ (LDET _ _ (lex_elim x0 (Weq (TV x0) t) (Wex x (Weq (TV x) t)) _) (LGEN x0 _ I)) (B7c X t)).
  cbn [occ tocc Wex]. rewrite Hx0. apply orb_false_iff; split; [apply Nat.eqb_neq; congruence|].
  apply orb_false_iff; split; [apply Nat.eqb_neq; congruence | reflexivity].
Qed.

(** ** Equality *)
Lemma tocc_gt z t : tmaxv t < z -> tocc z t = false.
Proof.
  intro H. destruct (tocc z t) eqn:E; [|reflexivity]. apply tocc_tmaxv in E. lia.
Qed.

Lemma leq_refl t : lprov (Weq t t).
Proof.
  set (z := S (tmaxv t)). assert (Hz : tocc z t = false) by (apply tocc_gt; lia).
  assert (h3 : lprov (Wim (Weq (TV z) t) (Weq t t))) by exact (LDET _ _ (lpc_W X _ _) (E8 X (TV z) t t)).
  assert (h5 : lprov (Wim (Weq t t) (Wal z (Weq t t)))) by exact (LB6a z t t Hz Hz).
  pose proof (lex z _ _ (lsyl _ _ _ h3 h5)) as h7.
  exact (LDET _ _ (LB6c z (Weq t t)) (LDET _ _ h7 (lb7 z t Hz))).
Qed.

Lemma leq_sym t s : lprov (Wim (Weq t s) (Weq s t)).
Proof.
  apply der_lprov, ded. mp (Weq t t); [mp (Weq t s); [dt (E8 X t s t) | dh] | dt (leq_refl t)].
Qed.

Lemma leq_trans t s r : lprov (Wim (Weq t s) (Wim (Weq s r) (Weq t r))).
Proof.
  apply der_lprov, ded, ded. mp (Weq s r); [mp (Weq s t); [dt (E8 X s t r) | ] | dh].
  mp (Weq t s); [dt (leq_sym t s) | dh].
Qed.

(** u = u', v = v' transport equations *)
Lemma leq_tr_eq u u' v v' : lprov (Wim (Weq u u') (Wim (Weq v v') (Wim (Weq u v) (Weq u' v')))).
Proof.
  apply der_lprov, ded, ded, ded.
  assert (Hu'v : der [Weq u v; Weq v v'; Weq u u'] (Weq u' v)).
  { mp (Weq u v); [mp (Weq u u'); [dt (E8 X u u' v) | dh] | dh]. }
  mp (Weq v v'); [mp (Weq u' v); [dt (leq_trans u' v v') | exact Hu'v] | dh].
Qed.

(** ** Term congruence:  x = s -> t = t[s/x] *)
Lemma leq_cong x s t : lprov (Wim (Weq (TV x) s) (Weq t (sbt x s t))).
Proof.
  induction t as [n| |t IH|t IH r IHr|t IH r IHr]; cbn.
  - destruct (Nat.eqb_spec n x) as [->|_]; [apply lpc_id | exact (LDET _ _ (lpc_K X _ _) (leq_refl _))].
  - exact (LDET _ _ (lpc_K X _ _) (leq_refl _)).
  - exact (lsyl _ _ _ IH (ES X _ _)).
  - apply der_lprov, ded.
    mp (Weq (TP (sbt x s t) r) (TP (sbt x s t) (sbt x s r))).
    + mp (Weq (TP t r) (TP (sbt x s t) r)); [dt (leq_trans (TP t r) (TP (sbt x s t) r) (TP (sbt x s t) (sbt x s r)))|].
      mp (Weq t (sbt x s t)); [dt (EPl X t (sbt x s t) r) | mp (Weq (TV x) s); [dt IH | dh]].
    + mp (Weq r (sbt x s r)); [dt (EPr X r (sbt x s r) (sbt x s t)) | mp (Weq (TV x) s); [dt IHr | dh]].
  - apply der_lprov, ded.
    mp (Weq (TM (sbt x s t) r) (TM (sbt x s t) (sbt x s r))).
    + mp (Weq (TM t r) (TM (sbt x s t) r)); [dt (leq_trans (TM t r) (TM (sbt x s t) r) (TM (sbt x s t) (sbt x s r)))|].
      mp (Weq t (sbt x s t)); [dt (EMl X t (sbt x s t) r) | mp (Weq (TV x) s); [dt IH | dh]].
    + mp (Weq r (sbt x s r)); [dt (EMr X r (sbt x s r) (sbt x s t)) | mp (Weq (TV x) s); [dt IHr | dh]].
Qed.

Lemma leq_cong' x s t : lprov (Wim (Weq (TV x) s) (Weq (sbt x s t) t)).
Proof. exact (lsyl _ _ _ (leq_cong x s t) (leq_sym _ _)). Qed.

(** ** Leibniz:  x = s -> (a <-> a[s/x])  when x and the variables of s are not bound in a *)
Lemma leib x s a : bnd x a = false -> sfree s a ->
  lprov (Wim (Weq (TV x) s) (Wim a (sb x s a))) /\ lprov (Wim (Weq (TV x) s) (Wim (sb x s a) a)).
Proof.
  set (h := Weq (TV x) s).
  induction a as [u v|a IHa b IHb|a IHa|z a IHa]; simpl; intros Hx Hs.
  - split; apply der_lprov, ded.
    + mp (Weq v (sbt x s v)); [mp (Weq u (sbt x s u)); [dt (leq_tr_eq u (sbt x s u) v (sbt x s v))|]|].
      * mp h; [dt (leq_cong x s u) | dh].
      * mp h; [dt (leq_cong x s v) | dh].
    + mp (Weq (sbt x s v) v); [mp (Weq (sbt x s u) u); [dt (leq_tr_eq (sbt x s u) u (sbt x s v) v)|]|].
      * mp h; [dt (leq_cong' x s u) | dh].
      * mp h; [dt (leq_cong' x s v) | dh].
  - apply orb_false_iff in Hx as [Hxa Hxb].
    destruct (IHa Hxa (sfree_im_l _ _ _ Hs)) as [A1 A2]. destruct (IHb Hxb (sfree_im_r _ _ _ Hs)) as [B1' B2'].
    split; apply der_lprov, ded, ded, ded.
    + mp b; [mp h; [dt B1' | dh] | mp a; [dh | mp (sb x s a); [mp h; [dt A2 | dh] | dh]]].
    + mp (sb x s b); [mp h; [dt B2' | dh] | mp (sb x s a); [dh | mp a; [mp h; [dt A1 | dh] | dh]]].
  - destruct (IHa Hx (sfree_n _ _ Hs)) as [A1 A2].
    split; apply der_lprov, ded.
    + mp (Wim (sb x s a) a); [dt (lpc_contra X (sb x s a) a) | mp h; [dt A2 | dh]].
    + mp (Wim a (sb x s a)); [dt (lpc_contra X a (sb x s a)) | mp h; [dt A1 | dh]].
  - apply orb_false_iff in Hx as [Hzx Hx]. rewrite Hzx.
    destruct (sfree_al _ _ _ Hs) as [Hs' Hzs].
    destruct (IHa Hx Hs') as [A1 A2].
    assert (V : lprov (Wim h (Wal z h))).
    { apply lvac. simpl. rewrite Hzs, orb_false_r. apply Nat.eqb_neq. apply Nat.eqb_neq in Hzx. congruence. }
    split.
    + exact (lsyl _ _ _ V (lsyl _ _ _ (LDET _ _ (LB4 z h _) (LGEN z _ A1)) (LB4 z a _))).
    + exact (lsyl _ _ _ V (lsyl _ _ _ (LDET _ _ (LB4 z h _) (LGEN z _ A2)) (LB4 z _ a))).
Qed.

(** ** Specialization and alphabetic variance *)
Lemma lspec x s a : tocc x s = false -> bnd x a = false -> sfree s a ->
  lprov (Wim (Wal x a) (sb x s a)).
Proof.
  intros Hxs Hx Hs. set (a' := sb x s a).
  destruct (leib x s a Hx Hs) as [L _].
  pose proof (LDET _ _ (lpc_C X _ _ _) L) as L'.
  pose proof (lal x _ _ L') as H1.
  pose proof (lsyl _ _ _ H1 (lall_ex x (Weq (TV x) s) a')) as H2.
  pose proof (LDET _ _ (LDET _ _ (lpc_C X _ _ _) H2) (lb7 x s Hxs)) as H3.
  pose proof (lex x _ _ (lvac x a' (occ_sb_self x s a Hxs Hx))) as H4.
  exact (lsyl _ _ _ H3 (lsyl _ _ _ H4 (LB6c x a'))).
Qed.

(** existential introduction *)
Lemma lexi x s a : tocc x s = false -> bnd x a = false -> sfree s a ->
  lprov (Wim (sb x s a) (Wex x a)).
Proof.
  intros Hxs Hx Hs. unfold Wex.
  pose proof (lspec x s (Wn a) Hxs Hx Hs) as H. cbn [sb] in H.
  exact (lsyl _ _ _ (lpc_nn_intro X _) (lcontra _ _ H)).
Qed.

Lemma sbt_back x y t : tocc y t = false -> sbt y (TV x) (sbt x (TV y) t) = t.
Proof.
  induction t; cbn; intro H; try reflexivity.
  - destruct (Nat.eqb_spec n x) as [->|]; cbn; [now rewrite Nat.eqb_refl|]. now rewrite H.
  - now rewrite IHt.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IHt1, IHt2.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IHt1, IHt2.
Qed.

Lemma sbt_noocc y s t : tocc y t = false -> sbt y s t = t.
Proof.
  induction t; cbn; intro H; try reflexivity.
  - now rewrite H.
  - now rewrite IHt.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IHt1, IHt2.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IHt1, IHt2.
Qed.

Lemma sb_noocc y s a : occ y a = false -> sb y s a = a.
Proof.
  induction a as [t r|a1 IH1 a2 IH2|a1 IH|z a1 IH]; cbn; intro H.
  - apply orb_false_iff in H as [H1 H2]. now rewrite !sbt_noocc.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IH1, IH2.
  - now rewrite IH.
  - apply orb_false_iff in H as [H1 H2]. rewrite H1. now rewrite IH.
Qed.

Lemma sb_back x y a : occ y a = false -> sb y (TV x) (sb x (TV y) a) = a.
Proof.
  induction a as [t r|a1 IH1 a2 IH2|a1 IH|z a1 IH]; cbn; intro H.
  - apply orb_false_iff in H as [H1 H2]. now rewrite !sbt_back.
  - apply orb_false_iff in H as [H1 H2]. now rewrite IH1, IH2.
  - now rewrite IH.
  - apply orb_false_iff in H as [H1 H2]. destruct (Nat.eqb_spec z x) as [->|].
    + cbn. rewrite H1. now rewrite sb_noocc.
    + cbn. rewrite H1. now rewrite IH.
Qed.

Lemma bnd_sb z x s a : bnd z (sb x s a) = bnd z a.
Proof.
  induction a as [t r|a1 IH1 a2 IH2|a1 IH|w a1 IH]; cbn; try reflexivity.
  - now rewrite IH1, IH2.
  - exact IH.
  - destruct (Nat.eqb w x); cbn; now rewrite ?IH.
Qed.

End LMeta.
