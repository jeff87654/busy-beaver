(** * The Hardy hierarchy below epsilon_0 and its link to the fast-growing hierarchy

    [hardy x n m]  ("H_x(n) = m"):  H_0(n) = n,  H_(b+1)(n) = H_b(n+1),  H_l(n) = H_(l[n])(n),
    with the fundamental sequences [fs] of Ord.v.  [HH x n] is the function (for [nf x]).
    Main facts (no axioms):
      HH_app   : H_(b+g) = H_b o H_g             (b + g in normal form, i.e. [all_ge g b])
      HH_orep  : H_(omega^a * k) = (H_(omega^a))^k
      HH_pow   : H_(omega^a)(n) = f_a(n)          (the standard bridge to [FGH])
      HH_cons  : H_(omega^a + b)(n) = f_a(H_b(n))
      HH_ge, HH_mono : H_x(n) >= n, monotone in n. *)

From Coq Require Import Arith Lia.
From BB8 Require Import Ord.
Set Default Goal Selector "!".

Inductive hardy : ord -> nat -> nat -> Prop :=
| hardy_zero : forall n, hardy oz n n
| hardy_succ : forall x b n m, okind x = KSucc b -> hardy b (S n) m -> hardy x n m
| hardy_lim : forall x n m, okind x = KLim -> hardy (fs x n) n m -> hardy x n m.

Theorem hardy_det : forall x n m m', hardy x n m -> hardy x n m' -> m = m'.
Proof.
  intros x n m m' H. revert m'. induction H as [n|x b n m K _ IH|x n m K _ IH]; intros m' H'.
  - inversion H'; subst; [reflexivity | discriminate | discriminate].
  - inversion H'; subst; [discriminate | | congruence].
    match goal with K' : okind _ = KSucc _ |- _ => rewrite K in K'; injection K' as <- end.
    apply IH. assumption.
  - inversion H'; subst; [discriminate | congruence | apply IH; assumption].
Qed.

Theorem hardy_total : forall x, nf x -> forall n, {m | hardy x n m}.
Proof.
  refine (well_founded_induction_type wf_ltn (fun x => nf x -> forall n, {m | hardy x n m}) _).
  intros x IH Hx n.
  destruct (okind x) as [|b|] eqn:K.
  - exists n. rewrite (okind_zero x K). apply hardy_zero.
  - assert (Hb : ltn b x).
    { apply okind_succ in K. destruct (opred_spec x b Hx K). repeat split; assumption. }
    destruct (IH b Hb (proj1 Hb) (S n)) as [m Hm]. exists m. eapply hardy_succ; eassumption.
  - assert (Hl : ltn (fs x n) x) by (apply fs_ltn; [exact Hx | apply okind_lim in K; apply K]).
    destruct (IH _ Hl (proj1 Hl) n) as [m Hm]. exists m. apply hardy_lim; assumption.
Defined.

Definition HH (x : ord) (n : nat) : nat :=
  match nf_dec x with
  | left H => proj1_sig (hardy_total x H n)
  | right _ => 0
  end.

Lemma HH_spec : forall x n, nf x -> hardy x n (HH x n).
Proof. intros x n Hx. unfold HH. destruct (nf_dec x) as [H|H]; [apply proj2_sig | contradiction]. Qed.

Lemma HH_unique : forall x n m, nf x -> hardy x n m -> HH x n = m.
Proof. intros. eapply hardy_det; [apply HH_spec |]; eassumption. Qed.

Global Opaque HH.

Lemma HH_zero : forall n, HH oz n = n.
Proof. intros. apply HH_unique; [apply nf_z | apply hardy_zero]. Qed.

Lemma HH_succ : forall x b n, nf x -> okind x = KSucc b -> HH x n = HH b (S n).
Proof.
  intros x b n Hx K. assert (Hb : nf b) by (apply okind_succ in K; apply (opred_spec x b Hx K)).
  apply HH_unique; [exact Hx|]. eapply hardy_succ; [exact K | apply HH_spec; exact Hb].
Qed.

Lemma HH_osucc : forall b n, nf b -> HH (osucc b) n = HH b (S n).
Proof. intros. apply HH_succ; [apply nf_osucc; assumption | apply okind_osucc]. Qed.

Lemma HH_lim : forall x n, nf x -> okind x = KLim -> HH x n = HH (fs x n) n.
Proof.
  intros x n Hx K. apply HH_unique; [exact Hx|]. apply hardy_lim; [exact K|].
  apply HH_spec. apply fs_nf_lt; [exact Hx | apply okind_lim in K; apply K].
Qed.

(** [all_ge] is preserved when the right summand descends *)
Lemma all_ge_lt : forall b g g', all_ge g b -> ole g' g -> nf g -> all_ge g' b.
Proof.
  induction b as [|a _ b IHb]; intros g g' H Hle Hg; simpl in *; [exact I|].
  destruct H as [H1 H2]. split; [| eapply IHb; eauto].
  destruct Hle as [<-|Hlt]; [exact H1|].
  destruct g as [|c d]; [inversion Hlt|]. eapply head_le_lt; eauto.
Qed.

Lemma okind_app : forall b g, g <> oz ->
  okind (oapp b g) = match okind g with KZero => KZero | KSucc p => KSucc (oapp b p) | KLim => KLim end.
Proof.
  intros b g Hg. destruct (okind g) as [|p|] eqn:K.
  - apply okind_zero in K. contradiction.
  - apply okind_succ. apply okind_succ in K. rewrite opred_app by exact Hg. rewrite K. reflexivity.
  - apply okind_lim. apply okind_lim in K as [_ K]. split; [apply oapp_ne; exact Hg|].
    rewrite opred_app by exact Hg. rewrite K. reflexivity.
Qed.

(** H_(b+g)(n) = H_b(H_g(n)) *)
Theorem HH_app : forall g b n, nf b -> nf g -> all_ge g b -> HH (oapp b g) n = HH b (HH g n).
Proof.
  intro g. induction g as [g IH] using (well_founded_ind wf_ltn). intros b n Hb Hg Hge.
  assert (Hbg : nf (oapp b g)) by (apply nf_oapp; assumption).
  destruct (okind g) as [|p|] eqn:K.
  - apply okind_zero in K. subst g. rewrite oapp_oz_r, HH_zero. reflexivity.
  - assert (Hgz : g <> oz) by (intro E; subst; discriminate).
    assert (Hp := K). apply okind_succ in Hp. destruct (opred_spec g p Hg Hp) as [Hnp Hpg].
    rewrite (HH_succ (oapp b g) (oapp b p)); [| exact Hbg | rewrite okind_app by exact Hgz; rewrite K; reflexivity].
    rewrite (HH_succ g p) by assumption.
    apply IH; [repeat split; assumption | exact Hb | exact Hnp | eapply all_ge_lt; eauto; right; exact Hpg].
  - assert (Hgz : g <> oz) by (apply okind_lim in K; apply K).
    destruct (fs_nf_lt g n Hg Hgz) as [Hf Hfg].
    rewrite HH_lim; [| exact Hbg | rewrite okind_app by exact Hgz; rewrite K; reflexivity].
    rewrite fs_app by exact Hgz. rewrite (HH_lim g) by assumption.
    apply IH; [repeat split; assumption | exact Hb | exact Hf | eapply all_ge_lt; eauto; right; exact Hfg].
Qed.

(** H_(omega^a + b)(n) = H_(omega^a)(H_b(n)) *)
Lemma HH_cons_pow : forall a b n, nf (ow a b) -> HH (ow a b) n = HH (opow a) (HH b n).
Proof.
  intros a b n H. change (ow a b) with (oapp (opow a) b).
  apply HH_app; [apply nf_opow; eapply nf_head; eauto | eapply nf_tail; eauto |].
  simpl. split; [apply nf_head_le; exact H | exact I].
Qed.

(** H_(omega^a * k)(n) = (H_(omega^a))^k(n) *)
Theorem HH_orep : forall a k n, nf a -> HH (orep a k oz) n = Nat.iter k (HH (opow a)) n.
Proof.
  intros a k n Ha. induction k as [|k IH]; [apply HH_zero|].
  simpl orep. rewrite HH_cons_pow; [| apply nf_orep0 with (k := S k); exact Ha].
  rewrite IH. reflexivity.
Qed.

(** The bridge: H_(omega^a)(n) = f_a(n). *)
Theorem HH_pow : forall a n, nf a -> HH (opow a) n = FGH a n.
Proof.
  intro a. induction a as [a IH] using (well_founded_ind wf_ltn). intros n Ha.
  assert (Hpa : nf (opow a)) by (apply nf_opow; exact Ha).
  destruct (okind a) as [|b|] eqn:K.
  - apply okind_zero in K. subst a. rewrite FGH_zero.
    rewrite (HH_succ (opow oz) oz) by (assumption || reflexivity). apply HH_zero.
  - assert (Hp := K). apply okind_succ in Hp. destruct (opred_spec a b Ha Hp) as [Hb Hba].
    assert (Haz : a <> oz) by (intro E; subst; discriminate).
    rewrite HH_lim; [| exact Hpa | apply okind_pow_lim; exact Haz].
    unfold opow at 1. rewrite (fs_pow_succ a b n Hp). rewrite HH_orep by exact Hb.
    rewrite (FGH_succ a b n Ha K). apply iter_ext. intro z. apply IH; [repeat split; assumption | exact Hb].
  - assert (Haz : a <> oz) by (apply okind_lim in K; apply K).
    destruct (fs_nf_lt a n Ha Haz) as [Hf Hfa].
    rewrite HH_lim; [| exact Hpa | apply okind_pow_lim; exact Haz].
    unfold opow at 1. rewrite fs_pow_lim by (exact Haz || (apply okind_lim in K; apply K)).
    rewrite (FGH_lim a n Ha K). apply IH; [repeat split; assumption | exact Hf].
Qed.

(** H_(omega^a + b)(n) = f_a(H_b(n)) *)
Theorem HH_cons : forall a b n, nf (ow a b) -> HH (ow a b) n = FGH a (HH b n).
Proof.
  intros a b n H. rewrite HH_cons_pow by exact H. apply HH_pow. eapply nf_head; eauto.
Qed.

Theorem HH_ge : forall x n, nf x -> n <= HH x n.
Proof.
  induction x as [|a _ b IHb]; intros n Hx; [rewrite HH_zero; lia|].
  rewrite HH_cons by exact Hx. eapply Nat.le_trans; [apply IHb; eapply nf_tail; eauto|].
  apply FGH_ge. eapply nf_head; eauto.
Qed.

Theorem HH_mono : forall x n n', nf x -> n <= n' -> HH x n <= HH x n'.
Proof.
  induction x as [|a _ b IHb]; intros n n' Hx Hn; [rewrite !HH_zero; lia|].
  rewrite !HH_cons by exact Hx. apply FGH_mono; [eapply nf_head; eauto|].
  apply IHb; [eapply nf_tail; eauto | exact Hn].
Qed.

(** H_(x)(n) >= f_a(n) when omega^a is the leading term of x *)
Theorem HH_cons_ge : forall a b n, nf (ow a b) -> FGH a n <= HH (ow a b) n.
Proof.
  intros a b n H. rewrite HH_cons by exact H. apply FGH_mono; [eapply nf_head; eauto|].
  apply HH_ge. eapply nf_tail; eauto.
Qed.

Example HH_omega_3 : HH omega 3 = FGH one 3.
Proof. apply HH_pow. apply nf_one'. Qed.

(** ** One fundamental-sequence step and descent do not increase H (arguments m >= max(1,k)) *)

Theorem HH_fs_le : forall x k m, nf x -> 1 <= m -> k <= m -> HH (fs x k) m <= HH x m.
Proof.
  induction x as [|a _ b IHb]; intros k m Hx Hm Hk; [cbn [fs]; lia|].
  assert (Ha : nf a) by (eapply nf_head; eauto).
  destruct b as [|c d].
  - change (HH (ow a oz) m) with (HH (opow a) m). rewrite (HH_pow a m Ha). destruct (okind a) as [|a'|] eqn:K.
    + apply okind_zero in K. subst a. cbn [fs]. rewrite HH_zero, FGH_zero. lia.
    + assert (Hp := K). apply okind_succ in Hp. destruct (opred_spec a a' Ha Hp) as [Ha' _].
      rewrite (fs_pow_succ a a' k Hp), HH_orep by exact Ha'. rewrite (FGH_succ a a' m Ha K).
      rewrite (iter_ext _ (FGH a') k m) by (intro; apply HH_pow; exact Ha').
      apply iter_mono; [intros; apply FGH_mono; assumption | intro; apply FGH_ge; exact Ha' | exact Hk | lia].
    + apply okind_lim in K as [Kz Kp]. rewrite (fs_pow_lim a k Kz Kp).
      change (ow (fs a k) oz) with (opow (fs a k)). rewrite HH_pow by (apply fs_nf_lt; assumption).
      apply FGH_fs_le; assumption.
  - assert (Hb : nf (ow c d)) by (eapply nf_tail; eauto).
    destruct (fs_nf_lt (ow a (ow c d)) k Hx ltac:(discriminate)) as [Hf _].
    rewrite fs_cons in Hf |- * by discriminate.
    rewrite (HH_cons a _ m Hf), (HH_cons a _ m Hx). apply FGH_mono; [exact Ha|].
    apply IHb; assumption.
Qed.

Theorem HH_desc_le : forall k x y m, nf x -> desc k x y -> 1 <= m -> k <= m -> HH y m <= HH x m.
Proof.
  intros k x y m Hx D. induction D as [x|x y Hne _ IH]; intros Hm Hk; [lia|].
  destruct (fs_nf_lt x k Hx Hne) as [H1 _].
  eapply Nat.le_trans; [apply IH; assumption | apply HH_fs_le; assumption].
Qed.

(** ** Lower bound for hydra-like games

    [P x n]: "the run reaches a configuration encoding ordinal x with counter n".
    [W v]  : "the run halts with score >= v" (downward closed).
    If a zero ordinal gives score >= n, a successor x = b+1 moves to (b, n') with n' >= n+1, and a
    limit x moves to some (y, n') with y < x normal, y descending to x[n] by [k]-steps (k <= n; e.g.
    y = x[n] itself with [desc_refl]) and n' >= n, then reaching (x, n) gives score >= H_x(n).
    This covers shifted arguments (n' = n+1 on limit steps) and steps that land above x[n]. *)
Theorem hardy_game : forall (P : ord -> nat -> Prop) (W : nat -> Prop),
  (forall a b, b <= a -> W a -> W b) ->
  (forall n, P oz n -> W n) ->
  (forall x b n, nf x -> okind x = KSucc b -> 1 <= n -> P x n -> exists n', S n <= n' /\ P b n') ->
  (forall x n, nf x -> okind x = KLim -> 1 <= n -> P x n ->
     exists y k n', nf y /\ olt y x /\ desc k y (fs x n) /\ k <= n /\ n <= n' /\ P y n') ->
  forall x n, nf x -> 1 <= n -> P x n -> W (HH x n).
Proof.
  intros P W Wd Hz Hs Hl x. induction x as [x IH] using (well_founded_ind wf_ltn).
  intros n Hx Hn Hp. destruct (okind x) as [|b|] eqn:K.
  - apply okind_zero in K. subst x. rewrite HH_zero. apply Hz. exact Hp.
  - destruct (Hs x b n Hx K Hn Hp) as (n' & Hn' & Hp').
    assert (Hpb := K). apply okind_succ in Hpb. destruct (opred_spec x b Hx Hpb) as [Hb Hbx].
    apply Wd with (a := HH b n'); [| apply IH; [repeat split; assumption | exact Hb | lia | exact Hp']].
    rewrite (HH_succ x b n Hx K). apply HH_mono; assumption.
  - destruct (Hl x n Hx K Hn Hp) as (y & k & n' & Hy & Hyx & D & Hk & Hn' & Hp').
    apply Wd with (a := HH y n'); [| apply IH; [repeat split; assumption | exact Hy | lia | exact Hp']].
    rewrite (HH_lim x n Hx K). eapply Nat.le_trans; [apply (HH_desc_le k y); [exact Hy | exact D | exact Hn | exact Hk]|].
    apply HH_mono; assumption.
Qed.

(** ** The shifted Hardy hierarchy G: G_0(n) = n, G_(b+1)(n) = G_b(n+1), G_l(n) = G_(l[n])(n+1) *)

Inductive hardyG : ord -> nat -> nat -> Prop :=
| hardyG_zero : forall n, hardyG oz n n
| hardyG_succ : forall x b n m, okind x = KSucc b -> hardyG b (S n) m -> hardyG x n m
| hardyG_lim : forall x n m, okind x = KLim -> hardyG (fs x n) (S n) m -> hardyG x n m.

Theorem hardyG_det : forall x n m m', hardyG x n m -> hardyG x n m' -> m = m'.
Proof.
  intros x n m m' H. revert m'. induction H as [n|x b n m K _ IH|x n m K _ IH]; intros m' H'.
  - inversion H'; subst; [reflexivity | discriminate | discriminate].
  - inversion H'; subst; [discriminate | | congruence].
    match goal with K' : okind _ = KSucc _ |- _ => rewrite K in K'; injection K' as <- end.
    apply IH. assumption.
  - inversion H'; subst; [discriminate | congruence | apply IH; assumption].
Qed.

Theorem hardyG_total : forall x, nf x -> forall n, {m | hardyG x n m}.
Proof.
  refine (well_founded_induction_type wf_ltn (fun x => nf x -> forall n, {m | hardyG x n m}) _).
  intros x IH Hx n.
  destruct (okind x) as [|b|] eqn:K.
  - exists n. rewrite (okind_zero x K). apply hardyG_zero.
  - assert (Hb : ltn b x).
    { apply okind_succ in K. destruct (opred_spec x b Hx K). repeat split; assumption. }
    destruct (IH b Hb (proj1 Hb) (S n)) as [m Hm]. exists m. eapply hardyG_succ; eassumption.
  - assert (Hl : ltn (fs x n) x) by (apply fs_ltn; [exact Hx | apply okind_lim in K; apply K]).
    destruct (IH _ Hl (proj1 Hl) (S n)) as [m Hm]. exists m. apply hardyG_lim; assumption.
Defined.

Definition GG (x : ord) (n : nat) : nat :=
  match nf_dec x with
  | left H => proj1_sig (hardyG_total x H n)
  | right _ => 0
  end.

Lemma GG_spec : forall x n, nf x -> hardyG x n (GG x n).
Proof. intros x n Hx. unfold GG. destruct (nf_dec x) as [H|H]; [apply proj2_sig | contradiction]. Qed.

Lemma GG_unique : forall x n m, nf x -> hardyG x n m -> GG x n = m.
Proof. intros. eapply hardyG_det; [apply GG_spec |]; eassumption. Qed.

Global Opaque GG.

Lemma GG_zero : forall n, GG oz n = n.
Proof. intros. apply GG_unique; [apply nf_z | apply hardyG_zero]. Qed.

Lemma GG_succ : forall x b n, nf x -> okind x = KSucc b -> GG x n = GG b (S n).
Proof.
  intros x b n Hx K. assert (Hb : nf b) by (apply okind_succ in K; apply (opred_spec x b Hx K)).
  apply GG_unique; [exact Hx|]. eapply hardyG_succ; [exact K | apply GG_spec; exact Hb].
Qed.

Lemma GG_lim : forall x n, nf x -> okind x = KLim -> GG x n = GG (fs x n) (S n).
Proof.
  intros x n Hx K. apply GG_unique; [exact Hx|]. apply hardyG_lim; [exact K|].
  apply GG_spec. apply fs_nf_lt; [exact Hx | apply okind_lim in K; apply K].
Qed.

(** G >= H *)
Theorem GG_ge_HH : forall x n, nf x -> HH x n <= GG x n.
Proof.
  intro x. induction x as [x IH] using (well_founded_ind wf_ltn). intros n Hx.
  destruct (okind x) as [|b|] eqn:K.
  - apply okind_zero in K. subst x. rewrite HH_zero, GG_zero. lia.
  - assert (Hp := K). apply okind_succ in Hp. destruct (opred_spec x b Hx Hp) as [Hb Hbx].
    rewrite (HH_succ x b n Hx K), (GG_succ x b n Hx K). apply IH; [repeat split; assumption | exact Hb].
  - assert (Hz : x <> oz) by (apply okind_lim in K; apply K).
    destruct (fs_nf_lt x n Hx Hz) as [Hf Hfx].
    rewrite (HH_lim x n Hx K), (GG_lim x n Hx K).
    eapply Nat.le_trans; [apply HH_mono; [exact Hf | apply (Nat.le_succ_diag_r n)] |].
    apply IH; [repeat split; assumption | exact Hf].
Qed.
