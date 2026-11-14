(** * HydraUpper: an UPPER bound for the hydra game of the published BB29/BB31/BB33 machines (and Argon's
    BB30/BB32/BB34 instances of the same template).

    Machine-independent part.  Depends only on the published library files Ord.v, Hardy.v, HydraOrd.v
    (busy-beaver BB31/verify/multifile = BB33/verify/multifile, byte-identical).

    The published game proof (BB33_game.v, Hardy.hardy_game) uses only that one chop moves the ordinary-sum
    ordinal x = o(hs) of the hydra into [x[n], x) (HydraOrd.chop_ord); that gives a LOWER bound.  For an upper
    bound we show that on the hydras the machines actually visit, the chop is exact up to one index:
         o(hs') = x[n]   or   o(hs') = x[n+1]                                   (chop_exact)
    The visited hydras are "good": in every node the children list is sorted (ordinals of the children
    non-increasing in tape order), except possibly for ONE extra leading leaf (ssl).  The initial hydras of
    the family have this shape, and both rounds preserve it (good_succ, good_chop_node, good_plug_repl).
    The only non-exact case is a node with children [leaf; node [leaf]] (ordinal omega), chopped to
    [leaf; leaf * n] (ordinal n+1 = omega[n+1]).

    Hardy side: with U(x, n) := H_x(n+2), one round never increases U (HH_up_lim), so a run from (x, n) halts
    with N + 2 <= H_x(n+2) ones.  HH_fs_shift is the tool for the comparisons with the new machines. *)

From BB8 Require Import Ord Hardy HydraOrd.
From Coq Require Import Lia List PeanoNat.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Sorted children lists and good hydras *)

Fixpoint srt (L : list tree) : Prop :=
  match L with
  | [] => True
  | c :: L' => Forall (fun t => ole (otree t) (otree c)) L' /\ srt L'
  end.

(** sorted, or one leading leaf followed by a sorted list *)
Definition ssl (L : list tree) : Prop := srt L \/ exists L0, L = leaf :: L0 /\ srt L0.

Inductive good : tree -> Prop :=
| good_intro : forall cs, ssl cs -> Forall good cs -> good (node cs).

Lemma good_inv : forall cs, good (node cs) -> ssl cs /\ Forall good cs.
Proof. intros cs H. inversion H; subst. split; assumption. Qed.

Lemma srt_app : forall A B, srt (A ++ B) <->
  srt A /\ srt B /\ Forall (fun a => Forall (fun b => ole (otree b) (otree a)) B) A.
Proof.
  induction A as [|a A IH]; intros B; simpl.
  - split; [intros H; split; [exact I | split; [exact H | constructor]] | intros (_ & H & _); exact H].
  - split.
    + intros [H1 H2]. apply IH in H2 as (H3 & H4 & H5). apply Forall_app in H1 as [H6 H7].
      split; [split; assumption|]. split; [exact H4|]. constructor; assumption.
    + intros [[H1 H2] [H3 H4]]. inversion H4 as [|? ? H5 H6]; subst.
      split; [apply Forall_app; split; assumption|]. apply IH. split; [exact H2|]. split; assumption.
Qed.

Lemma srt_repeat : forall C n, srt (repeat C n).
Proof.
  intros C n. induction n as [|n IH]; simpl; [exact I|].
  split; [apply Forall_repeat, ole_refl | exact IH].
Qed.

Lemma srt_chop : forall L P C n, srt (L ++ [P]) -> ole (otree C) (otree P) -> srt (L ++ repeat C n).
Proof.
  intros L P C n H HC. apply srt_app in H as (H1 & _ & H3). apply srt_app.
  split; [exact H1|]. split; [apply srt_repeat|].
  eapply Forall_impl; [| exact H3]. intros a Ha. inversion Ha as [|? ? Ha1 _]; subst.
  apply Forall_repeat. eapply ole_trans; eassumption.
Qed.

Lemma ssl_chop : forall L P C n, ssl (L ++ [P]) -> ole (otree C) (otree P) -> ssl (L ++ repeat C n).
Proof.
  intros L P C n [H | (L0 & E & H)] HC.
  - left. eapply srt_chop; eassumption.
  - destruct L as [|l L'].
    + left. apply srt_repeat.
    + simpl in E. injection E as E1 E2. subst. right. exists (L' ++ repeat C n). split; [reflexivity|].
      eapply srt_chop; eassumption.
Qed.

Lemma ssl_last : forall L u u', ssl (L ++ [u]) -> ole (otree u') (otree u) -> ssl (L ++ [u']).
Proof. intros L u u' H Hu. exact (ssl_chop L u u' 1 H Hu). Qed.

Lemma ssl_prefix : forall A B, ssl (A ++ B) -> ssl A.
Proof.
  intros A B [H | (L0 & E & H)].
  - left. apply srt_app in H as [H1 _]. exact H1.
  - destruct A as [|a A'].
    + left. exact I.
    + simpl in E. injection E as E1 E2. subst. right. exists A'. split; [reflexivity|].
      apply srt_app in H as [H1 _]. exact H1.
Qed.

Lemma good_succ : forall L0, good (node (L0 ++ [leaf])) -> good (node L0).
Proof.
  intros L0 H. apply good_inv in H as [H1 H2]. constructor.
  - eapply ssl_prefix; exact H1.
  - apply Forall_app in H2 as [H3 _]. exact H3.
Qed.

Lemma good_chop_node : forall L L' n,
  good (node (L ++ [node (L' ++ [leaf])])) -> good (node (L ++ repeat (node L') n)).
Proof.
  intros L L' n H. apply good_inv in H as [H1 H2]. apply Forall_app in H2 as [H3 H4].
  inversion H4 as [|? ? H5 _]; subst. apply good_inv in H5 as [H6 H7].
  constructor.
  - eapply ssl_chop; [exact H1|]. rewrite !otree_node, olist_leaf_snoc. right. apply olt_osucc.
  - apply Forall_app. split; [exact H3|]. apply Forall_repeat. constructor.
    + eapply ssl_prefix; exact H6.
    + apply Forall_app in H7 as [H8 _]. exact H8.
Qed.

Lemma Psi_le : forall sp z1 z2, ole z1 z2 -> ole (Psi sp z1) (Psi sp z2).
Proof.
  induction sp as [|L sp IH]; intros z1 z2 H; cbn [Psi]; [exact H|].
  apply Phi_le. unfold opow. apply ole_pow. apply IH. exact H.
Qed.

Lemma good_plug_repl : forall sp X Y, good (node Y) -> ole (olist Y) (olist X) ->
  good (node (plug sp X)) -> good (node (plug sp Y)).
Proof.
  induction sp as [|L sp IH]; intros X Y HY Hle H; cbn [plug] in H |- *; [exact HY|].
  apply good_inv in H as [H1 H2]. apply Forall_app in H2 as [H3 H4].
  inversion H4 as [|? ? H5 _]; subst.
  assert (H6 : good (node (plug sp Y))) by (eapply IH; eassumption).
  constructor.
  - eapply ssl_last; [exact H1|]. rewrite !otree_node, !olist_plug. apply Psi_le. exact Hle.
  - apply Forall_app. split; [exact H3|]. constructor; [exact H6 | constructor].
Qed.

Lemma good_plug_bottom : forall sp X, good (node (plug sp X)) -> good (node X).
Proof.
  induction sp as [|L sp IH]; intros X H; cbn [plug] in H; [exact H|].
  apply good_inv in H as [_ H2]. apply Forall_app in H2 as [_ H4].
  inversion H4 as [|? ? H5 _]; subst. apply IH. exact H5.
Qed.

Lemma good_leaf : good (node []).
Proof. constructor; [left; exact I | constructor]. Qed.

Lemma good_one : forall t, good t -> good (node [t]).
Proof. intros t H. constructor; [left; split; [constructor | exact I] | constructor; [exact H | constructor]]. Qed.

Lemma good_lead : forall t, good t -> good (node [leaf; t]).
Proof.
  intros t H. constructor.
  - right. exists [t]. split; [reflexivity|]. split; [constructor | exact I].
  - constructor; [exact good_leaf | constructor; [exact H | constructor]].
Qed.

Lemma good_leaves : forall k, good (node (repeat leaf k)).
Proof. intros k. constructor; [left; apply srt_repeat | apply Forall_repeat, good_leaf]. Qed.

(** ** Exactness of fundamental sequences on sorted lists *)

Lemma ocons_head : forall a x c, ole a c -> head_le x c -> head_le (ocons a x) c.
Proof.
  intros a [|b t] c Ha Hx; [exact Ha|]. unfold ocons. destruct (ocmp a b); simpl; assumption.
Qed.

Lemma Phi_head : forall L z c, Forall (fun t => ole (otree t) c) L -> head_le z c -> head_le (Phi L z) c.
Proof.
  induction L as [|t L IH]; intros z c H Hz; [exact Hz|].
  inversion H as [|? ? H1 H2]; subst. rewrite Phi_cons. apply ocons_head; [exact H1|]. apply IH; assumption.
Qed.

Lemma head_le_fs_gen : forall z k c, nf z -> head_le z c -> head_le (fs z k) c.
Proof.
  intros [|b t] k c Hz H; [exact I|]. eapply head_le_mono; [apply head_le_fs; exact Hz | exact H].
Qed.

Lemma Phi_fs_eq : forall L z k, z <> oz -> nf z -> Forall (fun t => head_le z (otree t)) L -> srt L ->
  fs (Phi L z) k = Phi L (fs z k).
Proof.
  induction L as [|t L IH]; intros z k Hz Hn Hh Hs; [reflexivity|].
  inversion Hh as [|? ? Hh1 Hh2]; subst. destruct Hs as [Hs1 Hs2].
  rewrite !Phi_cons.
  rewrite (ocons_big (otree t) (Phi L z)) by (apply Phi_head; assumption).
  rewrite (ocons_big (otree t) (Phi L (fs z k)))
    by (apply Phi_head; [exact Hs1 | apply head_le_fs_gen; assumption]).
  rewrite fs_cons by (apply Phi_ne; exact Hz). rewrite IH by assumption. reflexivity.
Qed.

Lemma ocons_oz_absorb : forall b t, b <> oz -> ocons oz (ow b t) = ow b t.
Proof. intros [|c d] t H; [congruence | reflexivity]. Qed.

Lemma Phi_leaf : forall y, Phi [leaf] y = ocons oz y.
Proof. reflexivity. Qed.

Lemma Phi_leaf_cons : forall M y, Phi (leaf :: M) y = ocons oz (Phi M y).
Proof. reflexivity. Qed.

Lemma osucc_one : forall g, osucc g = one -> g = oz.
Proof.
  intros [|a b] H; [reflexivity|]. unfold osucc, one in H. simpl in H. injection H as H1 H2.
  exfalso. exact (oapp_ne b one ltac:(discriminate) H2).
Qed.

(** One level: the node q with children L ++ [t] (o(t) = a), where omega^a becomes omega^a[k]. *)
Lemma level : forall L t a k, ssl (L ++ [t]) -> otree t = a -> a <> oz -> 1 <= k ->
  Phi L (fs (opow a) k) = fs (Phi L (opow a)) k \/ (L = [leaf] /\ a = one).
Proof.
  intros L t a k Hs Ht Ha Hk. subst a.
  assert (Hna : nf (otree t)) by apply nf_otree.
  assert (Hz : nf (opow (otree t))) by (apply nf_opow; exact Hna).
  assert (Hzne : opow (otree t) <> oz) by discriminate.
  assert (Hsrt : forall M, srt (M ++ [t]) -> Phi M (fs (opow (otree t)) k) = fs (Phi M (opow (otree t))) k).
  { intros M HM. apply srt_app in HM as (H1 & _ & H3). symmetry.
    apply Phi_fs_eq; [exact Hzne | exact Hz | | exact H1].
    eapply Forall_impl; [| exact H3]. intros c Hc. inversion Hc as [|? ? Hc1 _]; subst. exact Hc1. }
  destruct Hs as [Hs | (L0 & E & Hs)]; [left; apply Hsrt; exact Hs|].
  destruct L as [|l L'].
  - simpl in E. injection E as E1 E2. subst t. exfalso. apply Ha. reflexivity.
  - simpl in E. injection E as E1 E2. subst l L0.
    destruct L' as [|l' L''].
    + (* L = [leaf] *)
      rewrite !Phi_leaf. unfold opow at 2. rewrite ocons_oz_absorb by exact Ha.
      destruct (opred (otree t)) as [a'|] eqn:Ep.
      * destruct (oz_dec a') as [->|Ha'].
        -- right. split; [reflexivity|]. apply opred_inv in Ep. rewrite Ep. reflexivity.
        -- left. unfold opow. rewrite (fs_pow_succ _ _ _ Ep).
           destruct k as [|k]; [lia|]. simpl orep. apply ocons_oz_absorb. exact Ha'.
      * left. unfold opow. rewrite (fs_pow_lim _ _ Ha Ep). apply ocons_oz_absorb.
        apply fs_ne_oz; [exact Ha | | exact Hk].
        intro E1. rewrite E1 in Ep. discriminate.
    + (* L = leaf :: l' :: L'', with l' :: L'' ++ [t] sorted *)
      left. rewrite !Phi_leaf_cons.
      assert (Hs' : srt ((l' :: L'') ++ [t])) by exact Hs.
      rewrite (Hsrt _ Hs').
      apply srt_app in Hs as (H1 & H2 & H3).
      inversion H3 as [|? ? H4 _]; subst. inversion H4 as [|? ? H5 _]; subst.
      assert (Hl' : otree l' <> oz).
      { intro E0. rewrite E0 in H5. destruct H5 as [E5|E5]; [exact (Ha E5) | exact (olt_oz _ E5)]. }
      destruct H1 as [H1a H1b].
      assert (Hhd : Phi (l' :: L'') (opow (otree t)) = ow (otree l') (Phi L'' (opow (otree t)))).
      { rewrite Phi_cons. apply ocons_big. apply Phi_head; [exact H1a | exact H5]. }
      rewrite Hhd, (ocons_oz_absorb (otree l')) by exact Hl'.
      rewrite fs_cons by (apply Phi_ne; exact Hzne). apply ocons_oz_absorb. exact Hl'.
Qed.

Lemma Psi_lim : forall sp z, nf z -> okind z = KLim -> okind (Psi sp z) = KLim.
Proof.
  induction sp as [|L sp IH]; intros z Hz Hl; cbn [Psi]; [exact Hl|].
  assert (Hne : Psi sp z <> oz) by (intro E; pose proof (IH z Hz Hl) as H; rewrite E in H; discriminate).
  exact (proj2 (Phi_fs L (opow (Psi sp z)) 0 (nf_opow _ (nf_Psi _ _ Hz)) (okind_pow_lim _ Hne))).
Qed.

Lemma Psi_fs_eq : forall sp X k, 1 <= k -> nf (olist X) -> okind (olist X) = KLim ->
  good (node (plug sp X)) -> Psi sp (fs (olist X) k) = fs (Psi sp (olist X)) k.
Proof.
  induction sp as [|L sp IH]; intros X k Hk Hn Hl Hg; [reflexivity|].
  cbn [plug] in Hg. apply good_inv in Hg as [H1 H2]. apply Forall_app in H2 as [_ H4].
  inversion H4 as [|? ? H5 _]; subst.
  cbn [Psi]. rewrite (IH X k Hk Hn Hl H5).
  assert (Hl' : okind (Psi sp (olist X)) = KLim) by (apply Psi_lim; assumption).
  assert (Hne : Psi sp (olist X) <> oz) by (intro E; rewrite E in Hl'; discriminate).
  apply okind_lim in Hl' as [_ Hp].
  replace (opow (fs (Psi sp (olist X)) k)) with (fs (opow (Psi sp (olist X))) k)
    by (unfold opow; rewrite fs_pow_lim by assumption; reflexivity).
  assert (Hot : otree (node (plug sp X)) = Psi sp (olist X)) by (rewrite otree_node, olist_plug; reflexivity).
  destruct (level L (node (plug sp X)) (Psi sp (olist X)) k H1 Hot Hne Hk) as [E|[_ E]].
  - exact E.
  - exfalso. rewrite E in Hp. discriminate.
Qed.

(** ** One chop is exact up to one index *)
Theorem chop_exact : forall sp0 L L' n, 1 <= n ->
  good (node (plug sp0 (L ++ [node (L' ++ [leaf])]))) ->
  olist (plug sp0 (L ++ repeat (node L') n)) = fs (olist (plug sp0 (L ++ [node (L' ++ [leaf])]))) n \/
  olist (plug sp0 (L ++ repeat (node L') n)) = fs (olist (plug sp0 (L ++ [node (L' ++ [leaf])]))) (S n).
Proof.
  intros sp0 L L' n Hn Hg.
  pose proof (good_plug_bottom _ _ Hg) as Hq. apply good_inv in Hq as [Hs _].
  rewrite !olist_plug.
  assert (Hx : nf (olist (L ++ [node (L' ++ [leaf])]))) by apply nf_olist.
  assert (Hxl : okind (olist (L ++ [node (L' ++ [leaf])])) = KLim) by (exact (proj1 (chop_ord [] L L' 0))).
  assert (Hrep : olist (L ++ repeat (node L') n) = Phi L (fs (opow (otree (node (L' ++ [leaf])))) n)).
  { rewrite olist_app, olist_repeat, !otree_node, olist_leaf_snoc. unfold opow.
    rewrite (fs_pow_succ _ _ n (opred_osucc _)). reflexivity. }
  assert (Hold : olist (L ++ [node (L' ++ [leaf])]) = Phi L (opow (otree (node (L' ++ [leaf]))))).
  { rewrite olist_app. reflexivity. }
  assert (Hane : otree (node (L' ++ [leaf])) <> oz).
  { rewrite otree_node, olist_leaf_snoc. unfold osucc. apply oapp_ne. discriminate. }
  destruct (level L _ _ n Hs eq_refl Hane Hn) as [E | [EL Ea]].
  - left. rewrite Hrep, E, <- Hold.
    apply Psi_fs_eq; [exact Hn | exact Hx | exact Hxl | exact Hg].
  - right. subst L.
    rewrite otree_node, olist_leaf_snoc in Ea. apply osucc_one in Ea.
    assert (EL' : L' = []).
    { destruct L' as [|u L'']; [reflexivity|]. exfalso. unfold olist in Ea. rewrite Phi_cons in Ea.
      exact (ocons_ne _ _ Ea). }
    subst L'.
    replace (olist ([leaf] ++ repeat (node []) n)) with (fs (olist ([leaf] ++ [node ([] ++ [leaf])])) (S n)).
    + apply Psi_fs_eq; [lia | exact Hx | exact Hxl | exact Hg].
    + rewrite !olist_app, olist_repeat. change (otree (node [])) with oz. rewrite !Phi_leaf, ocons_orep.
      reflexivity.
Qed.

(** ** Hardy-hierarchy upper bounds *)

(** U(x, n) = H_x(n+2) does not increase along a limit round x -> x[n] or x[n+1] with n -> n+1. *)
Lemma HH_up_lim : forall x n, nf x -> okind x = KLim ->
  HH (fs x n) (n + 3) <= HH x (n + 2) /\ HH (fs x (S n)) (n + 3) <= HH x (n + 2).
Proof.
  intros x n Hx Hl.
  assert (Hxz : x <> oz) by (intro E; subst; discriminate).
  assert (Hf : forall j, nf (fs x j)) by (intro j; exact (proj1 (fs_nf_lt x j Hx Hxz))).
  assert (D : forall j m, 2 <= m -> HH (fs x j) (S m) <= HH (fs x (S j)) m).
  { intros j m Hm. rewrite <- HH_osucc by apply Hf.
    apply (HH_desc_le 2); [apply Hf | apply desc_fs_succ; [exact Hx | exact Hl | lia] | lia | lia]. }
  rewrite (HH_lim x (n + 2) Hx Hl). replace (n + 2) with (S (S n)) by lia. split.
  - apply Nat.le_trans with (m := HH (fs x n) (S (n + 3))); [apply HH_mono; [apply Hf | lia]|].
    apply Nat.le_trans with (m := HH (fs x (S n)) (n + 3)); [apply D; lia|].
    replace (n + 3) with (S (S (S n))) by lia. apply D. lia.
  - replace (n + 3) with (S (S (S n))) by lia. apply D. lia.
Qed.

(** H_(x[j])(m+i) <= H_(x[j+i])(m) for a limit x and m >= 2. *)
Lemma HH_fs_shift : forall x, nf x -> okind x = KLim ->
  forall i j m, 2 <= m -> HH (fs x j) (m + i) <= HH (fs x (j + i)) m.
Proof.
  intros x Hx Hl.
  assert (Hxz : x <> oz) by (intro E; subst; discriminate).
  assert (Hf : forall j, nf (fs x j)) by (intro j; exact (proj1 (fs_nf_lt x j Hx Hxz))).
  induction i as [|i IH]; intros j m Hm.
  - rewrite !Nat.add_0_r. lia.
  - replace (m + S i) with (S m + i) by lia.
    eapply Nat.le_trans; [apply IH; lia|].
    rewrite <- HH_osucc by apply Hf. replace (j + S i) with (S (j + i)) by lia.
    apply (HH_desc_le 2); [apply Hf | apply desc_fs_succ; [exact Hx | exact Hl | lia] | lia | lia].
Qed.

(** Strict growth in the argument at a limit: f_x(n) + n <= f_x(n+1) (HydraOrd.FGH_lim_step), iterated. *)
Lemma FGH_lim_plus : forall x n d, nf x -> okind x = KLim -> 1 <= n -> FGH x n + d <= FGH x (n + d).
Proof.
  intros x n d Hx Hl Hn. induction d as [|d IH]; [rewrite !Nat.add_0_r; lia|].
  replace (n + S d) with (S (n + d)) by lia.
  pose proof (FGH_lim_step x (n + d) Hx Hl ltac:(lia)). lia.
Qed.
