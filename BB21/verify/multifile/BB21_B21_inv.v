(** B21: the dominance invariant (Lemma D) on decomposed states. *)
From Coq Require Import Lia PeanoNat List Bool.
From BB8 Require Import BB21_B21_absdef BB21_B21_grow BB21_B21_steps.
Import ListNotations.
Set Default Goal Selector "!".

Lemma eng_eq : forall b, eng b = eng0 b.
Proof. reflexivity. Qed.

Definition lead1 (b : list nat) : nat := fst (lsplit b).

Lemma lead1_ones_app : forall n Y, (match Y with 1 :: _ => False | _ => True end) -> lead1 (repeat 1 n ++ Y) = n.
Proof.
  induction n; intros Y HY; unfold lead1 in *; simpl.
  - destruct Y as [| [| [| y]] Y]; simpl; try reflexivity. contradiction.
  - destruct (lsplit (repeat 1 n ++ Y)) as [p r] eqn:E. simpl. specialize (IHn Y HY). rewrite E in IHn. simpl in IHn. lia.
Qed.

Lemma lead1_ones : forall n, lead1 (ones n) = n.
Proof. intros. unfold ones. rewrite <- (app_nil_r (repeat 1 n)). apply lead1_ones_app. exact I. Qed.

Lemma lead1_le : forall b, lead1 b <= length b.
Proof.
  induction b as [| d b IH]; unfold lead1 in *; simpl; [lia |].
  destruct d as [| [| d]]; simpl; try lia. destruct (lsplit b) as [p r]. simpl in *. lia.
Qed.

Definition pc (a b : list nat) : Prop := (b = [2] /\ length a = 1) \/ 2 * lead1 b + 2 <= length a.

Fixpoint pairs_ok (l : list (list nat)) : Prop :=
  match l with
  | a :: ((b :: _) as t) => pc a b /\ pairs_ok t
  | _ => True
  end.

(** below the frontier: es nearest-first, l = lead1 of the frontier, n0 = |b0| *)
Fixpoint chainN (l : nat) (es : list nat) (n0 : nat) : Prop :=
  match es with
  | [] => 2 * l + 2 <= n0
  | e :: es' => 2 * l + 2 <= e /\ chainN e es' n0
  end.

Definition pure (b : list nat) := exists m, b = ones (S (S m)).
Definition small (b : list nat) := exists m, b = repeat 1 (S m) ++ [5].
Definition big (b : list nat) := exists m, (exists k, b = repeat 1 (S m) ++ Xs k /\ 1 <= m + k) \/ b = repeat 1 (S m) ++ [4; 1].

Definition tau0 (s : st) : nat :=
  match rev (es s) with
  | [] => lead1 (fr s) + 1
  | e1 :: _ => e1 + 1
  end.

Definition B0min (s : st) : nat := length (b0 s) - tau0 s.
Definition Bound (s : st) : nat := LBe (LBe (B0min s + 1) / 2).

Definition tailok (L : list (list nat)) : Prop :=
  exists M r, Forall (fun b => 2 <= length b) M /\ (L = M ++ [1] :: repeat [2] r \/ L = M ++ repeat [2] (S r)).

Record INV (s : st) : Prop := {
  i_es : esok (es s);
  i_frE : isE (fr s) = false;
  i_nz : Forall nzd (fr s :: up s);
  i_b0 : pure (b0 s) \/ small (b0 s) \/ big (b0 s);
  i_tail : tailok (fr s :: up s);
  i_chain : chainN (lead1 (fr s)) (es s) (length (b0 s));
  i_pairs : pairs_ok (fr s :: up s);
  i_F2 : hd 0 (fr s) = 2 -> big (b0 s);
  i_F3 : hd 0 (fr s) = 3 -> ~ pure (b0 s);
  i_FP : fr s = [1] -> big (b0 s);
  i_D : forall B, In B (fr s :: up s) -> 4 * length B + 16 <= Bound s;
  i_D' : big (b0 s) -> forall B, In B (fr s :: up s) -> 4 * length B + 16 <= eng0 (b0 s);
  i_min : 5 <= B0min s
}.

(** ** helper facts *)
Lemma chain_strip : forall es l n, chainN l es n -> 1 <= l -> chainN (l - 1) (map pred es) (n - 1).
Proof.
  induction es as [| e es IH]; intros l n H Hl; simpl in *.
  - lia.
  - destruct H as [H1 H2]. split; [lia |].
    replace (pred e) with (e - 1) by lia. apply IH; [exact H2 | lia].
Qed.

Lemma chain_lower : forall es l n, chainN l es n -> Forall (fun e => 2 * l + 2 <= e) es /\ 2 * l + 2 <= n.
Proof.
  induction es as [| e es IH]; intros l n H; simpl in *.
  - split; [constructor | exact H].
  - destruct H as [H1 H2]. destruct (IH e n H2) as [F Hn]. split; [| lia].
    constructor; [lia |]. eapply Forall_impl; [| exact F]. intros a Ha. simpl in Ha. lia.
Qed.

Lemma chain_mono : forall es l l' n, chainN l es n -> l' <= l -> chainN l' es n.
Proof. intros [| e es] l l' n H Hl; simpl in *; [lia | destruct H; split; [lia | assumption]]. Qed.

Lemma chain_last : forall es l n e1 r, chainN l es n -> rev es = e1 :: r -> 2 * e1 + 2 <= n.
Proof.
  induction es as [| e es IH] using rev_ind; intros l n e1 r H Hr; simpl in Hr; [discriminate |].
  rewrite rev_app_distr in Hr. simpl in Hr. inversion Hr; subst.
  clear Hr IH. revert l H. induction es as [| a es IH2]; intros l H; simpl in *.
  - destruct H. exact H0.
  - destruct H. eapply IH2. exact H0.
Qed.

Lemma tau0_le : forall s, chainN (lead1 (fr s)) (es s) (length (b0 s)) -> 2 * tau0 s <= length (b0 s).
Proof.
  intros s H. unfold tau0. destruct (rev (es s)) as [| e1 r] eqn:E.
  - apply (f_equal (@rev nat)) in E. rewrite rev_involutive in E. simpl in E. rewrite E in H. simpl in H. lia.
  - pose proof (chain_last _ _ _ _ _ H E). lia.
Qed.

Lemma pure_not_big : forall b, pure b -> ~ big b.
Proof.
  intros b [m ->] [m' [[k [E _]] | E]].
  - unfold ones in E. assert (In 4 (repeat 1 (S (S m)))) as I.
    { rewrite E. apply in_or_app. right. unfold Xs. simpl. left. reflexivity. }
    apply repeat_spec in I. discriminate.
  - unfold ones in E. assert (In 4 (repeat 1 (S (S m)))) as I.
    { rewrite E. apply in_or_app. right. simpl. left. reflexivity. }
    apply repeat_spec in I. discriminate.
Qed.

Lemma pairs_head_len : forall a a' L, pairs_ok (a :: L) -> length a' = length a -> pairs_ok (a' :: L).
Proof.
  intros a a' [| b L] H Hl; simpl in *; [exact I |]. destruct H as [H1 H2]. split; [| exact H2].
  unfold pc in *. rewrite Hl. exact H1.
Qed.

Lemma tail_head_len : forall a a' L, tailok (a :: L) -> 2 <= length a -> 2 <= length a' -> tailok (a' :: L).
Proof.
  intros a a' L [M [r [HM HL]]] Ha Ha'.
  destruct M as [| m M].
  - destruct HL as [HL | HL]; simpl in HL; inversion HL; subst; simpl in Ha; lia.
  - exists (a' :: M), r. inversion HM; subst. split; [constructor; assumption |].
    destruct HL as [HL | HL]; simpl in HL; inversion HL; subst; [left | right]; reflexivity.
Qed.

Lemma eng0_pos : forall b, pure b \/ small b \/ big b -> 1 <= eng0 b.
Proof.
  intros b [[m ->] | [[m ->] | [m [[k [-> _]] | ->]]]].
  - unfold ones. rewrite eng0_pure. lia.
  - rewrite eng_X0. pose proof (h_ge (S m) 1). lia.
  - rewrite eng_XS. pose proof (h_ge (S m + k) (iter 3 (h m) 1)). lia.
  - rewrite eng_41. pose proof (h_ge (S m) 0). lia.
Qed.

Lemma lead1_cons1 : forall tl, lead1 (1 :: tl) = S (lead1 tl).
Proof. intros. unfold lead1. simpl. destruct (lsplit tl). reflexivity. Qed.

Lemma lead1_split : forall tl p r, lsplit tl = (p, r) -> lead1 tl = p.
Proof. intros. unfold lead1. rewrite H. reflexivity. Qed.

Lemma all1_has_big : forall l a, In a l -> 2 <= a -> all1 l = false.
Proof.
  induction l as [| d l IH]; intros a Hin Ha; simpl in *; [contradiction |].
  destruct Hin as [-> | Hin].
  - destruct a as [| [| a]]; [lia | lia |]. reflexivity.
  - rewrite (IH a Hin Ha). apply andb_false_r.
Qed.

Lemma B0min_strip : forall s s', length (b0 s') = length (b0 s) - 1 -> tau0 s' = tau0 s - 1 ->
  1 <= tau0 s -> tau0 s <= length (b0 s) -> B0min s' = B0min s.
Proof. intros. unfold B0min. lia. Qed.

Lemma rev_map_pred : forall es, rev (map pred es) = map pred (rev es).
Proof. intros. symmetry. apply map_rev. Qed.

Lemma inv_est : forall s tl p e T, INV s -> fr s = 1 :: tl -> lsplit tl = (p, S (S e) :: T) ->
  INV (mk (ones (length (b0 s) - 1)) (map pred (es s)) (repeat 1 p ++ (jacc s + 3) :: S e :: T) (up s)).
Proof.
  intros s tl p e T I Hfr Hl. pose proof (lsplit_spec _ _ _ Hl) as Htl.
  assert (Hlf : lead1 (fr s) = S p) by (rewrite Hfr, lead1_cons1; f_equal; apply (lead1_split _ _ _ Hl)).
  pose proof (i_chain s I) as Ch. rewrite Hlf in Ch.
  destruct (chain_lower _ _ _ Ch) as [Fe Hn].
  assert (Hj : 4 <= jacc s) by (unfold jacc; pose proof (eng0_pos _ (i_b0 s I)); rewrite eng_eq; lia).
  set (fr' := repeat 1 p ++ (jacc s + 3) :: S e :: T).
  assert (Hlen : length fr' = length (fr s)) by (unfold fr'; rewrite Hfr, Htl; simpl; rewrite !app_length; simpl; lia).
  assert (Hl' : lead1 fr' = p) by (unfold fr'; apply lead1_ones_app; destruct (jacc s + 3) as [| [| ?]] eqn:?; [lia | lia | exact Logic.I]).
  assert (Hfr2 : 2 <= length (fr s)) by (rewrite Hfr, Htl; simpl; rewrite app_length; simpl; lia).
  assert (Htau : tau0 (mk (ones (length (b0 s) - 1)) (map pred (es s)) fr' (up s)) = tau0 s - 1).
  { unfold tau0. simpl. rewrite rev_map_pred. destruct (rev (es s)) as [| e1 r] eqn:E; simpl.
    - rewrite Hl', Hlf. lia.
    - assert (In e1 (es s)) by (apply in_rev; rewrite E; left; reflexivity).
      rewrite Forall_forall in Fe. specialize (Fe e1 H). lia. }
  assert (Ht1 : 1 <= tau0 s) by (unfold tau0; destruct (rev (es s)); lia).
  pose proof (tau0_le s (i_chain s I)) as Ht2.
  assert (HB : B0min (mk (ones (length (b0 s) - 1)) (map pred (es s)) fr' (up s)) = B0min s).
  { apply B0min_strip; simpl; [unfold ones; rewrite repeat_length; reflexivity | exact Htau | exact Ht1 | lia]. }
  constructor; simpl.
  - (* es *) unfold esok. rewrite Forall_map. eapply Forall_impl; [| exact Fe]. intros a Ha. destruct a; simpl in *; lia.
  - (* frontier not E *) unfold isE. rewrite (all1_has_big fr' (jacc s + 3)); [reflexivity | | lia].
    unfold fr'. apply in_or_app. right. left. reflexivity.
  - (* digits *) pose proof (i_nz s I) as Nz. apply Forall_cons_iff in Nz as [Nf Nu]. constructor; [| exact Nu].
    rewrite Hfr, Htl in Nf. unfold nzd in Nf. unfold fr', nzd.
    apply Forall_cons_iff in Nf as [_ Nf]. apply Forall_app in Nf as [N1 N2].
    apply Forall_app. split; [exact N1 |]. apply Forall_cons_iff in N2 as [_ N2].
    constructor; [lia | constructor; [lia | exact N2]].
  - (* b0 *) left. exists (length (b0 s) - 3). unfold ones. f_equal. lia.
  - (* tail *) apply (tail_head_len (fr s)); [exact (i_tail s I) | exact Hfr2 | lia].
  - (* chain *) rewrite Hl'. unfold ones. rewrite repeat_length. replace p with (S p - 1) by lia. apply chain_strip; [exact Ch | lia].
  - (* pairs *) apply (pairs_head_len (fr s)); [exact (i_pairs s I) | exact Hlen].
  - (* F2 *) intros H. exfalso. unfold fr' in H. destruct p; simpl in H; lia.
  - (* F3 *) intros H. exfalso. unfold fr' in H. destruct p; simpl in H; lia.
  - (* FP *) intros H. exfalso. unfold fr' in H. destruct p as [| [| p]]; simpl in H; inversion H; destruct T; discriminate.
  - (* D *) intros B HB'. unfold Bound. rewrite HB. destruct HB' as [<- | HB'].
    + rewrite Hlen. apply (i_D s I). left. reflexivity.
    + apply (i_D s I). right. exact HB'.
  - (* D' *) intros Hbig. exfalso. apply (pure_not_big _ (ex_intro _ (length (b0 s) - 3) eq_refl)).
    unfold ones in *. replace (S (S (length (b0 s) - 3))) with (length (b0 s) - 1) by lia. exact Hbig.
  - (* min *) rewrite HB. exact (i_min s I).
Qed.

Lemma UB_small : forall b, small b -> eng0 b <= h (length b - 1) 1.
Proof. intros b [m ->]. rewrite eng_X0. rewrite app_length, !repeat_length. apply h_mono2; simpl; lia. Qed.

Lemma UB_big : forall b, big b -> eng0 b <= h (length b - 1) 1.
Proof.
  intros b [m [[k [-> _]] | ->]].
  - rewrite eng_XS. unfold Xs. rewrite !app_length, !repeat_length. cbn [length].
    replace (S m + (1 + (k + 1)) - 1) with (S (S m + k)) by lia.
    change (h (S (S m + k)) 1) with (iter 4 (h (S m + k)) 1). cbn [iter].
    apply h_mono. change (iter 3 (h m) 1 <= iter 3 (h (S m + k)) 1).
    apply (iter_mono_g (h m) (h (S m + k))); [intros y; apply h_mono_m; lia | apply h_mono].
  - rewrite eng_41. rewrite app_length, !repeat_length. apply h_mono2; simpl; lia.
Qed.

Lemma LB_small : forall b, small b -> LBe (length b) <= eng0 b.
Proof. intros b [m ->]. rewrite eng_X0. unfold LBe. rewrite app_length, !repeat_length. apply h_mono2; simpl; lia. Qed.

Lemma LB_big : forall b, big b -> LBe (length b) <= eng0 b.
Proof.
  intros b [m [[k [-> _]] | ->]].
  - rewrite eng_XS. unfold LBe, Xs. rewrite !app_length, !repeat_length. apply h_mono2; simpl; lia.
  - rewrite eng_41. unfold LBe. rewrite app_length, !repeat_length. apply h_mono2; simpl; lia.
Qed.

Lemma chain_len : forall es l n, chainN l es n -> 2 * l + 2 + length es <= n.
Proof.
  induction es as [| e es IH]; intros l n H; simpl in *; [lia |].
  destruct H as [H1 H2]. pose proof (IH e n H2). lia.
Qed.

(** ** X blocks *)
Lemma Xl_len : forall k, length (Xl k) = S k.
Proof. intros [| k]; simpl; [reflexivity |]. rewrite app_length, repeat_length. simpl. lia. Qed.

Lemma Xl_head : forall k, exists a t, Xl k = a :: t /\ 4 <= a.
Proof. intros [| k]; simpl; eexists; eexists; split; try reflexivity; lia. Qed.

Lemma Xl_nz : forall k, nzd (Xl k).
Proof.
  intros [| k]; unfold nzd; simpl; constructor; try lia; [constructor |].
  apply Forall_app. split; [apply Forall_forall; intros a Ha; apply repeat_spec in Ha; lia | constructor; [lia | constructor]].
Qed.

Lemma W_props : forall n k, let W := ones n ++ Xl k in
  length W = n + S k /\ lead1 W = n /\ isE W = false /\ nzd W /\ hd 0 W <> 2 /\ hd 0 W <> 3 /\ W <> [1].
Proof.
  intros n k W. destruct (Xl_head k) as [a [t [Ht Ha]]].
  assert (HW : W = repeat 1 n ++ a :: t) by (unfold W, ones; rewrite Ht; reflexivity).
  repeat split.
  - unfold W, ones. rewrite app_length, repeat_length, Xl_len. reflexivity.
  - rewrite HW. apply lead1_ones_app. destruct a as [| [| ?]]; [lia | lia | exact Logic.I].
  - unfold isE. rewrite HW. rewrite (all1_has_big _ a); [reflexivity | apply in_or_app; right; left; reflexivity | lia].
  - unfold W, nzd. apply Forall_app. split; [apply Forall_forall; intros b Hb; unfold ones in Hb; apply repeat_spec in Hb; lia | apply Xl_nz].
  - rewrite HW. destruct n; simpl; lia.
  - rewrite HW. destruct n; simpl; lia.
  - rewrite HW. destruct n as [| [| n]]; simpl; intros E; inversion E; subst; try lia; destruct t; discriminate.
Qed.

Lemma eng_mod4 : forall b, pure b \/ small b \/ big b -> eng0 b mod 4 = 1.
Proof.
  intros b [[m ->] | [[m ->] | [m [[k [-> _]] | ->]]]].
  - unfold ones. rewrite eng0_pure. reflexivity.
  - destruct m; simpl repeat; simpl app; apply eng0_mod4.
  - destruct m; simpl repeat; simpl app; apply eng0_mod4.
  - destruct m; simpl repeat; simpl app; apply eng0_mod4.
Qed.

Lemma jacc_mod : forall s, INV s -> (jacc s) mod 4 = (2 * length (es s)) mod 4.
Proof.
  intros s I. unfold jacc. rewrite eng_eq. pose proof (eng_mod4 _ (i_b0 s I)) as M.
  pose proof (Nat.div_mod (eng0 (b0 s)) 4 ltac:(lia)) as D. rewrite M in D.
  remember (eng0 (b0 s) / 4) as q. rewrite D.
  replace (4 * q + 1 + 3 + 2 * length (es s)) with (2 * length (es s) + (q + 1) * 4) by lia.
  apply Nat.Div0.mod_add.
Qed.

Lemma jacc_even : forall s, INV s -> Nat.even (jacc s) = true.
Proof.
  intros s I. apply Nat.even_spec. unfold jacc. rewrite eng_eq. pose proof (eng_mod4 _ (i_b0 s I)) as M.
  pose proof (Nat.div_mod (eng0 (b0 s)) 4 ltac:(lia)) as D. rewrite M in D.
  exists (2 * (eng0 (b0 s) / 4) + 2 + length (es s)). lia.
Qed.

Lemma jacc_ge : forall s, INV s -> 4 <= jacc s.
Proof. intros s I. unfold jacc. rewrite eng_eq. pose proof (eng0_pos _ (i_b0 s I)). lia. Qed.

Lemma tail_dec : forall d T up W, tailok ((S (S d) :: T) :: up) -> 2 <= length W ->
  tailok (W :: (S d :: T) :: up).
Proof.
  intros d T up W [M [r [HM HL]]] HW.
  destruct M as [| m M].
  - destruct HL as [HL | HL]; simpl in HL; inversion HL; subst.
    exists [W], r. split; [constructor; [exact HW | constructor] |]. left. reflexivity.
  - inversion HM; subst. destruct HL as [HL | HL]; simpl in HL; inversion HL; subst.
    + exists (W :: (S d :: T) :: M), r. split; [| left; reflexivity].
      constructor; [exact HW | constructor; [simpl in *; lia | exact H2]].
    + exists (W :: (S d :: T) :: M), r. split; [| right; reflexivity].
      constructor; [exact HW | constructor; [simpl in *; lia | exact H2]].
Qed.

Lemma pairs_cons : forall a b L, pc a b -> pairs_ok (b :: L) -> pairs_ok (a :: b :: L).
Proof. intros. simpl. split; assumption. Qed.

Lemma half_le : forall x, 4 <= x -> (x - 4) / 2 + 2 <= x.
Proof. intros. pose proof (Nat.div_le_upper_bound (x - 4) 2 (x - 2) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma half_up : forall x, 2 * ((x - 4) / 2) <= x - 4.
Proof. intros. apply Nat.mul_div_le. lia. Qed.

Lemma half_ge : forall x, (x - 4) / 2 * 2 + 1 >= x - 4.
Proof. intros. pose proof (Nat.div_mod (x - 4) 2 ltac:(lia)). pose proof (Nat.mod_upper_bound (x - 4) 2 ltac:(lia)). lia. Qed.

Lemma inv_dec_es : forall s d T e es', INV s -> fr s = S (S d) :: T -> es s = e :: es' ->
  INV (mk (ones (length (b0 s) - 1)) (map pred es') (ones (pred e) ++ Xl ((jacc s - 4) / 2)) ((S d :: T) :: up s)).
Proof.
  intros s d T e es' I Hfr Hes. rewrite <- Nat.sub_1_r.
  set (k := (jacc s - 4) / 2). set (W := ones (e - 1) ++ Xl k).
  destruct (W_props (e - 1) k) as (WL & Wl & WE & Wn & W2 & W3 & W1). fold W in WL, Wl, WE, Wn, W2, W3, W1.
  pose proof (i_chain s I) as Ch. rewrite Hes in Ch. simpl in Ch. destruct Ch as [Ce Ch].
  destruct (chain_lower _ _ _ Ch) as [Fe Hn].
  pose proof (chain_len _ _ _ Ch) as Hlen.
  pose proof (jacc_ge s I) as Hj.
  pose proof (tau0_le s (i_chain s I)) as Ht2.
  assert (Hlfr : lead1 (fr s) = 0) by (rewrite Hfr; reflexivity).
  assert (Htau : tau0 (mk (ones (length (b0 s) - 1)) (map pred es') W ((S d :: T) :: up s)) = tau0 s - 1).
  { unfold tau0. simpl. rewrite rev_map_pred. rewrite Hes. simpl. destruct (rev es') as [| e1 r] eqn:E; simpl.
    - rewrite Wl. lia.
    - assert (In e1 es') by (apply in_rev; rewrite E; left; reflexivity).
      rewrite Forall_forall in Fe. specialize (Fe e1 H). lia. }
  assert (Ht1 : 1 <= tau0 s) by (unfold tau0; destruct (rev (es s)); lia).
  assert (HB : B0min (mk (ones (length (b0 s) - 1)) (map pred es') W ((S d :: T) :: up s)) = B0min s).
  { apply B0min_strip; simpl; [unfold ones; rewrite repeat_length; reflexivity | exact Htau | exact Ht1 | lia]. }
  assert (Hbeta : length (b0 s) <= 2 * B0min s) by (unfold B0min; lia).
  pose proof (i_min s I) as Hmin.
  (* size of the new block *)
  assert (HWsize : 4 * length W + 16 <= Bound s).
  { unfold Bound. rewrite WL. unfold k.
    destruct (i_b0 s I) as [Hp | [Hs | Hbg]].
    - assert (eng0 (b0 s) = 1) by (destruct Hp as [m ->]; unfold ones; apply eng0_pure).
      assert (jacc s = 4 + 2 * length (es s)) by (unfold jacc; rewrite eng_eq; lia).
      assert (Hk : (jacc s - 4) / 2 = length (es s))
        by (rewrite H0; replace (4 + 2 * length (es s) - 4) with (length (es s) * 2) by lia; apply Nat.div_mul; lia).
      pose proof (GAP (B0min s) (length (b0 s)) 0 Hmin Hbeta ltac:(lia)).
      rewrite Hk. rewrite Hes. simpl length. lia.
    - pose proof (UB_small _ Hs). pose proof (GAP (B0min s) (length (b0 s)) _ Hmin Hbeta H).
      pose proof (half_up (jacc s)). unfold jacc in *. rewrite eng_eq in *. rewrite Hes in *. simpl length in *. lia.
    - pose proof (UB_big _ Hbg). pose proof (GAP (B0min s) (length (b0 s)) _ Hmin Hbeta H).
      pose proof (half_up (jacc s)). unfold jacc in *. rewrite eng_eq in *. rewrite Hes in *. simpl length in *. lia. }
  assert (Hfrlen : length (S d :: T) = length (fr s)) by (rewrite Hfr; reflexivity).
  assert (Hn0 : 6 <= length (b0 s)) by lia.
  constructor; simpl.
  - unfold esok. rewrite Forall_map. eapply Forall_impl; [| exact Fe]. intros a Ha. destruct a; simpl in *; lia.
  - exact WE.
  - pose proof (i_nz s I) as Nz. apply Forall_cons_iff in Nz as [Nf Nu]. rewrite Hfr in Nf. unfold nzd in Nf.
    apply Forall_cons_iff in Nf as [_ Nf]. constructor; [exact Wn | constructor; [| exact Nu]].
    unfold nzd. constructor; [lia | exact Nf].
  - left. exists (length (b0 s) - 3). unfold ones. f_equal. lia.
  - apply tail_dec; [rewrite <- Hfr; exact (i_tail s I) | lia].
  - rewrite Wl. unfold ones. rewrite repeat_length. apply chain_strip; [exact Ch | lia].
  - apply pairs_cons.
    + unfold pc. right. destruct d as [| d].
      * pose proof (i_F2 s I ltac:(rewrite Hfr; reflexivity)) as Hbig.
        pose proof (i_D' s I Hbig (fr s) (or_introl eq_refl)) as HD.
        pose proof (half_ge (jacc s)) as Hh. unfold k in WL. rewrite WL.
        assert (lead1 (S 0 :: T) <= length (fr s)) by (rewrite <- Hfrlen; apply lead1_le).
        assert (jacc s >= eng0 (b0 s) + 3) by (unfold jacc; rewrite eng_eq; lia). lia.
      * assert (lead1 (S (S d) :: T) = 0) by reflexivity. rewrite H. rewrite WL. lia.
    + apply (pairs_head_len (fr s)); [exact (i_pairs s I) | exact Hfrlen].
  - intros H. exfalso. exact (W2 H).
  - intros H. exfalso. exact (W3 H).
  - intros H. exfalso. exact (W1 H).
  - intros B HB'. unfold Bound in *. rewrite HB. destruct HB' as [<- | [<- | HB']].
    + exact HWsize.
    + rewrite Hfrlen. apply (i_D s I). left. reflexivity.
    + apply (i_D s I). right. exact HB'.
  - intros Hbig. exfalso. apply (pure_not_big _ (ex_intro _ (length (b0 s) - 3) eq_refl)).
    unfold ones in *. replace (S (S (length (b0 s) - 3))) with (length (b0 s) - 1) by lia. exact Hbig.
  - rewrite HB. exact Hmin.
Qed.

Lemma tail_dec0 : forall d T up, tailok ((S (S d) :: T) :: up) -> tailok ((S d :: T) :: up).
Proof.
  intros d T up [M [r [HM HL]]].
  destruct M as [| m M].
  - destruct HL as [HL | HL]; simpl in HL; inversion HL; subst.
    exists [], r. split; [constructor |]. left. reflexivity.
  - inversion HM; subst. destruct HL as [HL | HL]; simpl in HL; inversion HL; subst.
    + exists ((S d :: T) :: M), r. split; [constructor; [simpl in *; lia | exact H2] | left; reflexivity].
    + exists ((S d :: T) :: M), r. split; [constructor; [simpl in *; lia | exact H2] | right; reflexivity].
Qed.

Lemma Bound_mono : forall s s', B0min s <= B0min s' -> Bound s <= Bound s'.
Proof. intros. unfold Bound. apply LBe_mono. apply Nat.div_le_mono; [lia |]. apply LBe_mono. lia. Qed.

Definition b0m (s : st) : list nat := ones (length (b0 s) - 1) ++ Xl ((jacc s - 4) / 2).

Lemma eng_ge13 : forall b, small b \/ big b -> 13 <= eng0 b.
Proof.
  intros b [[m ->] | [m [[k [-> _]] | ->]]].
  - rewrite eng_X0. pose proof (h_ge4x (S m) 1 ltac:(lia)). lia.
  - rewrite eng_XS. pose proof (h_ge4x (S m + k) (iter 3 (h m) 1) ltac:(lia)). lia.
  - rewrite eng_41. pose proof (h_ge4x (S m) 0 ltac:(lia)). lia.
Qed.

Lemma b0m_shape : forall s, INV s -> es s = [] ->
  (pure (b0 s) -> small (b0m s)) /\ (~ pure (b0 s) -> big (b0m s)) /\
  length (b0m s) = length (b0 s) + (jacc s - 4) / 2.
Proof.
  intros s I He. pose proof (i_chain s I) as Ch. rewrite He in Ch. simpl in Ch.
  assert (Hn : 2 <= length (b0 s)) by lia.
  assert (Hj : jacc s = eng0 (b0 s) + 3) by (unfold jacc; rewrite eng_eq, He; simpl; lia).
  split; [| split].
  - intros [m Hm]. assert (eng0 (b0 s) = 1) by (rewrite Hm; unfold ones; apply eng0_pure).
    unfold b0m. rewrite Hj, H. simpl. exists (length (b0 s) - 2). unfold ones. f_equal. f_equal. lia.
  - intros Hnp. destruct (i_b0 s I) as [Hp | Hsb]; [contradiction |].
    pose proof (eng_ge13 _ Hsb) as H13. pose proof (half_ge (jacc s)) as Hhg.
    exists (length (b0 s) - 2). left. exists ((jacc s - 4) / 2 - 1). split; [| lia].
    unfold b0m, ones. destruct ((jacc s - 4) / 2) as [| kk] eqn:Ek.
    + exfalso. pose proof (half_ge (jacc s)). lia.
    + simpl Xl. replace (S (length (b0 s) - 2)) with (length (b0 s) - 1) by lia.
      replace (S kk - 1) with kk by lia. reflexivity.
  - unfold b0m. rewrite app_length, Xl_len. unfold ones. rewrite repeat_length. lia.
Qed.

Lemma big_not_pure : forall b, big b -> ~ pure b.
Proof. intros b Hb Hp. exact (pure_not_big b Hp Hb). Qed.

Lemma small_not_pure : forall b, small b -> ~ pure b.
Proof.
  intros b [m ->] [m' E]. unfold ones in E. assert (In 5 (repeat 1 (S (S m')))) as I.
  { rewrite <- E. apply in_or_app. right. left. reflexivity. }
  apply repeat_spec in I. discriminate.
Qed.

Lemma b0m_D' : forall s, INV s -> es s = [] -> ~ pure (b0 s) ->
  LBe (LBe (B0min s + 1) / 2) <= eng0 (b0m s).
Proof.
  intros s I He Hnp. destruct (b0m_shape s I He) as [_ [Hbg HL]]. specialize (Hbg Hnp).
  pose proof (LB_big _ Hbg) as H1. eapply Nat.le_trans; [| exact H1]. apply LBe_mono.
  assert (Hj : jacc s = eng0 (b0 s) + 3) by (unfold jacc; rewrite eng_eq, He; simpl; lia).
  destruct (i_b0 s I) as [Hp | Hsb]; [contradiction |].
  assert (HLB : LBe (length (b0 s)) <= eng0 (b0 s)) by (destruct Hsb; [apply LB_small | apply LB_big]; assumption).
  assert (HB0 : B0min s + 1 <= length (b0 s)) by (unfold B0min, tau0; rewrite He; simpl; pose proof (i_chain s I) as Ch; rewrite He in Ch; simpl in Ch; lia).
  pose proof (LBe_mono _ _ HB0). pose proof (half_ge (jacc s)).
  assert (2 <= length (b0 s)) by (pose proof (i_chain s I) as Ch; rewrite He in Ch; simpl in Ch; lia).
  rewrite HL. pose proof (Nat.div_le_upper_bound (LBe (B0min s + 1)) 2 ((jacc s - 4) / 2 + 2) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma inv_dec_b0 : forall s d T, INV s -> es s = [] -> fr s = S (S d) :: T -> isE (S d :: T) = false ->
  INV (mk (b0m s) [] (S d :: T) (up s)).
Proof.
  intros s d T I He Hfr HE.
  destruct (b0m_shape s I He) as [Hsm [Hbg HL]].
  pose proof (i_chain s I) as Ch. rewrite He in Ch. simpl in Ch.
  assert (Hj : jacc s = eng0 (b0 s) + 3) by (unfold jacc; rewrite eng_eq, He; simpl; lia).
  assert (Hfrlen : length (S d :: T) = length (fr s)) by (rewrite Hfr; reflexivity).
  pose proof (half_ge (jacc s)) as Hhg.
  (* critical decrement bound *)
  assert (Hcrit : d = 0 -> 2 * length (fr s) + 7 <= (jacc s - 4) / 2 /\ big (b0 s)).
  { intros ->. pose proof (i_F2 s I ltac:(rewrite Hfr; reflexivity)) as Hbig.
    pose proof (i_D' s I Hbig (fr s) (or_introl eq_refl)) as HD. split; [lia | exact Hbig]. }
  assert (Hlead : 2 * lead1 (S d :: T) + 2 <= (jacc s - 4) / 2 + 2).
  { destruct d as [| d].
    - destruct (Hcrit eq_refl) as [Hc _]. pose proof (lead1_le (1 :: T)). simpl length in *. rewrite Hfr in Hc. simpl in Hc. lia.
    - change (lead1 (S (S d) :: T)) with 0. lia. }
  assert (Htau : tau0 (mk (b0m s) [] (S d :: T) (up s)) = lead1 (S d :: T) + 1) by reflexivity.
  assert (HB : B0min s <= B0min (mk (b0m s) [] (S d :: T) (up s))).
  { assert (Ht : tau0 s = 1) by (unfold tau0; rewrite He, Hfr; reflexivity).
    unfold B0min. rewrite Htau. simpl b0. rewrite HL, Ht. lia. }
  assert (Hnp3 : hd 0 (fr s) <> 3 \/ ~ pure (b0 s)).
  { destruct (Nat.eq_dec (hd 0 (fr s)) 3); [right; apply (i_F3 s I); exact e | left; exact n]. }
  constructor; simpl.
  - constructor.
  - exact HE.
  - pose proof (i_nz s I) as Nz. apply Forall_cons_iff in Nz as [Nf Nu]. rewrite Hfr in Nf. unfold nzd in Nf.
    apply Forall_cons_iff in Nf as [_ Nf]. constructor; [| exact Nu]. unfold nzd. constructor; [lia | exact Nf].
  - right. destruct (i_b0 s I) as [Hp | Hsb].
    + left. exact (Hsm Hp).
    + right. apply Hbg. destruct Hsb; [apply small_not_pure | apply big_not_pure]; assumption.
  - apply tail_dec0. rewrite <- Hfr. exact (i_tail s I).
  - rewrite HL. lia.
  - apply (pairs_head_len (fr s)); [exact (i_pairs s I) | exact Hfrlen].
  - intros H2. simpl in H2. assert (d = 1) by lia. subst d. apply Hbg. intros Hp. rewrite Hfr in Hnp3. simpl in Hnp3.
    destruct Hnp3 as [Hn | Hn]; [apply Hn; reflexivity | exact (Hn Hp)].
  - intros H3. destruct (i_b0 s I) as [Hp | Hsb].
    + apply small_not_pure. exact (Hsm Hp).
    + apply big_not_pure, Hbg. destruct Hsb; [apply small_not_pure | apply big_not_pure]; assumption.
  - intros H1. inversion H1; subst. destruct (Hcrit eq_refl) as [_ Hbig]. apply Hbg. apply big_not_pure. exact Hbig.
  - intros B HB'. eapply Nat.le_trans; [| apply Bound_mono; exact HB].
    destruct HB' as [<- | HB'].
    + rewrite Hfrlen. apply (i_D s I). left. reflexivity.
    + apply (i_D s I). right. exact HB'.
  - intros Hbig' B HB'. destruct (i_b0 s I) as [Hp | Hsb].
    + exfalso. pose proof (Hsm Hp) as Hs. destruct Hs as [m Hm]. destruct Hbig' as [m' [[k [Hk _]] | Hk]];
        rewrite Hm in Hk.
      * assert (In 5 (repeat 1 (S m') ++ Xs k)) as I5 by (rewrite <- Hk; apply in_or_app; right; left; reflexivity).
        apply in_app_or in I5. destruct I5 as [I5 | I5]; [apply repeat_spec in I5; discriminate |].
        unfold Xs in I5. simpl in I5. destruct I5 as [I5 | I5]; [discriminate |]. apply in_app_or in I5.
        destruct I5 as [I5 | [I5 | []]]; [apply repeat_spec in I5; discriminate | discriminate].
      * assert (In 5 (repeat 1 (S m') ++ [4; 1])) as I5 by (rewrite <- Hk; apply in_or_app; right; left; reflexivity).
        apply in_app_or in I5. destruct I5 as [I5 | [I5 | [I5 | []]]]; [apply repeat_spec in I5 | |]; discriminate.
    + assert (Hnp : ~ pure (b0 s)) by (destruct Hsb; [apply small_not_pure | apply big_not_pure]; assumption).
      pose proof (b0m_D' s I He Hnp) as HD.
      assert (4 * length B + 16 <= Bound s).
      { destruct HB' as [<- | HB']; [rewrite Hfrlen; apply (i_D s I); left; reflexivity | apply (i_D s I); right; exact HB']. }
      unfold Bound in H. lia.
  - pose proof (i_min s I). lia.
Qed.

(** ** completion of the frontier block next to b0 *)
Lemma chain_app : forall X l m n, chainN l (X ++ [m]) n <-> chainN l X m /\ 2 * m + 2 <= n.
Proof.
  induction X as [| x X IH]; intros l m n; simpl.
  - tauto.
  - rewrite IH. tauto.
Qed.

Lemma pairs_to_chain : forall Es a b L, pairs_ok (a :: map ones Es ++ b :: L) -> 2 <= length a ->
  Forall (fun e => 2 <= e) Es -> chainN (lead1 b) (rev Es) (length a).
Proof.
  induction Es as [| e Es IH]; intros a b L Hp Ha HE.
  - simpl in Hp |- *. destruct Hp as [[[-> Hl] | Hl] _]; [lia | exact Hl].
  - change (pc a (ones e) /\ pairs_ok (ones e :: map ones Es ++ b :: L)) in Hp.
    destruct Hp as [Hpc Hp]. inversion HE; subst. simpl rev. apply chain_app. split.
    + pose proof (IH (ones e) b L Hp) as R. unfold ones in R at 2. rewrite repeat_length in R.
      apply R; [unfold ones; rewrite repeat_length; exact H1 | exact H2].
    + unfold pc in Hpc. rewrite lead1_ones in Hpc. destruct Hpc as [[Hx _] | Hx]; [| exact Hx].
      unfold ones in Hx. destruct e as [| [| [| e]]]; try lia; discriminate.
Qed.

Lemma pairs_suffix : forall A L, pairs_ok (A ++ L) -> pairs_ok L.
Proof.
  induction A as [| a A IH]; intros L H; simpl in *; [exact H |].
  apply IH. destruct (A ++ L) as [| b t] eqn:E; [exact Logic.I | destruct H; exact H0].
Qed.

Lemma tail_suffix : forall A L, tailok (A ++ L) -> Forall (fun b => 2 <= length b) A -> L <> [] -> tailok L.
Proof.
  induction A as [| a A IH]; intros L H HA HL; simpl in *; [exact H |].
  inversion HA; subst. apply IH; [| exact H3 | exact HL].
  destruct H as [M [r [HM HL']]]. destruct M as [| m M].
  - destruct HL' as [E | E]; simpl in E; inversion E; subst; simpl in H2; lia.
  - apply Forall_cons_iff in HM as [_ HM']. exists M, r. split; [exact HM' |].
    destruct HL' as [E | E]; simpl in E; injection E as E' E''; [left | right]; exact E''.
Qed.

Lemma split_up : forall up, (exists b, In b up /\ isE b = false) ->
  exists Es fr2 up2, up = map ones Es ++ fr2 :: up2 /\ isE fr2 = false /\ Forall (fun e => 2 <= e) Es.
Proof.
  induction up as [| b up IH]; intros [c [Hc Hce]]; [contradiction |].
  destruct (isE b) eqn:Eb.
  - destruct Hc as [-> | Hc]; [congruence |].
    destruct (IH (ex_intro _ c (conj Hc Hce))) as [Es [fr2 [up2 [Hu [Hf HE]]]]].
    exists (length b :: Es), fr2, up2. unfold isE in Eb. apply andb_true_iff in Eb as [E1 E2].
    apply Nat.leb_le in E2. split; [| split; [exact Hf | constructor; [exact E2 | exact HE]]].
    simpl. rewrite Hu. f_equal. unfold ones. clear -E1. induction b as [| d b IHb]; simpl in *; [reflexivity |].
    apply andb_true_iff in E1 as [D E1]. apply Nat.eqb_eq in D. subst. f_equal. apply IHb. exact E1.
  - exists [], b, up. simpl. split; [reflexivity | split; [exact Eb | constructor]].
Qed.

Lemma tail_has_nonE : forall L, tailok L -> exists b, In b L /\ isE b = false.
Proof.
  intros L [M [r [_ [-> | ->]]]].
  - exists [1]. split; [apply in_or_app; right; left; reflexivity | reflexivity].
  - exists [2]. split; [apply in_or_app; right; left; reflexivity | reflexivity].
Qed.

Lemma all1_ones_eq : forall T, all1 T = true -> T = ones (length T).
Proof.
  induction T as [| d T IH]; simpl; intros H; [reflexivity |].
  apply andb_true_iff in H as [D H]. apply Nat.eqb_eq in D. subst. unfold ones in *. simpl. f_equal. apply IH. exact H.
Qed.

Lemma inv_compl : forall s T, INV s -> es s = [] -> fr s = 2 :: T -> all1 T = true -> T <> [] ->
  exists Es fr2 up2, up s = map ones Es ++ fr2 :: up2 /\
    INV (mk (b0m s) (rev Es ++ [length (fr s)]) fr2 up2).
Proof.
  intros s T I He Hfr HT HTn.
  destruct (b0m_shape s I He) as [_ [Hbg HL]].
  pose proof (i_chain s I) as Ch. rewrite He in Ch. simpl in Ch.
  pose proof (half_ge (jacc s)) as Hhg.
  assert (Hj : jacc s = eng0 (b0 s) + 3) by (unfold jacc; rewrite eng_eq, He; simpl; lia).
  pose proof (i_F2 s I ltac:(rewrite Hfr; reflexivity)) as Hbig.
  pose proof (i_D' s I Hbig (fr s) (or_introl eq_refl)) as HD.
  assert (Hq : 2 * length (fr s) + 7 <= (jacc s - 4) / 2) by lia.
  assert (Hbig' : big (b0m s)) by (apply Hbg, big_not_pure, Hbig).
  assert (Hfl : 2 <= length (fr s)) by (rewrite Hfr; destruct T; [congruence | simpl; lia]).
  (* the blocks above *)
  assert (Hne : exists b, In b (up s) /\ isE b = false).
  { pose proof (i_tail s I) as Ht. assert (tailok (up s)).
    { apply (tail_suffix [fr s]); [exact Ht | constructor; [exact Hfl | constructor] |].
      intros E. destruct Ht as [M [r [HM [E' | E']]]]; rewrite E, Hfr in E';
        destruct M as [| m M]; simpl in E'; inversion E'; try discriminate;
        try (destruct M; discriminate); subst; apply HTn; reflexivity. }
    apply tail_has_nonE. exact H. }
  destruct (split_up (up s) Hne) as [Es [fr2 [up2 [Hu [Hf2 HEs]]]]].
  exists Es, fr2, up2. split; [exact Hu |].
  assert (HP : pairs_ok (fr s :: map ones Es ++ fr2 :: up2)) by (rewrite <- Hu; exact (i_pairs s I)).
  assert (Htau : tau0 (mk (b0m s) (rev Es ++ [length (fr s)]) fr2 up2) = length (fr s) + 1).
  { unfold tau0. simpl. rewrite rev_app_distr, rev_involutive. reflexivity. }
  assert (Ht0 : tau0 s = 1) by (unfold tau0; rewrite He, Hfr; reflexivity).
  assert (HB : B0min s <= B0min (mk (b0m s) (rev Es ++ [length (fr s)]) fr2 up2)).
  { unfold B0min. rewrite Htau, Ht0. simpl b0. rewrite HL. lia. }
  assert (Hsub : forall B, In B (fr2 :: up2) -> In B (up s)).
  { intros B HB'. rewrite Hu. apply in_or_app. right. exact HB'. }
  constructor; simpl.
  - unfold esok. apply Forall_app. split; [apply Forall_rev; exact HEs | constructor; [exact Hfl | constructor]].
  - exact Hf2.
  - pose proof (i_nz s I) as Nz. apply Forall_cons_iff in Nz as [_ Nu]. rewrite Hu in Nu.
    apply Forall_app in Nu as [_ Nu]. exact Nu.
  - right. right. exact Hbig'.
  - pose proof (i_tail s I) as Ht. rewrite Hu in Ht.
    apply (tail_suffix (fr s :: map ones Es)); [exact Ht | | discriminate].
    constructor; [exact Hfl |]. rewrite Forall_map. eapply Forall_impl; [| exact HEs].
    intros e He'. unfold ones. rewrite repeat_length. exact He'.
  - apply chain_app. split.
    + apply (pairs_to_chain Es (fr s) fr2 up2 HP Hfl HEs).
    + rewrite HL. lia.
  - exact (pairs_suffix (fr s :: map ones Es) (fr2 :: up2) HP).
  - intros _. exact Hbig'.
  - intros _. apply big_not_pure. exact Hbig'.
  - intros _. exact Hbig'.
  - intros B HB'. eapply Nat.le_trans; [| apply Bound_mono; exact HB]. apply (i_D s I). right. apply Hsub. exact HB'.
  - intros _ B HB'. pose proof (b0m_D' s I He (big_not_pure _ Hbig)) as H1.
    assert (4 * length B + 16 <= Bound s) by (apply (i_D s I); right; apply Hsub; exact HB').
    unfold Bound in H. lia.
  - pose proof (i_min s I). lia.
Qed.

Lemma half2_up : forall x, 2 * ((x - 2) / 2) <= x - 2.
Proof. intros. apply Nat.mul_div_le. lia. Qed.

Lemma half2_ge : forall x, (x - 2) / 2 * 2 + 1 >= x - 2.
Proof. intros. pose proof (Nat.div_mod (x - 2) 2 ltac:(lia)). pose proof (Nat.mod_upper_bound (x - 2) 2 ltac:(lia)). lia. Qed.

Lemma inv_P : forall s up', INV s -> fr s = [1] -> up s = [2] :: up' ->
  INV (mk (ones (length (b0 s) - 1)) (map pred (es s)) (Xl ((jacc s - 2) / 2)) ([1] :: up')).
Proof.
  intros s up' I Hfr Hup.
  set (k := (jacc s - 2) / 2). set (W := Xl k).
  destruct (W_props 0 k) as (WL & Wl & WE & Wn & W2 & W3 & W1).
  change (ones 0 ++ Xl k) with W in WL, Wl, WE, Wn, W2, W3, W1.
  pose proof (i_chain s I) as Ch. rewrite Hfr in Ch. change (lead1 [1]) with 1 in Ch.
  destruct (chain_lower _ _ _ Ch) as [Fe Hn].
  pose proof (chain_len _ _ _ Ch) as Hlen.
  pose proof (tau0_le s (i_chain s I)) as Ht2.
  pose proof (i_FP s I Hfr) as Hbig.
  pose proof (eng_ge13 _ (or_intror Hbig)) as H13.
  assert (Hj : jacc s = eng0 (b0 s) + 3 + 2 * length (es s)) by (unfold jacc; rewrite eng_eq; lia).
  pose proof (half2_ge (jacc s)) as Hh1. pose proof (half2_up (jacc s)) as Hh2. fold k in Hh1, Hh2.
  assert (Htau : tau0 (mk (ones (length (b0 s) - 1)) (map pred (es s)) W ([1] :: up')) = tau0 s - 1).
  { unfold tau0. simpl. rewrite rev_map_pred. destruct (rev (es s)) as [| e1 r] eqn:E; simpl.
    - rewrite Wl, Hfr. reflexivity.
    - assert (In e1 (es s)) by (apply in_rev; rewrite E; left; reflexivity).
      rewrite Forall_forall in Fe. specialize (Fe e1 H). lia. }
  assert (Ht1 : 1 <= tau0 s) by (unfold tau0; destruct (rev (es s)); lia).
  assert (HB : B0min (mk (ones (length (b0 s) - 1)) (map pred (es s)) W ([1] :: up')) = B0min s).
  { apply B0min_strip; simpl; [unfold ones; rewrite repeat_length; reflexivity | exact Htau | exact Ht1 | lia]. }
  assert (Hbeta : length (b0 s) <= 2 * B0min s) by (unfold B0min; lia).
  pose proof (i_min s I) as Hmin.
  assert (HWsize : 4 * length W + 16 <= Bound s).
  { unfold Bound. rewrite WL. pose proof (UB_big _ Hbig). pose proof (GAP (B0min s) (length (b0 s)) _ Hmin Hbeta H). lia. }
  assert (Hup_in : forall B, In B up' -> In B (up s)) by (intros B HB'; rewrite Hup; right; exact HB').
  constructor; simpl.
  - unfold esok. rewrite Forall_map. eapply Forall_impl; [| exact Fe]. intros a Ha. destruct a; simpl in *; lia.
  - exact WE.
  - pose proof (i_nz s I) as Nz. apply Forall_cons_iff in Nz as [_ Nu]. rewrite Hup in Nu.
    apply Forall_cons_iff in Nu as [_ Nu]. constructor; [exact Wn | constructor; [| exact Nu]].
    unfold nzd. constructor; [lia | constructor].
  - left. exists (length (b0 s) - 3). unfold ones. f_equal. lia.
  - pose proof (i_tail s I) as Ht. rewrite Hfr, Hup in Ht. destruct Ht as [M [r [HM [E | E]]]].
    + destruct M as [| m M]; simpl in E.
      * injection E as E1. destruct r as [| r]; simpl in E1; [discriminate |]. injection E1 as E2.
        exists [W], r. rewrite E2. split; [constructor; [lia | constructor] | left; reflexivity].
      * injection E as E0 E1. subst m. apply Forall_cons_iff in HM as [HM _]. simpl in HM. lia.
    + destruct M as [| m M]; simpl in E; [discriminate |].
      injection E as E0 E1. subst m. apply Forall_cons_iff in HM as [HM _]. simpl in HM. lia.
  - rewrite Wl. unfold ones. rewrite repeat_length. replace 0 with (1 - 1) by lia. apply chain_strip; [exact Ch | lia].
  - split.
    + unfold pc. right. change (lead1 [1]) with 1. lia.
    + pose proof (i_pairs s I) as P. rewrite Hfr, Hup in P. destruct P as [_ P].
      exact (pairs_head_len [2] [1] up' P eq_refl).
  - intros H. exfalso. exact (W2 H).
  - intros H. exfalso. exact (W3 H).
  - intros H. exfalso. exact (W1 H).
  - intros B HB'. unfold Bound in *. rewrite HB. destruct HB' as [<- | [<- | HB']].
    + exact HWsize.
    + simpl. assert (In [2] (up s)) by (rewrite Hup; left; reflexivity).
      pose proof (i_D s I [2] (or_intror H)). unfold Bound in H0. simpl in *. lia.
    + apply (i_D s I). right. apply Hup_in. exact HB'.
  - intros Hbig'. exfalso. apply (pure_not_big _ (ex_intro _ (length (b0 s) - 3) eq_refl)).
    unfold ones in *. replace (S (S (length (b0 s) - 3))) with (length (b0 s) - 1) by lia. exact Hbig'.
  - rewrite HB. exact Hmin.
Qed.

Definition deep (b : list nat) := exists m k, b = repeat 1 (S m) ++ Xs k /\ 1 <= m + k.

Lemma deep_big : forall b, deep b -> big b.
Proof. intros b [m [k [-> H]]]. exists m. left. exists k. split; [reflexivity | exact H]. Qed.

Lemma deep_mod64 : forall b, deep b -> eng0 b mod 64 = 17.
Proof. intros b [m [k [-> H]]]. apply eng_XS_mod64. exact H. Qed.

Lemma b0m_deep : forall s, INV s -> es s = [] -> ~ pure (b0 s) -> deep (b0m s).
Proof.
  intros s I He Hnp. pose proof (i_chain s I) as Ch. rewrite He in Ch. simpl in Ch.
  assert (Hj : jacc s = eng0 (b0 s) + 3) by (unfold jacc; rewrite eng_eq, He; simpl; lia).
  destruct (i_b0 s I) as [Hp | Hsb]; [contradiction |].
  pose proof (eng_ge13 _ Hsb) as H13. pose proof (half_ge (jacc s)) as Hhg.
  exists (length (b0 s) - 2), ((jacc s - 4) / 2 - 1). split; [| lia].
  unfold b0m, ones. destruct ((jacc s - 4) / 2) as [| kk] eqn:Ek.
  - exfalso. lia.
  - simpl Xl. replace (S (length (b0 s) - 2)) with (length (b0 s) - 1) by lia.
    replace (S kk - 1) with kk by lia. reflexivity.
Qed.

(** ** the refill: the next phase starts *)
(** generic phase start: the frontier is 1^a,4,1 with 1 <= a <= |E_(N-1)| - 1 (B21: a = |E|-1; W2PR: a = |E|-2),
    followed by q >= 1 lone 2s *)
Lemma inv_refill_gen : forall s e es' a q, INV s -> fr s = [1] -> up s = [] -> es s = e :: es' -> 1 <= q ->
  1 <= a -> a <= e - 1 ->
  INV (mk (ones (length (b0 s) - 1)) (map pred es') (ones a ++ [4; 1]) (repeat [2] q)).
Proof.
  intros s e es' a q I Hfr Hup Hes Hq1 Ha1 Ha2.
  set (F := ones a ++ [4; 1]).
  pose proof (i_chain s I) as Ch. rewrite Hfr, Hes in Ch. change (lead1 [1]) with 1 in Ch. simpl in Ch. destruct Ch as [Ce Ch].
  destruct (chain_lower _ _ _ Ch) as [Fe Hn].
  pose proof (chain_len _ _ _ Ch) as Hlen.
  pose proof (tau0_le s (i_chain s I)) as Ht2.
  assert (HFl : length F = a + 2) by (unfold F, ones; rewrite app_length, repeat_length; simpl; lia).
  assert (HFlead : lead1 F = a) by (unfold F, ones; apply lead1_ones_app; exact Logic.I).
  assert (HFE : isE F = false).
  { unfold isE, F. rewrite (all1_has_big _ 4); [reflexivity | apply in_or_app; right; left; reflexivity | lia]. }
  set (s' := mk (ones (length (b0 s) - 1)) (map pred es') F (repeat [2] q)).
  assert (Htau : tau0 s' <= tau0 s - 1).
  { unfold tau0. simpl. rewrite rev_map_pred. rewrite Hes. simpl. destruct (rev es') as [| e1 r] eqn:E; simpl.
    - rewrite HFlead. lia.
    - assert (In e1 es') by (apply in_rev; rewrite E; left; reflexivity).
      rewrite Forall_forall in Fe. specialize (Fe e1 H). lia. }
  assert (Ht1 : 1 <= tau0 s) by (unfold tau0; destruct (rev (es s)); lia).
  assert (HB : B0min s <= B0min s').
  { unfold B0min. simpl b0. unfold ones. rewrite repeat_length. lia. }
  assert (Hbeta : length (b0 s) <= 2 * B0min s) by (unfold B0min; lia).
  pose proof (i_min s I) as Hmin.
  pose proof (GAP (B0min s) (length (b0 s)) 0 Hmin Hbeta ltac:(lia)) as HG.
  constructor; simpl.
  - unfold esok. rewrite Forall_map. eapply Forall_impl; [| exact Fe]. intros z Hz. destruct z; simpl in *; lia.
  - exact HFE.
  - constructor.
    + unfold F, nzd, ones. apply Forall_app. split; [apply Forall_forall; intros x Hx; apply repeat_spec in Hx; lia | repeat constructor; lia].
    + apply Forall_forall. intros b Hb. apply repeat_spec in Hb. rewrite Hb. unfold nzd. repeat constructor; lia.
  - left. exists (length (b0 s) - 3). unfold ones. f_equal. lia.
  - exists [F], (q - 1). split; [constructor; [lia | constructor] |]. right. simpl. f_equal.
    replace q with (S (q - 1)) at 1 by lia. reflexivity.
  - rewrite HFlead. unfold ones. rewrite repeat_length. apply (chain_mono _ (e - 1)); [apply chain_strip; [exact Ch | lia] | lia].
  - destruct q as [| q']; [lia |]. simpl. split.
    + unfold pc. right. change (lead1 [2]) with 0. lia.
    + clear. induction q' as [| q' IH]; simpl; [exact Logic.I | split; [left; split; reflexivity | exact IH]].
  - intros H. exfalso. unfold F, ones in H. destruct a; [lia | simpl in H; lia].
  - intros H. exfalso. unfold F, ones in H. destruct a; [lia | simpl in H; lia].
  - intros H. exfalso. unfold F, ones in H. destruct a as [| [| ?]]; simpl in H; discriminate.
  - intros B HB'. eapply Nat.le_trans; [| apply Bound_mono; exact HB]. unfold Bound in *. destruct HB' as [<- | HB'].
    + rewrite HFl. lia.
    + apply repeat_spec in HB'. rewrite HB'. cbn [length]. lia.
  - intros Hbig. exfalso. apply (pure_not_big _ (ex_intro _ (length (b0 s) - 3) eq_refl)).
    unfold ones in *. replace (S (S (length (b0 s) - 3))) with (length (b0 s) - 1) by lia. exact Hbig.
  - lia.
Qed.

Lemma inv_refill : forall s e es', INV s -> fr s = [1] -> up s = [] -> es s = e :: es' -> 1 <= jacc s / 4 ->
  INV (mk (ones (length (b0 s) - 1)) (map pred es') (ones (pred e) ++ [4; 1]) (repeat [2] (jacc s / 4))).
Proof.
  intros s e es' I Hfr Hup Hes Hq. pose proof (i_chain s I) as Ch. rewrite Hfr, Hes in Ch. simpl in Ch.
  apply (inv_refill_gen s e es' (pred e) (jacc s / 4) I Hfr Hup Hes Hq); [| lia].
  change (lead1 [1]) with 1 in Ch. destruct e; simpl in *; lia.
Qed.
