(** B21 / W2PR quantitative layer, part 2: B0min bookkeeping per transition (refill-independent). *)
From Coq Require Import Lia PeanoNat List Bool.
From BB8 Require Import BB21_B21_absdef BB21_B21_grow BB21_B21_steps BB21_B21_inv BB_FGH_wa BB21_B21_qnt.
Import ListNotations.
Set Default Goal Selector "!".

(** the merge map at depth 0 *)
Definition Gm (b : nat) : nat := Nat.max (S b) (LBe (b + 1) / 4 - 2).

Lemma good_Gm : good Gm.
Proof.
  split.
  - intros x. unfold Gm. lia.
  - intros x y H. unfold Gm. pose proof (LBe_mono (x + 1) (y + 1) ltac:(lia)).
    pose proof (Nat.div_le_mono (LBe (x + 1)) (LBe (y + 1)) 4 ltac:(lia) H0). lia.
Qed.

Lemma Gm_S : forall x, S x <= Gm x.
Proof. intros. unfold Gm. lia. Qed.

Lemma n0_ge6 : forall s, INV s -> 6 <= length (b0 s).
Proof.
  intros s I. pose proof (i_min s I). assert (1 <= tau0 s) by (unfold tau0; destruct (rev (es s)); lia).
  unfold B0min in *. lia.
Qed.

Lemma eng_nonpure : forall s, INV s -> ~ pure (b0 s) -> LBe (length (b0 s)) <= eng0 (b0 s).
Proof.
  intros s I Hnp. destruct (i_b0 s I) as [Hp | [Hs | Hb]]; [contradiction | apply LB_small; exact Hs | apply LB_big; exact Hb].
Qed.

(** with b0 pending, the J-acc and the merge length dominate B0min *)
Lemma jacc_ge_B0min : forall s, INV s -> ~ pure (b0 s) -> B0min s + 1 <= jacc s /\ B0min s <= (jacc s - 4) / 2.
Proof.
  intros s I Hnp. pose proof (eng_nonpure s I Hnp) as E. pose proof (n0_ge6 s I) as N.
  pose proof (LBe_big (length (b0 s)) ltac:(lia)) as L. unfold jacc. rewrite eng_eq. unfold B0min.
  split; [lia |]. apply Nat.div_le_lower_bound; lia.
Qed.

(** ** strips keep B0min *)
Lemma B0min_est : forall s tl p e T, INV s -> fr s = 1 :: tl -> lsplit tl = (p, S (S e) :: T) ->
  B0min (mk (ones (length (b0 s) - 1)) (map pred (es s)) (repeat 1 p ++ (jacc s + 3) :: S e :: T) (up s)) = B0min s.
Proof.
  intros s tl p e T I Hfr Hl.
  assert (Hlf : lead1 (fr s) = S p) by (rewrite Hfr, lead1_cons1; f_equal; apply (lead1_split _ _ _ Hl)).
  pose proof (i_chain s I) as Ch. rewrite Hlf in Ch.
  destruct (chain_lower _ _ _ Ch) as [Fe Hn].
  assert (Hl' : lead1 (repeat 1 p ++ (jacc s + 3) :: S e :: T) = p)
    by (apply lead1_ones_app; destruct (jacc s + 3) as [| [| ?]] eqn:?; [lia | lia | exact Logic.I]).
  pose proof (tau0_le s (i_chain s I)) as Ht2.
  assert (Ht1 : 1 <= tau0 s) by (unfold tau0; destruct (rev (es s)); lia).
  apply B0min_strip; simpl; [unfold ones; rewrite repeat_length; reflexivity | | exact Ht1 | lia].
  unfold tau0. simpl. rewrite rev_map_pred. destruct (rev (es s)) as [| e1 r] eqn:E; simpl.
  - rewrite Hl', Hlf. lia.
  - assert (In e1 (es s)) by (apply in_rev; rewrite E; left; reflexivity).
    rewrite Forall_forall in Fe. specialize (Fe e1 H). lia.
Qed.

Lemma B0min_dec_es : forall s d T e es', INV s -> fr s = S (S d) :: T -> es s = e :: es' ->
  B0min (mk (ones (length (b0 s) - 1)) (map pred es') (ones (pred e) ++ Xl ((jacc s - 4) / 2)) ((S d :: T) :: up s)) = B0min s.
Proof.
  intros s d T e es' I Hfr Hes.
  set (W := ones (pred e) ++ Xl ((jacc s - 4) / 2)).
  destruct (W_props (pred e) ((jacc s - 4) / 2)) as (WL & Wl & _). fold W in Wl.
  pose proof (i_chain s I) as Ch. rewrite Hes in Ch. simpl in Ch. destruct Ch as [Ce Ch].
  destruct (chain_lower _ _ _ Ch) as [Fe Hn].
  pose proof (tau0_le s (i_chain s I)) as Ht2.
  assert (Ht1 : 1 <= tau0 s) by (unfold tau0; destruct (rev (es s)); lia).
  apply B0min_strip; simpl; [unfold ones; rewrite repeat_length; reflexivity | | exact Ht1 | lia].
  unfold tau0. simpl. rewrite rev_map_pred. rewrite Hes. simpl. destruct (rev es') as [| e1 r] eqn:E; simpl.
  - rewrite Wl. rewrite Hfr in *. lia.
  - assert (In e1 es') by (apply in_rev; rewrite E; left; reflexivity).
    rewrite Forall_forall in Fe. specialize (Fe e1 H). lia.
Qed.

Lemma B0min_P : forall s up', INV s -> fr s = [1] -> up s = [2] :: up' ->
  B0min (mk (ones (length (b0 s) - 1)) (map pred (es s)) (Xl ((jacc s - 2) / 2)) ([1] :: up')) = B0min s.
Proof.
  intros s up' I Hf Hu.
  set (W := Xl ((jacc s - 2) / 2)).
  destruct (W_props 0 ((jacc s - 2) / 2)) as (_ & Wl & _).
  change (ones 0 ++ Xl ((jacc s - 2) / 2)) with W in Wl.
  pose proof (i_chain s I) as Ch. rewrite Hf in Ch. change (lead1 [1]) with 1 in Ch.
  destruct (chain_lower _ _ _ Ch) as [Fe Hn].
  pose proof (tau0_le s (i_chain s I)) as Ht2.
  assert (Ht1 : 1 <= tau0 s) by (unfold tau0; destruct (rev (es s)); lia).
  apply B0min_strip; simpl; [unfold ones; rewrite repeat_length; reflexivity | | exact Ht1 | lia].
  unfold tau0. simpl. rewrite rev_map_pred. destruct (rev (es s)) as [| e1 r] eqn:E; simpl.
  - rewrite Wl, Hf. reflexivity.
  - assert (In e1 (es s)) by (apply in_rev; rewrite E; left; reflexivity).
    rewrite Forall_forall in Fe. specialize (Fe e1 H). lia.
Qed.

(** ** merges into b0 *)
Lemma dec0_lead : forall s d T, INV s -> es s = [] -> fr s = S (S d) :: T ->
  lead1 (S d :: T) <= (jacc s - 4) / 2 /\ (~ pure (b0 s) -> 4 * lead1 (S d :: T) <= eng0 (b0 s)).
Proof.
  intros s d T I He Hfr.
  pose proof (half_ge (jacc s)) as Hhg.
  assert (Hj : jacc s = eng0 (b0 s) + 3) by (unfold jacc; rewrite eng_eq, He; simpl; lia).
  destruct d as [| d].
  - pose proof (i_F2 s I ltac:(rewrite Hfr; reflexivity)) as Hbig.
    pose proof (i_D' s I Hbig (fr s) (or_introl eq_refl)) as HD.
    assert (lead1 (1 :: T) <= length (fr s)) by (rewrite Hfr; pose proof (lead1_le (1 :: T)); simpl in *; lia).
    split; [lia | intros _; lia].
  - change (lead1 (S (S d) :: T)) with 0. pose proof (eng0_pos _ (i_b0 s I)). split; [lia | intros _; lia].
Qed.

Lemma B0min_dec0 : forall s d T, INV s -> es s = [] -> fr s = S (S d) :: T ->
  B0min s <= B0min (mk (b0m s) [] (S d :: T) (up s)) /\
  (~ pure (b0 s) -> Gm (B0min s) <= B0min (mk (b0m s) [] (S d :: T) (up s))).
Proof.
  intros s d T I He Hfr. destruct (b0m_shape s I He) as [_ [_ HL]].
  destruct (dec0_lead s d T I He Hfr) as [L1 L2].
  assert (Ht : tau0 s = 1) by (unfold tau0; rewrite He, Hfr; reflexivity).
  assert (Htau : tau0 (mk (b0m s) [] (S d :: T) (up s)) = lead1 (S d :: T) + 1) by reflexivity.
  pose proof (n0_ge6 s I) as N6.
  unfold B0min. rewrite Htau, Ht. simpl b0. rewrite HL. split; [lia |].
  intros Hnp. specialize (L2 Hnp). pose proof (eng_nonpure s I Hnp) as E. pose proof (half_ge (jacc s)) as Hhg.
  assert (Hj : jacc s = eng0 (b0 s) + 3) by (unfold jacc; rewrite eng_eq, He; simpl; lia).
  pose proof (Nat.mul_div_le (LBe (length (b0 s))) 4 ltac:(lia)).
  pose proof (LBe_big (length (b0 s)) ltac:(lia)).
  unfold Gm. replace (length (b0 s) - 1 + 1) with (length (b0 s)) by lia. lia.
Qed.

Lemma B0min_compl : forall s T Es fr2 up2, INV s -> es s = [] -> fr s = 2 :: T ->
  Gm (B0min s) <= B0min (mk (b0m s) (rev Es ++ [length (fr s)]) fr2 up2).
Proof.
  intros s T Es fr2 up2 I He Hfr. destruct (b0m_shape s I He) as [_ [_ HL]].
  pose proof (i_F2 s I ltac:(rewrite Hfr; reflexivity)) as Hbig.
  pose proof (i_D' s I Hbig (fr s) (or_introl eq_refl)) as HD.
  assert (Ht : tau0 s = 1) by (unfold tau0; rewrite He, Hfr; reflexivity).
  assert (Htau : tau0 (mk (b0m s) (rev Es ++ [length (fr s)]) fr2 up2) = length (fr s) + 1).
  { unfold tau0. simpl. rewrite rev_app_distr, rev_involutive. reflexivity. }
  pose proof (eng_nonpure s I (big_not_pure _ Hbig)) as E. pose proof (half_ge (jacc s)) as Hhg.
  assert (Hj : jacc s = eng0 (b0 s) + 3) by (unfold jacc; rewrite eng_eq, He; simpl; lia).
  pose proof (n0_ge6 s I) as N6.
  unfold B0min. rewrite Htau, Ht. simpl b0. rewrite HL.
  pose proof (Nat.mul_div_le (LBe (length (b0 s))) 4 ltac:(lia)).
  pose proof (LBe_big (length (b0 s)) ltac:(lia)).
  unfold Gm. replace (length (b0 s) - 1 + 1) with (length (b0 s)) by lia. lia.
Qed.
