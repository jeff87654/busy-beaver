(** B21: growth and residue facts about the engine level maps h. *)
From Coq Require Import Lia PeanoNat List Bool.
From BB8 Require Import BB21_B21_absdef.
Import ListNotations.
Set Default Goal Selector "!".

Lemma iter_ge4 : forall (g : nat -> nat), (forall y, y + 4 <= g y) -> forall n z, z + 4 * n <= iter n g z.
Proof. intros g Hg. induction n; intros z; simpl. - lia. - specialize (Hg (iter n g z)). specialize (IHn z). lia. Qed.

Lemma iter_mono_z : forall (g : nat -> nat), (forall a b, a <= b -> g a <= g b) ->
  forall n a b, a <= b -> iter n g a <= iter n g b.
Proof. intros g Hg. induction n; intros a b Hab; simpl. - exact Hab. - apply Hg, IHn, Hab. Qed.

Lemma iter_mono_n : forall (g : nat -> nat), (forall y, y <= g y) -> forall n n' z, n <= n' -> iter n g z <= iter n' g z.
Proof.
  intros g Hg n n' z H. replace n' with ((n' - n) + n) by lia. rewrite iter_add.
  generalize (iter n g z). intros w. induction (n' - n); simpl. - lia. - specialize (Hg (iter n0 g w)). lia.
Qed.

Lemma iter_mono_g : forall (g g' : nat -> nat), (forall y, g y <= g' y) -> (forall a b, a <= b -> g' a <= g' b) ->
  forall n z, iter n g z <= iter n g' z.
Proof.
  intros g g' H Hm. induction n; intros z; simpl. - lia. - specialize (H (iter n g z)). specialize (Hm _ _ (IHn z)). lia.
Qed.

Lemma h_ge : forall m x, x + 4 <= h m x.
Proof.
  induction m as [| m IH]; intros x; simpl. - lia.
  - pose proof (iter_ge4 (h m) IH (x + 3) 1). lia.
Qed.

Lemma h_mono : forall m a b, a <= b -> h m a <= h m b.
Proof.
  induction m as [| m IH]; intros a b Hab; simpl. - lia.
  - apply iter_mono_n; [intros y; pose proof (h_ge m y); lia | lia].
Qed.

Lemma h_step : forall m x, h m x <= h (S m) x.
Proof.
  intros m x. simpl. replace (x + 3) with (S (x + 2)) by lia. simpl.
  apply h_mono. pose proof (iter_ge4 (h m) (h_ge m) (x + 2) 1). lia.
Qed.

Lemma h_mono_m : forall m m' x, m <= m' -> h m x <= h m' x.
Proof.
  intros m m' x H. induction H. - lia. - pose proof (h_step m0 x). lia.
Qed.

Lemma h_mono2 : forall m m' a b, m <= m' -> a <= b -> h m a <= h m' b.
Proof. intros. pose proof (h_mono m a b H0). pose proof (h_mono_m m m' b H). lia. Qed.

Lemma h1 : forall x, h 1 x = 4 * x + 13.
Proof.
  intros x. simpl. assert (forall n z, iter n (fun y => y + 4) z = z + 4 * n).
  { induction n; intros z; simpl. - lia. - rewrite IHn. lia. }
  rewrite H. lia.
Qed.

Lemma h_ge4x : forall m x, 1 <= m -> 4 * x + 13 <= h m x.
Proof. intros. rewrite <- h1. apply h_mono_m. exact H. Qed.

(** residues *)
Lemma h1_iter : forall n, 3 * iter n (h 1) 1 + 13 = 16 * 4 ^ n.
Proof.
  induction n; cbn [iter]. - simpl. lia.
  - rewrite h1. rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma mod64_17 : forall z a, 3 * z + 13 = 64 * a -> z mod 64 = 17.
Proof.
  intros z a H. pose proof (Nat.div_mod z 64 ltac:(lia)) as Hd. pose proof (Nat.mod_upper_bound z 64 ltac:(lia)) as Hb.
  remember (z mod 64) as r. remember (z / 64) as q. lia.
Qed.

Lemma h_mod4 : forall m x, 1 <= m -> h m x mod 4 = 1.
Proof.
  induction m as [| m IH]; intros x Hm; [lia |].
  destruct m as [| m].
  - rewrite h1. replace (4 * x + 13) with (1 + (x + 3) * 4) by lia. rewrite Nat.Div0.mod_add. reflexivity.
  - simpl h. replace (x + 3) with (S (x + 2)) by lia. simpl iter. apply IH. lia.
Qed.

Lemma h_mod64 : forall m x, 2 <= m -> h m x mod 64 = 17.
Proof.
  induction m as [| m IH]; intros x Hm; [lia |].
  destruct m as [| [| m]]; [lia | |].
  - change (h 2 x) with (iter (x + 3) (h 1) 1). pose proof (h1_iter (x + 3)) as E.
    replace (x + 3) with (S (x + 2)) in E |- * by lia. rewrite Nat.pow_succ_r' in E.
    apply (mod64_17 _ (4 ^ (x + 2))). lia.
  - simpl h. replace (x + 3) with (S (x + 2)) by lia. simpl iter. apply IH. lia.
Qed.

(** ** the engine on the B0 shapes that occur *)
Lemma engf_ones : forall j i Y x, engf i (repeat 1 j ++ Y) x = engf (i + j) Y x.
Proof. induction j; intros; simpl. - rewrite Nat.add_0_r. reflexivity. - rewrite IHj. f_equal. lia. Qed.

Definition eng0 (b : list nat) : nat :=
  match b with
  | x :: d :: ds => engf 0 (d :: ds) x
  | _ => 0
  end.

Lemma eng0_shape : forall m Y, Y <> [] -> eng0 (repeat 1 (S m) ++ Y) = engf m Y 1.
Proof.
  intros m Y HY. destruct m as [| m].
  - simpl. destruct Y as [| y Y]; [congruence |]. reflexivity.
  - simpl. rewrite engf_ones. reflexivity.
Qed.

Lemma eng0_pure : forall m, eng0 (repeat 1 (S (S m))) = 1.
Proof. intros. simpl. rewrite <- (app_nil_r (repeat 1 m)). rewrite engf_ones. reflexivity. Qed.

Lemma eng_X0 : forall m, eng0 (repeat 1 (S m) ++ [5]) = h (S m) 1.
Proof. intros. rewrite eng0_shape by discriminate. reflexivity. Qed.

Definition Xs (k : nat) : list nat := [4] ++ repeat 1 k ++ [2].

Lemma eng_XS : forall m k, eng0 (repeat 1 (S m) ++ Xs k) = h (S m + k) (iter 3 (h m) 1).
Proof.
  intros. rewrite eng0_shape by discriminate. unfold Xs. simpl. rewrite engf_ones. simpl.
  replace (S (m + k)) with (S m + k) by lia. reflexivity.
Qed.

Lemma eng_41 : forall m, eng0 (repeat 1 (S m) ++ [4; 1]) = h (S m) 0.
Proof. intros. rewrite eng0_shape by discriminate. reflexivity. Qed.

Lemma engf_mod4 : forall ds i x, x mod 4 = 1 -> engf i ds x mod 4 = 1.
Proof.
  induction ds as [| d ds IH]; intros i x Hx; simpl; [exact Hx |].
  apply IH. destruct (d - 1) as [| n] eqn:E; [exact Hx |].
  destruct i as [| i].
  - assert (forall n z, iter n (h 0) z = z + 4 * n) as It.
    { induction n0; intros z; simpl. - lia. - rewrite IHn0. lia. }
    rewrite It. replace (x + 4 * S n) with (x + (S n) * 4) by lia. rewrite Nat.Div0.mod_add. exact Hx.
  - cbn [iter]. apply h_mod4. lia.
Qed.

Lemma eng0_mod4 : forall d ds, eng0 (1 :: d :: ds) mod 4 = 1.
Proof. intros. unfold eng0. apply engf_mod4. reflexivity. Qed.

Lemma eng_XS_mod64 : forall m k, 1 <= m + k -> eng0 (repeat 1 (S m) ++ Xs k) mod 64 = 17.
Proof. intros. rewrite eng_XS. apply h_mod64. lia. Qed.

(** ** growth gap *)
Definition LBe (n : nat) : nat := h (n - 2) 0.

Lemma h_S0 : forall m, 1 <= m -> 4 * h m 0 + 13 <= h (S m) 0.
Proof.
  intros m Hm. change (h (S m) 0) with (iter 3 (h m) 1). cbn [iter].
  pose proof (h_ge4x m (h m (h m 1)) Hm). pose proof (h_mono m 1 (h m (h m 1))).
  pose proof (h_ge m 1). pose proof (h_mono m 0 1). pose proof (h_ge m (h m 1)). lia.
Qed.

Lemma hm0_big : forall m, 2 <= m -> 100 * m + 100 <= h m 0.
Proof.
  intros m Hm. induction Hm.
  - change (h 2 0) with (iter 3 (h 1) 1). cbn [iter]. rewrite !h1. lia.
  - pose proof (h_S0 m ltac:(lia)). lia.
Qed.

Lemma LBe_mono : forall a b, a <= b -> LBe a <= LBe b.
Proof. intros. unfold LBe. apply h_mono_m. lia. Qed.

Lemma LBe_big : forall n, 4 <= n -> 50 * n <= LBe n.
Proof. intros. unfold LBe. pose proof (hm0_big (n - 2) ltac:(lia)). lia. Qed.

Lemma GAP : forall beta n U, 5 <= beta -> n <= 2 * beta -> U <= h (n - 1) 1 ->
  2 * U + 8 * n + 40 <= LBe (LBe (beta + 1) / 2).
Proof.
  intros beta n U Hb Hn HU.
  assert (H1 : 2 * beta + 3 <= LBe (beta + 1) / 2).
  { pose proof (LBe_big (beta + 1) ltac:(lia)). apply Nat.div_le_lower_bound; lia. }
  pose proof (LBe_mono _ _ H1) as H2.
  assert (E : LBe (2 * beta + 3) = iter 3 (h (2 * beta)) 1) by (unfold LBe; replace (2 * beta + 3 - 2) with (S (2 * beta)) by lia; reflexivity).
  rewrite E in H2. cbn [iter] in H2.
  set (M := 2 * beta) in *.
  assert (H3 : h (n - 1) 1 <= h M 1) by (apply h_mono_m; lia).
  pose proof (h_ge4x M (h M (h M 1)) ltac:(lia)) as A1.
  pose proof (h_ge4x M (h M 1) ltac:(lia)) as A2.
  pose proof (h_mono M (4 * h M 1 + 13) (h M (h M 1)) A2) as A3.
  pose proof (h_ge4x M (4 * h M 1 + 13) ltac:(lia)) as A4.
  pose proof (hm0_big M ltac:(lia)) as A5. pose proof (h_mono M 0 1 ltac:(lia)) as A6.
  lia.
Qed.
