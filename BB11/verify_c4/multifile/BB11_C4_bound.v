(** * A machine-checked score lower bound for the 11-state machine C4 *)

(** Machine C4 (start-A table):
      1RB1RH_1RC0LD_1LD1RJ_1LE1LB_1LF1LE_1RG0LE_1RA1RG_0LI1LF_0RC1LI_1RK0RG_---0LB
    The table, the configurations, the rules and the halting run are imported unchanged from BB11_C4.v
    (which proves [halt : halts tm c0] and passes check.py, and [score_exact]).

    Main results (no axioms), N = number of ones on the final tape (the halting cell holds 0, so sigma = N + 1
    if the halting transition is completed as 1RZ):
      Theorem sigma_lower_bound :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega2 (f 5 34)) < N.
      Theorem sigma_lower_bound_34 :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega2 34) < N.
      Theorem beats_M11b :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega1 (f_omega (f_omega 6)) < N.
        (BB11_M11b_upper.v proves for M11b: N_M11b + 1 < f_omega1 (f_omega (f_omega 6)), same definitions.)
      Theorem beats_M12_lower :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega1 (f_omega1 3)) < N.

    Definitions (as in BB12_M12_bound.v):
      f 0 n = n + 1, f (k+1) n = (f k)^n (n),
      f_omega n  = f n n,
      f_omega1 n = (f_omega)^n (n)   [= f_(omega+1)(n)],
      f_omega2 n = (f_omega1)^n (n)  [= f_(omega+2)(n)].

    Outline: along the Z loop, okZ (j, b) := 3 <= j /\ 4 f_omega(j-3) + 4 <= b is invariant and j - 3 grows by
    f_omega (Zs_dom); from (1,3) the loop reaches (549, W 548 38) after two steps.  One round with p >= 4n+8 gives
    p' >= 4 f_omega1(n) + 8 (Rnd_dom), so R rounds give 4 f_omega1^R(n) + 8.  Stock 1 has a1 = W_5(1091)/4 rounds and
    starts above 4 a1 + 8; stock 2 has more than f_omega2(a1) rounds and starts above 4 f_omega2(a1) + 8.
    All closed towers stay behind lemmas proved for variables. *)

From BB8 Require Import Individual112.
From BB8 Require Import BB11_C4.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

Lemma Zs_unfold : forall j b, Zs (j, b) = (j + b / 2 + 1, W (j + b / 2) (W (j - 1) 1)).
Proof. intros j b. Transparent Zs. reflexivity. Qed.

Lemma Rnd_unfold : forall p u,
  Rnd (p, u) = (fst (iter (p / 2 + 1) Zs (1, 3)) + u / 2, snd (iter (p / 2 + 1) Zs (1, 3)) + 2).
Proof. intros p u. Transparent Rnd. reflexivity. Qed.

Opaque W Zs Rnd.

(** ** Fast-growing hierarchy (copied from BB12_M12_bound.v) *)

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | O => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.
Definition f_omega1 (n : nat) : nat := iter n f_omega n.
Definition f_omega2 (n : nat) : nat := iter n f_omega1 n.

Lemma iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

Lemma iter_ge : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_n : forall g, (forall a, a <= g a) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge. exact Hg.
Qed.

Lemma iter_lin1 : forall g, (forall a, 1 <= a -> a + 1 <= g a) -> forall n x, 1 <= x -> x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x Hx; simpl. - lia.
  - specialize (IHn x Hx). specialize (Hg (iter n g x) ltac:(lia)). lia.
Qed.

Lemma iter_dom : forall K g h, (forall n z, K * n <= z -> K * g n <= h z) ->
  forall m n z, K * n <= z -> K * iter m g n <= iter m h z.
Proof. intros K g h Hd. induction m; intros n z Hz; simpl; auto. Qed.

Lemma f_S : forall k n, f (S k) n = iter n (f k) n.
Proof. reflexivity. Qed.

Lemma f_props : forall k, (forall n, n <= f k n) /\ (forall a b, a <= b -> f k a <= f k b).
Proof.
  induction k as [| k [Hid Hmono]].
  - split; intros; simpl; lia.
  - split.
    + intros n. rewrite f_S. apply iter_ge. exact Hid.
    + intros a b Hab. rewrite !f_S. transitivity (iter a (f k) b).
      * apply iter_mono_x; assumption.
      * apply iter_mono_n; assumption.
Qed.

Lemma f_id : forall k n, n <= f k n.
Proof. intros. apply f_props. Qed.

Lemma f_mono : forall k a b, a <= b -> f k a <= f k b.
Proof. intros. apply f_props. assumption. Qed.

Lemma f_gt : forall k n, 1 <= n -> n < f k n.
Proof.
  induction k; intros n Hn.
  - simpl. lia.
  - rewrite f_S. destruct n as [| n']; [lia |].
    simpl. pose proof (iter_ge (f k) (f_id k) n' (S n')).
    specialize (IHk (iter n' (f k) (S n')) ltac:(lia)). lia.
Qed.

Lemma f_level : forall k n, 1 <= n -> f k n <= f (S k) n.
Proof.
  intros k n Hn. rewrite f_S. destruct n as [| n']; [lia |].
  rewrite iter_S'. apply iter_ge. apply f_id.
Qed.

Lemma f_level_mono : forall d k n, 1 <= n -> f k n <= f (d + k) n.
Proof.
  induction d; intros k n Hn. - reflexivity.
  - specialize (IHd k n Hn). pose proof (f_level (d + k) n Hn). change (S d + k) with (S (d + k)). lia.
Qed.

Lemma iter_succ_add : forall n x, iter n S x = n + x.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Lemma f1 : forall n, f 1 n = 2 * n.
Proof. intros. rewrite f_S. rewrite iter_succ_add. lia. Qed.

Lemma f_dbl : forall k n, 1 <= k -> 2 * n <= f k n.
Proof.
  intros k n Hk. destruct n as [| n']. - lia.
  - rewrite <- f1. replace k with ((k - 1) + 1) by lia. apply f_level_mono. lia.
Qed.

Lemma f_omega_id : forall n, n <= f_omega n.
Proof. intros n. unfold f_omega. apply f_id. Qed.

Lemma f_omega_dbl : forall n, 1 <= n -> 2 * n <= f_omega n.
Proof. intros n Hn. unfold f_omega. apply f_dbl. exact Hn. Qed.

Lemma f_omega_mono : forall a b, a <= b -> f_omega a <= f_omega b.
Proof.
  intros [| a'] b Hab.
  - destruct b as [| b'].
    + reflexivity.
    + change (f_omega 0) with 1. pose proof (f_omega_id (S b')). lia.
  - unfold f_omega.
    pose proof (f_level_mono (b - S a') (S a') (S a') ltac:(lia)) as L1.
    replace (b - S a' + S a') with b in L1 by lia.
    pose proof (f_mono b (S a') b Hab). lia.
Qed.

Lemma f_omega1_id : forall n, n <= f_omega1 n.
Proof. intros n. unfold f_omega1. apply iter_ge, f_omega_id. Qed.

Lemma f_omega1_mono : forall a b, a <= b -> f_omega1 a <= f_omega1 b.
Proof.
  intros a b Hab. unfold f_omega1.
  transitivity (iter a f_omega b).
  - apply iter_mono_x; [apply f_omega_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega_id | exact Hab].
Qed.

Lemma f_omega2_id : forall n, n <= f_omega2 n.
Proof. intros n. unfold f_omega2. apply iter_ge, f_omega1_id. Qed.

Lemma f_omega2_mono : forall a b, a <= b -> f_omega2 a <= f_omega2 b.
Proof.
  intros a b Hab. unfold f_omega2.
  transitivity (iter a f_omega1 b).
  - apply iter_mono_x; [apply f_omega1_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega1_id | exact Hab].
Qed.

Lemma f_omega_0 : f_omega 0 = 1.
Proof. reflexivity. Qed.

Lemma f_omega1_eq : forall n, f_omega1 n = iter n f_omega n.
Proof. reflexivity. Qed.

Lemma f_omega2_eq : forall n, f_omega2 n = iter n f_omega1 n.
Proof. reflexivity. Qed.

Opaque f f_omega f_omega1 f_omega2.

(** ** Lower bounds for W (copied from BB12_M12_bound.v) *)

Lemma W_S_0 : forall j, W (S j) 0 = W j 2.
Proof. intros j. rewrite W_S. reflexivity. Qed.

Lemma W_S' : forall j b, W (S j) b = iter b (W j) (W j 2).
Proof. intros j b. rewrite W_S, iter_S'. reflexivity. Qed.

Lemma W_S_2 : forall j, W (S j) 2 = W j (W j (W j 2)).
Proof. intros j. rewrite W_S. reflexivity. Qed.

Lemma W_mono : forall j a b, a <= b -> W j a <= W j b.
Proof.
  induction j as [| j IHj]; intros a b Hab.
  - rewrite !W_0. lia.
  - rewrite !W_S. apply iter_mono_n; [| lia].
    intros x. pose proof (W_grow j x). lia.
Qed.

Lemma pow2_ge : forall j, j + 2 <= 2 ^ (j + 1).
Proof. induction j. - simpl. lia. - change (S j + 1) with (S (j + 1)). rewrite Nat.pow_succ_r'. lia. Qed.

Lemma W_bound_all : forall j,
  (forall n z, 2 ^ (j + 1) * n <= z -> 2 ^ (j + 1) * f (S j) n <= W (S j) z) /\
  2 ^ (j + 2) * (j + 1) <= W (S j) 2.
Proof.
  induction j as [| j [Hw Hx]].
  - split.
    + intros n z Hz. rewrite W_1, f1. simpl (2 ^ (0 + 1)) in *. lia.
    + rewrite W_1. simpl. lia.
  - pose proof (pow2_ge j) as HKj.
    set (K := 2 ^ (j + 1)) in *.
    assert (HK1 : 2 ^ (S j + 1) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK2 : 2 ^ (j + 2) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK3 : 2 ^ (S j + 2) = 4 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    rewrite HK2 in Hx.
    assert (HX1 : K * 1 <= W (S j) 2) by nia.
    split.
    + intros n y Hy. rewrite HK1 in *. rewrite W_S', f_S.
      destruct n as [| n']. { cbn [iter]. lia. }
      set (n := S n') in *.
      assert (Hm : 2 * n + 1 <= y) by nia.
      pose proof (iter_dom K (f (S j)) (W (S j)) Hw y 1 (W (S j) 2) HX1) as Hd.
      assert (Hc : 2 * iter n (f (S j)) n <= iter y (f (S j)) 1).
      { transitivity (iter (2 * n + 1) (f (S j)) 1).
        2:{ apply iter_mono_n; [apply f_id | exact Hm]. }
        replace (2 * n + 1) with (1 + (n + n)) by lia. rewrite !iter_add.
        change (iter 1 (f (S j)) ?z) with (f (S j) z).
        pose proof (iter_lin1 (f (S j)) ltac:(intros a Ha; pose proof (f_gt (S j) a Ha); lia) n 1 ltac:(lia)).
        pose proof (iter_mono_x (f (S j)) (f_mono (S j)) n n (iter n (f (S j)) 1) ltac:(lia)).
        pose proof (f_dbl (S j) (iter n (f (S j)) (iter n (f (S j)) 1)) ltac:(lia)).
        lia. }
      nia.
    + rewrite HK3, W_S_2.
      pose proof (Hw (2 * (j + 1)) (W (S j) 2) ltac:(nia)) as H1.
      pose proof (f_dbl (S j) (2 * (j + 1)) ltac:(lia)) as H2.
      pose proof (Hw (4 * (j + 1)) (W (S j) (W (S j) 2)) ltac:(nia)) as H3.
      pose proof (f_dbl (S j) (4 * (j + 1)) ltac:(lia)) as H4.
      nia.
Qed.

Lemma W_omega_bound0 : forall m,
  2 * f_omega (S m) + 3 <= W (S (S m)) 2.
Proof.
  intros m.
  rewrite W_S_2.
  destruct (W_bound_all m) as [Hwb Hx].
  assert (H1 : 2 ^ (m + 1) * (2 * (m + 1)) <= W (S m) 2).
  { replace (m + 2) with (m + 1 + 1) in Hx by lia.
    rewrite Nat.pow_add_r in Hx. simpl (2 ^ 1) in Hx. nia. }
  pose proof (Hwb (2 * (m + 1)) (W (S m) 2) H1) as H2.
  pose proof (W_grow (S m) (W (S m) (W (S m) 2))) as H3.
  assert (H4 : f (S m) (S m) <= f (S m) (2 * (m + 1))) by (apply f_mono; lia).
  assert (H5 : 2 <= 2 ^ (m + 1)) by (pose proof (pow2_ge m); lia).
  Transparent f_omega. unfold f_omega. Opaque f_omega.
  set (P := 2 ^ (m + 1)) in *.
  set (F1 := f (S m) (S m)) in *.
  set (F2 := f (S m) (2 * (m + 1))) in *.
  set (Z := W (S m) (W (S m) (W (S m) 2))) in *.
  nia.
Qed.

Lemma W_omega_bound : forall m,
  4 * f_omega (S m) + 4 <= W (S (S (S m))) 1.
Proof.
  intros m.
  rewrite W_S. cbn [iter].
  pose proof (W_omega_bound0 m) as H0.
  set (Z := W (S (S m)) 2) in *. clearbody Z.
  rewrite W_S.
  pose proof (iter_lin3 (W (S m)) (W_grow (S m)) (S Z) 2).
  lia.
Qed.

Lemma W_level : forall j b, W j b <= W (S j) b.
Proof.
  intros j b. rewrite W_S. cbn [iter]. apply W_mono.
  pose proof (iter_lin3 (W j) (W_grow j) b 2). lia.
Qed.

Lemma W_level_mono : forall d j b, W j b <= W (d + j) b.
Proof.
  induction d as [| d IHd]; intros j b; [reflexivity |].
  pose proof (IHd j b). pose proof (W_level (d + j) b). change (S d + j) with (S (d + j)). lia.
Qed.

Lemma W24 : W 2 4 = 1091.
Proof. rewrite W_S. cbn [iter]. rewrite !W_1. reflexivity. Qed.

Lemma W21 : W 2 1 = 38.
Proof. rewrite W_S. cbn [iter]. rewrite !W_1. reflexivity. Qed.

(** W_6(38) is far above W_5(1091). *)
Lemma W5_le_W548 : 2 * W 5 1091 + 16 <= W 548 38.
Proof.
  pose proof (W_level_mono 542 6 38) as H1. change (542 + 6) with 548 in H1.
  assert (H2 : W 6 38 = W 5 (W 5 (W 5 (iter 36 (W 5) 2)))).
  { rewrite W_S. reflexivity. }
  pose proof (iter_lin3 (W 5) (W_grow 5) 36 2) as H3.
  pose proof (W_mono 5 4 (iter 36 (W 5) 2) ltac:(lia)) as H4.
  pose proof (W_level_mono 3 2 4) as H5. change (3 + 2) with 5 in H5. rewrite W24 in H5.
  pose proof (W_mono 5 1091 (W 5 (iter 36 (W 5) 2)) ltac:(lia)) as H6.
  pose proof (W_level_mono 4 1 (W 5 (W 5 (iter 36 (W 5) 2)))) as H7. change (4 + 1) with 5 in H7.
  rewrite W_1 in H7.
  pose proof (W_grow 5 1091) as H8.
  rewrite H2 in H1. lia.
Qed.

Lemma a1_ge : f 5 34 <= W 5 (W 2 4) / 4.
Proof.
  rewrite W24.
  destruct (W_bound_all 4) as [Hw _].
  pose proof (Hw 34 1091 ltac:(simpl; lia)) as H. simpl (2 ^ (4 + 1)) in H.
  generalize (W 5 1091) (f 5 34) H. intros w x Hx. mods; lia.
Qed.

(** ** The Z loop *)

Definition okZ (jb : nat * nat) : Prop := 3 <= fst jb /\ 4 * f_omega (fst jb - 3) + 4 <= snd jb.

Lemma Zs_dom : forall jb, okZ jb ->
  okZ (Zs jb) /\ fst jb + 1 <= fst (Zs jb) /\ f_omega (fst jb - 3) <= fst (Zs jb) - 3.
Proof.
  intros [j b] [Hj Hb]. cbn [fst snd] in *. rewrite Zs_unfold. unfold okZ. cbn [fst snd].
  set (F := f_omega (j - 3)) in *.
  assert (Hb2 : 2 * F + 2 <= b / 2) by (mods; lia).
  set (k := j + b / 2) in *.
  assert (Hk : k = S (S (S (k - 3)))) by lia.
  pose proof (W_omega_bound (k - 3)) as Hw. rewrite <- Hk in Hw.
  pose proof (W_grow (j - 1) 1) as Hg.
  pose proof (W_mono k 1 (W (j - 1) 1) ltac:(lia)) as Hm.
  replace (k + 1 - 3) with (S (k - 3)) by lia.
  split; [split; lia | split; lia].
Qed.

Lemma Zs_iter_dom : forall t jb, okZ jb ->
  okZ (iter t Zs jb) /\ fst jb + t <= fst (iter t Zs jb) /\ iter t f_omega (fst jb - 3) <= fst (iter t Zs jb) - 3.
Proof.
  induction t as [| t IHt]; intros jb Hok; cbn [iter].
  - split; [exact Hok | lia].
  - destruct (IHt jb Hok) as [H1 [H2 H3]].
    destruct (Zs_dom _ H1) as [H4 [H5 H6]].
    pose proof (f_omega_mono _ _ H3).
    split; [exact H4 | split; lia].
Qed.

Lemma Zs13 : Zs (1, 3) = (3, 1091).
Proof.
  rewrite Zs_unfold.
  change (1 + 3 / 2 + 1) with 3. change (1 + 3 / 2) with 2. change (1 - 1) with 0.
  rewrite W_0. change (1 + 3) with 4. rewrite W24. reflexivity.
Qed.

Lemma Zs3 : Zs (3, 1091) = (549, W 548 38).
Proof.
  rewrite Zs_unfold.
  change (3 + 1091 / 2 + 1) with 549. change (3 + 1091 / 2) with 548. change (3 - 1) with 2.
  rewrite W21. reflexivity.
Qed.

Lemma Z12 : iter 2 Zs (1, 3) = (549, W 548 38).
Proof. cbn [iter]. rewrite Zs13, Zs3. reflexivity. Qed.

Lemma ok549 : okZ (549, W 548 38).
Proof.
  rewrite <- Zs3. apply Zs_dom. unfold okZ. cbn [fst snd]. change (3 - 3) with 0. rewrite f_omega_0. lia.
Qed.

Lemma Z_any : forall t, 2 <= t ->
  okZ (iter t Zs (1, 3)) /\ t + 547 <= fst (iter t Zs (1, 3)) /\
  iter (t - 2) f_omega 546 <= fst (iter t Zs (1, 3)) - 3.
Proof.
  intros t Ht.
  assert (E : iter t Zs (1, 3) = iter (t - 2) Zs (549, W 548 38)).
  { rewrite <- Z12, <- iter_add. f_equal. lia. }
  rewrite E.
  destruct (Zs_iter_dom (t - 2) _ ok549) as [H1 [H2 H3]]. cbn [fst] in *. change (549 - 3) with 546 in H3.
  split; [exact H1 | split; lia].
Qed.

Lemma fst_iter3 : W 548 38 / 2 + 550 <= fst (iter 3 Zs (1, 3)).
Proof.
  change (iter 3 Zs (1, 3)) with (Zs (iter 2 Zs (1, 3))).
  rewrite Z12, Zs_unfold. cbn [fst]. lia.
Qed.

(** ** Arithmetic of f_omega iterates *)

Lemma f_omega_lin1 : forall a, 1 <= a -> a + 1 <= f_omega a.
Proof. intros a Ha. pose proof (f_omega_dbl a Ha). lia. Qed.

Lemma iter_fo_4 : forall k x, 2 <= k -> 1 <= x -> 4 * (x + k - 2) <= iter k f_omega x.
Proof.
  intros k x Hk Hx. replace k with (2 + (k - 2)) by lia. rewrite iter_add. cbn [iter].
  pose proof (iter_lin1 f_omega f_omega_lin1 (k - 2) x Hx) as H1.
  set (y := iter (k - 2) f_omega x) in *.
  pose proof (f_omega_dbl y ltac:(lia)) as H2.
  pose proof (f_omega_dbl (f_omega y) ltac:(lia)) as H3.
  lia.
Qed.

Lemma iter_fo_f1 : forall n, 1 <= n -> 4 * f_omega1 n + 5 <= iter (2 * n + 3) f_omega 546.
Proof.
  intros n Hn. replace (2 * n + 3) with (3 + (n + n)) by lia. rewrite !iter_add. cbn [iter].
  pose proof (iter_lin1 f_omega f_omega_lin1 n 546 ltac:(lia)) as H1.
  set (Y := iter n f_omega 546) in *.
  pose proof (iter_mono_x f_omega f_omega_mono n n Y ltac:(lia)) as H2.
  pose proof (iter_ge f_omega f_omega_id n Y) as H3.
  rewrite <- f_omega1_eq in H2.
  set (Z := iter n f_omega Y) in *.
  pose proof (f_omega_dbl Z ltac:(lia)) as H4.
  pose proof (f_omega_dbl (f_omega Z) ltac:(lia)) as H5.
  pose proof (f_omega_dbl (f_omega (f_omega Z)) ltac:(lia)) as H6.
  lia.
Qed.

(** ** Rounds *)

Lemma Rnd_dom : forall n pu, 1 <= n -> 4 * n + 8 <= fst pu -> 4 * f_omega1 n + 8 <= fst (Rnd pu).
Proof.
  intros n [p u] Hn Hp. cbn [fst] in Hp. rewrite Rnd_unfold. cbn [fst].
  assert (Ht : 2 * n + 5 <= p / 2 + 1) by (mods; lia).
  destruct (Z_any (p / 2 + 1) ltac:(lia)) as [_ [_ H3]].
  pose proof (iter_mono_n f_omega f_omega_id (2 * n + 3) (p / 2 + 1 - 2) 546 ltac:(lia)) as H4.
  pose proof (iter_fo_f1 n Hn) as H5.
  lia.
Qed.

Lemma Rnd_iter_dom : forall R n pu, 1 <= n -> 4 * n + 8 <= fst pu ->
  4 * iter R f_omega1 n + 8 <= fst (iter R Rnd pu).
Proof.
  induction R as [| R IHR]; intros n pu Hn Hp; cbn [iter]; [lia |].
  apply Rnd_dom.
  - pose proof (iter_ge f_omega1 f_omega1_id R n). lia.
  - apply IHR; assumption.
Qed.

(** ** Stock 1 and stock 2 *)

(** Never let the kernel compare [fst (x, y)] with [x] for closed towers x, y (it compares the pair with the
    whnf of x first and may start evaluating y): reduce such projections by this lemma instead. *)
Lemma fst_pair : forall a b : nat, fst (a, b) = a.
Proof. reflexivity. Qed.


(** Closed towers: every lemma below that mentions one is proved by [exact] of a lemma about variables, or by
    [lia] on hypotheses; no rewrite with a pattern containing evars ever runs on such a goal (the unifier would
    try to evaluate W_5(1091) to weak head normal form). *)
Lemma Q1_gen : forall a T, 1 <= a -> 4 * a + 8 <= fst T ->
  4 * f_omega2 a + 8 <= fst (iter a Rnd (fst T, snd T + 2)).
Proof.
  intros a T Ha HT. rewrite f_omega2_eq.
  apply Rnd_iter_dom; [exact Ha | rewrite fst_pair; exact HT].
Qed.

Lemma div4_pos : forall w, 7 <= w -> 1 <= w / 4.
Proof. intros w Hw. mods; lia. Qed.

Lemma a1_pos : 1 <= W 5 (W 2 4) / 4.
Proof.
  pose proof (W_grow 2 4) as H1. pose proof (W_grow 5 (W 2 4)) as H2.
  exact (div4_pos (W 5 (W 2 4)) ltac:(lia)).
Qed.

Lemma T3_gen : forall w w' v x, w = w' -> v / 2 + 550 <= x -> 2 * w' + 16 <= v -> 4 * (w / 4) + 8 <= x.
Proof. intros w w' v x E H1 H2. subst w'. mods; lia. Qed.

Lemma W5_eq : W 5 (W 2 4) = W 5 1091.
Proof. rewrite W24. reflexivity. Qed.

Lemma T3_big : 4 * (W 5 (W 2 4) / 4) + 8 <= fst (iter 3 Zs (1, 3)).
Proof. exact (T3_gen (W 5 (W 2 4)) (W 5 1091) (W 548 38) (fst (iter 3 Zs (1, 3))) W5_eq fst_iter3 W5_le_W548). Qed.

Lemma Q1_dom : 4 * f_omega2 (W 5 (W 2 4) / 4) + 8 <= fst nQ1.
Proof. exact (Q1_gen (W 5 (W 2 4) / 4) (iter 3 Zs (1, 3)) a1_pos T3_big). Qed.

Lemma stock2_dom : forall F q1 u1, 1 <= F -> 4 * F + 8 <= q1 ->
  4 * f_omega2 F + 8 <=
  fst (iter (snd (iter (q1 / 2 + 1) Zs (1, 3)) / 4) Rnd
    (fst (iter ((fst (iter (q1 / 2 + 1) Zs (1, 3)) + u1 / 2 + 1) / 2) Zs (1, 3)),
     snd (iter ((fst (iter (q1 / 2 + 1) Zs (1, 3)) + u1 / 2 + 1) / 2) Zs (1, 3)) + 2)).
Proof.
  intros F q1 u1 HF Hq.
  set (k := q1 / 2 + 1).
  assert (Hk : 2 * F + 5 <= k) by (unfold k; mods; lia).
  destruct (Z_any k ltac:(lia)) as [[_ HM] [HM2 _]].
  set (M := iter k Zs (1, 3)) in *.
  pose proof (f_omega_id (fst M - 3)) as Hid.
  assert (Hc : F <= snd M / 4) by (generalize (f_omega (fst M - 3)) HM Hid; intros; mods; lia).
  set (s := (fst M + u1 / 2 + 1) / 2).
  assert (Hs : F + 276 <= s) by (unfold s; mods; lia).
  destruct (Z_any s ltac:(lia)) as [_ [_ HT]].
  pose proof (iter_fo_4 (s - 2) 546 ltac:(lia) ltac:(lia)) as H4.
  set (T := iter s Zs (1, 3)) in *.
  pose proof (Rnd_iter_dom (snd M / 4) F (fst T, snd T + 2) HF ltac:(cbn [fst]; lia)) as HR.
  pose proof (iter_mono_n f_omega1 f_omega1_id F (snd M / 4) F Hc) as Hm.
  rewrite <- f_omega2_eq in Hm.
  lia.
Qed.

Lemma f2a1_pos : 1 <= f_omega2 (W 5 (W 2 4) / 4).
Proof. pose proof (f_omega2_id (W 5 (W 2 4) / 4)) as H1. pose proof a1_pos as H2. lia. Qed.

Lemma FIN_dom : 4 * f_omega2 (f_omega2 (W 5 (W 2 4) / 4)) + 8 <= fst nFIN.
Proof. exact (stock2_dom (f_omega2 (W 5 (W 2 4) / 4)) (fst nQ1) (snd nQ1) f2a1_pos Q1_dom). Qed.

(** ** Headline theorems *)

Lemma N_ge : f_omega2 (f_omega2 (f 5 34)) < snd nFIN + 3 + fst nFIN.
Proof.
  pose proof FIN_dom as H1.
  pose proof (f_omega2_mono _ _ a1_ge) as H2.
  pose proof (f_omega2_mono _ _ H2) as H3.
  lia.
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega2 (f 5 34)) < N.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (snd nFIN + 3 + fst nFIN).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  exact N_ge.
Qed.

Lemma f34 : 34 <= f 5 34.
Proof. apply f_id. Qed.

Theorem sigma_lower_bound_34 :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega2 34) < N.
Proof.
  destruct sigma_lower_bound as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof (f_omega2_mono _ _ (f_omega2_mono _ _ f34)). lia.
Qed.

(** f_omega2 x >= f_omega1 x, f_omega1 x >= f_omega (f_omega x) and f_omega2 x >= f_omega1 (f_omega1 x). *)
Lemma f2_ge_f1 : forall x, 1 <= x -> f_omega1 x <= f_omega2 x.
Proof.
  intros x Hx. rewrite f_omega2_eq.
  pose proof (iter_mono_n f_omega1 f_omega1_id 1 x x Hx) as H. cbn [iter] in H. exact H.
Qed.

Lemma f1_ge_ff : forall x, 2 <= x -> f_omega (f_omega x) <= f_omega1 x.
Proof.
  intros x Hx. rewrite f_omega1_eq.
  pose proof (iter_mono_n f_omega f_omega_id 2 x x Hx) as H. cbn [iter] in H. exact H.
Qed.

Lemma f2_ge_f1f1 : forall x, 2 <= x -> f_omega1 (f_omega1 x) <= f_omega2 x.
Proof.
  intros x Hx. rewrite f_omega2_eq.
  pose proof (iter_mono_n f_omega1 f_omega1_id 2 x x Hx) as H. cbn [iter] in H. exact H.
Qed.

Theorem beats_M11b :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega1 (f_omega (f_omega 6)) < N.
Proof.
  destruct sigma_lower_bound_34 as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof (f1_ge_ff 34 ltac:(lia)) as A1.
  pose proof (f_omega_mono _ _ (f_omega_mono 6 34 ltac:(lia))) as A2.
  pose proof (f2_ge_f1 34 ltac:(lia)) as A3.
  pose proof (f_omega1_mono _ _ (Nat.le_trans _ _ _ A2 (Nat.le_trans _ _ _ A1 A3))) as A4.
  pose proof (f_omega2_id 34) as A5.
  pose proof (f2_ge_f1 (f_omega2 34) ltac:(lia)) as A6.
  lia.
Qed.

Theorem beats_M12_lower :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega1 (f_omega1 3)) < N.
Proof.
  destruct sigma_lower_bound_34 as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof (f2_ge_f1f1 34 ltac:(lia)) as A1.
  pose proof (f_omega1_mono _ _ (f_omega1_mono 3 34 ltac:(lia))) as A2.
  pose proof (f_omega2_mono _ _ (Nat.le_trans _ _ _ A2 A1)) as A3.
  lia.
Qed.
