(** * A machine-checked score lower bound for the 12-state machine P12 *)

(** Main result (no axioms), N = number of ones on the final tape:
      Theorem sigma_lower_bound :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 8 f_omega2 (f 3 6) < N.
    f 0 n = n + 1, f (k+1) n = (f k)^n (n), f_omega n = f n n, f_omega1 n = f_omega^n (n), f_omega2 n = f_omega1^n (n)
    (the definitions of BB11_C4_bound.v).  One round takes p - 4 to >= f_omega1 (p - 4); a big round takes a base
    D >= 4y+8 to >= 4 f_omega2(y) + 8; D_0 >= 4 f_3(6) + 8. *)

From BB8 Require Import Individual122.
From BB8 Require Import BB12_P12.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

Opaque W Be Rd Big.

(** ** Fast-growing hierarchy (copied from BB11_C4_bound.v / BB12_M12_bound.v) *)

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

(** ** The class-2 loop: two passes apply f_omega to q - 3 *)

Lemma Be2_dom : forall q u, 4 <= q -> 4 <= u -> u mod 2 = 0 ->
  2 * f_omega (q - 3) + 3 + q <= fst (iter 2 Be (q, u)).
Proof.
  intros q u Hq Hu He. cbn [iter].
  rewrite !Be_eq. cbn [fst snd].
  pose proof (W_omega_bound (q - 4)) as Hw.
  replace (S (S (S (q - 4)))) with (q - 1) in Hw by lia.
  replace (S (q - 4)) with (q - 3) in Hw by lia.
  set (F := f_omega (q - 3)) in *. set (w := W (q - 1) 1) in *. clearbody F w.
  mods; lia.
Qed.

Lemma Be_iter_dom : forall k q u, 4 <= q -> 4 <= u -> u mod 2 = 0 ->
  iter k f_omega (q - 3) + 3 <= fst (iter (2 * k) Be (q, u)).
Proof.
  induction k as [| k IHk]; intros q u Hq Hu He.
  - rewrite Nat.mul_0_r. cbn [iter fst]. lia.
  - replace (2 * S k) with (2 + 2 * k) by lia. rewrite iter_add.
    pose proof (IHk q u Hq Hu He) as H1.
    destruct (iter_Be_ok (2 * k) q u ltac:(lia) Hu He) as [_ [H3 [H4 H5]]].
    destruct (iter (2 * k) Be (q, u)) as [q2 u2]. cbn [fst snd] in *.
    pose proof (Be2_dom q2 u2 ltac:(lia) H3 H4) as H6.
    assert (H7 : iter k f_omega (q - 3) <= q2 - 3) by lia.
    pose proof (f_omega_mono _ _ H7) as H8.
    change (iter (S k) f_omega (q - 3)) with (f_omega (iter k f_omega (q - 3))). lia.
Qed.

Lemma Be_fst_mono : forall n m q u, 1 <= q -> 4 <= u -> u mod 2 = 0 -> n <= m ->
  fst (iter n Be (q, u)) <= fst (iter m Be (q, u)).
Proof.
  intros n m q u Hq Hu He Hnm. replace m with ((m - n) + n) by lia. rewrite iter_add.
  destruct (iter_Be_ok n q u Hq Hu He) as [H1 [H2 [H3 _]]].
  destruct (iter n Be (q, u)) as [q2 u2]. cbn [fst snd] in *.
  destruct (iter_Be_ok (m - n) q2 u2 H1 H2 H3) as [_ [_ [_ H4]]]. lia.
Qed.

(** ** One round: p - 4 goes to at least f_omega1 (p - 4) *)

Lemma f_omega_lin1 : forall a, 1 <= a -> a + 1 <= f_omega a.
Proof. intros a Ha. pose proof (f_omega_dbl a Ha). lia. Qed.

Lemma Rd_dom : forall p u, 5 <= p -> 1 <= u -> u mod 2 = 0 ->
  f_omega1 (p - 4) + 4 <= fst (Rd (p, u)).
Proof.
  intros p u Hp Hu He.
  rewrite Rd_eq.
  assert (Hm : p - 4 + 1 <= ((W p u + 1) / 2) / 2).
  { pose proof (W_mono p 1 u Hu) as H1.
    pose proof (W_omega_bound (p - 3)) as H2. replace (S (S (S (p - 3)))) with p in H2 by lia.
    pose proof (f_omega_id (S (p - 3))) as H3.
    set (w := W p u) in *. set (w1 := W p 1) in *. set (F := f_omega (S (p - 3))) in *. clearbody w w1 F.
    mods; lia. }
  set (m := (W p u + 1) / 2) in *. clearbody m.
  pose proof (W_grow (p - 1) 1) as Hg.
  pose proof (Be_iter_dom (m / 2) (p - 1) (W (p - 1) 1 + 2) ltac:(lia) ltac:(lia) (W_even1 (p - 1))) as H1.
  assert (Hmm : 2 * (m / 2) <= m) by (mods; lia).
  pose proof (Be_fst_mono (2 * (m / 2)) m (p - 1) (W (p - 1) 1 + 2) ltac:(lia) ltac:(lia) (W_even1 (p - 1))
    Hmm) as H2.
  replace (p - 1 - 3) with (p - 4) in H1 by lia.
  pose proof (iter_mono_n f_omega f_omega_id (S (p - 4)) (m / 2) (p - 4) ltac:(lia)) as H3.
  cbn [iter] in H3. rewrite <- f_omega1_eq in H3.
  pose proof (f_omega_lin1 (f_omega1 (p - 4)) ltac:(pose proof (f_omega1_id (p - 4)); lia)) as H4.
  lia.
Qed.

Lemma Rd_iter_dom : forall r p u, 5 <= p -> 4 <= u -> u mod 2 = 0 ->
  iter r f_omega1 (p - 4) + 4 <= fst (iter r Rd (p, u)).
Proof.
  induction r as [| r IHr]; intros p u Hp Hu He.
  - cbn [iter fst]. lia.
  - cbn [iter]. pose proof (IHr p u Hp Hu He) as H1.
    pose proof (iter_ge f_omega1 f_omega1_id r (p - 4)) as H0.
    destruct (iter_Rd_ok r p u ltac:(lia) He Hu) as [_ [H3 H4]].
    destruct (iter r Rd (p, u)) as [p2 u2]. cbn [fst snd] in *.
    pose proof (Rd_dom p2 u2 ltac:(lia) ltac:(lia) H3) as H5.
    pose proof (f_omega1_mono (iter r f_omega1 (p - 4)) (p2 - 4) ltac:(lia)) as H6.
    lia.
Qed.

(** ** Big rounds: base >= 4y+8  ==>  next base >= 4 f_omega2(y) + 8 *)

Lemma F1_8x : forall x, 3 <= x -> 8 * x <= f_omega1 x.
Proof.
  intros x Hx. rewrite f_omega1_eq.
  pose proof (iter_mono_n f_omega f_omega_id 3 x x Hx) as H0. cbn [iter] in H0.
  pose proof (f_omega_dbl x ltac:(lia)) as H1.
  pose proof (f_omega_dbl (f_omega x) ltac:(lia)) as H2.
  pose proof (f_omega_dbl (f_omega (f_omega x)) ltac:(lia)) as H3.
  lia.
Qed.

Lemma f_omega1_lin1 : forall a, 1 <= a -> a + 1 <= f_omega1 a.
Proof.
  intros a Ha. rewrite f_omega1_eq.
  pose proof (iter_mono_n f_omega f_omega_id 1 a a Ha) as Hz. cbn [iter] in Hz.
  pose proof (f_omega_lin1 a Ha). lia.
Qed.

Lemma iter_f1_2y : forall y k, 3 <= y -> 2 * y + 2 <= k -> 8 * f_omega2 y <= iter k f_omega1 3.
Proof.
  intros y k Hy Hk.
  replace k with (S y + (k - S y)) by lia. rewrite iter_add.
  pose proof (iter_lin1 f_omega1 f_omega1_lin1 (k - S y) 3 ltac:(lia)) as H1.
  pose proof (iter_mono_x f_omega1 f_omega1_mono (S y) y (iter (k - S y) f_omega1 3) ltac:(lia)) as H2.
  cbn [iter] in H2. rewrite <- f_omega2_eq in H2.
  pose proof (F1_8x (f_omega2 y) ltac:(pose proof (f_omega2_id y); lia)) as H3.
  cbn [iter]. lia.
Qed.

Lemma Big_dom : forall D y, 3 <= y -> 4 * y + 8 <= D -> 4 * f_omega2 y + 8 <= Big D.
Proof.
  intros D y Hy HD.
  rewrite Big_eq.
  pose proof (Rd_iter_dom ((D - 2) / 2) 7 (W 4 1 + 2) ltac:(lia) ltac:(pose proof (W_grow 4 1); lia) (W_even1 4)) as H1.
  assert (Hr : 2 * y + 2 <= (D - 2) / 2) by (mods; lia).
  pose proof (iter_f1_2y y ((D - 2) / 2) Hy Hr) as H2.
  change (7 - 4) with 3 in H1.
  pose proof (f_omega2_id y) as H3.
  set (P := iter ((D - 2) / 2) Rd (7, W 4 1 + 2)) in *.
  set (F := f_omega2 y) in *. set (I3 := iter ((D - 2) / 2) f_omega1 3) in *. clearbody P F I3.
  destruct P as [a b]. cbn [fst snd] in *. lia.
Qed.

Lemma FIN_dom_gen : forall E y, 3 <= y -> 4 * y + 8 <= E ->
  4 * f_omega2 y + 8 <= fst (iter ((E - 3) / 2) Rd (7, W 4 1 + 2)).
Proof.
  intros E y Hy HE.
  pose proof (Rd_iter_dom ((E - 3) / 2) 7 (W 4 1 + 2) ltac:(lia) ltac:(pose proof (W_grow 4 1); lia) (W_even1 4)) as H1.
  assert (Hr : 2 * y + 2 <= (E - 3) / 2) by (mods; lia).
  pose proof (iter_f1_2y y ((E - 3) / 2) Hy Hr) as H2.
  pose proof (f_omega2_id y) as H3.
  change (7 - 4) with 3 in H1. lia.
Qed.

Lemma chain_dom : forall k D y, 3 <= y -> 4 * y + 8 <= D -> 4 * iter k f_omega2 y + 8 <= iter k Big D.
Proof.
  induction k as [| k IHk]; intros D y Hy HD; cbn [iter]; [lia |].
  apply Big_dom; [| apply IHk; assumption].
  pose proof (iter_ge f_omega2 f_omega2_id k y). lia.
Qed.

(** W 4 1 = W 3 (W 3 2) >= 8 f_3(6) *)
Lemma iter_two : forall (g : nat -> nat) x, iter 2 g x = g (g x).
Proof. reflexivity. Qed.

Lemma iter_S_gen : forall (g : nat -> nat) n x, iter (S n) g x = g (iter n g x).
Proof. reflexivity. Qed.

Lemma W41_ge : 8 * f 3 6 <= W 4 1.
Proof.
  rewrite (W_S 3 1), (iter_two (W 3) 2).
  destruct (W_bound_all 2) as [Hw Hx].
  change (2 ^ (2 + 2) * (2 + 1)) with 48 in Hx.
  assert (H48 : 2 ^ (2 + 1) * 6 <= W 3 2) by (change (2 ^ (2 + 1) * 6) with 48; exact Hx).
  pose proof (Hw 6 (W 3 2) H48) as H. change (2 ^ (2 + 1)) with 8 in H. exact H.
Qed.

Lemma D0_ge_gen : forall w F, 8 * F <= w -> 4 * F + 8 <= 7 + w / 2 + 2.
Proof. intros w F H. mods; lia. Qed.

Lemma f36_ge : 3 <= f 3 6.
Proof. pose proof (f_id 3 6). lia. Qed.

Lemma N_dom : 4 * iter 8 f_omega2 (f 3 6) + 8 <= fst nP.
Proof.
  pose proof (D0_ge_gen (W 4 1) (f 3 6) W41_ge) as H0.
  pose proof (chain_dom 7 nD0 (f 3 6) f36_ge H0) as H7.
  pose proof (iter_ge f_omega2 f_omega2_id 7 (f 3 6)) as Hg.
  pose proof f36_ge as H3.
  pose proof (FIN_dom_gen nD7 (iter 7 f_omega2 (f 3 6)) ltac:(lia) H7) as H8.
  rewrite (iter_S_gen f_omega2 7 (f 3 6)). exact H8.
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 8 f_omega2 (f 3 6) < N.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (snd nP + fst nP + 1).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof N_dom. lia.
Qed.
