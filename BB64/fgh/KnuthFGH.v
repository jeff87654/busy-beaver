(** * KnuthFGH: Knuth arrows 2 ^k x against the standard fast-growing hierarchy of the published Ord.v.

    [kn n a b] is the Knuth arrow a ^n b with a ^0 b = a * b, a ^(n+1) b = (a ^n)^b(1); it is the same text as the
    [knuth] of the published BB34_score.v, BB43_score.v, BB44_bound.v, BB54_score.v (each machine file proves the
    pointwise equality with its own copy).  The FGH is Ord.v's: [fin_fgh k] = f_k (f_0 = S, f_(k+1)(n) = f_k^n(n)),
    [FGH omega n = fin_fgh n n] (FGH_omega), [FGH (osucc omega) n = (FGH omega)^n(n)] (FGH_osucc).

    Main facts, all over abstract arguments:
      fin_lower  : 1 <= x -> 2 ^k x <= f_(k+1)(x)
      fin_lower2 : 4 <= x -> 2 ^(k+1) (x+2) <= f_(k+2)(x)
      fin_upper  : 1 <= k -> 4 <= x -> f_(k+1)(x) <= 2 ^k (3x)
      fw_le_kn3  : 4 <= m -> f_omega(m) <= 2 ^(m+1) 3
      fw_ge      : 3 <= L -> 2 ^L (L+3) <= f_omega(L+1)
      fw_le_F    : 4 <= n -> f_omega(n) <= 2 ^(n+1) (n+3)
    and growth lemmas for kn (quad: 4 * 2 ^k y <= 2 ^k (y+2), k >= 1). *)

From BB8 Require Import Ord.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".

Fixpoint kn (n a b : nat) : nat :=
  match n with
  | 0 => a * b
  | S n' => Nat.iter b (kn n' a) 1
  end.

Lemma kn_S : forall n a b, kn (S n) a (S b) = kn n a (kn (S n) a b).
Proof. reflexivity. Qed.

Lemma kn_S0 : forall k b, kn (S k) 2 b = Nat.iter b (kn k 2) 1.
Proof. reflexivity. Qed.

Lemma kn_1 : forall k, kn k 2 1 = 2.
Proof. induction k as [|k IH]; [reflexivity | simpl; exact IH]. Qed.

Lemma kn_2 : forall k, kn k 2 2 = 4.
Proof. induction k as [|k IH]; [reflexivity | simpl; rewrite kn_1; exact IH]. Qed.

Lemma iter2_kn : forall k, Nat.iter 2 (kn k 2) 1 = 4.
Proof. intros k. simpl. rewrite kn_1. apply kn_2. Qed.

Lemma iter_add' : forall (f : nat -> nat) a b x, Nat.iter (a + b) f x = Nat.iter a f (Nat.iter b f x).
Proof. intros f a. induction a as [|a IH]; intros b x; [reflexivity | simpl; rewrite IH; reflexivity]. Qed.

Lemma kn_1_pow : forall b, kn 1 2 b = 2 ^ b.
Proof. induction b as [|b IH]; [reflexivity | rewrite kn_S, IH; simpl; lia]. Qed.

Lemma ge_2b : forall k b, kn k 2 b >= 2 * b.
Proof.
  induction k as [|k IHk]; intros b; [simpl; lia|].
  induction b as [|b IHb]; [simpl; lia|].
  destruct b as [|b']; [rewrite kn_1; lia|].
  rewrite kn_S. pose proof (IHk (kn (S k) 2 (S b'))). lia.
Qed.

Lemma kn_pos : forall k b, kn (S k) 2 b >= 1.
Proof. intros k [|b]; [simpl; lia | pose proof (ge_2b (S k) (S b)); lia]. Qed.

Lemma strict_b : forall k b, kn (S k) 2 (S b) > kn (S k) 2 b.
Proof. intros k b. rewrite kn_S. pose proof (ge_2b k (kn (S k) 2 b)). pose proof (kn_pos k b). lia. Qed.

Lemma mono_b : forall k b1 b2, b1 <= b2 -> kn k 2 b1 <= kn k 2 b2.
Proof.
  intros [|k] b1 b2 Hle; [simpl; lia|].
  induction Hle as [|b2 Hle IH]; [lia|]. pose proof (strict_b k b2). lia.
Qed.

Lemma step_k : forall k b, b >= 1 -> kn k 2 b <= kn (S k) 2 b.
Proof.
  intros k b Hb. destruct b as [|[|b']]; [lia | rewrite !kn_1; lia|].
  rewrite (kn_S k 2 (S b')). apply mono_b.
  destruct b' as [|b'']; [rewrite kn_1; lia | pose proof (ge_2b (S k) (S (S b''))); lia].
Qed.

Lemma mono_k : forall k1 k2 b, k1 <= k2 -> b >= 1 -> kn k1 2 b <= kn k2 2 b.
Proof.
  intros k1 k2 b Hk Hb. induction Hk as [|k2 Hk IH]; [lia|].
  pose proof (step_k k2 b Hb). lia.
Qed.

Lemma mono_kb : forall k1 k2 b1 b2, k1 <= k2 -> 1 <= b1 -> b1 <= b2 -> kn k1 2 b1 <= kn k2 2 b2.
Proof. intros. eapply Nat.le_trans; [apply mono_k; eassumption | apply mono_b; assumption]. Qed.

Lemma k4_gt : forall j, kn j 2 4 >= j + 6.
Proof.
  induction j as [|j IH]; [simpl; lia|].
  destruct j as [|j']; [simpl; lia|].
  rewrite (kn_S (S j') 2 3), (kn_S (S j') 2 2), kn_2.
  pose proof (ge_2b (S j') (kn (S j') 2 4)). lia.
Qed.

Lemma k3 : forall n, kn (S n) 2 3 = kn n 2 4.
Proof. intros n. rewrite (kn_S n 2 2), kn_2. reflexivity. Qed.

Lemma k4 : forall n, kn (S n) 2 4 = kn n 2 (kn n 2 4).
Proof. intros n. rewrite (kn_S n 2 3), k3. reflexivity. Qed.

Lemma k4_big : forall j, kn j 2 4 >= 3 * (j + 1).
Proof.
  induction j as [|j IH]; [simpl; lia|].
  rewrite k4. pose proof (ge_2b j (kn j 2 4)). lia.
Qed.

Lemma dbl : forall k y, 1 <= k -> 2 * kn k 2 y <= kn k 2 (S y).
Proof. intros [|k] y Hk; [lia|]. rewrite kn_S. apply ge_2b. Qed.

Lemma quad : forall k y, 1 <= k -> 4 * kn k 2 y <= kn k 2 (y + 2).
Proof.
  intros k y Hk. replace (y + 2) with (S (S y)) by lia.
  pose proof (dbl k y Hk). pose proof (dbl k (S y) Hk). lia.
Qed.

Lemma plus1 : forall k y, 1 <= k -> 1 <= y -> kn k 2 y + 2 <= kn k 2 (S y).
Proof.
  intros [|k] y Hk Hy; [lia|]. pose proof (dbl (S k) y ltac:(lia)).
  pose proof (mono_b (S k) 1 y Hy). rewrite kn_1 in *. lia.
Qed.

(** ** Iterations *)

Lemma it_infl : forall f, (forall x, x <= f x) -> forall n x, x <= Nat.iter n f x.
Proof.
  intros f Hf n. induction n as [|n IH]; intros x; [simpl; lia|].
  rewrite Nat.iter_succ. eapply Nat.le_trans; [apply IH | apply Hf].
Qed.

Lemma it_mono_x : forall f, (forall x y, x <= y -> f x <= f y) ->
  forall n x y, x <= y -> Nat.iter n f x <= Nat.iter n f y.
Proof. intros f Hf n. induction n as [|n IH]; intros x y H; [exact H|]. rewrite !Nat.iter_succ. apply Hf, IH, H. Qed.

(** iterates of g stay above a threshold t, and g <= f there *)
Lemma it_le_ge : forall (f g : nat -> nat) t, (forall a b, a <= b -> f a <= f b) ->
  (forall y, t <= y -> g y <= f y) -> (forall y, t <= y -> t <= g y) ->
  forall n x, t <= x -> Nat.iter n g x <= Nat.iter n f x /\ t <= Nat.iter n g x.
Proof.
  intros f g t Hf Hgf Hgt n. induction n as [|n IH]; intros x Hx; [simpl; lia|].
  destruct (IH x Hx) as [H1 H2]. rewrite !Nat.iter_succ. split; [| apply Hgt; exact H2].
  eapply Nat.le_trans; [apply Hgf; exact H2 | apply Hf; exact H1].
Qed.

Lemma it_le_ge1 : forall (f g : nat -> nat) t, (forall a b, a <= b -> f a <= f b) ->
  (forall y, t <= y -> g y <= f y) -> (forall y, t <= y -> t <= g y) ->
  forall n x, t <= x -> Nat.iter n g x <= Nat.iter n f x.
Proof. intros f g t Hf Hgf Hgt n x Hx. exact (proj1 (it_le_ge f g t Hf Hgf Hgt n x Hx)). Qed.

(** ** The finite levels f_k *)

Lemma fin_ge : forall k x, x <= fin_fgh k x.
Proof. induction k as [|k IH]; intros x; cbn [fin_fgh]; [lia|]. apply it_infl. exact IH. Qed.

Lemma fin_mono : forall k x y, x <= y -> fin_fgh k x <= fin_fgh k y.
Proof.
  intros k x y H. rewrite <- !FGH_fin. apply FGH_mono; [apply nf_ofin | exact H].
Qed.

Lemma iter_fin0 : forall j y, Nat.iter j (fin_fgh 0) y = j + y.
Proof. induction j as [|j IH]; intros y; [reflexivity|]. rewrite Nat.iter_succ, IH. reflexivity. Qed.

Lemma fin1 : forall y, fin_fgh 1 y = 2 * y.
Proof. intros y. change (fin_fgh 1 y) with (Nat.iter y (fin_fgh 0) y). rewrite iter_fin0. lia. Qed.

Lemma fin_lower : forall k x, 1 <= x -> kn k 2 x <= fin_fgh (S k) x.
Proof.
  induction k as [|k IH]; intros x Hx; [rewrite fin1; simpl; lia|].
  change (fin_fgh (S (S k)) x) with (Nat.iter x (fin_fgh (S k)) x).
  rewrite kn_S0.
  eapply Nat.le_trans; [apply it_mono_x; [intros a b H; apply mono_b; exact H | exact Hx]|].
  apply (it_le_ge1 (fin_fgh (S k)) (kn k 2) 1); [intros; apply fin_mono; assumption | | | lia].
  - intros y Hy. apply IH. exact Hy.
  - intros y Hy. pose proof (ge_2b k y). lia.
Qed.

Lemma fin_lower2 : forall k x, 4 <= x -> kn (S k) 2 (x + 2) <= fin_fgh (S (S k)) x.
Proof.
  intros k x Hx.
  change (fin_fgh (S (S k)) x) with (Nat.iter x (fin_fgh (S k)) x).
  rewrite kn_S0, iter_add', iter2_kn.
  eapply Nat.le_trans; [apply it_mono_x; [intros a b H; apply mono_b; exact H | exact Hx]|].
  apply (it_le_ge1 (fin_fgh (S k)) (kn k 2) 1); [intros; apply fin_mono; assumption | | | lia].
  - intros y Hy. apply fin_lower. exact Hy.
  - intros y Hy. pose proof (ge_2b k y). lia.
Qed.

Lemma three_le_pow2 : forall y, 4 <= y -> 3 * y <= 2 ^ y.
Proof.
  intros y Hy. induction Hy as [|y Hy IH]; [simpl; lia|].
  rewrite Nat.pow_succ_r'. pose proof (Nat.pow_gt_lin_r 2 y ltac:(lia)). lia.
Qed.

Lemma kn_ge_3y : forall k y, 1 <= k -> 4 <= y -> 3 * y <= kn k 2 y.
Proof.
  intros k y Hk Hy. pose proof (mono_k 1 k y Hk ltac:(lia)) as H. rewrite kn_1_pow in H.
  pose proof (three_le_pow2 y Hy). lia.
Qed.

Lemma iter_fin1 : forall j x, Nat.iter j (fin_fgh 1) x = 2 ^ j * x.
Proof.
  induction j as [|j IH]; intros x; [simpl; lia|].
  rewrite Nat.iter_succ, IH, fin1, Nat.pow_succ_r', Nat.mul_assoc. reflexivity.
Qed.

Lemma fin2_le : forall x, fin_fgh 2 x <= kn 1 2 (3 * x).
Proof.
  intros x. rewrite kn_1_pow.
  change (fin_fgh 2 x) with (Nat.iter x (fin_fgh 1) x). rewrite iter_fin1.
  pose proof (Nat.pow_gt_lin_r 2 x ltac:(lia)) as H1.
  assert (H2 : 2 ^ x * x <= 2 ^ x * 2 ^ x) by (apply Nat.mul_le_mono_l; lia).
  rewrite <- Nat.pow_add_r in H2.
  assert (H3 : 2 ^ (x + x) <= 2 ^ (3 * x)) by (apply Nat.pow_le_mono_r; lia).
  exact (Nat.le_trans _ _ _ H2 H3).
Qed.

Theorem fin_upper : forall k x, 1 <= k -> 4 <= x -> fin_fgh (S k) x <= kn k 2 (3 * x).
Proof.
  intros k. induction k as [|k IHk]; intros x Hk Hx; [lia|].
  destruct k as [|k'].
  - apply fin2_le.
  - assert (HI : forall j, Nat.iter j (fin_fgh (S (S k'))) x <= Nat.iter (2 * j) (kn (S k') 2) x).
    { induction j as [|j IHj]; [apply Nat.eq_le_incl; reflexivity|].
      replace (2 * S j) with (S (S (2 * j))) by lia. rewrite !Nat.iter_succ.
      assert (Ha : 4 <= Nat.iter j (fin_fgh (S (S k'))) x)
        by (pose proof (it_infl _ (fin_ge (S (S k'))) j x); lia).
      assert (Hinf : forall y, y <= kn (S k') 2 y) by (intro y; pose proof (ge_2b (S k') y); lia).
      assert (Hb : 4 <= Nat.iter (2 * j) (kn (S k') 2) x)
        by (pose proof (it_infl _ Hinf (2 * j) x); lia).
      eapply Nat.le_trans; [apply IHk; [lia | exact Ha]|].
      apply mono_b.
      eapply Nat.le_trans; [apply Nat.mul_le_mono_l; exact IHj|].
      apply kn_ge_3y; [lia | exact Hb]. }
    change (fin_fgh (S (S (S k'))) x) with (Nat.iter x (fin_fgh (S (S k'))) x).
    eapply Nat.le_trans; [apply HI|].
    assert (Hx2 : x <= kn (S (S k')) 2 x) by (pose proof (ge_2b (S (S k')) x); lia).
    eapply Nat.le_trans; [apply it_mono_x; [intros a b H; apply mono_b; exact H | exact Hx2]|].
    rewrite (kn_S0 (S k') x), (kn_S0 (S k') (3 * x)).
    rewrite <- iter_add'. replace (2 * x + x) with (3 * x) by lia. lia.
Qed.

(** ** f_omega against Knuth arrows *)

Lemma fw_le_kn3 : forall m, 4 <= m -> FGH omega m <= kn (S m) 2 3.
Proof.
  intros m Hm. rewrite FGH_omega. destruct m as [|k]; [lia|].
  eapply Nat.le_trans; [apply fin_upper; lia|].
  rewrite k3, k4. apply mono_kb; [lia | lia |].
  pose proof (k4_big k). lia.
Qed.

Lemma fw_ge : forall L, 3 <= L -> kn L 2 (L + 3) <= FGH omega (S L).
Proof.
  intros L HL. rewrite FGH_omega. destruct L as [|k]; [lia|].
  replace (S k + 3) with (S (S k) + 2) by lia. apply fin_lower2. lia.
Qed.

Lemma fw_le_F : forall n, 4 <= n -> FGH omega n <= kn (S n) 2 (n + 3).
Proof.
  intros n Hn. eapply Nat.le_trans; [apply fw_le_kn3; exact Hn|]. apply mono_b. lia.
Qed.

Lemma fw_mono : forall a b, a <= b -> FGH omega a <= FGH omega b.
Proof. intros. apply FGH_mono; [apply nf_omega | assumption]. Qed.

(** ** Windows for the shapes that occur *)

(** 2 ^L 3 + L + 3 (the 44-B shape) lies strictly between f_omega(m) and f_omega(M) for m+1 <= L < M. *)
Theorem window_kn3 : forall L m M, 4 <= m -> m + 1 <= L -> S L <= M ->
  FGH omega m < kn L 2 3 + L + 3 /\ kn L 2 3 + L + 3 < FGH omega M.
Proof.
  intros L m M Hm HmL HLM. split.
  - pose proof (fw_le_kn3 m Hm). pose proof (mono_k (S m) L 3 ltac:(lia) ltac:(lia)). lia.
  - eapply Nat.lt_le_trans; [| apply fw_mono; exact HLM].
    eapply Nat.lt_le_trans; [| apply fw_ge; lia].
    destruct L as [|k]; [lia|].
    pose proof (mono_b (S k) 4 (S k + 3) ltac:(lia)) as H1.
    pose proof (dbl (S k) 3 ltac:(lia)) as H2.
    rewrite k3 in *. pose proof (k4_gt k). lia.
Qed.

(** 2 ^L 6 + L (the 44-C shape): f_omega(L) < . < f_omega(L+1). *)
Theorem window_kn6 : forall L, 4 <= L -> FGH omega L < kn L 2 6 + L /\ kn L 2 6 + L < FGH omega (S L).
Proof.
  intros L HL. split.
  - rewrite FGH_omega. destruct L as [|k]; [lia|].
    eapply Nat.le_lt_trans; [apply fin_upper; lia|].
    rewrite (kn_S k 2 5). assert (H : 3 * S k <= kn (S k) 2 5).
    { pose proof (k4_big (S k)). pose proof (mono_b (S k) 4 5 ltac:(lia)). lia. }
    pose proof (mono_b k (3 * S k) (kn (S k) 2 5) H). lia.
  - eapply Nat.lt_le_trans; [| apply fw_ge; lia].
    pose proof (mono_b L 7 (L + 3) ltac:(lia)) as H1.
    pose proof (dbl L 6 ltac:(lia)) as H2.
    pose proof (k4_gt L). pose proof (mono_b L 4 6 ltac:(lia)). lia.
Qed.

(** 2 ^L (2 ^L 5 + 1) + L - 1 (the 44-A shape): f_omega(L+1) < . < f_omega(L+2). *)
Theorem window_knA : forall L, 4 <= L ->
  FGH omega (S L) < kn L 2 (kn L 2 5 + 1) + L - 1 /\ kn L 2 (kn L 2 5 + 1) + L - 1 < FGH omega (S (S L)).
Proof.
  intros L HL. pose proof (k4_big L) as HB. pose proof (mono_b L 4 5 ltac:(lia)) as H45. split.
  - rewrite FGH_omega. eapply Nat.le_lt_trans; [apply fin_upper; lia|].
    pose proof (mono_b L (3 * S L) (kn L 2 5 + 1) ltac:(lia)). lia.
  - eapply Nat.lt_le_trans; [| apply fw_ge; lia].
    replace (S L + 3) with (S (L + 3)) by lia. rewrite kn_S.
    destruct L as [|k]; [lia|].
    pose proof (mono_k (S k) (S (S k)) (S k + 3) ltac:(lia) ltac:(lia)) as H1.
    pose proof (mono_b (S k) 6 (S k + 3) ltac:(lia)) as H2.
    pose proof (dbl (S k) 5 ltac:(lia)) as H3.
    pose proof (mono_b (S k) (kn (S k) 2 5 + 2) (kn (S (S k)) 2 (S k + 3)) ltac:(lia)) as H4.
    pose proof (dbl (S k) (kn (S k) 2 5 + 1) ltac:(lia)) as H5.
    replace (S (kn (S k) 2 5 + 1)) with (kn (S k) 2 5 + 2) in H5 by lia.
    pose proof (k4_gt (S k)) as H6. pose proof (mono_b (S k) 4 (kn (S k) 2 5 + 1) ltac:(lia)) as H7.
    lia.
Qed.
