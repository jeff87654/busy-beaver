(** * Size of the BB(4,3) champion's score in Knuth arrows *)

(** sigma = 4 * e4 + 18 (BB43_run.v).  We prove
      sigma > 2 ^^^ (2 ^^^ (2 ^^^ (2^96 - 1)))      (^^^ = pentation, Knuth's three up-arrows),
    using only symbolic recursion: no large number is ever evaluated. *)

From TM43 Require Import BB43_rules BB43_run.
From Coq Require Import Lia PeanoNat.
From Coq.micromega Require Import ZifyNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(** Knuth's up-arrows: [knuth 1 a b = a^b], [knuth 2 a b = a^^b] (tetration), [knuth 3 a b] = pentation. *)
Fixpoint knuth (n a b : nat) : nat :=
  match n with
  | 0 => a * b
  | S n' => Nat.iter b (knuth n' a) 1
  end.

Lemma knuth_S : forall n a b, knuth (S n) a (S b) = knuth n a (knuth (S n) a b).
Proof. reflexivity. Qed.

Lemma knuth1 : forall b, knuth 1 2 b = 2 ^ b.
Proof. induction b. - reflexivity. - rewrite knuth_S, IHb. simpl knuth. rewrite Nat.pow_succ_r'. lia. Qed.

(** For n >= 1, [knuth n 2] is strictly increasing and above the identity. *)
Lemma knuth_props : forall n, 1 <= n ->
  (forall b, b < knuth n 2 b) /\ (forall b b', b <= b' -> knuth n 2 b <= knuth n 2 b').
Proof.
  induction n as [|n IH]; intros Hn; [lia|].
  destruct n as [|n].
  - split.
    + intros b. rewrite knuth1. apply Nat.pow_gt_lin_r. lia.
    + intros b b' H. rewrite !knuth1. apply Nat.pow_le_mono_r; lia.
  - destruct (IH ltac:(lia)) as [Hgt Hmono].
    assert (Hstep : forall b, knuth (S (S n)) 2 b < knuth (S (S n)) 2 (S b)).
    { intros b. rewrite knuth_S. apply Hgt. }
    assert (Hm : forall b k, knuth (S (S n)) 2 b <= knuth (S (S n)) 2 (b + k)).
    { intros b k. induction k as [|k IHk].
      - rewrite Nat.add_0_r. lia.
      - rewrite Nat.add_succ_r. specialize (Hstep (b + k)). lia. }
    split.
    + intros b. induction b as [|b IHb].
      * simpl. lia.
      * specialize (Hstep b). lia.
    + intros b b' H. replace b' with (b + (b' - b)) by lia. apply Hm.
Qed.

Lemma knuth_gt : forall n b, 1 <= n -> b < knuth n 2 b.
Proof. intros. apply knuth_props. assumption. Qed.

Lemma knuth_mono : forall n b b', 1 <= n -> b <= b' -> knuth n 2 b <= knuth n 2 b'.
Proof. intros. apply knuth_props; assumption. Qed.

Lemma double_le_pow : forall x, 2 * x <= 2 ^ x.
Proof.
  induction x as [|x IH]. - simpl. lia.
  - rewrite Nat.pow_succ_r'. destruct x as [|x]. + simpl. lia.
    + assert (2 <= 2 ^ S x) by (change 2 with (2 ^ 1) at 1; apply Nat.pow_le_mono_r; lia). lia.
Qed.

(** 2 ^^ y >= 2 y for y >= 1. *)
Lemma tet_double : forall y, 1 <= y -> 2 * y <= knuth 2 2 y.
Proof.
  induction y as [|y IH]; intros H; [lia|].
  destruct y as [|y].
  - reflexivity.
  - rewrite knuth_S, knuth1.
    specialize (IH ltac:(lia)).
    pose proof (double_le_pow (2 * S y)).
    assert (2 ^ (2 * S y) <= 2 ^ knuth 2 2 (S y)) by (apply Nat.pow_le_mono_r; lia).
    lia.
Qed.

(** ** The machine's functions *)

Lemma iter_S : forall (f : nat -> nat) n x, Nat.iter (S n) f x = f (Nat.iter n f x).
Proof. reflexivity. Qed.
Lemma iter_0 : forall (f : nat -> nat) x, Nat.iter 0 f x = x.
Proof. reflexivity. Qed.

Lemma iter_g_closed : forall n, Nat.iter n g 1 + 5 = 6 * 2 ^ n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl Nat.iter. unfold g at 1. rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma f1_closed : forall x, f1 x + 5 = 6 * 2 ^ (S (S (S x))).
Proof. intros. apply iter_g_closed. Qed.

Lemma pow_le_f1 : forall x, 2 ^ x <= f1 x.
Proof.
  intros. pose proof (f1_closed x).
  assert (2 ^ x <= 2 ^ (S (S (S x)))) by (apply Nat.pow_le_mono_r; lia).
  assert (1 <= 2 ^ x) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  lia.
Qed.

Lemma tower_le_iter_f1 : forall n, knuth 2 2 n <= Nat.iter n f1 1.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite knuth_S, knuth1. simpl Nat.iter.
    eapply Nat.le_trans; [apply Nat.pow_le_mono_r; [lia | exact IH] | apply pow_le_f1].
Qed.

Lemma G_ge : forall c, knuth 2 2 (S c) <= G c.
Proof.
  intros. unfold G.
  apply (Nat.le_trans _ (knuth 2 2 (2 * c + 11))); [apply knuth_mono; lia | apply tower_le_iter_f1].
Qed.

Lemma iter_G_ge : forall k x, 2 <= x -> knuth 3 2 (S k) <= Nat.iter k G x.
Proof.
  induction k as [|k IH]; intros x Hx.
  - exact Hx.
  - rewrite knuth_S. simpl Nat.iter.
    eapply Nat.le_trans; [| apply G_ge].
    apply knuth_mono; [lia |]. specialize (IH x Hx). lia.
Qed.

(** One cascade: from e >= 2 * (2^^^K) and the next G-iteration count (2e+7)/3 or (2e+4)/3. *)
Lemma cascade : forall k x, 2 <= x -> 2 * knuth 3 2 k <= Nat.iter k G x.
Proof.
  intros k x Hx.
  eapply Nat.le_trans; [| apply iter_G_ge; exact Hx].
  rewrite knuth_S. apply tet_double.
  pose proof (knuth_gt 3 k ltac:(lia)). lia.
Qed.

Theorem E4_lower : forall x y, 2 <= y ->
  knuth 3 2 (knuth 3 2 (knuth 3 2 ((2 * x + 7) / 3))) < E4 x y.
Proof.
  intros x y Hy.
  set (k1 := (2 * x + 7) / 3).
  set (X := knuth 3 2 k1).
  assert (H2 : 2 * X <= E2 x y) by (apply cascade; exact Hy).
  set (k2 := (2 * E2 x y + 7) / 3).
  assert (Hk2 : X <= k2) by (unfold k2; lia).
  set (Y := knuth 3 2 k2).
  assert (H3 : 2 * Y <= E3 x y) by (apply cascade; exact Hy).
  set (k3 := (2 * E3 x y + 4) / 3).
  assert (Hk3 : Y <= k3) by (unfold k3; lia).
  assert (H4 : 2 * knuth 3 2 k3 <= E4 x y) by (apply cascade; exact Hy).
  assert (HY : knuth 3 2 X <= Y) by (apply knuth_mono; lia).
  assert (HZ : knuth 3 2 (knuth 3 2 X) <= knuth 3 2 k3) by (apply knuth_mono; lia).
  pose proof (knuth_gt 3 k3 ltac:(lia)).
  fold X. lia.
Qed.

(** ** The concrete values *)

Lemma e1_closed : e1 + 5 = 6 * 2 ^ 94.
Proof.
  unfold e1. rewrite iter_S, iter_S, iter_0.
  assert (E : f1 1 = 91) by reflexivity. rewrite E.
  apply f1_closed.
Qed.

Lemma k1_value : (2 * e1 + 7) / 3 = 2 ^ 96 - 1.
Proof.
  pose proof e1_closed as H.
  assert (P : 2 ^ 96 = 4 * 2 ^ 94).
  { change 96 with (2 + 94). rewrite Nat.pow_add_r. reflexivity. }
  rewrite P. revert H. generalize e1. generalize (2 ^ 94). intros p x Hx. lia.
Qed.

Lemma v_ge_2 : 2 <= v.
Proof.
  unfold v. rewrite iter_S.
  pose proof (f1_closed (Nat.iter 2 f1 1)) as H. revert H. generalize (Nat.iter 2 f1 1). intros z H.
  assert (2 ^ 3 <= 2 ^ S (S (S z))) by (apply Nat.pow_le_mono_r; lia). simpl (2 ^ 3) in *.
  lia.
Qed.

(** The score: sigma = 4 * e4 + 18 > 2 ^^^ 2 ^^^ 2 ^^^ (2^96 - 1). *)
Theorem sigma_lower : knuth 3 2 (knuth 3 2 (knuth 3 2 (2 ^ 96 - 1))) < sigma.
Proof.
  pose proof (E4_lower e1 v v_ge_2) as H.
  rewrite k1_value, <- e4_eq in H.
  unfold sigma. revert H. generalize (knuth 3 2 (knuth 3 2 (knuth 3 2 (2 ^ 96 - 1)))).
  intros T H. lia.
Qed.
