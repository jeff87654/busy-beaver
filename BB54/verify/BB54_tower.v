(** * The comparison of the two towers that occur in the runtime bounds.

    The runtime bound of the wiki, as it was originally published, is

        f_w^2 (10 ↑^4 10 ↑↑ 65533) ,

    and the refined one is

        f_w^2 (2 ↑^4 2 ↑^3 4)  =  f_w^2 (2 ↑↑ 65536) .

    The two differ in the base of the inner tower.  This file proves, in Coq,
    that the base-10 tower is the *smaller* one:

        10 ↑↑ 65533  <  2 ↑↑ 65536 ,          ([tower10_lt])

    i.e. the inequality

        10 ↑↑ 65533  <  2 ↑^3 4

    whose direction decides the comparison of the two bounds.  (It is the
    inequality that the write-up had reversed.)

    Everything is symbolic: the towers are never evaluated.  The proof
    works with the invariant

        4 · (10 ↑↑ n)  +  4   ≤   2 ↑↑ (n+3) ,            ([tower10_inv])

    which propagates from [n] to [n+1] and gives the result at
    [n = 65533], because 65533 + 3 = 65536.

    The arrow convention is [knuth n a b = a ↑^n b]; in particular
    [knuth 2 a m] is the tower of [a]'s of height [m]. *)

From TM54 Require Import BB54_score BB54_bound.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(** ** The first two levels of the arrows, as powers.

    [knuth 1 a x = a ^ x] and [knuth 2 a (S m) = a ^ (knuth 2 a m)]. *)

Lemma knuth_1_pow : forall a x, knuth 1 a x = a ^ x.
Proof.
  intros a x. unfold knuth at 1.
  induction x as [|x IH].
  - reflexivity.
  - rewrite Nat.iter_succ, IH.
    change (knuth 0 a) with (fun y => a * y).
    rewrite Nat.pow_succ_r'. reflexivity.
Qed.

Lemma knuth_2_pow : forall a m, knuth 2 a (S m) = a ^ (knuth 2 a m).
Proof. intros a m. rewrite knuth_S. apply knuth_1_pow. Qed.

(** ** Elementary facts about the powers of two. *)

Lemma pow2_pos : forall k, 1 <= 2 ^ k.
Proof.
  induction k as [|k IH].
  - simpl. lia.
  - rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma pow2_ge2 : forall k, 1 <= k -> 2 <= 2 ^ k.
Proof.
  induction k as [|k IH]; intros H.
  - lia.
  - rewrite Nat.pow_succ_r'. pose proof (pow2_pos k). lia.
Qed.

Lemma pow2_ge4 : forall k, 2 <= k -> 4 <= 2 ^ k.
Proof.
  intros k Hk. destruct k as [|k]; [lia|].
  destruct k as [|k]; [lia|].
  rewrite Nat.pow_succ_r'. rewrite Nat.pow_succ_r'.
  pose proof (pow2_pos k). lia.
Qed.

Lemma pow2_mul4 : forall k, 4 * 2 ^ k = 2 ^ (k + 2).
Proof.
  intros k. replace 4 with (2 ^ 2) by reflexivity.
  rewrite <- (Nat.pow_add_r 2 2 k). replace (2 + k) with (k + 2) by lia.
  reflexivity.
Qed.

Lemma pow2_add4 : forall u, 1 <= u -> 2 ^ u + 4 <= 2 ^ (u + 2).
Proof.
  intros u Hu. replace (u + 2) with (S (S u)) by lia.
  rewrite Nat.pow_succ_r'. rewrite Nat.pow_succ_r'.
  pose proof (pow2_ge2 u Hu). lia.
Qed.

Lemma pow_two_pow : forall k x, (2 ^ k) ^ x = 2 ^ (k * x).
Proof.
  intros k x. revert k.
  induction x as [|x IH]; intros k.
  - rewrite Nat.pow_0_r, Nat.mul_0_r, Nat.pow_0_r. reflexivity.
  - rewrite Nat.pow_succ_r'. rewrite IH.
    rewrite <- (Nat.pow_add_r 2 k (k * x)).
    replace (k + k * x) with (k * S x) by (rewrite Nat.mul_succ_r; lia).
    reflexivity.
Qed.

(** ** The towers are at least one.

    [knuth 2 a m >= 1] for every [a >= 1]; this is what is needed to apply
    the monotonicity of the powers. *)

Lemma knuth2_pos : forall a m, 1 <= a -> 1 <= knuth 2 a m.
Proof.
  intros a m Ha. induction m as [|m IH].
  - reflexivity.
  - rewrite knuth_2_pow.
    assert (Hp : forall b, 1 <= a ^ b).
    { induction b as [|b Hb]; simpl; lia. }
    apply Hp.
Qed.

Lemma tower2_ge2 : forall m, 2 <= knuth 2 2 (S m).
Proof.
  intros m. rewrite knuth_2_pow.
  apply pow2_ge2. apply knuth2_pos. lia.
Qed.

Lemma tower2_ge4 : forall m, 4 <= knuth 2 2 (S (S m)).
Proof.
  intros m. rewrite knuth_2_pow.
  apply pow2_ge4. apply tower2_ge2.
Qed.

(** ** The invariant.

    For every [n]:

        4 · (10 ↑↑ n)  +  4   ≤   2 ↑↑ (n+3) .

    The statement is given in the successor form, because the induction
    step has to match the successor form of the tower on the right. *)

Lemma tower10_inv : forall n,
  4 * knuth 2 10 n + 4 <= knuth 2 2 (S (S (S n))).
Proof.
  induction n as [|n IH].
  - (* the base case: 4 * 1 + 4 = 8 <= 2 ↑↑ 3 = 16 *)
    simpl. lia.
  - (* the step *)
    rewrite knuth_2_pow.
    rewrite (knuth_2_pow 2 (S (S (S n)))).
    (* the goal is
         4 · 10^(10 ↑↑ n)  +  4   ≤   2 ^(2 ↑↑ (n+3)) *)
    assert (H1 : 10 ^ (knuth 2 10 n) <= 16 ^ (knuth 2 10 n))
      by (apply Nat.pow_le_mono_l; lia).
    assert (H2 : 16 ^ (knuth 2 10 n) = 2 ^ (4 * knuth 2 10 n)).
    { rewrite <- (pow_two_pow 4 (knuth 2 10 n)).
      replace 16 with (2 ^ 4) by reflexivity. reflexivity. }
    assert (H3 : 4 * knuth 2 10 n + 2
                 <= knuth 2 2 (S (S (S n))) - 2) by lia.
    assert (H4 : 2 ^ (4 * knuth 2 10 n + 2)
                 <= 2 ^ (knuth 2 2 (S (S (S n))) - 2))
      by (apply Nat.pow_le_mono_r; lia).
    assert (H5 : 2 ^ (knuth 2 2 (S (S (S n))) - 2) + 4
                 <= 2 ^ (knuth 2 2 (S (S (S n))))).
    { assert (H5' : 2 ^ (knuth 2 2 (S (S (S n))) - 2) + 4
                     <= 2 ^ (knuth 2 2 (S (S (S n))) - 2 + 2))
        by (apply pow2_add4; pose proof (tower2_ge4 n); lia).
      replace (knuth 2 2 (S (S (S n))) - 2 + 2)
        with (knuth 2 2 (S (S (S n)))) in H5' by lia.
      exact H5'. }
    assert (H6 : 4 * 10 ^ (knuth 2 10 n) + 4
                 <= 2 ^ (4 * knuth 2 10 n + 2) + 4).
    { assert (H7 : 4 * 10 ^ (knuth 2 10 n) + 4
                   <= 4 * 16 ^ (knuth 2 10 n) + 4) by lia.
      rewrite H2 in H7.
      rewrite (pow2_mul4 (4 * knuth 2 10 n)) in H7.
      exact H7. }
    assert (H8 : 2 ^ (4 * knuth 2 10 n + 2) + 4
                 <= 2 ^ (knuth 2 2 (S (S (S n))) - 2) + 4) by lia.
    lia.
Qed.

(** ** The comparison of the two inner towers.

    [10 ↑↑ 65533 < 2 ↑↑ 65536 = 2 ↑^3 4]: the base-10 tower of the wiki's
    original bound is *below* the base-2 tower of the refined bound. *)

Theorem tower10_lt : knuth 2 10 65533 < knuth 2 2 65536.
Proof.
  pose proof (tower10_inv 65533) as H.
  replace (S (S (S 65533))) with 65536 in H by reflexivity.
  lia.
Qed.

(** The same, in the form in which the two bounds write it: the inner tower
    of the wiki's original bound is below the third arrow of the refined
    one. *)

Corollary tower10_lt_tower3 : knuth 2 10 65533 < knuth 3 2 4.
Proof.
  rewrite knuth_3_2_4. apply tower10_lt.
Qed.
