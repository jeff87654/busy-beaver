(** * Tower.v : a coarse "size scale" for the upper bound.

    T P m := iter m (U (S P)) 0.  Every quantity on the halting tape is shown to be <= T Ptop m for a small fixed m
    (Ptop = 12 R2 Bx + 11 = the parked count after exhaustion #2, an upper bound for every clear depth).  The scale is
    closed under sums, products and applying U (S P) one level up, and T P m <= U (S (S P)) m feeds FArith.UB_chain. *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Set Default Goal Selector "!".
From Dev Require Import Abs Chain.
From K31 Require Import K31_Abs.
From Score Require Import Score.
From Fgh Require Import FArith.
Local Open Scope nat_scope.
Opaque U arrow Bx f f_omega.

Lemma iter_U_mono3 : forall n n' j j' x x', n <= n' -> j <= j' -> x <= x' -> iter n (U j) x <= iter n' (U j') x'.
Proof.
  intros n n' j j' x x' Hn Hj Hx.
  assert (H1 : iter n (U j) x <= iter n (U j') x).
  { apply sc_iter_dom; [intro a; apply sc_U_mono2; lia | exact (sc_U_mono j')]. }
  pose proof (sc_iter_mono_x (U j') (sc_U_mono j') n x x' Hx) as H2.
  assert (Hg : forall z, z <= U j' z) by (intro z; pose proof (sc_U_lin j' z); lia).
  pose proof (iter_count_mono (U j') Hg n n' x' Hn) as H3. lia.
Qed.

(** an iterate with a nonzero start is an iterate from 0 *)
Lemma iter_shift0 : forall n j x, iter n (U j) x <= iter (n + x) (U j) 0.
Proof.
  intros n j x. rewrite sc_iter_add. apply sc_iter_mono_x; [exact (sc_U_mono j) |].
  pose proof (iter_ge_count x j 0). lia.
Qed.

Lemma iter_le_U : forall n j, iter n (U j) 0 <= U (S j) n.
Proof.
  intros n j. rewrite U_S. apply iter_U_mono3; lia.
Qed.

Section Scale.
Variable P : nat.
Definition T (m : nat) : nat := iter m (U (S P)) 0.

Lemma T_S : forall m, T (S m) = U (S P) (T m).
Proof. reflexivity. Qed.

Lemma T_mono : forall m m', m <= m' -> T m <= T m'.
Proof. intros. unfold T. apply iter_U_mono3; lia. Qed.

Lemma T_1 : P + 3 <= T 1.
Proof. rewrite T_S. change (T 0) with 0. pose proof (sc_U0_ge (S P)). lia. Qed.

Lemma T_small : forall c m, c <= P + 3 -> 1 <= m -> c <= T m.
Proof. intros c m Hc Hm. pose proof T_1. pose proof (T_mono 1 m Hm). lia. Qed.

Lemma T_U : forall a m, a <= T m -> U (S P) a <= T (S m).
Proof. intros a m H. rewrite T_S. apply sc_U_mono, H. Qed.

Lemma T_sum : forall a b m, a <= T m -> b <= T m -> a + b <= T (S m).
Proof. intros a b m Ha Hb. rewrite T_S. pose proof (sc_U_lin (S P) (T m)). lia. Qed.

Lemma sq_le_U0 : forall z, z * z <= U 0 z.
Proof.
  intro z. rewrite U_0. pose proof (dbl_closed (2 * z + 2) 0) as Hd.
  pose proof (Nat.pow_gt_lin_r 2 z ltac:(lia)) as Hl.
  assert (E : 2 ^ (2 * z + 2) = 2 ^ z * 2 ^ z * 4)
    by (replace (2 * z + 2) with (z + z + 2) by lia; rewrite !Nat.pow_add_r; reflexivity).
  rewrite E in Hd. generalize dependent (2 ^ z). intros X Hl Hd. nia.
Qed.

Lemma T_mul : forall a b m, a <= T m -> b <= T m -> a * b <= T (S m).
Proof.
  intros a b m Ha Hb. rewrite T_S.
  pose proof (Nat.mul_le_mono a (T m) b (T m) Ha Hb).
  pose proof (sq_le_U0 (T m)). pose proof (sc_U_mono2 0 (S P) (T m) (T m) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma T_iter : forall n j x m, j <= P -> n + x <= T m -> iter n (U j) x <= T (S m).
Proof.
  intros n j x m Hj H. pose proof (iter_shift0 n j x) as H1.
  pose proof (iter_U_mono3 (n + x) (n + x) j P 0 0 ltac:(lia) Hj ltac:(lia)) as H2.
  pose proof (iter_le_U (n + x) P) as H3. pose proof (T_U (n + x) m H) as H4. lia.
Qed.

Lemma T_le_U2 : forall m, T m <= U (S (S P)) m.
Proof. intro m. unfold T. apply iter_le_U. Qed.

Lemma T_up : forall a m m', a <= T m -> m <= m' -> a <= T m'.
Proof. intros a m m' H Hm. pose proof (T_mono m m' Hm). lia. Qed.

End Scale.

Print Assumptions T_iter.
Print Assumptions T_mul.
