(** * FArith.v : two-sided comparison of the clearing function U with the fast-growing hierarchy.

    f and f_omega are Score.f / Score.f_omega (verbatim copies of BB9_fw2_bound.v; Score/Fw2Link.v checks the
    identification).  New here, besides the monotonicity facts:
      f_le_U2   : f (k + 2) n <= U k n                       (sharp upper bound for f: two levels below U)
      arrow_le_f: 1 <= n -> arrow k 2 n <= f (k + 1) n        (lower bound for f, the FGH fact F1)
      U_lt_f    : U j x < f (j + 2) (2 x + 4)
      U4        : 4 * U j x <= U j (x + 1)
    and the bracket lemmas around the exhaustion-#2 accumulator R2 Bx = iter 2 (U (12 Bx + 24)) 0:
      fw26_le_R2 : f_omega (12 Bx + 26) <= R2 Bx
      R2_lt_fw27 : 64 * R2 Bx < f_omega (12 Bx + 27)
      LB_chain   : R2 Bx <= K -> iter 2 (U K) 0 <= Rl -> Rl < N -> f_omega (f_omega (12 Bx + 26)) < N
      UB_chain   : N <= U (S (S P)) m -> P + 2 m + 8 <= 64 R2 Bx -> N < f_omega (f_omega (12 Bx + 27))
    and the coarse placement f_(omega+1)(3) < . < f_(omega+1)(4) (f_(omega+1) n = iter n f_omega n). *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Set Default Goal Selector "!".
From Dev Require Import Abs Chain.
From Score Require Import Score.
Local Open Scope nat_scope.
Opaque U arrow Bx.
Transparent f f_omega.

(** ** Iteration helpers *)
Lemma iter_ge_id : forall g, (forall z, z <= g z) -> forall n x, x <= iter n g x.
Proof. intros g Hg. induction n; intros x; simpl; [lia |]. specialize (IHn x). specialize (Hg (iter n g x)). lia. Qed.

Lemma iter_count_mono : forall g, (forall z, z <= g z) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x H. induction H as [| m H IH]; [lia |].
  change (iter (S m) g x) with (g (iter m g x)). specialize (Hg (iter m g x)). lia.
Qed.

(** ** f : growth and monotonicity *)
Lemma f_0 : forall n, f 0 n = S n.
Proof. reflexivity. Qed.

Lemma f_ge : forall k x, x <= f k x.
Proof.
  induction k as [| k IH]; intros x.
  - rewrite f_0. lia.
  - rewrite f_S. apply iter_ge_id, IH.
Qed.

Lemma f_mono : forall k x y, x <= y -> f k x <= f k y.
Proof.
  induction k as [| k IH]; intros x y H.
  - rewrite (f_0 x), (f_0 y). lia.
  - rewrite !f_S.
    pose proof (sc_iter_mono_x (f k) (IH) x x y H) as H1.
    pose proof (iter_count_mono (f k) (f_ge k) x y y H) as H2. lia.
Qed.

Lemma f_lvl : forall k n, 1 <= n -> f k n <= f (S k) n.
Proof.
  intros k [| n] Hn; [lia |]. rewrite f_S. change (iter (S n) (f k) (S n)) with (f k (iter n (f k) (S n))).
  apply f_mono, iter_ge_id, f_ge.
Qed.

Lemma f_lvl_le : forall d k n, 1 <= n -> f k n <= f (d + k) n.
Proof.
  induction d; intros k n Hn; [reflexivity |].
  change (S d + k) with (S (d + k)). pose proof (IHd k n Hn). pose proof (f_lvl (d + k) n Hn). lia.
Qed.

Lemma f_mono2 : forall k k' n n', k <= k' -> 1 <= n -> n <= n' -> f k n <= f k' n'.
Proof.
  intros k k' n n' Hk Hn Hn'.
  pose proof (f_lvl_le (k' - k) k n Hn) as H1. replace (k' - k + k) with k' in H1 by lia.
  pose proof (f_mono k' n n' Hn'). lia.
Qed.

Lemma fomega_ge : forall n, n <= f_omega n.
Proof. intro n. apply f_ge. Qed.

Lemma fomega_mono : forall a b, 1 <= a -> a <= b -> f_omega a <= f_omega b.
Proof. intros a b Ha Hab. unfold f_omega. apply f_mono2; lia. Qed.

Lemma f_le_fomega : forall k n, 1 <= n -> f k n <= f_omega (k + n).
Proof. intros k n Hn. unfold f_omega. apply f_mono2; lia. Qed.

(** ** F2 (sharp): f (k+2) n <= U k n *)
Lemma f1_eq : forall m, f 1 m = 2 * m.
Proof.
  intro m. rewrite f_S. assert (H : forall i x, iter i (f 0) x = x + i).
  { induction i; intros x; cbn [iter]; [lia |]. rewrite IHi, f_0. lia. }
  rewrite H. lia.
Qed.

Lemma f2_eq : forall n, f 2 n = 2 ^ n * n.
Proof.
  intro n. rewrite f_S. assert (H : forall i x, iter i (f 1) x = 2 ^ i * x).
  { induction i; intros x; cbn [iter]; [simpl; lia |]. rewrite IHi, f1_eq, Nat.pow_succ_r', Nat.mul_assoc. reflexivity. }
  apply H.
Qed.

Lemma fomega_eq : forall n, f_omega n = f n n.
Proof. reflexivity. Qed.

Lemma f_le_U2 : forall k n, f (S (S k)) n <= U k n.
Proof.
  induction k as [| k IH]; intros n.
  - rewrite f2_eq, U_0. pose proof (dbl_closed (2 * n + 2) 0) as Hd.
    pose proof (Nat.pow_gt_lin_r 2 n ltac:(lia)) as Hl.
    assert (E : 2 ^ (2 * n + 2) = 2 ^ n * 2 ^ n * 4)
      by (replace (2 * n + 2) with (n + n + 2) by lia; rewrite !Nat.pow_add_r; reflexivity).
    rewrite E in Hd. generalize dependent (2 ^ n). intros X Hl Hd. nia.
  - rewrite f_S, U_S.
    assert (Hg : forall a, a + 1 <= U k a) by (intro a; pose proof (sc_U_lin k a); lia).
    assert (H1 : iter n (f (S (S k))) n <= iter n (U k) n) by (apply sc_iter_dom; [exact IH | exact (sc_U_mono k)]).
    assert (H2 : n <= iter (n + 2) (U k) 0) by (pose proof (sc_iter_count (U k) Hg (n + 2) 0); lia).
    assert (H3 : iter n (U k) n <= iter n (U k) (iter (n + 2) (U k) 0))
      by (apply sc_iter_mono_x; [exact (sc_U_mono k) | exact H2]).
    rewrite <- sc_iter_add in H3. replace (n + (n + 2)) with (2 * n + 2) in H3 by lia. lia.
Qed.

Lemma fomega_le_U2 : forall k, f_omega (S (S k)) <= U k (S (S k)).
Proof. intro k. unfold f_omega. apply f_le_U2. Qed.

(** ** F1: arrow k 2 n <= f (k+1) n *)
Lemma arrow_pos : forall k z, 1 <= z -> 1 <= arrow k 2 z.
Proof.
  induction k as [| k IH]; intros z Hz.
  - rewrite arrow_0. lia.
  - rewrite arrow_S_iter. clear Hz. induction z; cbn [iter]; [lia |]. apply IH. exact IHz.
Qed.

Lemma arrow_le_f : forall k n, 1 <= n -> arrow k 2 n <= f (S k) n.
Proof.
  induction k as [| k IH]; intros n Hn.
  - rewrite arrow_0, f1_eq. lia.
  - rewrite arrow_S_iter, f_S.
    assert (H : forall m, 1 <= iter m (arrow k 2) 1 /\ iter m (arrow k 2) 1 <= iter m (f (S k)) 1).
    { induction m as [| m [IHa IHb]]; cbn [iter]; [lia |]. split; [apply arrow_pos; exact IHa |].
      pose proof (IH _ IHa). pose proof (f_mono (S k) _ _ IHb). lia. }
    destruct (H n) as [_ Hb]. pose proof (sc_iter_mono_x (f (S k)) (f_mono (S k)) n 1 n Hn). lia.
Qed.

Lemma U_lt_f : forall j x, U j x < f (S (S j)) (2 * x + 4).
Proof. intros j x. pose proof (U_closed j x). pose proof (arrow_le_f (S j) (2 * x + 4) ltac:(lia)). lia. Qed.

(** ** U: multiplicative headroom *)
Lemma U4 : forall j x, 4 * U j x <= U j (S x).
Proof.
  intros [| j] x.
  - rewrite !U_0. replace (2 * S x + 2) with (S (S (2 * x + 2))) by lia.
    pose proof (dbl_closed (2 * x + 2) 0) as H1. pose proof (dbl_closed (S (S (2 * x + 2))) 0) as H2.
    rewrite !Nat.pow_succ_r' in H2. lia.
  - rewrite !U_S. replace (2 * S x + 2) with (S (S (2 * x + 2))) by lia.
    change (iter (S (S (2 * x + 2))) (U j) 0) with (U j (U j (iter (2 * x + 2) (U j) 0))).
    pose proof (sc_U_lin j (iter (2 * x + 2) (U j) 0)). pose proof (sc_U_lin j (U j (iter (2 * x + 2) (U j) 0))).
    lia.
Qed.

Lemma U64 : forall j x, 64 * U j x <= U j (x + 3).
Proof.
  intros j x. pose proof (U4 j x). pose proof (U4 j (S x)). pose proof (U4 j (S (S x))).
  replace (x + 3) with (S (S (S x))) by lia. lia.
Qed.

Opaque f f_omega.

(** ** Brackets around R2 Bx *)
Lemma U_iter3 : forall J, U J (U J 0 + 3) <= U (S J) 1.
Proof.
  intro J. rewrite U_S. change (iter (2 * 1 + 2) (U J) 0) with (U J (U J (U J (U J 0)))).
  apply sc_U_mono. pose proof (sc_U_lin J (U J 0)). pose proof (sc_U_lin J (U J (U J 0))). lia.
Qed.

Lemma fw26_le_R2 : f_omega (12 * Bx + 26) <= R2 Bx.
Proof.
  unfold R2. set (J := 12 * Bx + 24). replace (12 * Bx + 26) with (S (S J)) by (unfold J; lia).
  clearbody J. change (iter 2 (U J) 0) with (U J (U J 0)).
  pose proof (fomega_le_U2 J). pose proof (sc_U0_ge J). pose proof (sc_U_mono J (S (S J)) (U J 0) ltac:(lia)). lia.
Qed.

Lemma R2_lt_fw27 : 64 * R2 Bx < f_omega (12 * Bx + 27).
Proof.
  unfold R2. set (J := 12 * Bx + 24). replace (12 * Bx + 27) with (S (S (S J))) by (unfold J; lia).
  assert (HJ : 3 <= J) by (unfold J; lia). clearbody J. change (iter 2 (U J) 0) with (U J (U J 0)).
  pose proof (U64 J (U J 0)). pose proof (U_iter3 J). pose proof (U_lt_f (S J) 1).
  pose proof (f_mono (S (S (S J))) (2 * 1 + 4) (S (S (S J))) ltac:(lia)).
  rewrite fomega_eq. lia.
Qed.

Lemma R2_pos : 26 <= R2 Bx.
Proof. pose proof (fomega_ge (12 * Bx + 26)). pose proof fw26_le_R2. lia. Qed.

(** ** The two chains used at the halt *)
Theorem LB_chain : forall K Rl N, R2 Bx <= K -> iter 2 (U K) 0 <= Rl -> Rl < N ->
  f_omega (f_omega (12 * Bx + 26)) < N.
Proof.
  intros K Rl N HK HR HN.
  pose proof fw26_le_R2 as H1. pose proof (fomega_ge (12 * Bx + 26)) as H0.
  pose proof (fomega_mono (f_omega (12 * Bx + 26)) K ltac:(lia) ltac:(lia)) as H2.
  destruct K as [| [| K']]; [lia | lia |].
  pose proof (fomega_le_U2 K') as H3.
  pose proof (sc_U_mono2 K' (S (S K')) (S (S K')) (S (S K')) ltac:(lia) ltac:(lia)) as H4.
  pose proof (sc_U0_ge (S (S K'))) as H5.
  pose proof (sc_U_mono (S (S K')) (S (S K')) (U (S (S K')) 0) ltac:(lia)) as H6.
  change (iter 2 (U (S (S K'))) 0) with (U (S (S K')) (U (S (S K')) 0)) in HR.
  lia.
Qed.

Theorem UB_chain : forall P m N, N <= U (S (S P)) m -> P + 2 * m + 8 <= 64 * R2 Bx ->
  N < f_omega (f_omega (12 * Bx + 27)).
Proof.
  intros P m N HN HP.
  pose proof (U_lt_f (S (S P)) m) as H1.
  pose proof (f_le_fomega (S (S (S (S P)))) (2 * m + 4) ltac:(lia)) as H2.
  pose proof R2_lt_fw27 as H3.
  pose proof (fomega_mono (S (S (S (S P)))  + (2 * m + 4)) (f_omega (12 * Bx + 27)) ltac:(lia) ltac:(lia)) as H4.
  lia.
Qed.

(** ** Coarse placement: f_(omega+1) n = iter n f_omega n *)
Definition f_w1 (n : nat) : nat := iter n f_omega n.

Lemma fomega3_le_Bx : f_omega 3 <= 12 * Bx + 26.
Proof.
  pose proof (fomega_le_U2 1) as H1. pose proof (sc_U0_ge 10) as H2.
  pose proof (sc_U_mono2 1 10 3 (U 10 0) ltac:(lia) ltac:(lia)) as H3.
  pose proof Bx_def as E. lia.
Qed.

Lemma Bx_le_fomega2_4 : 12 * Bx + 27 <= f_omega (f_omega 4).
Proof.
  assert (H64 : 15 <= f 2 4) by (rewrite f2_eq; simpl; lia).
  assert (H4 : 15 <= f_omega 4).
  { rewrite fomega_eq. pose proof (f_lvl_le 2 2 4 ltac:(lia)) as H. change (2 + 2) with 4 in H. lia. }
  pose proof (fomega_mono 15 (f_omega 4) ltac:(lia) H4) as H15.
  (* 12 Bx + 27 <= 64 Bx <= U 10 (U 10 0 + 3) <= U 11 1 <= U 12 5 < f 14 14 = f_omega 14 <= f_omega 15 *)
  pose proof Bx_def as E. pose proof (sc_U_lin 10 (U 10 0)).
  pose proof (U64 10 (U 10 0)) as A1. pose proof (U_iter3 10) as A2.
  pose proof (sc_U_mono2 11 12 1 5 ltac:(lia) ltac:(lia)) as A3.
  pose proof (U_lt_f 12 5) as A4. change (2 * 5 + 4) with 14 in A4.
  pose proof (fomega_mono 14 15 ltac:(lia) ltac:(lia)) as A7.
  pose proof (fomega_eq 14) as A8.
  lia.
Qed.

Theorem coarse_lower : forall N, f_omega (f_omega (12 * Bx + 26)) < N -> f_w1 3 < N.
Proof.
  intros N HN. unfold f_w1. cbn [iter].
  pose proof fomega3_le_Bx as H1. pose proof (fomega_ge 3).
  pose proof (fomega_mono (f_omega 3) (12 * Bx + 26) ltac:(lia) H1) as H2.
  pose proof (fomega_ge (f_omega 3)).
  pose proof (fomega_mono (f_omega (f_omega 3)) (f_omega (12 * Bx + 26)) ltac:(lia) H2) as H3.
  lia.
Qed.

Theorem coarse_upper : forall N, N < f_omega (f_omega (12 * Bx + 27)) -> N < f_w1 4.
Proof.
  intros N HN. unfold f_w1. cbn [iter].
  pose proof Bx_le_fomega2_4 as H1.
  pose proof (fomega_mono (12 * Bx + 27) (f_omega (f_omega 4)) ltac:(lia) H1) as H2.
  pose proof (fomega_mono (f_omega (12 * Bx + 27)) (f_omega (f_omega (f_omega 4))) ltac:(pose proof (fomega_ge (12 * Bx + 27)); lia) H2) as H3.
  lia.
Qed.

(** Bx in Knuth arrows: 2 Bx + 4 = 2 ^(13 arrows) 3 (Abs.arrow k = k arrows). *)
Lemma Bx_knuth : 2 * Bx + 4 = arrow 13 2 3.
Proof.
  (* explicit instances only: an unapplied arrow_two would try to unify 2 with a closed arrow term and evaluate it *)
  rewrite Bx_closed, (arrow_SS 12 2 2), (arrow_two 13), (arrow_SS 11 2 3), (arrow_SS 11 2 2), (arrow_two 12).
  reflexivity.
Qed.

Lemma R2_knuth : 2 * R2 Bx + 4 = arrow (12 * Bx + 26) 2 4.
Proof.
  unfold R2. set (J := 12 * Bx + 24). replace (12 * Bx + 26) with (S (S J)) by (unfold J; lia). clearbody J.
  change (iter 2 (U J) 0) with (U J (U J 0)). rewrite (U_closed J (U J 0)), (U_closed J 0).
  change (2 * 0 + 4) with 4. rewrite (arrow_SS (S J) 2 3), (arrow_SS (S J) 2 2), (arrow_two (S (S J))). reflexivity.
Qed.

Print Assumptions LB_chain.
Print Assumptions UB_chain.
Print Assumptions coarse_lower.
Print Assumptions coarse_upper.
