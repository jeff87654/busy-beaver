(** C04 score arithmetic: every clear value at depth K >= R2 Bx beats fw2's bound f_omega (f_omega 465009).

    Machine: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF.
    Pure arithmetic on top of dev/Abs.v (U, arrow, Bx) and dev/Chain.v (R2).  No machine reasoning here.

    Main results (no axioms):
      S1        : forall K, R2 Bx <= K -> f_omega (f_omega (465 * 1000 + 9)) < U K 0.
      S1_11     : forall K, 11 * R2 Bx <= K -> f_omega (f_omega (465 * 1000 + 9)) < U K 0.
      S1_core   : forall a K, f_omega a + 2 <= K -> f_omega (f_omega a) < U K 0.
      S1_iter   : the same for any clear iter v (U K) B with v >= 1 (CDP's output).
      S1_lin    : forall K x c, R2 Bx <= K -> U K 0 <= x -> f_omega (f_omega (465 * 1000 + 9)) < 6 * x + c.
      beats_fw2 : forall K x N, 11 * R2 Bx <= K -> U K 0 <= x -> 6 * x <= N -> f_omega (f_omega (465 * 1000 + 9)) < N.
    Helpers: f_le_U (f k x <= U k x), fomega_arrow (2 f_omega m + 4 <= 2 ^(m+1 arrows) (2m+4)),
      U0_arrow (2 U K 0 + 4 = 2 ^(K+1 arrows) 4), monotonicity of U in the argument (strict) and in the level.

    [f] and [f_omega] are copied verbatim from BB9/verify_fw2/multifile/BB9_fw2_bound.v (its [iter] is the same
    Fixpoint as Abs.iter); Fw2Link.v checks that they are convertible to fw2's own constants. *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From Dev Require Import Abs Chain.
Opaque U arrow.

Local Open Scope nat_scope.

(** ** Iteration *)

Lemma sc_iter_add : forall a b g x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl; [reflexivity | rewrite IHa; reflexivity]. Qed.

Lemma sc_iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros x y Hxy; simpl; [exact Hxy |]. apply Hg, IHn, Hxy. Qed.

Lemma sc_iter_dom : forall g h, (forall a, g a <= h a) -> (forall a b, a <= b -> h a <= h b) ->
  forall n x, iter n g x <= iter n h x.
Proof.
  intros g h Hgh Hh. induction n; intros x; simpl; [lia |].
  specialize (IHn x). specialize (Hgh (iter n g x)). specialize (Hh _ _ IHn). lia.
Qed.

Lemma sc_iter_count : forall g, (forall a, a + 1 <= g a) -> forall n x, x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x; simpl; [lia |].
  specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

(** ** U: growth and monotonicity *)

Lemma sc_U_lin : forall j x, 2 * x + 2 <= U j x.
Proof.
  assert (Hdbl : forall a b, a + b <= dbl a b).
  { induction a; intros b.
    - change (dbl O b) with b. lia.
    - change (dbl (S a) b) with (dbl a (2 * b + 2)). specialize (IHa (2 * b + 2)). lia. }
  assert (Hit : forall i n, (forall z, z + 1 <= U i z) -> n <= iter n (U i) O).
  { intros i n Hi. pose proof (sc_iter_count (U i) Hi n O). lia. }
  intros [| i] x.
  - rewrite U_0. specialize (Hdbl (2 * x + 2) O). lia.
  - rewrite U_S. apply Hit. intro z.
    pose proof (U_closed i z) as E. pose proof (arrow_gt_arg (S i) (2 * z + 4) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma sc_U_succ : forall j x, U j x < U j (S x).
Proof.
  intros [| j] x.
  - rewrite !U_0. replace (2 * S x + 2) with (S (S (2 * x + 2))) by lia.
    pose proof (dbl_closed (2 * x + 2) 0) as H1.
    pose proof (dbl_closed (S (S (2 * x + 2))) 0) as H2.
    rewrite !Nat.pow_succ_r' in H2.
    pose proof (Nat.pow_nonzero 2 (2 * x + 2) ltac:(lia)). lia.
  - rewrite !U_S. replace (2 * S x + 2) with (S (S (2 * x + 2))) by lia.
    change (iter (S (S (2 * x + 2))) (U j) 0) with (U j (U j (iter (2 * x + 2) (U j) 0))).
    pose proof (sc_U_lin j (iter (2 * x + 2) (U j) 0)).
    pose proof (sc_U_lin j (U j (iter (2 * x + 2) (U j) 0))). lia.
Qed.

Lemma sc_U_strict : forall j a b, a < b -> U j a < U j b.
Proof.
  intros j a b H. induction H as [| m H IH]; [apply sc_U_succ |].
  pose proof (sc_U_succ j m). lia.
Qed.

Lemma sc_U_mono : forall j a b, a <= b -> U j a <= U j b.
Proof.
  intros j a b H. destruct (Nat.eq_dec a b) as [-> | Hne]; [lia |].
  pose proof (sc_U_strict j a b ltac:(lia)). lia.
Qed.

Lemma sc_U_level1 : forall j x, U j x <= U (S j) x.
Proof.
  intros j x. rewrite U_S. replace (2 * x + 2) with (S (2 * x + 1)) by lia.
  change (iter (S (2 * x + 1)) (U j) 0) with (U j (iter (2 * x + 1) (U j) 0)).
  apply sc_U_mono.
  assert (Hg : forall a, a + 1 <= U j a) by (intro a; pose proof (sc_U_lin j a); lia).
  pose proof (sc_iter_count (U j) Hg (2 * x + 1) 0). lia.
Qed.

Lemma sc_U_level : forall d j x, U j x <= U (d + j) x.
Proof.
  induction d; intros j x; [reflexivity |].
  specialize (IHd j x). pose proof (sc_U_level1 (d + j) x). change (S d + j) with (S (d + j)). lia.
Qed.

(** U is monotone in both the level and the argument. *)
Lemma sc_U_mono2 : forall j j' x x', j <= j' -> x <= x' -> U j x <= U j' x'.
Proof.
  intros j j' x x' Hj Hx.
  pose proof (sc_U_level (j' - j) j x) as H1. replace (j' - j + j) with j' in H1 by lia.
  pose proof (sc_U_mono j' x x' Hx). lia.
Qed.

Lemma sc_U0_ge : forall j, j + 2 <= U j O.
Proof.
  induction j.
  - pose proof (sc_U_lin 0 O). lia.
  - rewrite U_S. change (2 * O + 2) with 2%nat. cbn [iter].
    pose proof (sc_U_lin j (U j O)). lia.
Qed.

Lemma U_S0 : forall j, U (S j) 0 = U j (U j 0).
Proof. intro j. rewrite U_S. reflexivity. Qed.

(** Every clear iter v (U K) B with v >= 1 is at least U K 0 (CDP's output, e.g. R1 = iter 2 (U K) 0). *)
Lemma iter_U_ge : forall v K B, 1 <= v -> U K 0 <= iter v (U K) B.
Proof.
  intros [| v] K B Hv; [lia |]. change (iter (S v) (U K) B) with (U K (iter v (U K) B)).
  apply sc_U_mono. lia.
Qed.

(** The clear value in Knuth-arrow form. *)
Lemma U0_arrow : forall K, 2 * U K 0 + 4 = arrow (S K) 2 4.
Proof. intro K. exact (U_closed K 0). Qed.

(** ** The fast-growing hierarchy (verbatim from BB9_fw2_bound.v) *)

(** The fast-growing hierarchy: f 0 n = n + 1, f (k+1) n = (f k)^n (n), f_omega n = f n n. *)
Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | O => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.

Lemma f_S : forall k n, f (S k) n = iter n (f k) n.
Proof. reflexivity. Qed.

(** FGH upper bound: f_k is dominated by the clearing function U_k. *)
Lemma f_le_U : forall k x, f k x <= U k x.
Proof.
  induction k as [| k IH]; intros n.
  - change (f 0 n) with (S n). pose proof (sc_U_lin 0 n). lia.
  - rewrite f_S, U_S.
    assert (Hg : forall a, a + 1 <= U k a) by (intro a; pose proof (sc_U_lin k a); lia).
    assert (H1 : iter n (f k) n <= iter n (U k) n) by (apply sc_iter_dom; [exact IH | exact (sc_U_mono k)]).
    assert (H2 : n <= iter (n + 2) (U k) 0) by (pose proof (sc_iter_count (U k) Hg (n + 2) 0); lia).
    assert (H3 : iter n (U k) n <= iter n (U k) (iter (n + 2) (U k) 0))
      by (apply sc_iter_mono_x; [exact (sc_U_mono k) | exact H2]).
    rewrite <- sc_iter_add in H3. replace (n + (n + 2)) with (2 * n + 2) in H3 by lia. lia.
Qed.

Opaque f.

Lemma fomega_le_U : forall m, f_omega m <= U m m.
Proof. intro m. unfold f_omega. apply f_le_U. Qed.

(** The record's form of the FGH upper bound: f_omega m <= 2 ^(m+1 arrows) (2m+4), here with the exact constants. *)
Lemma fomega_arrow : forall m, 2 * f_omega m + 4 <= arrow (S m) 2 (2 * m + 4).
Proof. intro m. pose proof (fomega_le_U m). pose proof (U_closed m m). lia. Qed.

Opaque f_omega.

(** ** S1: the clear value beats f_omega o f_omega *)

Theorem S1_core : forall a K, f_omega a + 2 <= K -> f_omega (f_omega a) < U K 0.
Proof.
  intros a K HK. set (X := f_omega a) in *. clearbody X.
  pose proof (fomega_le_U X) as H1.
  pose proof (sc_U0_ge X) as H2.
  pose proof (sc_U_mono X X (U X 0) ltac:(lia)) as H3.
  pose proof (U_S0 X) as E1.
  pose proof (sc_U_lin (S X) (U (S X) 0)) as H4.
  pose proof (U_S0 (S X)) as E2.
  pose proof (sc_U_mono2 (S (S X)) K 0 0 ltac:(lia) ltac:(lia)) as H5.
  lia.
Qed.

(** Bx >= 2^16 - 2, so the exhaustion-#1 depth 12 Bx + 24 is above 465009. *)
Lemma U0_big : forall y, 12 <= y -> 256 * 256 <= U 0 y + 2.
Proof.
  intros y Hy. rewrite U_0.
  pose proof (dbl_closed (2 * y + 2) 0) as H.
  pose proof (Nat.pow_le_mono_r 2 16 (2 * y + 2) ltac:(lia) ltac:(lia)) as P.
  replace (2 ^ 16) with (256 * 256) in P by reflexivity.
  lia.
Qed.

Lemma Bx_big : 465 * 1000 + 9 <= 12 * Bx + 24.
Proof.
  assert (H : forall y, 12 <= y -> 465 * 1000 + 9 <= 12 * U 10 y + 24).
  { intros y Hy. pose proof (U0_big y Hy). pose proof (sc_U_mono2 0 10 y y ltac:(lia) ltac:(lia)). lia. }
  assert (H12 : 12 <= U 10 O) by (pose proof (sc_U0_ge 10) as H0; revert H0; generalize (U 10 O); intros; lia).
  pose proof (H (U 10 O) H12) as G. rewrite <- Bx_def in G. exact G.
Qed.

(** fw2's inner value is tiny next to the exhaustion-#2 accumulator. *)
Lemma fw_lt_R2 : forall a, a <= 12 * Bx + 24 -> f_omega a + 2 <= R2 Bx.
Proof.
  intros a Ha. unfold R2. set (J := 12 * Bx + 24) in *. clearbody J.
  change (iter 2 (U J) 0) with (U J (U J 0)).
  pose proof (fomega_le_U a).
  pose proof (sc_U_succ a a). pose proof (sc_U_succ a (S a)).
  pose proof (sc_U0_ge J).
  pose proof (sc_U_mono2 a J (S (S a)) (U J 0) ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma fw_lt_R2' : f_omega (465 * 1000 + 9) + 2 <= R2 Bx.
Proof. exact (fw_lt_R2 _ Bx_big). Qed.

Theorem S1 : forall K, R2 Bx <= K -> f_omega (f_omega (465 * 1000 + 9)) < U K 0.
Proof. intros K HK. apply S1_core. pose proof fw_lt_R2'. lia. Qed.

Theorem S1_11 : forall K, 11 * R2 Bx <= K -> f_omega (f_omega (465 * 1000 + 9)) < U K 0.
Proof. intros K HK. apply S1. lia. Qed.

(** Any clear at depth K (iter v (U K) B, v >= 1), in particular R_E = iter 2 (U K) 0 and every later clear
    at depth >= K, beats it as well. *)
Theorem S1_iter : forall K v B, R2 Bx <= K -> 1 <= v -> f_omega (f_omega (465 * 1000 + 9)) < iter v (U K) B.
Proof.
  intros K v B HK Hv. pose proof (S1 K HK). pose proof (iter_U_ge v K B Hv). lia.
Qed.

(** Clears at a deeper level, or from a larger argument. *)
Theorem S1_mono : forall K j x, R2 Bx <= K -> K <= j -> f_omega (f_omega (465 * 1000 + 9)) < U j x.
Proof.
  intros K j x HK Hj. pose proof (S1 K HK). pose proof (sc_U_mono2 K j 0 x Hj ltac:(lia)). lia.
Qed.

(** The halting tape carries 6 x + c ones with x >= the clear value (6 R_last + 3, or the token 6 R_E + 1). *)
Theorem S1_lin : forall K x c, R2 Bx <= K -> U K 0 <= x -> f_omega (f_omega (465 * 1000 + 9)) < 6 * x + c.
Proof. intros K x c HK Hx. pose proof (S1 K HK). lia. Qed.

(** ** S3: the comparison with fw2's published bound (sigma_lower_bound: f_omega (f_omega 465009) < N + 1) *)

Theorem beats_fw2 : forall K x N, 11 * R2 Bx <= K -> U K 0 <= x -> 6 * x <= N ->
  f_omega (f_omega (465 * 1000 + 9)) < N.
Proof. intros K x N HK Hx HN. pose proof (S1_11 K HK). lia. Qed.

(** Same with the busycoq ones-count convention (N ones on the tape; the score is at least N). *)
Theorem beats_fw2_ones : forall K x N, 11 * R2 Bx <= K -> U K 0 <= x -> 6 * x <= N ->
  f_omega (f_omega (465 * 1000 + 9)) < N + 1.
Proof. intros K x N HK Hx HN. pose proof (beats_fw2 K x N HK Hx HN). lia. Qed.

Print Assumptions S1.
Print Assumptions S1_11.
Print Assumptions S1_iter.
Print Assumptions S1_lin.
Print Assumptions beats_fw2.
Print Assumptions beats_fw2_ones.
