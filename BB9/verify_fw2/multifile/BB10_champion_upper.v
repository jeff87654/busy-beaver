(** * A machine-checked UPPER bound on the score of the BB(10) champion *)

(** Machine (Racheline 2024, wiki "Champions"):
      1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ
    BB10_champion_1RB1RA.v proves [halt : halts tm c0] (check.py PASS); BB10_champion_bound.v proves the exact score
    [score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (b2 + 3)] (standard score b2 + 4) and the lower bound
    f_omega (f_omega 25) < score.  This file bounds the score from above, for comparisons with other 10-state machines.

    [arrow] is the constant of BB9_record_1RB0RA.v / BB9_record_bound.v (arrow 0 a b = a * b,
    arrow (S k) a b = (arrow k a)^b 1, so arrow 1 2 x = 2^x); the 9-state files are only Required (not Imported).

    Main results (no axioms):
      Lemma U_arrow_tight : forall j, 1 <= j ->
        (forall x, U j x <= arrow j 2 (2 * x + 4)) /\ X j <= arrow (S j) 2 4.
      Lemma Tv_le_tight : forall m, Tv m 1 7 <= arrow (3 * m + 4) 2 (6 * m + 7).
      Lemma b1_le_tight : b1 <= arrow 25 2 49.
      Theorem champion_upper : b2 + 4 <= arrow (3 * (b1 / 4) + 4) 2 (2 * (3 * (b1 / 4) + 4)) /\
                               3 * (b1 / 4) + 4 <= arrow 25 2 49.
      Theorem champion_upper_ex : exists Np, 4 <= Np /\ Np <= arrow 25 2 49 /\
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ N + 1 <= arrow Np 2 (2 * Np).

    The argument (paper version: investigations/halt_redirect/score_comparison.md section 6):
      U_j x <= 2 ^(j arrows) (2x+4) and X_j <= 2 ^(j+1 arrows) 4 for j >= 1, by induction on j (iterating U_j costs
      two applications of A = arrow j 2 per step, and A ^(2n) (arrow (S j) 2 4) = arrow (S j) 2 (2n+4)).
      Tv m 1 7 is 3m+2 applications of U_d with 3 <= d <= 3m+3 on arguments >= 7, hence at most
      (arrow K 2)^(6m+4) 7 <= arrow (S K) 2 (6m+7) with K = 3m+3. *)

From BB8 Require Import Individual102.
From BB8 Require Import BB10_champion_1RB1RA BB10_champion_bound.
From BB8 Require BB9_record_1RB0RA BB9_record_bound BB9_record_vs_champion.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

Notation arrow := BB9_record_1RB0RA.arrow.

(** Never let a tactic compute these numbers. *)
Opaque U X Tv b1 b2 BB9_record_1RB0RA.arrow.

(** ** Up-arrow facts (from the BB(9) record files) *)

Lemma iter_bridge : forall n g x, iter n g x = BB9_record_1RB0RA.iter n g x.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Lemma A_iter10 : forall k m n, iter m (arrow k 2) (arrow (S k) 2 n) = arrow (S k) 2 (m + n).
Proof. intros. rewrite iter_bridge. apply BB9_record_vs_champion.A_iter. Qed.

Lemma A_mono : forall k x y, x <= y -> arrow k 2 x <= arrow k 2 y.
Proof. exact BB9_record_bound.arrow_mono. Qed.

Lemma A_idk : forall k x, x <= arrow k 2 x.
Proof. exact BB9_record_vs_champion.A_id. Qed.

Lemma A_lvl : forall d k x, arrow k 2 x <= arrow (d + k) 2 x.
Proof. exact BB9_record_bound.arrow_level_mono. Qed.

Lemma A_SS : forall k a b, arrow (S k) a (S b) = arrow k a (arrow (S k) a b).
Proof. exact BB9_record_1RB0RA.arrow_SS. Qed.

Lemma A_two : forall k, arrow k 2 2 = 4.
Proof. exact BB9_record_1RB0RA.arrow_two. Qed.

Lemma A_pow : forall a b, arrow 1 a b = a ^ b.
Proof. exact BB9_record_1RB0RA.arrow_1_pow. Qed.

(** 2y + 4 <= 2 ^(j arrows) y for j >= 1 and y >= 4 *)
Lemma lin_j : forall j y, 1 <= j -> 4 <= y -> 2 * y + 4 <= arrow j 2 y.
Proof.
  intros j y Hj Hy. destruct (Nat.eq_dec j 1) as [-> | Hne].
  - rewrite A_pow. apply BB9_record_vs_champion.pow2_lin. exact Hy.
  - apply BB9_record_vs_champion.A_lin; lia.
Qed.

(** arrow (S K) 2 3 = arrow K 2 4 >= 12 for K >= 2 *)
Lemma A_S3 : forall K, 2 <= K -> 7 <= arrow (S K) 2 3.
Proof.
  intros K HK. rewrite (A_SS K 2 2), (A_two (S K)).
  pose proof (BB9_record_vs_champion.A_lin K 4 HK ltac:(lia)). lia.
Qed.

(** ** The tight bound on the clearing functions *)

Lemma Ucge : forall j y, y <= U j y.
Proof. intros. pose proof (Ugrow j y). lia. Qed.

(** iterating U_j from X >= 4 costs two applications of an A with U_j y <= A (A y) *)
Lemma iter_dom2 : forall j K, (forall y, 4 <= y -> U j y <= arrow K 2 (arrow K 2 y)) ->
  forall n x, 4 <= x -> iter n (U j) x <= iter (2 * n) (arrow K 2) x.
Proof.
  intros j K HU. induction n as [| n IH]; intros x Hx. - simpl. lia.
  - change (iter (S n) (U j) x) with (U j (iter n (U j) x)).
    replace (2 * S n) with (S (S (2 * n))) by lia.
    change (iter (S (S (2 * n))) (arrow K 2) x) with (arrow K 2 (arrow K 2 (iter (2 * n) (arrow K 2) x))).
    pose proof (iter_ge (U j) (Ucge j) n x) as G.
    specialize (IH x Hx).
    transitivity (arrow K 2 (arrow K 2 (iter n (U j) x))); [apply HU; lia |].
    apply A_mono, A_mono. exact IH.
Qed.

Lemma U1_le : forall x, U 1 x <= arrow 1 2 (2 * x + 4).
Proof.
  intros x. rewrite U_S, X_0, A_pow. replace (x - 2 * 0) with x by lia.
  induction x as [| x IH].
  - simpl. lia.
  - change (iter (S x) (U 0) 7) with (U 0 (iter x (U 0) 7)). rewrite U_0.
    replace (2 * S x + 4) with (2 + (2 * x + 4)) by lia. rewrite Nat.pow_add_r.
    assert (P16 : 2 ^ 4 <= 2 ^ (2 * x + 4)) by (apply Nat.pow_le_mono_r; lia).
    change (2 ^ 4) with 16 in P16. change (2 ^ 2) with 4.
    set (P := 2 ^ (2 * x + 4)) in *. set (I := iter x (U 0) 7) in *. lia.
Qed.

Lemma X1_le : X 1 <= arrow 2 2 4.
Proof.
  rewrite X1_val, (A_SS 1 2 3), (A_SS 1 2 2), (A_two 2), !A_pow.
  assert (P : 2 ^ 7 <= 2 ^ (2 ^ 4)) by (apply Nat.pow_le_mono_r; [lia | simpl; lia]).
  change (2 ^ 7) with 128 in P. lia.
Qed.

Lemma U_arrow_tight : forall j, 1 <= j ->
  (forall x, U j x <= arrow j 2 (2 * x + 4)) /\ X j <= arrow (S j) 2 4.
Proof.
  induction j as [| j IH]; intros Hj; [lia |].
  destruct (Nat.eq_dec j 0) as [-> | Hne].
  { split; [exact U1_le | exact X1_le]. }
  destruct (IH ltac:(lia)) as [HU HX].
  assert (HU2 : forall y, 4 <= y -> U j y <= arrow j 2 (arrow j 2 y)).
  { intros y Hy. pose proof (HU y) as E1. pose proof (lin_j j y ltac:(lia) Hy) as E2.
    pose proof (A_mono j _ _ E2) as E3. lia. }
  assert (HX4 : 4 <= X j) by (pose proof (Xgrow j); lia).
  pose proof (iter_dom2 j j HU2) as HI.
  split.
  - intros x. rewrite U_S.
    pose proof (HI (x - 2 * j) (X j) HX4) as E5.
    pose proof (iter_mono_n (arrow j 2) (A_idk j) (2 * (x - 2 * j)) (2 * x) (X j) ltac:(lia)) as E6.
    pose proof (iter_mono_x (arrow j 2) (A_mono j) (2 * x) (X j) (arrow (S j) 2 4) HX) as E7.
    pose proof (A_iter10 j (2 * x) 4) as E8.
    lia.
  - rewrite X_S.
    pose proof (HI 2 (X j) HX4) as E9.
    change (iter 2 (U j) (X j)) with (U j (U j (X j))) in E9.
    pose proof (iter_mono_x (arrow j 2) (A_mono j) (2 * 2) (X j) (arrow (S j) 2 4) HX) as E10.
    pose proof (A_iter10 j (2 * 2) 4) as E11. change (2 * 2 + 4) with 8 in E11.
    pose proof (BB9_record_vs_champion.A_lin (S j) 4 ltac:(lia) ltac:(lia)) as E12.
    pose proof (A_mono (S j) 8 (arrow (S j) 2 4) ltac:(lia)) as E13.
    assert (E14 : arrow (S (S j)) 2 4 = arrow (S j) 2 (arrow (S j) 2 4)).
    { rewrite (A_SS (S j) 2 3), (A_SS (S j) 2 2), (A_two (S (S j))). reflexivity. }
    rewrite E14. lia.
Qed.

Lemma U_le_K_tight : forall j K y, 1 <= j -> j <= K -> 4 <= y -> U j y <= arrow K 2 (arrow K 2 y).
Proof.
  intros j K y Hj HK Hy. destruct (U_arrow_tight j Hj) as [HU _]. pose proof (HU y) as E0.
  pose proof (lin_j j y Hj Hy) as E1.
  pose proof (A_lvl (K - j) j y) as E2. replace (K - j + j) with K in E2 by lia.
  pose proof (A_mono j (2 * y + 4) (arrow K 2 y) ltac:(lia)) as E3.
  pose proof (A_lvl (K - j) j (arrow K 2 y)) as E4. replace (K - j + j) with K in E4 by lia.
  lia.
Qed.

(** ** The rebuilt lists *)

Lemma iterK : forall d K, 1 <= d -> d <= K ->
  forall n x, 4 <= x -> iter n (U d) x <= iter (2 * n) (arrow K 2) x.
Proof. intros d K Hd HK. apply iter_dom2. intros y Hy. apply U_le_K_tight; assumption. Qed.

Lemma Tpre_ge : forall m j B, B <= Tpre m j B.
Proof.
  induction m as [| m IH]; intros j B. - simpl. lia.
  - cbn [Tpre]. pose proof (iter_ge (U (j + 2)) (Ucge (j + 2)) 3 B). pose proof (IH (j + 3) (iter 3 (U (j + 2)) B)). lia.
Qed.

Lemma Tpre_le : forall m j B K, j + 3 * m <= K -> 4 <= B -> Tpre m j B <= iter (6 * m) (arrow K 2) B.
Proof.
  induction m as [| m IH]; intros j B K HK HB.
  - simpl. lia.
  - cbn [Tpre].
    set (z := iter 3 (U (j + 2)) B).
    assert (Gz : B <= z) by (unfold z; apply iter_ge, Ucge).
    pose proof (iterK (j + 2) K ltac:(lia) ltac:(lia) 3 B HB) as E1. fold z in E1.
    pose proof (IH (j + 3) z K ltac:(lia) ltac:(lia)) as E2.
    pose proof (iter_mono_x (arrow K 2) (A_mono K) (6 * m) z (iter (2 * 3) (arrow K 2) B) E1) as E3.
    assert (E4 : iter (6 * m) (arrow K 2) (iter (2 * 3) (arrow K 2) B) = iter (6 * S m) (arrow K 2) B).
    { replace (6 * S m) with (6 * m + 2 * 3) by lia. rewrite iter_add. reflexivity. }
    lia.
Qed.

Lemma Tv_le_tight : forall m, Tv m 1 7 <= arrow (3 * m + 4) 2 (6 * m + 7).
Proof.
  intros m. rewrite Tv_unfold.
  set (K := 1 + 3 * m + 2).
  set (P := Tpre m 1 7).
  assert (GP : 7 <= P) by (unfold P; apply Tpre_ge).
  pose proof (Tpre_le m 1 7 K ltac:(unfold K; lia) ltac:(lia)) as E1. fold P in E1.
  pose proof (iterK K K ltac:(unfold K; lia) ltac:(lia) 2 P ltac:(lia)) as E2.
  change (iter 2 (U K) P) with (U K (U K P)) in E2.
  pose proof (iter_mono_x (arrow K 2) (A_mono K) (2 * 2) P (iter (6 * m) (arrow K 2) 7) E1) as E3.
  assert (E4 : iter (2 * 2) (arrow K 2) (iter (6 * m) (arrow K 2) 7) = iter (6 * m + 4) (arrow K 2) 7).
  { replace (6 * m + 4) with (2 * 2 + 6 * m) by lia. rewrite iter_add. reflexivity. }
  pose proof (A_S3 K ltac:(unfold K; lia)) as E5.
  pose proof (iter_mono_x (arrow K 2) (A_mono K) (6 * m + 4) 7 (arrow (S K) 2 3) E5) as E6.
  pose proof (A_iter10 K (6 * m + 4) 3) as E7.
  replace (6 * m + 4 + 3) with (6 * m + 7) in E7 by lia.
  replace (3 * m + 4) with (S K) by (unfold K; lia).
  lia.
Qed.

Lemma b1_le_tight : b1 <= arrow 25 2 49.
Proof. rewrite b1_def. exact (Tv_le_tight 7). Qed.

(** ** The score *)

(** arithmetic for a variable q (never run lia on the closed b1 / 4) *)
Lemma Tv_plus4 : forall q, Tv q 1 7 + 4 <= arrow (3 * q + 4) 2 (2 * (3 * q + 4)).
Proof.
  intros q. pose proof (Tv_le_tight q) as E1.
  set (y := arrow (3 * q + 4) 2 (6 * q + 7)) in *.
  assert (E2 : arrow (3 * q + 4) 2 (2 * (3 * q + 4)) = arrow (3 * q + 3) 2 y).
  { unfold y. replace (3 * q + 4) with (S (3 * q + 3)) by lia. replace (2 * S (3 * q + 3)) with (S (6 * q + 7)) by lia.
    rewrite A_SS. replace (S (3 * q + 3)) with (3 * q + 4) by lia. reflexivity. }
  assert (Gy : 3 <= y) by (unfold y; pose proof (A_idk (3 * q + 4) (6 * q + 7)); lia).
  pose proof (BB9_record_vs_champion.A_lin (3 * q + 3) y ltac:(lia) Gy) as E3.
  rewrite E2. set (Tq := Tv q 1 7) in *. set (Ay := arrow (3 * q + 3) 2 y) in *. lia.
Qed.

Lemma quarter_le : forall b, 16 <= b -> 3 * (b / 4) + 4 <= b.
Proof. intros b Hb. pose proof (Nat.div_mod_eq b 4). pose proof (Nat.mod_upper_bound b 4 ltac:(lia)). lia. Qed.

Lemma b1_ge16 : 16 <= b1.
Proof.
  rewrite b1_def. destruct (Tv_big 7 1 7 ltac:(lia)) as [_ H].
  revert H. generalize (Tv 7 1 7). intros t H. lia.
Qed.

Theorem champion_upper : b2 + 4 <= arrow (3 * (b1 / 4) + 4) 2 (2 * (3 * (b1 / 4) + 4)) /\
                         3 * (b1 / 4) + 4 <= arrow 25 2 49.
Proof.
  split.
  - rewrite b2_def. unfold second. apply Tv_plus4.
  - pose proof (quarter_le b1 b1_ge16) as E1. pose proof b1_le_tight as E2.
    set (q := 3 * (b1 / 4) + 4) in *. set (A := arrow 25 2 49) in *. clearbody q A.
    revert E1 E2. generalize b1. intros bb E1 E2. lia.
Qed.

Lemma four_le : forall q, 4 <= 3 * q + 4.
Proof. intros; lia. Qed.

Theorem champion_upper_ex : exists Np, 4 <= Np /\ Np <= arrow 25 2 49 /\
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ N + 1 <= arrow Np 2 (2 * Np).
Proof.
  destruct champion_upper as [H1 H2].
  destruct score_exact as [c [R1 [R2 R3]]].
  exists (3 * (b1 / 4) + 4).
  split; [apply four_le |]. split; [exact H2 |].
  exists c, (b2 + 3). split; [exact R1 |]. split; [exact R2 |]. split; [exact R3 |].
  set (Np := 3 * (b1 / 4) + 4) in *. set (A := arrow Np 2 (2 * Np)) in *. clearbody Np A.
  revert H1. generalize b2. intros v H1. lia.
Qed.

Print Assumptions U_arrow_tight.
Print Assumptions b1_le_tight.
Print Assumptions champion_upper.
Print Assumptions champion_upper_ex.
