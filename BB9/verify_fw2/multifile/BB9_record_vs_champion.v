(** * The BB(9) record candidate beats the BB(9) champion: the two exact scores compared *)

(** Record candidate: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH---
      (BB9_record_1RB0RA.v: halts; BB9_record_bound.v: ones at the halt = 6 bp + 108 (Bx/5) + 82, and
       2 bp + 4 = 2 ^(12 Bx - 9 arrows) 8 with 2 Bx + 4 = 2 ^13 3).
    Champion (Jacobzheng 2024): 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH
      (BB9_champion_bound.v: ones at the halt = b2 + 3 with the head on a 0 and the halting transition 1RZ,
       so its standard score is b2 + 4; b1 = U 7 (U 7 (U 5 (U 3 (U 1 3)))), b2 = second b1.)

    Main results (no axioms):
      Theorem sigma_ours_gt_champion :
        exists cc Nc co No, c0 -[ champion tm ]->* cc /\ halted (champion tm) cc /\ champion.ones cc Nc /\
          c0 -->* co /\ halted tm co /\ ones co No /\ Nc + 1 < No.
      Theorem record_beats_champion :
        (exists c, c0 -[ champion tm ]->* c /\ halted (champion tm) c /\ champion.ones c (b2 + 3)) /\
        (exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ b2 + 4 < N).

    The argument (A k n = 2 ^(k arrows) n, the arrow of BB9_record_1RB0RA.v):
      1. The champion's clearing functions satisfy  U j x <= A (j+2) (2x+4)  and  X j <= A (j+3) 4  (Uc_le),
         hence U j y <= A K (A K y) for y >= 3, j + 2 <= K (Uc_le_K).
      2. b1 <= A 9 ^8 (280) <= A 10 11 (b1_le); the champion's second clearing gives
         second b <= A (b+4) (b+6) for every b (second_le), so b2 <= A (b1+4) (b1+6).
      3. Ours: N > 2 bp + 4 = A K 8 with K = 12 Bx - 9, and A K 8 = A (K-1) (A K 7) >= A (b1+4) (b1+7)
         > A (b1+4) (b1+6) + 4 because K - 1 >= b1 + 4 and A K 7 >= b1 + 7 (both since b1 <= A 10 11 << Bx). *)

From BB8 Require Import Individual92.
From BB8 Require BB9_champion_1RB1RA BB9_champion_bound.
From BB8 Require Import BB9_record_1RB0RA BB9_record_bound.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

Opaque arrow.
Opaque BB9_champion_bound.U BB9_champion_bound.X BB9_champion_bound.b1 BB9_champion_bound.b2.

Notation Uc := BB9_champion_bound.U.
Notation Xc := BB9_champion_bound.X.
Notation iterc := BB9_champion_bound.iter.

(** ** Up-arrows with base 2 *)

Lemma A_id : forall k x, x <= arrow k 2 x.
Proof. intros. apply arrow_props. Qed.

Lemma iterr_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

(** A k ^m (A (k+1) n) = A (k+1) (m+n) *)
Lemma A_iter : forall k m n, iter m (arrow k 2) (arrow (S k) 2 n) = arrow (S k) 2 (m + n).
Proof.
  intros k m n. induction m as [| m IH]. - reflexivity.
  - change (iter (S m) (arrow k 2) (arrow (S k) 2 n)) with (arrow k 2 (iter m (arrow k 2) (arrow (S k) 2 n))).
    rewrite IH. change (S m + n) with (S (m + n)). rewrite arrow_SS. reflexivity.
Qed.

Lemma pow2_lin : forall y, 4 <= y -> 2 * y + 4 <= 2 ^ y.
Proof.
  intros y Hy. induction y as [| y IH]; [lia |].
  destruct (Nat.eq_dec y 3) as [-> | Hne]; [simpl; lia |].
  rewrite Nat.pow_succ_r'. specialize (IH ltac:(lia)). lia.
Qed.

Lemma A_lin : forall k y, 2 <= k -> 3 <= y -> 2 * y + 4 <= arrow k 2 y.
Proof.
  intros k y Hk Hy.
  pose proof (arrow_level_mono (k - 2) 2 y) as L. replace (k - 2 + 2) with k in L by lia.
  enough (E : 2 * y + 4 <= arrow 2 2 y) by lia.
  destruct (Nat.eq_dec y 3) as [-> | Hne].
  - rewrite (arrow_SS 1 2 2), (arrow_two 2), arrow_1_pow. simpl. lia.
  - pose proof (arrow_level 1 y) as L2. rewrite arrow_1_pow in L2.
    pose proof (pow2_lin y ltac:(lia)). lia.
Qed.

(** ** Upper bounds for the champion's clearing functions *)

Lemma Uc_ge : forall j y, y <= Uc j y.
Proof. intros. pose proof (BB9_champion_bound.Ugrow j y). lia. Qed.

Lemma iterc_dom : forall j K, (forall y, 3 <= y -> Uc j y <= arrow K 2 (arrow K 2 y)) ->
  forall n X, 3 <= X -> iterc n (Uc j) X <= iter (2 * n) (arrow K 2) X.
Proof.
  intros j K HU. induction n as [| n IH]; intros X HX. - simpl. lia.
  - change (iterc (S n) (Uc j) X) with (Uc j (iterc n (Uc j) X)).
    replace (2 * S n) with (S (S (2 * n))) by lia.
    change (iter (S (S (2 * n))) (arrow K 2) X) with (arrow K 2 (arrow K 2 (iter (2 * n) (arrow K 2) X))).
    pose proof (BB9_champion_bound.iter_ge (Uc j) (Uc_ge j) n X) as G.
    specialize (IH X HX).
    transitivity (arrow K 2 (arrow K 2 (iterc n (Uc j) X))); [apply HU; lia |].
    apply arrow_mono, arrow_mono. exact IH.
Qed.

Lemma Uc_le : forall j, (forall x, Uc j x <= arrow (j + 2) 2 (2 * x + 4)) /\ Xc j <= arrow (j + 3) 2 4.
Proof.
  induction j as [| j [HU HX]].
  - split.
    + intros x. rewrite BB9_champion_bound.U_0. change (0 + 2) with 2.
      pose proof (A_lin 2 (2 * x + 4) ltac:(lia) ltac:(lia)) as E. lia.
    + rewrite BB9_champion_bound.X_0. change (0 + 3) with 3.
      pose proof (A_lin 3 4 ltac:(lia) ltac:(lia)) as E. lia.
  - assert (HU2 : forall y, 3 <= y -> Uc j y <= arrow (j + 2) 2 (arrow (j + 2) 2 y)).
    { intros y Hy. pose proof (HU y) as E1. pose proof (A_lin (j + 2) y ltac:(lia) Hy) as E2.
      pose proof (arrow_mono (j + 2) _ _ E2) as E3. lia. }
    assert (HX3 : 3 <= Xc j) by (pose proof (BB9_champion_bound.Xgrow j); lia).
    pose proof (iterc_dom j (j + 2) HU2) as HI.
    split.
    + intros x. rewrite BB9_champion_bound.U_S. replace (S j + 2) with (j + 3) by lia.
      pose proof (HI (x - 2 * j) (Xc j) HX3) as E5.
      pose proof (iter_mono_n (arrow (j + 2) 2) (A_id (j + 2)) (2 * (x - 2 * j)) (2 * x) (Xc j) ltac:(lia)) as E6.
      pose proof (iterr_mono_x (arrow (j + 2) 2) (arrow_mono (j + 2)) (2 * x) (Xc j) (arrow (j + 3) 2 4) HX) as E7.
      pose proof (A_iter (j + 2) (2 * x) 4) as E8. replace (S (j + 2)) with (j + 3) in E8 by lia.
      lia.
    + rewrite BB9_champion_bound.X_S. replace (S j + 3) with (S (j + 3)) by lia.
      pose proof (HI 2 (Xc j) HX3) as E9.
      change (iterc 2 (Uc j) (Xc j)) with (Uc j (Uc j (Xc j))) in E9.
      pose proof (iterr_mono_x (arrow (j + 2) 2) (arrow_mono (j + 2)) (2 * 2) (Xc j) (arrow (j + 3) 2 4) HX) as E10.
      pose proof (A_iter (j + 2) (2 * 2) 4) as E11. replace (S (j + 2)) with (j + 3) in E11 by lia.
      change (2 * 2 + 4) with 8 in E11.
      pose proof (A_lin (j + 3) 4 ltac:(lia) ltac:(lia)) as E12.
      pose proof (arrow_mono (j + 3) 8 (arrow (j + 3) 2 4) ltac:(lia)) as E13.
      assert (E14 : arrow (S (j + 3)) 2 4 = arrow (j + 3) 2 (arrow (j + 3) 2 4)).
      { rewrite (arrow_SS (j + 3) 2 3), (arrow_SS (j + 3) 2 2), (arrow_two (S (j + 3))). reflexivity. }
      rewrite E14. lia.
Qed.

Lemma Uc_le_K : forall j K y, j + 2 <= K -> 3 <= y -> Uc j y <= arrow K 2 (arrow K 2 y).
Proof.
  intros j K y HK Hy. destruct (Uc_le j) as [HU _]. pose proof (HU y) as E0.
  pose proof (A_lin (j + 2) y ltac:(lia) Hy) as E1.
  pose proof (arrow_level_mono (K - (j + 2)) (j + 2) y) as E2.
  replace (K - (j + 2) + (j + 2)) with K in E2 by lia.
  pose proof (arrow_mono (j + 2) (2 * y + 4) (arrow K 2 y) ltac:(lia)) as E3.
  pose proof (arrow_level_mono (K - (j + 2)) (j + 2) (arrow K 2 y)) as E4.
  replace (K - (j + 2) + (j + 2)) with K in E4 by lia.
  lia.
Qed.

(** ** The champion's b1 and b2 *)

Lemma A10_3 : 280 <= arrow 10 2 3.
Proof.
  rewrite (arrow_SS 9 2 2), (arrow_two 10).
  pose proof (arrow_level_mono 7 2 4) as L. change (7 + 2) with 9 in L.
  rewrite (arrow_SS 1 2 3), (arrow_SS 1 2 2), (arrow_two 2), !arrow_1_pow in L.
  change (2 ^ 4) with 16 in L.
  assert (P : 2 ^ 9 <= 2 ^ 16) by (apply Nat.pow_le_mono_r; lia).
  change (2 ^ 9) with 512 in P. lia.
Qed.

Lemma step2 : forall K m y a, a <= iter m (arrow K 2) y -> arrow K 2 (arrow K 2 a) <= iter (S (S m)) (arrow K 2) y.
Proof. intros. simpl. apply arrow_mono, arrow_mono. assumption. Qed.

Lemma b1_le : BB9_champion_bound.b1 <= arrow 10 2 11.
Proof.
  rewrite BB9_champion_bound.b1_def, BB9_champion_bound.U1_3.
  assert (G0 : 280 <= iter 0 (arrow 9 2) 280) by (simpl; lia).
  pose proof (Uc_le_K 3 9 280 ltac:(lia) ltac:(lia)) as E1.
  pose proof (step2 9 0 280 280 G0) as F1.
  pose proof (Uc_ge 3 280) as G1.
  pose proof (Uc_le_K 5 9 (Uc 3 280) ltac:(lia) ltac:(lia)) as E2.
  pose proof (step2 9 2 280 (Uc 3 280) ltac:(lia)) as F2.
  pose proof (Uc_ge 5 (Uc 3 280)) as G2.
  pose proof (Uc_le_K 7 9 (Uc 5 (Uc 3 280)) ltac:(lia) ltac:(lia)) as E3.
  pose proof (step2 9 4 280 (Uc 5 (Uc 3 280)) ltac:(lia)) as F3.
  pose proof (Uc_ge 7 (Uc 5 (Uc 3 280))) as G3.
  pose proof (Uc_le_K 7 9 (Uc 7 (Uc 5 (Uc 3 280))) ltac:(lia) ltac:(lia)) as E4.
  pose proof (step2 9 6 280 (Uc 7 (Uc 5 (Uc 3 280))) ltac:(lia)) as F4.
  pose proof (iterr_mono_x (arrow 9 2) (arrow_mono 9) 8 280 (arrow 10 2 3) A10_3) as F5.
  pose proof (A_iter 9 8 3) as F6. change (8 + 3) with 11 in F6.
  lia.
Qed.

Lemma Pv_ge : forall m j B, B <= BB9_champion_bound.Pv m j B.
Proof.
  induction m as [| m IH]; intros j B. - simpl. lia.
  - cbn [BB9_champion_bound.Pv]. pose proof (Uc_ge (S j) B). pose proof (IH (j + 2) (Uc (S j) B)). lia.
Qed.

Lemma Pv_le : forall m j B K, j + 2 * m + 1 <= K -> 3 <= B ->
  BB9_champion_bound.Pv m j B <= iter (2 * m) (arrow K 2) B.
Proof.
  induction m as [| m IH]; intros j B K HK HB.
  - simpl. lia.
  - cbn [BB9_champion_bound.Pv].
    pose proof (Uc_ge (S j) B) as G.
    pose proof (IH (j + 2) (Uc (S j) B) K ltac:(lia) ltac:(lia)) as E1.
    pose proof (Uc_le_K (S j) K B ltac:(lia) HB) as E2.
    pose proof (iterr_mono_x (arrow K 2) (arrow_mono K) (2 * m) _ _ E2) as E3.
    assert (E4 : iter (2 * m) (arrow K 2) (arrow K 2 (arrow K 2 B)) = iter (2 * S m) (arrow K 2) B).
    { replace (2 * S m) with (2 * m + 2) by lia. rewrite iter_add. reflexivity. }
    lia.
Qed.

Lemma second_le : forall b, BB9_champion_bound.second b <= arrow (b + 4) 2 (b + 6).
Proof.
  intros b. unfold BB9_champion_bound.second.
  assert (Hd : 2 * (b / 2) <= b) by (apply Nat.mul_div_le; lia).
  pose proof (Pv_le (b / 2) 0 3 (b + 1) ltac:(lia) ltac:(lia)) as E1.
  pose proof (Pv_ge (b / 2) 0 3) as G0.
  generalize dependent (BB9_champion_bound.Pv (b / 2) 0 3). intros P E1 G0.
  pose proof (iter_mono_n (arrow (b + 1) 2) (A_id (b + 1)) (2 * (b / 2)) b 3 Hd) as E2.
  clear Hd. generalize dependent (b / 2). intros h E1 E2.
  pose proof (iterr_mono_x (arrow (b + 1) 2) (arrow_mono (b + 1)) b 3 (arrow (b + 2) 2 2)
                ltac:(rewrite arrow_two; lia)) as E3.
  pose proof (A_iter (b + 1) b 2) as E4. replace (S (b + 1)) with (b + 2) in E4 by lia.
  (* P <= A (b+2) (b+2) <= A (b+4) (b+2) *)
  pose proof (arrow_level_mono 2 (b + 2) (b + 2)) as E5. replace (2 + (b + 2)) with (b + 4) in E5 by lia.
  (* the two clearings at depth b+1 *)
  pose proof (iterc_dom (S b) (b + 3) (fun y Hy => Uc_le_K (S b) (b + 3) y ltac:(lia) Hy) 2 P ltac:(lia)) as E6.
  change (iterc 2 (Uc (S b)) P) with (Uc (S b) (Uc (S b) P)) in E6.
  pose proof (iterr_mono_x (arrow (b + 3) 2) (arrow_mono (b + 3)) (2 * 2) P (arrow (b + 4) 2 (b + 2))
                ltac:(lia)) as E7.
  pose proof (A_iter (b + 3) (2 * 2) (b + 2)) as E8. replace (S (b + 3)) with (b + 4) in E8 by lia.
  replace (2 * 2 + (b + 2)) with (b + 6) in E8 by lia.
  lia.
Qed.

Lemma b2_le : BB9_champion_bound.b2 <= arrow (BB9_champion_bound.b1 + 4) 2 (BB9_champion_bound.b1 + 6).
Proof. rewrite BB9_champion_bound.b2_def. apply second_le. Qed.

(** ** The comparison *)

Lemma compare_core : forall b K, b + 5 <= K -> b + 7 <= arrow K 2 7 ->
  arrow (b + 4) 2 (b + 6) + 5 <= arrow K 2 8.
Proof.
  intros b K HK H7.
  set (y := arrow (b + 4) 2 (b + 6)).
  assert (Gy : 6 <= y) by (unfold y; pose proof (A_id (b + 4) (b + 6)); lia).
  assert (E1 : arrow (b + 4) 2 (b + 7) = arrow (b + 3) 2 y).
  { unfold y. replace (b + 4) with (S (b + 3)) by lia. replace (b + 7) with (S (b + 6)) by lia.
    rewrite arrow_SS. reflexivity. }
  pose proof (A_lin (b + 3) y ltac:(lia) ltac:(lia)) as E2.
  pose proof (arrow_level_mono (K - 1 - (b + 4)) (b + 4) (b + 7)) as E3.
  replace (K - 1 - (b + 4) + (b + 4)) with (K - 1) in E3 by lia.
  pose proof (arrow_mono (K - 1) (b + 7) (arrow K 2 7) H7) as E4.
  assert (E5 : arrow K 2 8 = arrow (K - 1) 2 (arrow K 2 7)).
  { replace K with (S (K - 1)) at 1 by lia. rewrite arrow_SS. replace (S (K - 1)) with K by lia. reflexivity. }
  lia.
Qed.

(** 2 ^13 3 >= 2 ^10 12  (arrows) *)
Lemma A13_ge : arrow 10 2 12 <= arrow 13 2 3.
Proof.
  rewrite (arrow_SS 12 2 2), (arrow_two 13), (arrow_SS 11 2 3), (arrow_SS 11 2 2), (arrow_two 12).
  pose proof (A_lin 11 4 ltac:(lia) ltac:(lia)) as E1.
  pose proof (arrow_mono 11 12 (arrow 11 2 4) ltac:(lia)) as E2.
  pose proof (arrow_level 10 12) as E3.
  lia.
Qed.

(** 2 ^11 7 >= 2 ^10 12  (arrows) *)
Lemma A11_7 : arrow 10 2 12 <= arrow 11 2 7.
Proof.
  rewrite (arrow_SS 10 2 6).
  pose proof (A_lin 11 6 ltac:(lia) ltac:(lia)) as E1.
  pose proof (arrow_mono 10 12 (arrow 11 2 6) ltac:(lia)) as E2.
  lia.
Qed.

Theorem record_beats_champion :
  (exists c, c0 -[ BB9_champion_1RB1RA.tm ]->* c /\ halted BB9_champion_1RB1RA.tm c /\
             BB9_champion_bound.ones c (BB9_champion_bound.b2 + 3)) /\
  (exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ BB9_champion_bound.b2 + 4 < N).
Proof.
  split; [exact BB9_champion_bound.score_exact |].
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (6 * bp + 108 * (Bx / 5) + 82).
  split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  pose proof b2_le as Eb2. pose proof b1_le as Eb1. pose proof bp_closed as Ebp.
  pose proof Bx_arrow13 as E13. pose proof Bx_ge6 as H6.
  pose proof A13_ge as F1. pose proof A11_7 as F2.
  pose proof (A_lin 10 11 ltac:(lia) ltac:(lia)) as F3.
  pose proof (A_lin 10 12 ltac:(lia) ltac:(lia)) as F3'.
  (* K = 12 Bx - 9 *)
  assert (HK : BB9_champion_bound.b1 + 5 <= 12 * Bx - 9).
  { assert (E : arrow 10 2 12 = arrow 9 2 (arrow 10 2 11)) by (rewrite (arrow_SS 9 2 11); reflexivity).
    pose proof (A_lin 9 (arrow 10 2 11) ltac:(lia) ltac:(pose proof (A_id 10 11); lia)) as F4.
    lia. }
  assert (H7 : BB9_champion_bound.b1 + 7 <= arrow (12 * Bx - 9) 2 7).
  { pose proof (arrow_level_mono (12 * Bx - 9 - 11) 11 7) as L.
    replace (12 * Bx - 9 - 11 + 11) with (12 * Bx - 9) in L by lia.
    assert (E : arrow 10 2 12 = arrow 9 2 (arrow 10 2 11)) by (rewrite (arrow_SS 9 2 11); reflexivity).
    pose proof (A_lin 9 (arrow 10 2 11) ltac:(lia) ltac:(pose proof (A_id 10 11); lia)) as F4.
    lia. }
  pose proof (compare_core BB9_champion_bound.b1 (12 * Bx - 9) HK H7) as Hc.
  generalize dependent (Bx / 5). intros.
  lia.
Qed.

(** The same, as one statement about the two halting configurations.  The champion halts on a 0 with the
    halting transition E0 = 1RZ, so its standard score is Nc + 1; ours halts in state I on a 1 (I1 undefined, a
    1RZ write leaves the count unchanged), so its standard score is No.  Hence No > Nc + 1. *)
Theorem sigma_ours_gt_champion :
  exists cc Nc co No,
    c0 -[ BB9_champion_1RB1RA.tm ]->* cc /\ halted BB9_champion_1RB1RA.tm cc /\ BB9_champion_bound.ones cc Nc /\
    c0 -->* co /\ halted tm co /\ ones co No /\
    Nc + 1 < No.
Proof.
  destruct record_beats_champion as [[cc [Hc1 [Hc2 Hc3]]] [co [No [Ho1 [Ho2 [Ho3 Hlt]]]]]].
  exists cc, (BB9_champion_bound.b2 + 3), co, No.
  split; [exact Hc1 |]. split; [exact Hc2 |]. split; [exact Hc3 |].
  split; [exact Ho1 |]. split; [exact Ho2 |]. split; [exact Ho3 |].
  revert Hlt. generalize BB9_champion_bound.b2. intros b Hb. lia.
Qed.

Print Assumptions record_beats_champion.
Print Assumptions sigma_ours_gt_champion.
