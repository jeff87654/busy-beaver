(** An upper bound on fw2's exact score, so that C04 beats fw2 itself (not only fw2's published lower bound).

    fw2 = 1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA (bb8_list/proofs/BB9_fw2_1RB0RD.v,
    BB9_fw2_bound.v; identical to busy-beaver/BB9/verify_fw2/multifile).  BB9_fw2_bound.score_exact: the halting
    configuration holds b3 + 3 ones, b3 = second (second b1), b1 = U 1 10, second b = Tv (b / 4) 1 37.

    Here (fw2's U is written V, its X is XF, its iter is iterF; U is Abs.U):
      V_le_U        : V i x <= U (S i) x, XF i <= U (S i) 1
      second_le     : second b <= U (3 b + 5) (3 b + 39)
      fw2_b3_bound  : forall K, R2 Bx <= K -> b3 + 5 <= U K 0
      fw2_side      : forall N K x, 11 * R2 Bx <= K -> U K 0 <= x -> 6 * x <= N ->
                        exists cf Nf, c0 -[ fw2 ]->* cf /\ halted fw2 cf /\ ones cf Nf /\ Nf + 1 < N
    Build: python coqc_score.py Fw2Upper.v 600 --fw2 *)
From BB8 Require Import Individual92.
From BB8 Require BB9_fw2_1RB0RD BB9_fw2_bound.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From Dev Require Import Abs Chain.
From Score Require Import Score.

Local Open Scope nat_scope.

Notation V := BB9_fw2_1RB0RD.U.
Notation XF := BB9_fw2_1RB0RD.X.
Notation iterF := BB9_fw2_1RB0RD.iter.
Notation Tpre := BB9_fw2_1RB0RD.Tpre.

Lemma Tv_eq : forall m j B, BB9_fw2_1RB0RD.Tv m j B = V (j + 3 * m + 2) (V (j + 3 * m + 1) (Tpre m j B)).
Proof. reflexivity. Qed.

Lemma Tpre_S : forall m j B, Tpre (S m) j B = Tpre m (j + 3) (V (j + 2) (V (j + 2) (V (j + 1) B))).
Proof. reflexivity. Qed.

Lemma Tpre_0 : forall j B, Tpre 0 j B = B.
Proof. reflexivity. Qed.

Opaque U arrow BB9_fw2_1RB0RD.U BB9_fw2_1RB0RD.X BB9_fw2_1RB0RD.Tv BB9_fw2_1RB0RD.Tpre
  BB9_fw2_1RB0RD.b1 BB9_fw2_1RB0RD.b2 BB9_fw2_1RB0RD.b3 Bx.

Lemma iterF_eq : forall n g x, iterF n g x = iter n g x.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma sc_iter_mono_n : forall g, (forall a, a <= g a) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x H. replace m with ((m - n) + n) by lia. rewrite sc_iter_add.
  generalize (iter n g x). intro y. induction (m - n) as [| k IH]; simpl; [lia |].
  specialize (Hg (iter k g y)). lia.
Qed.

Lemma U0_lin4 : forall x, 4 * x + 6 <= U 0 x.
Proof.
  intro x. rewrite U_0. pose proof (dbl_closed (2 * x + 2) 0) as H.
  rewrite Nat.pow_add_r in H. change (2 ^ 2) with 4 in H.
  pose proof (Nat.pow_gt_lin_r 2 (2 * x) ltac:(lia)). lia.
Qed.

Lemma U_step4 : forall j x, 4 * U (S j) x + 6 <= U (S j) (S x).
Proof.
  intros j x. rewrite !U_S. replace (2 * S x + 2) with (S (S (2 * x + 2))) by lia.
  change (iter (S (S (2 * x + 2))) (U j) 0) with (U j (U j (iter (2 * x + 2) (U j) 0))).
  pose proof (sc_U_lin j (iter (2 * x + 2) (U j) 0)).
  pose proof (sc_U_lin j (U j (iter (2 * x + 2) (U j) 0))). lia.
Qed.

(** ** fw2's clearing functions are dominated by Abs.U one level up *)

Lemma V_le : forall i, (forall x, V i x <= U (S i) x) /\ XF i <= U (S i) 1.
Proof.
  induction i as [| i [HV HX]].
  - split.
    + intro x. rewrite BB9_fw2_1RB0RD.U_0, U_S. replace (2 * x + 2) with (S (S (2 * x))) by lia.
      change (iter (S (S (2 * x))) (U 0) 0) with (U 0 (U 0 (iter (2 * x) (U 0) 0))).
      assert (Hg : forall a, a + 1 <= U 0 a) by (intro a; pose proof (sc_U_lin 0 a); lia).
      pose proof (sc_iter_count (U 0) Hg (2 * x) 0).
      pose proof (U0_lin4 (iter (2 * x) (U 0) 0)). pose proof (U0_lin4 (U 0 (iter (2 * x) (U 0) 0))). lia.
    + rewrite BB9_fw2_1RB0RD.X_0, U_S.
      change (iter (2 * 1 + 2) (U 0) 0) with (U 0 (U 0 (U 0 (U 0 0)))).
      pose proof (U0_lin4 0). pose proof (U0_lin4 (U 0 0)).
      pose proof (sc_U_lin 0 (U 0 (U 0 0))). pose proof (sc_U_lin 0 (U 0 (U 0 (U 0 0)))). lia.
  - split.
    + intro x. rewrite BB9_fw2_1RB0RD.U_S, iterF_eq, (U_S (S i)).
      set (n := x - 2 * i).
      assert (H1 : iter n (V i) (XF i) <= iter n (U (S i)) (XF i))
        by (apply sc_iter_dom; [exact HV | exact (sc_U_mono (S i))]).
      assert (H2 : iter n (U (S i)) (XF i) <= iter n (U (S i)) (iter 2 (U (S i)) 0)).
      { apply sc_iter_mono_x; [exact (sc_U_mono (S i)) |].
        change (iter 2 (U (S i)) 0) with (U (S i) (U (S i) 0)).
        pose proof (sc_U0_ge (S i)). pose proof (sc_U_mono (S i) 1 (U (S i) 0) ltac:(lia)). lia. }
      rewrite <- sc_iter_add in H2.
      assert (Hg : forall a, a <= U (S i) a) by (intro a; pose proof (sc_U_lin (S i) a); lia).
      pose proof (sc_iter_mono_n (U (S i)) Hg (n + 2) (2 * x + 2) 0 ltac:(unfold n; lia)). lia.
    + rewrite BB9_fw2_1RB0RD.X_S, U_S.
      change (iter (2 * 1 + 2) (U (S i)) 0) with (U (S i) (U (S i) (U (S i) (U (S i) 0)))).
      pose proof (sc_U0_ge (S i)) as G.
      pose proof (sc_U_mono (S i) 1 (U (S i) 0) ltac:(lia)) as M1.
      pose proof (sc_U_mono (S i) (XF i) (U (S i) 1) HX) as M2.
      pose proof (sc_U_mono (S i) (V i (XF i)) (U (S i) (XF i)) (HV (XF i))) as M3.
      pose proof (sc_U_mono (S i) _ _ M2) as M4.
      pose proof (sc_U_mono (S i) _ _ M1) as M5.
      pose proof (sc_U_mono (S i) _ _ M5) as M6.
      pose proof (HV (V i (XF i))) as M0.
      lia.
Qed.

Lemma V_le_U : forall i x, V i x <= U (S i) x.
Proof. intro i. apply (proj1 (V_le i)). Qed.

Lemma V_lev : forall L l y, l + 1 <= L -> V l y <= U L y.
Proof.
  intros L l y Hl. pose proof (V_le_U l y). pose proof (sc_U_mono2 (S l) L y y ltac:(lia) ltac:(lia)). lia.
Qed.

(** ** The trip clears *)

Lemma Tpre_le : forall m j B L, j + 3 * m + 3 <= L -> Tpre m j B <= iter (3 * m) (U L) B.
Proof.
  induction m; intros j B L HL.
  - rewrite Tpre_0. replace (3 * 0) with 0 by lia. change (iter 0 (U L) B) with B. lia.
  - rewrite Tpre_S.
    pose proof (IHm (j + 3) (V (j + 2) (V (j + 2) (V (j + 1) B))) L ltac:(lia)) as H1.
    assert (H2 : V (j + 2) (V (j + 2) (V (j + 1) B)) <= iter 3 (U L) B).
    { change (iter 3 (U L) B) with (U L (U L (U L B))).
      pose proof (V_lev L (j + 1) B ltac:(lia)) as A1.
      pose proof (V_lev L (j + 2) (V (j + 1) B) ltac:(lia)) as A2.
      pose proof (V_lev L (j + 2) (V (j + 2) (V (j + 1) B)) ltac:(lia)) as A3.
      pose proof (sc_U_mono L _ _ A1) as A4.
      pose proof (sc_U_mono L _ _ (Nat.le_trans _ _ _ A2 A4)) as A5.
      lia. }
    pose proof (sc_iter_mono_x (U L) (sc_U_mono L) (3 * m) _ _ H2) as H3.
    rewrite <- sc_iter_add in H3. replace (3 * m + 3) with (3 * S m) in H3 by lia. lia.
Qed.

Lemma Tv_le : forall m j B, BB9_fw2_1RB0RD.Tv m j B <= iter (3 * m + 2) (U (j + 3 * m + 3)) B.
Proof.
  intros m j B. rewrite Tv_eq. set (L := j + 3 * m + 3).
  pose proof (Tpre_le m j B L ltac:(unfold L; lia)) as H1.
  replace (3 * m + 2) with (S (S (3 * m))) by lia.
  change (iter (S (S (3 * m))) (U L) B) with (U L (U L (iter (3 * m) (U L) B))).
  pose proof (V_lev L (j + 3 * m + 1) (Tpre m j B) ltac:(unfold L; lia)) as A1.
  pose proof (V_lev L (j + 3 * m + 2) (V (j + 3 * m + 1) (Tpre m j B)) ltac:(unfold L; lia)) as A2.
  pose proof (sc_U_mono L _ _ H1) as A3.
  pose proof (sc_U_mono L _ _ (Nat.le_trans _ _ _ A1 A3)) as A4.
  lia.
Qed.

(** n clears at one level are absorbed by one more level. *)
Lemma iter_U_absorb : forall n L B, iter n (U L) B <= U (S L) (n + B).
Proof.
  intros n L B. rewrite U_S. replace (2 * (n + B) + 2) with (n + (n + 2 * B + 2)) by lia.
  rewrite sc_iter_add. apply sc_iter_mono_x; [exact (sc_U_mono L) |].
  assert (Hg : forall a, a + 1 <= U L a) by (intro a; pose proof (sc_U_lin L a); lia).
  pose proof (sc_iter_count (U L) Hg (n + 2 * B + 2) 0). lia.
Qed.

Lemma second_le : forall b, BB9_fw2_1RB0RD.second b <= U (3 * b + 5) (3 * b + 39).
Proof.
  intro b. unfold BB9_fw2_1RB0RD.second.
  pose proof (Nat.Div0.mul_div_le b 4) as Hq.
  pose proof (Tv_le (b / 4) 1 37) as H1.
  pose proof (iter_U_absorb (3 * (b / 4) + 2) (1 + 3 * (b / 4) + 3) 37) as H2.
  set (q := b / 4) in *. clearbody q.
  pose proof (sc_U_mono2 (S (1 + 3 * q + 3)) (3 * b + 5) (3 * q + 2 + 37) (3 * b + 39) ltac:(lia) ltac:(lia)).
  lia.
Qed.

(** ** fw2's score is below every clear value at depth K >= R2 Bx *)

Theorem fw2_b3_bound : forall K, R2 Bx <= K -> BB9_fw2_1RB0RD.b3 + 5 <= U K 0.
Proof.
  intros K HK.
  (* b1 <= M := U 2 10 *)
  assert (Hb1 : BB9_fw2_1RB0RD.b1 <= U 2 10) by (rewrite BB9_fw2_1RB0RD.b1_def; apply V_le_U).
  set (M := U 2 10) in *.
  (* Bx >= 16 M + 30 *)
  assert (HBx : 16 * M + 30 <= Bx).
  { pose proof (U_step4 1 10) as S1. pose proof (U_step4 1 11) as S2.
    assert (H12 : 12 <= U 10 0) by (pose proof (sc_U0_ge 10) as H0; revert H0; generalize (U 10 O); intros; lia).
    pose proof (sc_U_mono2 2 10 12 (U 10 0) ltac:(lia) H12) as G.
    rewrite <- Bx_def in G. unfold M. lia. }
  clearbody M.
  set (j0 := 3 * M + 38).
  (* b2 <= Z := U (S j0) (S j0) *)
  assert (Hb2 : BB9_fw2_1RB0RD.b2 <= U (S j0) (S j0)).
  { rewrite BB9_fw2_1RB0RD.b2_def. pose proof (second_le BB9_fw2_1RB0RD.b1).
    pose proof (sc_U_mono2 (3 * BB9_fw2_1RB0RD.b1 + 5) (S j0) (3 * BB9_fw2_1RB0RD.b1 + 39) (S j0)
      ltac:(unfold j0; lia) ltac:(unfold j0; lia)). lia. }
  set (Z := U (S j0) (S j0)) in *.
  (* R2 Bx >= 4 Z + 6 *)
  assert (HR2 : 4 * Z + 6 <= R2 Bx).
  { unfold R2. set (J := 12 * Bx + 24).
    change (iter 2 (U J) 0) with (U J (U J 0)).
    pose proof (sc_U0_ge J).
    assert (HJ : S j0 <= J) by (unfold J, j0; lia).
    clearbody J.
    pose proof (sc_U_mono2 (S j0) J (S (S j0)) (U J 0) ltac:(lia) ltac:(lia)).
    pose proof (U_step4 j0 (S j0)). unfold Z. lia. }
  assert (HZ : 2 * S j0 + 2 <= Z) by (unfold Z; apply sc_U_lin).
  clearbody Z.
  (* b3 <= U Y Y, Y = 3 Z + 39 *)
  set (Y := 3 * Z + 39).
  assert (Hb3 : BB9_fw2_1RB0RD.b3 <= U Y Y).
  { rewrite BB9_fw2_1RB0RD.b3_def. pose proof (second_le BB9_fw2_1RB0RD.b2).
    pose proof (sc_U_mono2 (3 * BB9_fw2_1RB0RD.b2 + 5) Y (3 * BB9_fw2_1RB0RD.b2 + 39) Y
      ltac:(unfold Y; lia) ltac:(unfold Y; lia)). lia. }
  assert (HY : Y + 2 <= K) by (unfold Y; lia).
  clearbody Y.
  pose proof (sc_U0_ge Y) as G1.
  pose proof (sc_U_mono Y Y (U Y 0) ltac:(lia)) as G2.
  pose proof (U_S0 Y) as E1.
  pose proof (sc_U0_ge (S Y)) as G3.
  pose proof (sc_U_lin (S Y) (U (S Y) 0)) as G4.
  pose proof (U_S0 (S Y)) as E2.
  pose proof (sc_U_mono2 (S (S Y)) K 0 0 ltac:(lia) ltac:(lia)) as G5.
  lia.
Qed.

Theorem fw2_score_lt : forall K x N, R2 Bx <= K -> U K 0 <= x -> x <= N -> BB9_fw2_1RB0RD.b3 + 3 + 1 < N.
Proof. intros K x N HK Hx HN. pose proof (fw2_b3_bound K HK). lia. Qed.

(** The fw2 half of a beats statement in the style of BB9_fw2_vs_records.v: fw2's halting configuration holds Nf ones
    with Nf + 1 (its score) < N, for any N >= 6 x, x >= U K 0, K >= 11 R2 Bx (the C04 hypothesis). *)
Theorem fw2_side : forall N K x, 11 * R2 Bx <= K -> U K 0 <= x -> 6 * x <= N ->
  exists cf Nf, c0 -[ BB9_fw2_1RB0RD.tm ]->* cf /\ halted BB9_fw2_1RB0RD.tm cf /\
    BB9_fw2_bound.ones cf Nf /\ Nf + 1 < N.
Proof.
  intros N K x HK Hx HN.
  destruct BB9_fw2_bound.score_exact as [cf [H1 [H2 H3]]].
  exists cf, (BB9_fw2_1RB0RD.b3 + 3).
  split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  apply (fw2_score_lt K x N); lia.
Qed.

Print Assumptions fw2_b3_bound.
Print Assumptions fw2_side.
