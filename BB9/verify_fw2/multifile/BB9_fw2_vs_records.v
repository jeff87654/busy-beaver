(** * The 9-state f_omega^2 machine beats all previous BB(9) records and the BB(10) champion *)

(** Machine:
      1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA
    (BB9_fw2_1RB0RD.v: halts, check.py PASS; BB9_fw2_bound.v: score_exact proves ones c (b3 + 3)
     and sigma_lower_bound proves f_omega (f_omega (465 * 1000 + 9)) < (b3 + 3) + 1.)

    Main results (all machine-checked, no axioms):
      1. fw2_beats_redir_0LA_fh  : beats 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LI0LC_1RG1LD_1LC1RH_0LH0RF_---0LA
      2. fw2_beats_redir_0LA     : beats 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LI0LC_1RG1LD_1LC0RH_1RG1LF_---0LA
      3. fw2_beats_record        : beats 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH---
      4. fw2_beats_bb9_champion  : beats 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH (Jacobzheng)
      5. fw2_beats_bb10_champion : beats 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ (Racheline) *)

From BB8 Require Import Individual92.
From BB8 Require Import BB9_fw2_1RB0RD BB9_fw2_bound.
From BB8 Require BB9_champion_1RB1RA BB9_champion_bound.
From BB8 Require BB9_record_1RB0RA BB9_record_bound BB9_record_vs_champion.
From BB8 Require BB9_redir_0LA BB9_redir_0LA_bound.
From BB8 Require BB9_redir_0LA_fh BB9_redir_0LA_fh_bound.
From BB8 Require Individual102 BB10_champion_1RB1RA BB10_champion_bound BB10_champion_upper.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

Module TM10 := Individual102.Individual102.Permute.Flip.Compute.TM.

Notation arrow := BB9_redir_0LA_fh.arrow.

Opaque U X Tv b1 b2 b3 f.
Opaque BB9_redir_0LA_fh.arrow BB9_redir_0LA.arrow BB9_record_1RB0RA.arrow.
Opaque BB9_redir_0LA_fh.U BB9_redir_0LA_fh.bf BB9_redir_0LA.U BB9_redir_0LA.bf.
Opaque BB9_record_1RB0RA.U BB9_record_1RB0RA.Bx BB9_record_bound.bp.
Opaque BB9_champion_bound.U BB9_champion_bound.X BB9_champion_bound.b1 BB9_champion_bound.b2.
Opaque BB10_champion_1RB1RA.U BB10_champion_1RB1RA.X BB10_champion_1RB1RA.Tv
  BB10_champion_1RB1RA.b1 BB10_champion_1RB1RA.b2.

(** ** Bridging up-arrows to the fast-growing hierarchy f *)

Lemma iter_fh_eq : forall n g x, BB9_redir_0LA_fh.iter n g x = iter n g x.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma arrow_0_2 : forall n, arrow 0 2 n = 2 * n.
Proof. Transparent BB9_redir_0LA_fh.arrow. reflexivity. Qed.
Opaque BB9_redir_0LA_fh.arrow.

Lemma arrow_0LA_agree : forall k a b, BB9_redir_0LA.arrow k a b = arrow k a b.
Proof.
  Transparent BB9_redir_0LA.arrow BB9_redir_0LA_fh.arrow.
  induction k; intros a b; [reflexivity |]. simpl.
  induction b; [reflexivity |]. simpl. rewrite IHb, IHk. reflexivity.
Qed.
Opaque BB9_redir_0LA.arrow BB9_redir_0LA_fh.arrow.

Lemma arrow_iter_mono : forall k n x y, x <= y -> iter n (arrow k 2) x <= iter n (arrow k 2) y.
Proof.
  intros. apply iter_mono_x; [intros; apply BB9_redir_0LA_fh.arrow_mono; assumption | assumption].
Qed.

Lemma f_arrow_ge : forall k n, 1 <= n -> arrow k 2 n <= f (S k) n.
Proof.
  induction k as [| k IH]; intros n Hn.
  - rewrite f1, arrow_0_2. lia.
  - rewrite f_S, BB9_redir_0LA_fh.arrow_S_iter, iter_fh_eq.
    assert (Hj : forall j, iter j (arrow k 2) n <= iter j (f (S k)) n).
    { induction j as [| j IHj]; [simpl; lia |]. cbn [iter].
      pose proof (iter_ge (f (S k)) (f_id (S k)) j n).
      pose proof (BB9_redir_0LA_fh.arrow_mono k _ _ IHj).
      pose proof (IH (iter j (f (S k)) n) ltac:(lia)). lia. }
    specialize (Hj n). pose proof (arrow_iter_mono k n 1 n Hn). lia.
Qed.

Lemma arrow_le_fo : forall k n m, 1 <= n -> S k <= m -> n <= m -> arrow k 2 n <= f_omega m.
Proof.
  intros k n m Hn Hk Hnm. unfold f_omega.
  pose proof (f_arrow_ge k n Hn) as H1.
  pose proof (f_level_mono (m - S k) (S k) n Hn) as H2.
  replace (m - S k + S k) with m in H2 by lia.
  pose proof (f_mono m n m Hnm) as H3.
  lia.
Qed.

Opaque f_omega.

Lemma arrow_2x : forall k n, 1 <= k -> 2 * arrow k 2 n <= arrow k 2 (S n).
Proof.
  intros [| k] n Hk; [lia |].
  rewrite BB9_redir_0LA_fh.arrow_SS. apply BB9_redir_0LA_fh.arrow_double.
Qed.

Lemma arrow_16x : forall k n, 1 <= k -> 16 * arrow k 2 n <= arrow k 2 (n + 4).
Proof.
  intros k n Hk.
  pose proof (arrow_2x k n Hk) as H1.
  pose proof (arrow_2x k (S n) Hk) as H2.
  pose proof (arrow_2x k (S (S n)) Hk) as H3.
  pose proof (arrow_2x k (S (S (S n))) Hk) as H4.
  replace (n + 4) with (S (S (S (S n)))) by lia. lia.
Qed.

(** ** 1. Beating BB9_redir_0LA_fh *)

Theorem fw2_beats_redir_0LA_fh :
  exists cfh Nfh c N,
    c0 -[ BB9_redir_0LA_fh.tm ]->* cfh /\ halted BB9_redir_0LA_fh.tm cfh /\ BB9_redir_0LA_fh_bound.ones cfh Nfh /\
    c0 -->* c /\ halted tm c /\ ones c N /\
    Nfh + 1 < N.
Proof.
  destruct BB9_redir_0LA_fh_bound.score_closed as [cfh [Nfh [H1 [H2 [H3 Hfh]]]]].
  destruct sigma_lower_bound as [c [N [H5 [H6 [H7 Hfw]]]]].
  exists cfh, Nfh, c, N.
  split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  split; [exact H5 | split; [exact H6 | split; [exact H7 |]]].
  pose proof (Nat.Div0.mul_div_le (12 * BB9_redir_0LA_fh.bf + 8) 5) as Hnn.
  change ((12 * BB9_redir_0LA_fh.bf + 8) / 5) with BB9_redir_0LA_fh_bound.nn in Hnn.
  pose proof (Nat.Div0.mul_div_le (BB9_redir_0LA_fh_bound.KK + 12 * BB9_redir_0LA_fh_bound.b3 - 2) 5) as Huu.
  change ((BB9_redir_0LA_fh_bound.KK + 12 * BB9_redir_0LA_fh_bound.b3 - 2) / 5) with BB9_redir_0LA_fh_bound.uu in Huu.
  pose proof BB9_redir_0LA_fh.bf_closed as Hbf.
  pose proof BB9_redir_0LA_fh_bound.KK_eq as HKK.
  pose proof BB9_redir_0LA_fh_bound.b4_closed as Hb4.
  pose proof BB9_redir_0LA_fh_bound.b4_big as Hb4_big.
  set (bf := BB9_redir_0LA_fh.bf) in *.
  set (nn := BB9_redir_0LA_fh_bound.nn) in *.
  set (KK := BB9_redir_0LA_fh_bound.KK) in *.
  set (b3f := BB9_redir_0LA_fh_bound.b3) in *.
  set (b4f := BB9_redir_0LA_fh_bound.b4) in *.
  set (uu := BB9_redir_0LA_fh_bound.uu) in *.
  clearbody bf nn KK b3f b4f uu.
  pose proof (BB9_redir_0LA_fh_bound.arrow_k3 (KK + 42)) as Hk3.
  pose proof (BB9_redir_0LA_fh.arrow_mono (KK + 42) 3 4 ltac:(lia)) as Hm34.
  assert (HNfh : Nfh + 2 <= 16 * arrow (KK + 42) 2 4) by lia.
  pose proof (arrow_16x (KK + 42) 4 ltac:(lia)) as H16. change (4 + 4) with 8 in H16.
  pose proof (arrow_le_fo (KK + 42) 8 (KK + 43) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfo1.
  pose proof (BB9_redir_0LA_fh_bound.arrow_k3 37) as H37_3.
  assert (HKK_le : KK + 43 <= 16 * arrow 37 2 3) by lia.
  pose proof (arrow_16x 37 3 ltac:(lia)) as H37_16. change (3 + 4) with 7 in H37_16.
  pose proof (arrow_le_fo 37 7 (465 * 1000 + 9) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfo2.
  assert (HKK_fo : KK + 43 <= f_omega (465 * 1000 + 9)) by lia.
  pose proof (f_omega_mono (KK + 43) (f_omega (465 * 1000 + 9)) ltac:(lia) HKK_fo) as Hfo_mono.
  lia.
Qed.

(** ** 2. Beating BB9_redir_0LA *)

Theorem fw2_beats_redir_0LA :
  exists co No c N,
    c0 -[ BB9_redir_0LA.tm ]->* co /\ halted BB9_redir_0LA.tm co /\ BB9_redir_0LA_bound.ones co No /\
    c0 -->* c /\ halted tm c /\ ones c N /\
    No + 1 < N.
Proof.
  destruct BB9_redir_0LA_bound.score_closed as [co [Ho1 [Ho2 Ho3]]].
  destruct sigma_lower_bound as [c [N [H1 [H2 [H3 Hfw]]]]].
  set (No := 3 * BB9_redir_0LA.arrow (BB9_redir_0LA_bound.KK + 2) 2 5 +
             10 * BB9_redir_0LA_bound.nn + 6 * (BB9_redir_0LA_bound.KK / 5) + 11) in *.
  exists co, No, c, N.
  split; [exact Ho1 | split; [exact Ho2 | split; [exact Ho3 |]]].
  split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  assert (HNo : No = 3 * arrow (BB9_redir_0LA_bound.KK + 2) 2 5 +
                     10 * BB9_redir_0LA_bound.nn + 6 * (BB9_redir_0LA_bound.KK / 5) + 11).
  { unfold No. rewrite arrow_0LA_agree. reflexivity. }
  clearbody No.
  pose proof BB9_redir_0LA.bf_closed as Hbf. rewrite arrow_0LA_agree in Hbf.
  pose proof BB9_redir_0LA_bound.KK_eq as HKK.
  pose proof (Nat.Div0.mul_div_le (12 * BB9_redir_0LA.bf + 8) 5) as Hnn.
  change ((12 * BB9_redir_0LA.bf + 8) / 5) with BB9_redir_0LA_bound.nn in Hnn.
  pose proof (Nat.Div0.mul_div_le BB9_redir_0LA_bound.KK 5) as HK5.
  set (bf := BB9_redir_0LA.bf) in *.
  set (nn := BB9_redir_0LA_bound.nn) in *.
  set (KK := BB9_redir_0LA_bound.KK) in *.
  set (K5 := KK / 5) in *.
  clearbody bf nn KK K5.
  pose proof (BB9_redir_0LA_fh_bound.arrow_k3 (KK + 2)) as Hk3.
  pose proof (BB9_redir_0LA_fh.arrow_mono (KK + 2) 3 5 ltac:(lia)) as Hm35.
  assert (HNo16 : No + 2 <= 16 * arrow (KK + 2) 2 5) by lia.
  pose proof (arrow_16x (KK + 2) 5 ltac:(lia)) as H16. change (5 + 4) with 9 in H16.
  pose proof (arrow_le_fo (KK + 2) 9 (KK + 9) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfo1.
  pose proof (BB9_redir_0LA_fh_bound.arrow_k3 37) as H37_3.
  assert (HKK_le : KK + 9 <= 16 * arrow 37 2 3) by lia.
  pose proof (arrow_16x 37 3 ltac:(lia)) as H37_16. change (3 + 4) with 7 in H37_16.
  pose proof (arrow_le_fo 37 7 (465 * 1000 + 9) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfo2.
  assert (HKK_fo : KK + 9 <= f_omega (465 * 1000 + 9)) by lia.
  pose proof (f_omega_mono (KK + 9) (f_omega (465 * 1000 + 9)) ltac:(lia) HKK_fo) as Hfo_mono.
  lia.
Qed.

(** ** 3. Beating BB9_record_1RB0RA *)

Theorem fw2_beats_record :
  exists cr Nr c N,
    c0 -[ BB9_record_1RB0RA.tm ]->* cr /\ halted BB9_record_1RB0RA.tm cr /\ BB9_record_bound.ones cr Nr /\
    c0 -->* c /\ halted tm c /\ ones c N /\
    Nr + 1 < N.
Proof.
  destruct BB9_record_bound.score_closed as [cr [Hr1 [Hr2 Hr3]]].
  destruct sigma_lower_bound as [c [N [H1 [H2 [H3 Hfw]]]]].
  set (Nr := 3 * BB9_record_1RB0RA.arrow (12 * BB9_record_1RB0RA.Bx - 9) 2 8 +
             108 * (BB9_record_1RB0RA.Bx / 5) + 70) in *.
  exists cr, Nr, c, N.
  split; [exact Hr1 | split; [exact Hr2 | split; [exact Hr3 |]]].
  split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  assert (HNr : Nr = 3 * arrow (12 * BB9_record_1RB0RA.Bx - 9) 2 8 +
                     108 * (BB9_record_1RB0RA.Bx / 5) + 70).
  { unfold Nr. rewrite BB9_redir_0LA_fh_bound.arrow_agree. reflexivity. }
  clearbody Nr.
  pose proof BB9_record_bound.Bx_arrow13 as HBx. rewrite BB9_redir_0LA_fh_bound.arrow_agree in HBx.
  pose proof (Nat.Div0.mul_div_le BB9_record_1RB0RA.Bx 5) as HBx5.
  set (Bx := BB9_record_1RB0RA.Bx) in *.
  set (Bx5 := Bx / 5) in *.
  clearbody Bx Bx5.
  pose proof (BB9_redir_0LA_fh_bound.arrow_k3 13) as H13_3.
  pose proof (BB9_redir_0LA_fh_bound.arrow_k3 (12 * Bx - 9)) as Hk3.
  pose proof (BB9_redir_0LA_fh.arrow_mono (12 * Bx - 9) 3 8 ltac:(lia)) as Hm38.
  assert (HNr16 : Nr + 2 <= 16 * arrow (12 * Bx - 9) 2 8) by lia.
  pose proof (arrow_16x (12 * Bx - 9) 8 ltac:(lia)) as H16. change (8 + 4) with 12 in H16.
  pose proof (arrow_le_fo (12 * Bx - 9) 12 (12 * Bx) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfo1.
  assert (HBx_le : 12 * Bx <= 16 * arrow 13 2 3) by lia.
  pose proof (arrow_16x 13 3 ltac:(lia)) as H13_16. change (3 + 4) with 7 in H13_16.
  pose proof (arrow_le_fo 13 7 (465 * 1000 + 9) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfo2.
  assert (HBx_fo : 12 * Bx <= f_omega (465 * 1000 + 9)) by lia.
  pose proof (f_omega_mono (12 * Bx) (f_omega (465 * 1000 + 9)) ltac:(lia) HBx_fo) as Hfo_mono.
  lia.
Qed.

(** ** 4. Beating the 9-state champion BB9_champion_1RB1RA *)

Theorem fw2_beats_bb9_champion :
  exists cc Nc c N,
    c0 -[ BB9_champion_1RB1RA.tm ]->* cc /\ halted BB9_champion_1RB1RA.tm cc /\ BB9_champion_bound.ones cc Nc /\
    c0 -->* c /\ halted tm c /\ ones c N /\
    Nc + 1 < N + 1.
Proof.
  destruct BB9_champion_bound.score_exact as [cc [H1 [H2 H3]]].
  destruct sigma_lower_bound as [c [N [H4 [H5 [H6 Hfw]]]]].
  exists cc, (BB9_champion_bound.b2 + 3), c, N.
  split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  split; [exact H4 | split; [exact H5 | split; [exact H6 |]]].
  pose proof BB9_record_vs_champion.b1_le as Hb1.
  pose proof BB9_record_vs_champion.b2_le as Hb2.
  rewrite BB9_redir_0LA_fh_bound.arrow_agree in Hb1, Hb2.
  set (b1c := BB9_champion_bound.b1) in *.
  set (b2c := BB9_champion_bound.b2) in *.
  clearbody b1c b2c.
  pose proof (BB9_redir_0LA_fh_bound.arrow_k3 10) as H10_3.
  pose proof (BB9_redir_0LA_fh.arrow_mono 10 3 11 ltac:(lia)) as Hm10.
  pose proof (arrow_2x 10 11 ltac:(lia)) as H2x10.
  pose proof (arrow_le_fo 10 12 (465 * 1000 + 9) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfo1.
  assert (Hb1_fo : b1c + 7 <= f_omega (465 * 1000 + 9)) by lia.
  pose proof (BB9_redir_0LA_fh_bound.arrow_k3 (b1c + 4)) as Hk3.
  pose proof (BB9_redir_0LA_fh.arrow_mono (b1c + 4) 3 (b1c + 6) ltac:(lia)) as Hm6.
  pose proof (arrow_2x (b1c + 4) (b1c + 6) ltac:(lia)) as H2x.
  replace (S (b1c + 6)) with (b1c + 7) in H2x by lia.
  pose proof (arrow_le_fo (b1c + 4) (b1c + 7) (b1c + 7) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfo2.
  pose proof (f_omega_mono (b1c + 7) (f_omega (465 * 1000 + 9)) ltac:(lia) Hb1_fo) as Hfo_mono.
  lia.
Qed.

(** ** 5. Beating the 10-state champion BB10_champion_1RB1RA *)

Theorem fw2_beats_bb10_champion :
  exists c10 N10 c9 N9,
    TM10.evstep BB10_champion_1RB1RA.tm TM10.c0 c10 /\
    TM10.halted BB10_champion_1RB1RA.tm c10 /\
    BB10_champion_bound.ones c10 N10 /\
    c0 -->* c9 /\ halted tm c9 /\ ones c9 N9 /\
    N10 + 1 < N9 + 1.
Proof.
  destruct BB10_champion_upper.champion_upper_ex as [Np [HNp4 [HNp_le [c10 [N10 [H1 [H2 [H3 HN10]]]]]]]].
  destruct sigma_lower_bound as [c9 [N9 [H4 [H5 [H6 Hfw]]]]].
  exists c10, N10, c9, N9.
  split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  split; [exact H4 | split; [exact H5 | split; [exact H6 |]]].
  rewrite BB9_redir_0LA_fh_bound.arrow_agree in HNp_le, HN10.
  pose proof (arrow_2x 25 49 ltac:(lia)) as H2x.
  pose proof (arrow_le_fo 25 50 (465 * 1000 + 9) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfo1.
  assert (H2Np : 2 * Np <= f_omega (465 * 1000 + 9)) by lia.
  pose proof (arrow_le_fo Np (2 * Np) (2 * Np) ltac:(lia) ltac:(lia) ltac:(lia)) as Hfo2.
  pose proof (f_omega_mono (2 * Np) (f_omega (465 * 1000 + 9)) ltac:(lia) H2Np) as Hfo_mono.
  lia.
Qed.

Print Assumptions fw2_beats_redir_0LA_fh.
Print Assumptions fw2_beats_redir_0LA.
Print Assumptions fw2_beats_record.
Print Assumptions fw2_beats_bb9_champion.
Print Assumptions fw2_beats_bb10_champion.
