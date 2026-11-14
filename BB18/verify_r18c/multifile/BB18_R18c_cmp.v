(** * R18c (BB18_R18c.v) beats the EXACT score of J18_w2_C (BB18_J18_w2_C_tnf.v), the previous BB(18) entry.

    J18_w2_C's halting tape holds exactly NJ = 2j + 2 ones, for the k, a2, j of its [score_exact]
    (hoc 0 2 10 + 6 = 3(k + 2), a2 = (ho k)^3 (hoc 0 k 10), a2 + 2(k + 1) + 2 = 3j + 2); its halt O0 is read on a 0,
    so sigma(J18_w2_C) = NJ + 1.  R18c halts on R1, read on a 1, so sigma(R18c) = N.  Proved here:

      beats_J18C_exact : R18c halts with N ones and NJ + 1 < N for every k, a2, j satisfying J18_w2_C's equations;
      beats_J18C_score : exists NJ, J18_w2_C's halting tape holds NJ ones and R18c's holds N > NJ + 1.

    Method: the generic upper bounds of JZ_UB.v (written here) for J18_w2_C's own definitions h, hc, G, ho, hoc give
    NJ + 1 <= f_w2 (k + 30) and k + 30 <= f_wk 1 (f 4 2), while R18c's [sigma_lower_bound] gives
    f_w2 (f_wk 1 (f 4 2)) < N.  The three files define iter, f, f_omega, f_wk, f_w2 with the same text; the
    equalities used to move between them are proved below for all arguments. *)

From BB8 Require Import Individual182.
From BB8 Require BB18_J18_w2_C_tnf BB18_R18c BB17_J17_w2_champ JZ_UB.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.

Module J := BB18_J18_w2_C_tnf.
Module R := BB18_R18c.
Module U := JZ_UB.
(* JZ_UB's hierarchy is never unfolded here (closed instances must not be reduced): only its equations are used *)
Opaque U.iter U.f U.f_omega U.f_wk U.f_w2.
(* the main files make the hierarchy opaque at their end; the equalities below unfold it for variables only *)
Transparent R.f R.f_omega R.f_wk R.f_w2.

(** ** The three files' hierarchies agree *)
Lemma J_iter : forall {X : Type} n (g : X -> X) x, J.iter n g x = U.iter n g x.
Proof. induction n; intros; [rewrite U.iter_0; reflexivity | rewrite U.iter_S1, <- IHn; reflexivity]. Qed.

Lemma R_iter : forall {X : Type} n (g : X -> X) x, R.iter n g x = U.iter n g x.
Proof. induction n; intros; [rewrite U.iter_0; reflexivity | rewrite U.iter_S1, <- IHn; reflexivity]. Qed.

Lemma R_f : forall k n, R.f k n = U.f k n.
Proof.
  induction k as [| k IH]; intros n; [reflexivity |].
  rewrite R.f_S, U.f_S, R_iter. apply U.iter_ext. exact IH.
Qed.

Lemma R_f_omega : forall n, R.f_omega n = U.f_omega n.
Proof. intros n. rewrite R.f_omega_eq, U.f_omega_eq. apply R_f. Qed.

Lemma R_f_wk : forall k n, R.f_wk k n = U.f_wk k n.
Proof.
  induction k as [| k IH]; intros n.
  - rewrite R.f_wk_0, U.f_wk_0. apply R_f_omega.
  - rewrite R.f_wk_S, U.f_wk_S, R_iter. apply U.iter_ext. exact IH.
Qed.

Lemma R_f_w2 : forall n, R.f_w2 n = U.f_w2 n.
Proof. intros n. rewrite R.f_w2_eq, U.f_w2_eq. apply R_f_wk. Qed.

(** ** J18_w2_C's level maps satisfy the hypotheses of JZ_UB *)
Lemma J_h_S : forall m x, J.h (S m) x = U.iter (x + 2) (J.h m) 2.
Proof. intros. rewrite J.h_S, J_iter. reflexivity. Qed.

Lemma J_ho_S : forall m a, J.ho (S m) a = U.iter (a + 1) (J.ho m) 6.
Proof. intros. rewrite J.ho_S, J_iter. reflexivity. Qed.

Lemma J_hc_ub : forall n m x, J.hc m n x + 4 <= U.f_omega (m + n + x + 5).
Proof. exact (U.hc_ub J.h J.h_0 J_h_S J.hc J.hc_0 J.hc_S). Qed.

Lemma J_G0_ub : forall c, J.G0 c + 22 <= U.f_omega (c + 13).
Proof.
  intros c. rewrite J.G0_eq.
  pose proof (J_hc_ub c 1 6) as Hc.
  pose proof (U.f_omega_ge2 (1 + c + 6 + 5) ltac:(lia)) as H2.
  pose proof (U.f_omega_dbl (1 + c + 6 + 5) ltac:(lia)) as H3.
  replace (S (1 + c + 6 + 5)) with (c + 13) in H3 by lia. lia.
Qed.

Lemma J_G_ub : forall a, J.G a + 20 <= U.f_omega (a + 20).
Proof.
  intros a.
  pose proof (Nat.div_mod a 3 ltac:(lia)) as Ha. pose proof (Nat.mod_upper_bound a 3 ltac:(lia)) as Hy.
  remember (a / 3) as c eqn:Ec. remember (a mod 3) as y eqn:Ey. clear Ec Ey. subst a.
  destruct y as [| [| [| y]]]; [| | | lia].
  - replace (3 * c + 0) with (3 * c) by lia. rewrite J.G_cy0.
    pose proof (J_G0_ub c). pose proof (U.f_omega_mono (c + 13) (3 * c + 20) ltac:(lia)). lia.
  - rewrite J.G_cy1. pose proof (U.f_omega_ge2 (3 * c + 1 + 20) ltac:(lia)). lia.
  - rewrite J.G_cy2.
    pose proof (J_G0_ub c). pose proof (U.f_omega_mono (c + 13) (3 * c + 2 + 20) ltac:(lia)). lia.
Qed.

Lemma J_ho_ub : forall m a, J.ho m a + 20 <= U.f_wk m (a + 20).
Proof. exact (U.ho_ub J.G 6 J.ho J_G_ub ltac:(lia) J.ho_0 J_ho_S). Qed.

Lemma J_hoc_ub : forall n m a, J.hoc m n a + 20 <= U.f_wk (S (m + n)) (n + a + 20).
Proof. exact (U.hoc_ub J.G 6 J.ho J_G_ub ltac:(lia) J.ho_0 J_ho_S J.hoc J.hoc_0 J.hoc_S). Qed.

Lemma J_iter_ho_ub : forall p m a, U.iter p (J.ho m) a + 20 <= U.f_wk (S m) (p + a + 20).
Proof. exact (U.iter_ho_ub J.G 6 J.ho J_G_ub ltac:(lia) J.ho_0 J_ho_S). Qed.

(** ** J18_w2_C's exact count, from above *)

(** a value plus a small constant is at most one more step of f_wk *)
Lemma absorb : forall K c y, c <= y -> 1 <= y -> y + c <= U.f_wk K y.
Proof. intros K c y Hc Hy. pose proof (U.f_wk_ge2 K y Hy). lia. Qed.

Lemma J18C_count_ub : forall k a2 j,
  a2 = J.iter 3 (J.ho k) (J.hoc 0 k 10) ->
  a2 + 2 * S k + 2 = 3 * j + 2 ->
  2 * j + 2 + 1 <= U.f_w2 (k + 30).
Proof.
  intros k a2 j Ha2 Hj. rewrite J_iter in Ha2.
  pose proof (J_hoc_ub k 0 10) as Hb. replace (S (0 + k)) with (S k) in Hb by lia.
  replace (k + 10 + 20) with (k + 30) in Hb by lia.
  pose proof (J_iter_ho_ub 3 k (J.hoc 0 k 10)) as Ha. rewrite <- Ha2 in Ha.
  remember (J.hoc 0 k 10) as b eqn:Eb. clear Eb.
  pose proof (U.f_wk_ge2 (S k) (k + 30) ltac:(lia)) as G1.
  pose proof (U.iter_wk_le (S k) 4 (k + 30) (k + 30) ltac:(lia) ltac:(lia)) as H4.
  rewrite !U.iter_S1, U.iter_0 in H4.
  remember (U.f_wk (S k) (k + 30)) as X eqn:EX.
  (* X = f_wk (S k) (k + 30) >= b + 20;  a2 + 20 <= f_wk (S k) (3 + b + 20) <= W = f_wk (S k) (f_wk (S k) X) *)
  pose proof (absorb (S k) 3 X ltac:(lia) ltac:(lia)) as HX3.
  pose proof (U.f_wk_mono (S k) (3 + b + 20) (U.f_wk (S k) X) ltac:(lia)) as H1.
  pose proof (U.f_wk_ge2 (S k) X ltac:(lia)) as G2.
  pose proof (U.f_wk_ge2 (S k) (U.f_wk (S k) X) ltac:(lia)) as G3.
  pose proof (absorb (S k) (2 * k + 5) (U.f_wk (S k) (U.f_wk (S k) X)) ltac:(lia) ltac:(lia)) as HW2.
  (* f_wk (S k) W = iter 4 (f_wk (S k)) (k + 30) <= f_wk (S (S k)) (k + 30) <= f_w2 (k + 30) *)
  pose proof (U.f_wk_le_w2 (S (S k)) (k + 30) ltac:(lia) ltac:(lia)) as H5.
  lia.
Qed.

Lemma J18C_k_ub : forall k, J.hoc 0 2 10 + 6 = 3 * S (S k) -> k + 30 <= U.f_wk 1 (U.f 4 2).
Proof.
  intros k Hk.
  rewrite J.hoc_S, J.hoc_S, J.hoc_0, J.ho_0, J.G10_eq in Hk.
  pose proof (J_ho_ub 1 14) as H1. replace (14 + 20) with 34 in H1 by lia.
  pose proof (U.f_wk_id 1 34) as HY.
  (* f_wk 0 (f_wk 1 34) = f_wk 0 (iter 34 (f_wk 0) 34) = iter 35 (f_wk 0) 34 <= f_wk 1 64 <= f_wk 1 (f 4 2) *)
  pose proof (U.iter_wk_le 0 35 34 64 ltac:(lia) ltac:(lia)) as H3.
  rewrite U.iter_S1 in H3.
  assert (HY34 : U.iter 34 (U.f_wk 0) 34 = U.f_wk 1 34) by (rewrite U.f_wk_S; reflexivity).
  rewrite HY34 in H3.
  remember (U.f_wk 1 34) as Y eqn:EY.
  pose proof (absorb 0 14 Y ltac:(lia) ltac:(lia)) as H2.
  pose proof R.f4_2_ge as H64. rewrite R_f in H64.
  pose proof (U.f_wk_mono 1 64 (U.f 4 2) H64) as H4.
  lia.
Qed.

(** ** The comparisons *)
Theorem beats_J18C_exact : exists c N, c0 -[ R.tm ]->* c /\ halted R.tm c /\ R.ones c N /\
  forall k a2 j,
    J.hoc 0 2 10 + 6 = 3 * S (S k) ->
    a2 = J.iter 3 (J.ho k) (J.hoc 0 k 10) ->
    a2 + 2 * S k + 2 = 3 * j + 2 ->
    2 * j + 2 + 1 < N.
Proof.
  destruct R.sigma_lower_bound as (c & N & Hrun & Hhalt & Hones & _ & HB).
  rewrite R_f, R_f_wk, R_f_w2 in HB.
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  intros k a2 j Hk Ha2 Hj.
  pose proof (J18C_count_ub k a2 j Ha2 Hj) as H1.
  pose proof (J18C_k_ub k Hk) as H2.
  pose proof (U.f_w2_mono (k + 30) (U.f_wk 1 (U.f 4 2)) H2) as H3.
  exact (Nat.le_lt_trans _ _ _ (Nat.le_trans _ _ _ H1 H3) HB).
Qed.

Theorem beats_J18C_score : exists NJ,
  (exists c, c0 -[ J.tm ]->* c /\ halted J.tm c /\ J.ones c NJ) /\
  exists c N, c0 -[ R.tm ]->* c /\ halted R.tm c /\ R.ones c N /\ NJ + 1 < N.
Proof.
  destruct J.score_exact as (k & a2 & j & cJ & Hk & Ha2 & Hj & HrunJ & HhaltJ & HonesJ).
  destruct beats_J18C_exact as (c & N & Hrun & Hhalt & Hones & HB).
  exists (2 * j + 2). split; [exists cJ; auto |].
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  exact (HB k a2 j Hk Ha2 Hj).
Qed.

(** ** J17_champ (BB17_J17_w2_champ.v, BB(17)): R18c beats BB(17) + 1 against J17_champ's EXACT score.

    J17_champ's halting tape holds exactly NK = 2j + 4 ones, for the q1, k1, a2, j of its [score_exact]
    (iter 5 G 4 + 6 = 9(q1 + 1) + 1, k1 = 3 q1 + 1, a2 = hoc 1 (k1 + 1) 4, a2 + 6(q1 + 1) + 2 = 3(j + 2)); its halt O0
    is read on a 0, so sigma(J17_champ) = NK + 1 and BB(18) >= BB(17) + 1 gives sigma NK + 2.  Proved:

      beats_J17_exact : R18c halts with N ones and NK + 2 < N, i.e. sigma(R18c) = N > sigma(J17_champ) + 1.

    J17_champ's engine is the same as J18_w2_C's except its head map G a = hc 0 (a/3 + 1) 2 + 2(a/3 + 1) + 2 and
    the reset value 4 of its outer level maps. *)
Module K := BB17_J17_w2_champ.

Lemma K_iter : forall {X : Type} n (g : X -> X) x, K.iter n g x = U.iter n g x.
Proof. induction n; intros; [rewrite U.iter_0; reflexivity | rewrite U.iter_S1, <- IHn; reflexivity]. Qed.

Lemma K_h_S : forall m x, K.h (S m) x = U.iter (x + 2) (K.h m) 2.
Proof. intros. rewrite K.h_S, K_iter. reflexivity. Qed.

Lemma K_ho_S : forall m a, K.ho (S m) a = U.iter (a + 1) (K.ho m) 4.
Proof. intros. rewrite K.ho_S, K_iter. reflexivity. Qed.

Lemma K_hc_ub : forall n m x, K.hc m n x + 4 <= U.f_omega (m + n + x + 5).
Proof. exact (U.hc_ub K.h K.h_0 K_h_S K.hc K.hc_0 K.hc_S). Qed.

Lemma K_G_ub : forall a, K.G a + 20 <= U.f_omega (a + 20).
Proof.
  intros a. rewrite K.G_eq.
  pose proof (Nat.div_mod a 3 ltac:(lia)) as Ha.
  remember (a / 3) as c eqn:Ec. clear Ec.
  pose proof (K_hc_ub (S c) 0 2) as Hc.
  pose proof (U.f_omega_ge2 (0 + S c + 2 + 5) ltac:(lia)) as H1.
  pose proof (U.f_omega_dbl (0 + S c + 2 + 5) ltac:(lia)) as H2.
  pose proof (U.f_omega_dbl (S (0 + S c + 2 + 5)) ltac:(lia)) as H3.
  pose proof (U.f_omega_mono (S (S (0 + S c + 2 + 5))) (a + 20) ltac:(lia)) as H4.
  lia.
Qed.

Lemma K_hoc_ub : forall n m a, K.hoc m n a + 20 <= U.f_wk (S (m + n)) (n + a + 20).
Proof. exact (U.hoc_ub K.G 4 K.ho K_G_ub ltac:(lia) K.ho_0 K_ho_S K.hoc K.hoc_0 K.hoc_S). Qed.

Lemma K_iter_ho_ub : forall p m a, U.iter p (K.ho m) a + 20 <= U.f_wk (S m) (p + a + 20).
Proof. exact (U.iter_ho_ub K.G 4 K.ho K_G_ub ltac:(lia) K.ho_0 K_ho_S). Qed.

Lemma J17_count_ub : forall q1 k1 a2 j,
  k1 = 3 * q1 + 1 ->
  a2 = K.hoc 1 (S k1) 4 ->
  a2 + 2 * (3 * S q1) + 2 = 3 * S (S j) ->
  2 * j + 4 + 2 <= U.f_w2 (k1 + 25).
Proof.
  intros q1 k1 a2 j Hk1 Ha2 Hj.
  pose proof (K_hoc_ub (S k1) 1 4) as Ha. rewrite <- Ha2 in Ha.
  replace (S (1 + S k1)) with (S (S (S k1))) in Ha by lia.
  replace (S k1 + 4 + 20) with (k1 + 25) in Ha by lia.
  pose proof (U.f_wk_ge2 (S (S (S k1))) (k1 + 25) ltac:(lia)) as G1.
  pose proof (absorb (S (S (S k1))) (2 * k1) (U.f_wk (S (S (S k1))) (k1 + 25)) ltac:(lia) ltac:(lia)) as HX.
  pose proof (U.iter_wk_le (S (S (S k1))) 2 (k1 + 25) (k1 + 25) ltac:(lia) ltac:(lia)) as H2.
  rewrite !U.iter_S1, U.iter_0 in H2.
  pose proof (U.f_wk_le_w2 (S (S (S (S k1)))) (k1 + 25) ltac:(lia) ltac:(lia)) as H3.
  lia.
Qed.

Lemma J17_k_ub : forall q1 k1, K.iter 5 K.G 4 + 6 = 9 * S q1 + 1 -> k1 = 3 * q1 + 1 ->
  k1 + 25 <= U.f_wk 1 (U.f 4 2).
Proof.
  intros q1 k1 Hq Hk1.
  rewrite <- K.iter_ho0_G, K_iter in Hq.
  pose proof (K_iter_ho_ub 5 0 4) as H1. replace (5 + 4 + 20) with 29 in H1 by lia.
  pose proof (U.f_wk_id 1 29) as HY.
  pose proof (U.iter_wk_le 0 30 29 64 ltac:(lia) ltac:(lia)) as H3.
  rewrite U.iter_S1 in H3.
  assert (HY29 : U.iter 29 (U.f_wk 0) 29 = U.f_wk 1 29) by (rewrite U.f_wk_S; reflexivity).
  rewrite HY29 in H3.
  remember (U.f_wk 1 29) as Y eqn:EY.
  pose proof (absorb 0 5 Y ltac:(lia) ltac:(lia)) as H2.
  pose proof R.f4_2_ge as H64. rewrite R_f in H64.
  pose proof (U.f_wk_mono 1 64 (U.f 4 2) H64) as H4.
  lia.
Qed.

Theorem beats_J17_exact : exists c N, c0 -[ R.tm ]->* c /\ halted R.tm c /\ R.ones c N /\
  forall q1 k1 a2 j,
    K.iter 5 K.G 4 + 6 = 9 * S q1 + 1 ->
    k1 = 3 * q1 + 1 ->
    a2 = K.hoc 1 (S k1) 4 ->
    a2 + 2 * (3 * S q1) + 2 = 3 * S (S j) ->
    2 * j + 4 + 2 < N.
Proof.
  destruct R.sigma_lower_bound as (c & N & Hrun & Hhalt & Hones & _ & HB).
  rewrite R_f, R_f_wk, R_f_w2 in HB.
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  intros q1 k1 a2 j Hq Hk1 Ha2 Hj.
  pose proof (J17_count_ub q1 k1 a2 j Hk1 Ha2 Hj) as H1.
  pose proof (J17_k_ub q1 k1 Hq Hk1) as H2.
  pose proof (U.f_w2_mono _ _ H2) as H3.
  exact (Nat.le_lt_trans _ _ _ (Nat.le_trans _ _ _ H1 H3) HB).
Qed.

Theorem beats_J17_score : exists NK,
  (exists c, Individual172.Individual172.Permute.Flip.Compute.TM.evstep K.tm
               Individual172.Individual172.Permute.Flip.Compute.TM.c0 c /\
             Individual172.Individual172.Permute.Flip.Compute.TM.halted K.tm c /\
             K.ones c NK) /\
  exists c N, c0 -[ R.tm ]->* c /\ halted R.tm c /\ R.ones c N /\ NK + 2 < N.
Proof.
  destruct K.score_exact as (q1 & k1 & a2 & j & cK & Hq & Hk1 & Ha2 & Hj & HrunK & HhaltK & HonesK).
  destruct beats_J17_exact as (c & N & Hrun & Hhalt & Hones & HB).
  exists (2 * j + 4). split; [exists cK; auto |].
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  exact (HB q1 k1 a2 j Hq Hk1 Ha2 Hj).
Qed.
