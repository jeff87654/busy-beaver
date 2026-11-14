(** * J19_sq (BB19_J19_w2_sq.v) beats the EXACT scores of R18c + 1 (BB18_R18c.v, BB(18) + 1) and of J20
      (BB20_JZ20.v, Jacobzheng's 20-state machine, the BB(20) entry before J20_cube).

    J19_sq halts reading a 0 (S0), so sigma(J19_sq) = N + 1.
    - R18c's halting tape holds exactly NR = 2(j + 1) + 1 ones, for the a1, k1, b0, a2, j of its [score_exact]; it halts
      reading a 1, so sigma(R18c) = NR and BB(18) + 1 gives a 19-state machine with sigma NR + 1.
        beats_R18c_exact / beats_R18c_score : NR < N, i.e. sigma(J19_sq) = N + 1 > NR + 1.
    - J20's halting tape holds exactly NZ = 2j + 1 ones, for the k, a2, j of its [score_exact]; it halts reading a 0,
      so sigma(J20) = NZ + 1.
        beats_J20_exact / beats_J20_score : NZ < N, i.e. sigma(J19_sq) > sigma(J20).

    Method: the generic upper bounds of JZ_UB.v for R18c's and J20's own definitions h, hc, G, ho, hoc give
    NR + 1 <= f_w2 Z and NZ + 1 <= f_w2 Z' with Z, Z' <= f_w2 (f 5 2), while J19_sq's [sigma_lower_bound] gives
    f_w2 (f_w2 (f 5 2)) < N.  The files define iter, f, f_omega, f_wk, f_w2 with the same text; the equalities used to
    move between them are proved below for all arguments. *)

From BB8 Require Import Individual192.
From BB8 Require BB18_R18c BB20_JZ20 BB19_J19_w2_sq JZ_UB.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.

Module R := BB18_R18c.
Module Z := BB20_JZ20.
Module Q := BB19_J19_w2_sq.
Module U := JZ_UB.
(* JZ_UB's hierarchy is never unfolded here (closed instances must not be reduced): only its equations are used *)
Opaque U.iter U.f U.f_omega U.f_wk U.f_w2.
(* the main files make the hierarchy opaque at their end; the equalities below unfold it for variables only *)
Transparent Q.f Q.f_omega Q.f_wk Q.f_w2.

Lemma absorb : forall K c y, c <= y -> 1 <= y -> y + c <= U.f_wk K y.
Proof. intros K c y Hc Hy. pose proof (U.f_wk_ge2 K y Hy). lia. Qed.

(** ** J19_sq's hierarchy is JZ_UB's *)
Lemma Q_iter : forall {X : Type} n (g : X -> X) x, Q.iter n g x = U.iter n g x.
Proof. induction n; intros; [rewrite U.iter_0; reflexivity | rewrite U.iter_S1, <- IHn; reflexivity]. Qed.

Lemma Q_f : forall k n, Q.f k n = U.f k n.
Proof.
  induction k as [| k IH]; intros n; [reflexivity |].
  rewrite Q.f_S, U.f_S, Q_iter. apply U.iter_ext. exact IH.
Qed.

Lemma Q_f_omega : forall n, Q.f_omega n = U.f_omega n.
Proof. intros n. rewrite Q.f_omega_eq, U.f_omega_eq. apply Q_f. Qed.

Lemma Q_f_wk : forall k n, Q.f_wk k n = U.f_wk k n.
Proof.
  induction k as [| k IH]; intros n.
  - rewrite Q.f_wk_0, U.f_wk_0. apply Q_f_omega.
  - rewrite Q.f_wk_S, U.f_wk_S, Q_iter. apply U.iter_ext. exact IH.
Qed.

Lemma Q_f_w2 : forall n, Q.f_w2 n = U.f_w2 n.
Proof. intros n. rewrite Q.f_w2_eq, U.f_w2_eq. apply Q_f_wk. Qed.

Lemma Q_bound : exists c N, c0 -[ Q.tm ]->* c /\ halted Q.tm c /\ Q.ones c N /\
  U.f_w2 (U.f_w2 (U.f 5 2)) < N.
Proof.
  destruct Q.sigma_lower_bound as (c & N & Hrun & Hhalt & Hones & HB & _).
  rewrite Q_f, Q_iter, (U.iter_ext Q.f_w2 U.f_w2 Q_f_w2), !U.iter_S1, U.iter_0 in HB.
  exists c, N. auto.
Qed.

Lemma f52 : 64 <= U.f 5 2.
Proof. pose proof Q.f5_2_ge as H. rewrite Q_f in H. exact H. Qed.

(** small arithmetic side conditions, proved without any hypothesis in the context *)
Lemma side_30 : forall k, k + 10 + 20 <= k + 30.  Proof. intros; lia. Qed.
Lemma side_31 : forall k, S k + 10 + 20 <= k + 31.  Proof. intros; lia. Qed.
Lemma side_21 : forall k b, S k + b + 20 <= k + b + 21.  Proof. intros; lia. Qed.
Lemma side_k30 : forall k, k + 1 + 20 <= k + 30.  Proof. intros; lia. Qed.

Lemma small_le_Tz : forall K y z, K <= 64 -> y <= 64 -> 64 <= z -> U.f_wk K y <= U.f_w2 z.
Proof.
  intros K y z HK Hy Hz.
  pose proof (U.f_wk_mono K y z ltac:(lia)).
  pose proof (U.f_wk_le_w2 K z ltac:(lia) ltac:(lia)). lia.
Qed.

(** ** R18c's level maps *)
Lemma R_iter : forall {X : Type} n (g : X -> X) x, R.iter n g x = U.iter n g x.
Proof. induction n; intros; [rewrite U.iter_0; reflexivity | rewrite U.iter_S1, <- IHn; reflexivity]. Qed.

Lemma R_h_S : forall m x, R.h (S m) x = U.iter (x + 2) (R.h m) 2.
Proof. intros. rewrite R.h_S, R_iter. reflexivity. Qed.

Lemma R_ho_S : forall m a, R.ho (S m) a = U.iter (a + 1) (R.ho m) 15.
Proof. intros. rewrite R.ho_S, R_iter. reflexivity. Qed.

Lemma R_hc_ub : forall n m x, R.hc m n x + 4 <= U.f_omega (m + n + x + 5).
Proof. exact (U.hc_ub R.h R.h_0 R_h_S R.hc R.hc_0 R.hc_S). Qed.

Lemma R_Gcy0 : forall c, R.Gcy (S c) 0 = R.hc 1 c 6 + 2 * c + 4.  Proof. reflexivity. Qed.
Lemma R_Gcy1 : forall c, R.Gcy c 1 = R.hc 1 (S c) 7 + 2 * S c + 4.  Proof. reflexivity. Qed.
Lemma R_Gcy2 : forall c, R.Gcy c 2 = R.hc 1 (S c) 11 + 2 * S c + 4.  Proof. reflexivity. Qed.

(** hc 1 n x + 2n + 26 <= f_omega (n + x + 21)  (n + x + 6 <= ... with two doublings) *)
Lemma R_hc1_ub : forall n x, R.hc 1 n x + 2 * n + 26 <= U.f_omega (n + x + 8).
Proof.
  intros n x. pose proof (R_hc_ub n 1 x) as Hc.
  pose proof (U.f_omega_ge2 (1 + n + x + 5) ltac:(lia)) as H1.
  pose proof (U.f_omega_dbl (1 + n + x + 5) ltac:(lia)) as H2.
  pose proof (U.f_omega_dbl (S (1 + n + x + 5)) ltac:(lia)) as H3.
  replace (S (S (1 + n + x + 5))) with (n + x + 8) in H3 by lia. lia.
Qed.

Lemma R_G_ub : forall a, R.G a + 20 <= U.f_omega (a + 20).
Proof.
  intros a.
  pose proof (Nat.div_mod a 3 ltac:(lia)) as Ha. pose proof (Nat.mod_upper_bound a 3 ltac:(lia)) as Hy.
  remember (a / 3) as c eqn:Ec. remember (a mod 3) as y eqn:Ey. clear Ec Ey. subst a.
  rewrite (R.G_cy c y Hy).
  destruct y as [| [| [| y]]]; [| | | lia].
  - destruct c as [| c].
    + replace (R.Gcy 0 0) with 4 by reflexivity. pose proof (U.f_omega_ge2 (3 * 0 + 0 + 20) ltac:(lia)). lia.
    + rewrite R_Gcy0. pose proof (R_hc1_ub c 6).
      pose proof (U.f_omega_mono (c + 6 + 8) (3 * S c + 0 + 20) ltac:(lia)). lia.
  - rewrite R_Gcy1. pose proof (R_hc1_ub (S c) 7).
    pose proof (U.f_omega_mono (S c + 7 + 8) (3 * c + 1 + 20) ltac:(lia)). lia.
  - rewrite R_Gcy2. pose proof (R_hc1_ub (S c) 11).
    pose proof (U.f_omega_mono (S c + 11 + 8) (3 * c + 2 + 20) ltac:(lia)). lia.
Qed.

Lemma R_ho_ub : forall m a, R.ho m a + 20 <= U.f_wk m (a + 20).
Proof. exact (U.ho_ub R.G 15 R.ho R_G_ub ltac:(lia) R.ho_0 R_ho_S). Qed.

Lemma R_hoc_ub : forall n m a, R.hoc m n a + 20 <= U.f_wk (S (m + n)) (n + a + 20).
Proof. exact (U.hoc_ub R.G 15 R.ho R_G_ub ltac:(lia) R.ho_0 R_ho_S R.hoc R.hoc_0 R.hoc_S). Qed.

Lemma R_iter_ho_ub : forall p m a, U.iter p (R.ho m) a + 20 <= U.f_wk (S m) (p + a + 20).
Proof. exact (U.iter_ho_ub R.G 15 R.ho R_G_ub ltac:(lia) R.ho_0 R_ho_S). Qed.

Lemma R_hoc_ub_le : forall n m a K z, S (m + n) <= K -> n + a + 20 <= z -> R.hoc m n a + 20 <= U.f_wk K z.
Proof. exact (U.hoc_ub_le R.G 15 R.ho R_G_ub ltac:(lia) R.ho_0 R_ho_S R.hoc R.hoc_0 R.hoc_S). Qed.

Lemma R_iter_ho_ub_le : forall p m a K z, S m <= K -> p + a + 20 <= z -> U.iter p (R.ho m) a + 20 <= U.f_wk K z.
Proof. exact (U.iter_ho_ub_le R.G 15 R.ho R_G_ub ltac:(lia) R.ho_0 R_ho_S). Qed.

(** R18c's exact count NR = 2(j + 1) + 1, from above.  (No tactic here matches or converts a hypothesis that holds a
    closed instance of the level maps: such instances would be reduced.) *)
Lemma R18c_count_core : forall a1 k1 b0 a2 j z,
  a1 + 6 = 3 * S (S k1) ->
  a2 + 20 <= U.f_wk (S (S (S k1))) (k1 + b0 + 21) ->
  a2 + 2 * (1 + S k1) + 2 = 3 * S j + 1 ->
  a1 + 20 <= U.f_wk 3 29 ->
  b0 + 20 <= U.f_wk 1 29 ->
  64 <= z ->
  2 * S j + 1 <= U.f_w2 (U.f_w2 z).
Proof.
  intros a1 k1 b0 a2 j z Hk1 Ha Hj Hh1 Hh2 Hz.
  pose proof (U.f_wk_ge2 (S (S (S k1))) (k1 + b0 + 21) ltac:(lia)) as G1.
  pose proof (absorb (S (S (S k1))) (2 * k1 + 6) (U.f_wk (S (S (S k1))) (k1 + b0 + 21)) ltac:(lia) ltac:(lia)) as HX.
  pose proof (U.iter_wk_le (S (S (S k1))) 2 (k1 + b0 + 21) (k1 + b0 + 21) ltac:(lia) ltac:(lia)) as H2.
  rewrite !U.iter_S1, U.iter_0 in H2.
  pose proof (U.f_wk_le_w2 (S (S (S (S k1)))) (k1 + b0 + 21) ltac:(lia) ltac:(lia)) as H3.
  pose proof (U.f_wk_level_le 1 3 29 ltac:(lia) ltac:(lia)) as L1.
  pose proof (U.f_wk_ge2 3 29 ltac:(lia)) as L2.
  pose proof (absorb 3 (U.f_wk 3 29) (U.f_wk 3 29) ltac:(lia) ltac:(lia)) as L3.
  pose proof (U.iter_wk_le 3 2 29 29 ltac:(lia) ltac:(lia)) as L4.
  rewrite !U.iter_S1, U.iter_0 in L4.
  pose proof (small_le_Tz 4 29 z ltac:(lia) ltac:(lia) Hz) as L5.
  pose proof (U.f_w2_mono (k1 + b0 + 21) (U.f_w2 z) ltac:(lia)) as H4.
  lia.
Qed.

Lemma R18c_count_ub : forall a1 k1 b0 a2 j,
  a1 = R.hoc 0 2 7 ->
  a1 + 6 = 3 * S (S k1) ->
  b0 = R.iter 2 (R.ho 0) 7 ->
  a2 = R.hoc 1 (S k1) b0 ->
  a2 + 2 * (1 + S k1) + 2 = 3 * S j + 1 ->
  2 * S j + 1 <= U.f_w2 (U.f_w2 (U.f 5 2)).
Proof.
  intros a1 k1 b0 a2 j Ha1 Hk1 Hb0 Ha2 Hj. rewrite R_iter in Hb0.
  pose proof (R_hoc_ub_le (S k1) 1 b0 (S (S (S k1))) (k1 + b0 + 21) (le_n _) (side_21 k1 b0)) as Ha.
  rewrite <- Ha2 in Ha.
  pose proof (R_hoc_ub_le 2 0 7 3 29 (le_n _) (le_n _)) as Hh1. rewrite <- Ha1 in Hh1.
  pose proof (R_iter_ho_ub_le 2 0 7 1 29 (le_n _) (le_n _)) as Hh2. rewrite <- Hb0 in Hh2.
  exact (R18c_count_core a1 k1 b0 a2 j (U.f 5 2) Hk1 Ha Hj Hh1 Hh2 f52).
Qed.

Theorem beats_R18c_exact : exists c N, c0 -[ Q.tm ]->* c /\ halted Q.tm c /\ Q.ones c N /\
  forall a1 k1 b0 a2 j,
    a1 = R.hoc 0 2 7 ->
    a1 + 6 = 3 * S (S k1) ->
    b0 = R.iter 2 (R.ho 0) 7 ->
    a2 = R.hoc 1 (S k1) b0 ->
    a2 + 2 * (1 + S k1) + 2 = 3 * S j + 1 ->
    2 * S j + 1 < N.
Proof.
  destruct Q_bound as (c & N & Hrun & Hhalt & Hones & HB).
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  intros a1 k1 b0 a2 j Ha1 Hk1 Hb0 Ha2 Hj.
  exact (Nat.le_lt_trans _ _ _ (R18c_count_ub a1 k1 b0 a2 j Ha1 Hk1 Hb0 Ha2 Hj) HB).
Qed.

Theorem beats_R18c_score : exists NR,
  (exists c, Individual182.Individual182.Permute.Flip.Compute.TM.evstep R.tm
               Individual182.Individual182.Permute.Flip.Compute.TM.c0 c /\
             Individual182.Individual182.Permute.Flip.Compute.TM.halted R.tm c /\
             R.ones c NR) /\
  exists c N, c0 -[ Q.tm ]->* c /\ halted Q.tm c /\ Q.ones c N /\ NR < N.
Proof.
  destruct R.score_exact as (a1 & k1 & b0 & a2 & j & cR & Ha1 & Hk1 & Hb0 & Ha2 & Hj & HrunR & HhaltR & HonesR).
  destruct beats_R18c_exact as (c & N & Hrun & Hhalt & Hones & HB).
  exists (2 * S j + 1). split; [exists cR; auto |].
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  exact (HB a1 k1 b0 a2 j Ha1 Hk1 Hb0 Ha2 Hj).
Qed.

(** ** J20's level maps (Jacobzheng's machine) *)
Lemma Z_iter : forall {X : Type} n (g : X -> X) x, Z.iter n g x = U.iter n g x.
Proof. induction n; intros; [rewrite U.iter_0; reflexivity | rewrite U.iter_S1, <- IHn; reflexivity]. Qed.

Lemma Z_h_S : forall m x, Z.h (S m) x = U.iter (x + 2) (Z.h m) 2.
Proof. intros. rewrite Z.h_S, Z_iter. reflexivity. Qed.

Lemma Z_ho_S : forall m a, Z.ho (S m) a = U.iter (a + 1) (Z.ho m) 3.
Proof. intros. rewrite Z.ho_S, Z_iter. reflexivity. Qed.

Lemma Z_hc_ub : forall n m x, Z.hc m n x + 4 <= U.f_omega (m + n + x + 5).
Proof. exact (U.hc_ub Z.h Z.h_0 Z_h_S Z.hc Z.hc_0 Z.hc_S). Qed.

Lemma Z_G_ub : forall a, Z.G a + 20 <= U.f_omega (a + 20).
Proof.
  intros a. rewrite Z.G_eq.
  pose proof (Nat.div_mod a 3 ltac:(lia)) as Ha. pose proof (Nat.mod_upper_bound a 3 ltac:(lia)) as Hy.
  remember (a / 3) as c eqn:Ec. remember (a mod 3) as y eqn:Ey. clear Ec Ey.
  pose proof (Z_hc_ub c 1 (y + 3)) as Hc.
  pose proof (U.f_omega_ge2 (1 + c + (y + 3) + 5) ltac:(lia)) as H1.
  pose proof (U.f_omega_dbl (1 + c + (y + 3) + 5) ltac:(lia)) as H2.
  pose proof (U.f_omega_dbl (S (1 + c + (y + 3) + 5)) ltac:(lia)) as H3.
  pose proof (U.f_omega_mono (S (S (1 + c + (y + 3) + 5))) (a + 20) ltac:(lia)) as H4.
  lia.
Qed.

Lemma Z_ho_ub : forall m a, Z.ho m a + 20 <= U.f_wk m (a + 20).
Proof. exact (U.ho_ub Z.G 3 Z.ho Z_G_ub ltac:(lia) Z.ho_0 Z_ho_S). Qed.

Lemma Z_hoc_ub : forall n m a, Z.hoc m n a + 20 <= U.f_wk (S (m + n)) (n + a + 20).
Proof. exact (U.hoc_ub Z.G 3 Z.ho Z_G_ub ltac:(lia) Z.ho_0 Z_ho_S Z.hoc Z.hoc_0 Z.hoc_S). Qed.

Lemma Z_iter_ho_ub : forall p m a, U.iter p (Z.ho m) a + 20 <= U.f_wk (S m) (p + a + 20).
Proof. exact (U.iter_ho_ub Z.G 3 Z.ho Z_G_ub ltac:(lia) Z.ho_0 Z_ho_S). Qed.

Lemma Z_ho_ub_le : forall m a K z, m <= K -> a + 20 <= z -> Z.ho m a + 20 <= U.f_wk K z.
Proof. exact (U.ho_ub_le Z.G 3 Z.ho Z_G_ub ltac:(lia) Z.ho_0 Z_ho_S). Qed.

Lemma Z_hoc_ub_le : forall n m a K z, S (m + n) <= K -> n + a + 20 <= z -> Z.hoc m n a + 20 <= U.f_wk K z.
Proof. exact (U.hoc_ub_le Z.G 3 Z.ho Z_G_ub ltac:(lia) Z.ho_0 Z_ho_S Z.hoc Z.hoc_0 Z.hoc_S). Qed.

(** J20's exact count NZ = 2j + 1, from above *)
Lemma J20_count_core : forall k a2 j b I h11 z,
  I + 10 = 3 * k + 2 ->
  b + 20 <= U.f_wk (S k) (k + 30) ->
  a2 + 20 <= U.f_wk (S k) (2 + b + 20) ->
  a2 + 2 * S k + 4 = 3 * j ->
  h11 + 20 <= U.f_wk 1 21 ->
  I + 20 <= U.f_wk 3 (2 + h11 + 20) ->
  64 <= z ->
  2 * j + 1 <= U.f_w2 (U.f_w2 z).
Proof.
  intros k a2 j b I h11 z Hk Hb Ha Hj Y1 Y2 Hz.
  pose proof (U.f_wk_ge2 (S k) (k + 30) ltac:(lia)) as G1.
  pose proof (U.iter_wk_le (S k) 4 (k + 30) (k + 30) ltac:(lia) ltac:(lia)) as H4.
  rewrite !U.iter_S1, U.iter_0 in H4.
  pose proof (absorb (S k) 2 (U.f_wk (S k) (k + 30)) ltac:(lia) ltac:(lia)) as HX2.
  pose proof (U.f_wk_mono (S k) (2 + b + 20) (U.f_wk (S k) (U.f_wk (S k) (k + 30))) ltac:(lia)) as H1.
  pose proof (U.f_wk_ge2 (S k) (U.f_wk (S k) (k + 30)) ltac:(lia)) as G3.
  pose proof (U.f_wk_ge2 (S k) (U.f_wk (S k) (U.f_wk (S k) (k + 30))) ltac:(lia)) as G2.
  pose proof (absorb (S k) (2 * k + 8) (U.f_wk (S k) (U.f_wk (S k) (U.f_wk (S k) (k + 30)))) ltac:(lia) ltac:(lia)) as HW.
  pose proof (U.f_wk_le_w2 (S (S k)) (k + 30) ltac:(lia) ltac:(lia)) as H5.
  pose proof (U.f_wk_ge2 1 21 ltac:(lia)) as Y3.
  pose proof (absorb 1 22 (U.f_wk 1 21) ltac:(lia) ltac:(lia)) as Y4.
  pose proof (U.iter_wk_le 1 2 21 21 ltac:(lia) ltac:(lia)) as Y5.
  rewrite !U.iter_S1, U.iter_0 in Y5.
  pose proof (U.f_wk_mono 3 (2 + h11 + 20) (U.f_wk 2 21) ltac:(lia)) as Y6.
  pose proof (U.f_wk_id 2 21) as Y0.
  pose proof (U.f_wk_mono 2 21 z ltac:(lia)) as Y8.
  pose proof (U.f_wk_level_le 2 4 z ltac:(lia) ltac:(lia)) as Y9.
  pose proof (U.f_wk_ge2 3 (U.f_wk 2 21) ltac:(lia)) as Y10.
  pose proof (U.f_wk_level_le 3 4 (U.f_wk 2 21) ltac:(lia) ltac:(lia)) as Y11.
  pose proof (U.f_wk_mono 4 (U.f_wk 2 21) (U.f_wk 4 z) ltac:(lia)) as Y12.
  pose proof (absorb 4 18 (U.f_wk 3 (U.f_wk 2 21)) ltac:(lia) ltac:(lia)) as Y15.
  pose proof (U.f_wk_mono 4 (U.f_wk 3 (U.f_wk 2 21)) (U.f_wk 4 (U.f_wk 4 z)) ltac:(lia)) as Y16.
  pose proof (U.iter_wk_le 4 3 z z ltac:(lia) ltac:(lia)) as Y13.
  rewrite !U.iter_S1, U.iter_0 in Y13.
  pose proof (U.f_wk_le_w2 5 z ltac:(lia) ltac:(lia)) as Y14.
  pose proof (U.f_w2_mono (k + 30) (U.f_w2 z) ltac:(lia)) as H6.
  lia.
Qed.

Lemma J20_count_ub : forall k a2 j,
  Z.iter 2 (Z.ho 2) (Z.ho 1 1) + 10 = 3 * k + 2 ->
  a2 = Z.iter 2 (Z.ho k) (Z.hoc 0 k 1) ->
  a2 + 2 * S k + 4 = 3 * j ->
  2 * j + 1 <= U.f_w2 (U.f_w2 (U.f 5 2)).
Proof.
  intros k a2 j Hk Ha2 Hj. rewrite Z_iter in Hk, Ha2.
  pose proof (Z_hoc_ub_le k 0 1 (S k) (k + 30) (le_n _) (side_k30 k)) as Hb.
  pose proof (Z_iter_ho_ub 2 k (Z.hoc 0 k 1)) as Ha. rewrite <- Ha2 in Ha.
  pose proof (Z_ho_ub_le 1 1 1 21 (le_n _) (le_n _)) as Y1.
  pose proof (Z_iter_ho_ub 2 2 (Z.ho 1 1)) as Y2.
  exact (J20_count_core k a2 j (Z.hoc 0 k 1) _ (Z.ho 1 1) (U.f 5 2) Hk Hb Ha Hj Y1 Y2 f52).
Qed.

Theorem beats_J20_exact : exists c N, c0 -[ Q.tm ]->* c /\ halted Q.tm c /\ Q.ones c N /\
  forall k a2 j,
    Z.iter 2 (Z.ho 2) (Z.ho 1 1) + 10 = 3 * k + 2 ->
    a2 = Z.iter 2 (Z.ho k) (Z.hoc 0 k 1) ->
    a2 + 2 * S k + 4 = 3 * j ->
    2 * j + 1 < N.
Proof.
  destruct Q_bound as (c & N & Hrun & Hhalt & Hones & HB).
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  intros k a2 j Hk Ha2 Hj.
  exact (Nat.le_lt_trans _ _ _ (J20_count_ub k a2 j Hk Ha2 Hj) HB).
Qed.

Theorem beats_J20_score : exists NZ,
  (exists c, Individual202.Individual202.Permute.Flip.Compute.TM.evstep Z.tm
               Individual202.Individual202.Permute.Flip.Compute.TM.c0 c /\
             Individual202.Individual202.Permute.Flip.Compute.TM.halted Z.tm c /\
             Z.ones c NZ) /\
  exists c N, c0 -[ Q.tm ]->* c /\ halted Q.tm c /\ Q.ones c N /\ NZ < N.
Proof.
  destruct Z.score_exact as (k & a2 & j & cZ & Hk & Ha2 & Hj & HrunZ & HhaltZ & HonesZ).
  destruct beats_J20_exact as (c & N & Hrun & Hhalt & Hones & HB).
  exists (2 * j + 1). split; [exists cZ; auto |].
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  exact (HB k a2 j Hk Ha2 Hj).
Qed.
