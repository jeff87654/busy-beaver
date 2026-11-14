(** * J20_cube (BB20_J20_w2_cube.v) beats BB(19) + 1 against J19_sq's EXACT score (BB19_J19_w2_sq.v).

    J19_sq's halting tape holds exactly NQ = 2(j + 1) + 1 ones, for the k1, a2, k2, a3, j of its [score_exact]
    (iter 2 (ho 0) 10 + 4 = 3(k1 + 2) + 1, a2 = hoc 0 (k1 + 1) 10, a2 + 2(k1 + 1) + 2 = 3(k2 + 2),
    a3 = (ho k2)^4 (hoc 0 k2 10), a3 + 2(k2 + 1) + 2 = 3(j + 1)); its halt S0 is read on a 0, so sigma(J19_sq) =
    NQ + 1 and BB(19) + 1 gives a 20-state machine with sigma NQ + 2.  J20_cube halts reading a 0 (T0), so
    sigma(J20_cube) = N + 1.  Proved here:

      beats_J19sq_exact : J20_cube halts with N ones and NQ + 1 < N for every k1, a2, k2, a3, j satisfying J19_sq's
                          equations, i.e. sigma(J20_cube) = N + 1 > NQ + 2 = sigma(J19_sq) + 1;
      beats_J19sq_score : the same, with J19_sq's halting tape (its [score_exact]).

    The two machines have the same engine definitions (h, hc, G0, Gcy, G, ho, hoc with the same text).  Method: the
    generic upper bounds of JZ_UB.v for J19_sq's definitions give NQ + 1 <= f_w2 (k2 + 30) and
    k2 + 30 <= f_w2 (f_w2 (f 5 2)), while J20_cube's [sigma_lower_bound] gives f_w2^3 (f 5 2) < N. *)

From BB8 Require Import Individual202.
From BB8 Require BB19_J19_w2_sq BB20_J20_w2_cube JZ_UB.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.

Module Q := BB19_J19_w2_sq.
Module C := BB20_J20_w2_cube.
Module U := JZ_UB.
(* JZ_UB's hierarchy is never unfolded here (closed instances must not be reduced): only its equations are used *)
Opaque U.iter U.f U.f_omega U.f_wk U.f_w2.
(* the main files make the hierarchy opaque at their end; the equalities below unfold it for variables only *)
Transparent C.f C.f_omega C.f_wk C.f_w2.

Lemma absorb : forall K c y, c <= y -> 1 <= y -> y + c <= U.f_wk K y.
Proof. intros K c y Hc Hy. pose proof (U.f_wk_ge2 K y Hy). lia. Qed.

(** ** J20_cube's hierarchy is JZ_UB's *)
Lemma C_iter : forall {X : Type} n (g : X -> X) x, C.iter n g x = U.iter n g x.
Proof. induction n; intros; [rewrite U.iter_0; reflexivity | rewrite U.iter_S1, <- IHn; reflexivity]. Qed.

Lemma C_f : forall k n, C.f k n = U.f k n.
Proof.
  induction k as [| k IH]; intros n; [reflexivity |].
  rewrite C.f_S, U.f_S, C_iter. apply U.iter_ext. exact IH.
Qed.

Lemma C_f_omega : forall n, C.f_omega n = U.f_omega n.
Proof. intros n. rewrite C.f_omega_eq, U.f_omega_eq. apply C_f. Qed.

Lemma C_f_wk : forall k n, C.f_wk k n = U.f_wk k n.
Proof.
  induction k as [| k IH]; intros n.
  - rewrite C.f_wk_0, U.f_wk_0. apply C_f_omega.
  - rewrite C.f_wk_S, U.f_wk_S, C_iter. apply U.iter_ext. exact IH.
Qed.

Lemma C_f_w2 : forall n, C.f_w2 n = U.f_w2 n.
Proof. intros n. rewrite C.f_w2_eq, U.f_w2_eq. apply C_f_wk. Qed.

Lemma C_bound : exists c N, c0 -[ C.tm ]->* c /\ halted C.tm c /\ C.ones c N /\
  U.f_w2 (U.f_w2 (U.f_w2 (U.f 5 2))) < N.
Proof.
  destruct C.sigma_lower_bound as (c & N & Hrun & Hhalt & Hones & HB & _).
  rewrite C_f, C_iter, (U.iter_ext C.f_w2 U.f_w2 C_f_w2), !U.iter_S1, U.iter_0 in HB.
  exists c, N. auto.
Qed.

Lemma f52 : 64 <= U.f 5 2.
Proof. pose proof C.f5_2_ge as H. rewrite C_f in H. exact H. Qed.

(** small arithmetic side conditions, proved without any hypothesis in the context *)
Lemma side_30 : forall k, k + 10 + 20 <= k + 30.  Proof. intros; lia. Qed.
Lemma side_31 : forall k, S k + 10 + 20 <= k + 31.  Proof. intros; lia. Qed.

(** ** J19_sq's level maps *)
Lemma Q_iter : forall {X : Type} n (g : X -> X) x, Q.iter n g x = U.iter n g x.
Proof. induction n; intros; [rewrite U.iter_0; reflexivity | rewrite U.iter_S1, <- IHn; reflexivity]. Qed.

Lemma Q_h_S : forall m x, Q.h (S m) x = U.iter (x + 2) (Q.h m) 2.
Proof. intros. rewrite Q.h_S, Q_iter. reflexivity. Qed.

Lemma Q_ho_S : forall m a, Q.ho (S m) a = U.iter (a + 1) (Q.ho m) 6.
Proof. intros. rewrite Q.ho_S, Q_iter. reflexivity. Qed.

Lemma Q_hc_ub : forall n m x, Q.hc m n x + 4 <= U.f_omega (m + n + x + 5).
Proof. exact (U.hc_ub Q.h Q.h_0 Q_h_S Q.hc Q.hc_0 Q.hc_S). Qed.

Lemma Q_Gcy0 : forall c, Q.Gcy c 0 = Q.G0 c.  Proof. reflexivity. Qed.
Lemma Q_Gcy1 : forall c, Q.Gcy c 1 = 3 * c + 5.  Proof. reflexivity. Qed.
Lemma Q_Gcy2 : forall c, Q.Gcy c 2 = Q.G0 c + 2.  Proof. reflexivity. Qed.

Lemma Q_G0_ub : forall c, Q.G0 c + 22 <= U.f_omega (c + 13).
Proof.
  intros c. rewrite Q.G0_eq.
  pose proof (Q_hc_ub c 1 6) as Hc.
  pose proof (U.f_omega_ge2 (1 + c + 6 + 5) ltac:(lia)) as H2.
  pose proof (U.f_omega_dbl (1 + c + 6 + 5) ltac:(lia)) as H3.
  replace (S (1 + c + 6 + 5)) with (c + 13) in H3 by lia. lia.
Qed.

Lemma Q_G_ub : forall a, Q.G a + 20 <= U.f_omega (a + 20).
Proof.
  intros a.
  pose proof (Nat.div_mod a 3 ltac:(lia)) as Ha. pose proof (Nat.mod_upper_bound a 3 ltac:(lia)) as Hy.
  remember (a / 3) as c eqn:Ec. remember (a mod 3) as y eqn:Ey. clear Ec Ey. subst a.
  rewrite (Q.G_cy c y Hy).
  destruct y as [| [| [| y]]]; [| | | lia].
  - rewrite Q_Gcy0. pose proof (Q_G0_ub c). pose proof (U.f_omega_mono (c + 13) (3 * c + 0 + 20) ltac:(lia)). lia.
  - rewrite Q_Gcy1. pose proof (U.f_omega_ge2 (3 * c + 1 + 20) ltac:(lia)). lia.
  - rewrite Q_Gcy2. pose proof (Q_G0_ub c). pose proof (U.f_omega_mono (c + 13) (3 * c + 2 + 20) ltac:(lia)). lia.
Qed.

Lemma Q_ho_ub : forall m a, Q.ho m a + 20 <= U.f_wk m (a + 20).
Proof. exact (U.ho_ub Q.G 6 Q.ho Q_G_ub ltac:(lia) Q.ho_0 Q_ho_S). Qed.

Lemma Q_hoc_ub : forall n m a, Q.hoc m n a + 20 <= U.f_wk (S (m + n)) (n + a + 20).
Proof. exact (U.hoc_ub Q.G 6 Q.ho Q_G_ub ltac:(lia) Q.ho_0 Q_ho_S Q.hoc Q.hoc_0 Q.hoc_S). Qed.

Lemma Q_iter_ho_ub : forall p m a, U.iter p (Q.ho m) a + 20 <= U.f_wk (S m) (p + a + 20).
Proof. exact (U.iter_ho_ub Q.G 6 Q.ho Q_G_ub ltac:(lia) Q.ho_0 Q_ho_S). Qed.

Lemma Q_hoc_ub_le : forall n m a K z, S (m + n) <= K -> n + a + 20 <= z -> Q.hoc m n a + 20 <= U.f_wk K z.
Proof. exact (U.hoc_ub_le Q.G 6 Q.ho Q_G_ub ltac:(lia) Q.ho_0 Q_ho_S Q.hoc Q.hoc_0 Q.hoc_S). Qed.

Lemma Q_iter_ho_ub_le : forall p m a K z, S m <= K -> p + a + 20 <= z -> U.iter p (Q.ho m) a + 20 <= U.f_wk K z.
Proof. exact (U.iter_ho_ub_le Q.G 6 Q.ho Q_G_ub ltac:(lia) Q.ho_0 Q_ho_S). Qed.

(** ** J19_sq's exact count, from above.  (No tactic here matches or converts a hypothesis that holds a closed
    instance of the level maps: such instances would be reduced.) *)
Lemma J19sq_count_core : forall k2 a3 j b,
  b + 20 <= U.f_wk (S k2) (k2 + 30) ->
  a3 + 20 <= U.f_wk (S k2) (4 + b + 20) ->
  a3 + 2 * S k2 + 2 = 3 * S j ->
  2 * S j + 1 + 1 <= U.f_w2 (k2 + 30).
Proof.
  intros k2 a3 j b Hb Ha Hj.
  pose proof (U.f_wk_ge2 (S k2) (k2 + 30) ltac:(lia)) as G1.
  pose proof (U.iter_wk_le (S k2) 4 (k2 + 30) (k2 + 30) ltac:(lia) ltac:(lia)) as H4.
  rewrite !U.iter_S1, U.iter_0 in H4.
  pose proof (absorb (S k2) 4 (U.f_wk (S k2) (k2 + 30)) ltac:(lia) ltac:(lia)) as HX4.
  pose proof (U.f_wk_mono (S k2) (4 + b + 20) (U.f_wk (S k2) (U.f_wk (S k2) (k2 + 30))) ltac:(lia)) as H1.
  pose proof (U.f_wk_ge2 (S k2) (U.f_wk (S k2) (k2 + 30)) ltac:(lia)) as G2.
  pose proof (U.f_wk_ge2 (S k2) (U.f_wk (S k2) (U.f_wk (S k2) (k2 + 30))) ltac:(lia)) as G3.
  pose proof (absorb (S k2) (2 * k2 + 6) (U.f_wk (S k2) (U.f_wk (S k2) (U.f_wk (S k2) (k2 + 30)))) ltac:(lia) ltac:(lia)) as HW.
  pose proof (U.f_wk_le_w2 (S (S k2)) (k2 + 30) ltac:(lia) ltac:(lia)) as H5.
  lia.
Qed.

Lemma J19sq_count_ub : forall k2 a3 j,
  a3 = Q.iter 4 (Q.ho k2) (Q.hoc 0 k2 10) ->
  a3 + 2 * S k2 + 2 = 3 * S j ->
  2 * S j + 1 + 1 <= U.f_w2 (k2 + 30).
Proof.
  intros k2 a3 j Ha3 Hj. rewrite Q_iter in Ha3.
  pose proof (Q_hoc_ub_le k2 0 10 (S k2) (k2 + 30) (le_n _) (side_30 k2)) as Hb.
  pose proof (Q_iter_ho_ub 4 k2 (Q.hoc 0 k2 10)) as Ha. rewrite <- Ha3 in Ha.
  exact (J19sq_count_core k2 a3 j (Q.hoc 0 k2 10) Hb Ha Hj).
Qed.

Lemma J19sq_k2_core : forall k1 a2 k2 I z,
  I + 4 = 3 * S (S k1) + 1 ->
  I + 20 <= U.f_wk 1 32 ->
  a2 + 20 <= U.f_wk (S (S k1)) (k1 + 31) ->
  a2 + 2 * S k1 + 2 = 3 * S (S k2) ->
  64 <= z ->
  k2 + 30 <= U.f_w2 (U.f_w2 z).
Proof.
  intros k1 a2 k2 I z Hk1 K1 Ha Hk2 Hz.
  pose proof (U.f_wk_ge2 (S (S k1)) (k1 + 31) ltac:(lia)) as G1.
  pose proof (absorb (S (S k1)) (2 * k1 + 10) (U.f_wk (S (S k1)) (k1 + 31)) ltac:(lia) ltac:(lia)) as H1.
  pose proof (U.iter_wk_le (S (S k1)) 2 (k1 + 31) (k1 + 31) ltac:(lia) ltac:(lia)) as H2.
  rewrite !U.iter_S1, U.iter_0 in H2.
  pose proof (U.f_wk_le_w2 (S (S (S k1))) (k1 + 31) ltac:(lia) ltac:(lia)) as H3.
  pose proof (U.f_wk_ge2 1 32 ltac:(lia)) as K2.
  pose proof (absorb 1 11 (U.f_wk 1 32) ltac:(lia) ltac:(lia)) as K3.
  pose proof (U.iter_wk_le 1 2 32 32 ltac:(lia) ltac:(lia)) as K4.
  rewrite !U.iter_S1, U.iter_0 in K4.
  pose proof (U.f_wk_mono 2 32 z ltac:(lia)) as K6.
  pose proof (U.f_wk_le_w2 2 z ltac:(lia) ltac:(lia)) as K7.
  pose proof (U.f_w2_mono (k1 + 31) (U.f_w2 z) ltac:(lia)) as H4.
  lia.
Qed.

Lemma J19sq_k2_ub : forall k1 a2 k2,
  U.iter 2 (Q.ho 0) 10 + 4 = 3 * S (S k1) + 1 ->
  a2 = Q.hoc 0 (S k1) 10 ->
  a2 + 2 * S k1 + 2 = 3 * S (S k2) ->
  k2 + 30 <= U.f_w2 (U.f_w2 (U.f 5 2)).
Proof.
  intros k1 a2 k2 Hk1 Ha2 Hk2.
  pose proof (Q_hoc_ub_le (S k1) 0 10 (S (S k1)) (k1 + 31) (le_n _) (side_31 k1)) as Ha. rewrite <- Ha2 in Ha.
  pose proof (Q_iter_ho_ub_le 2 0 10 1 32 (le_n _) (le_n _)) as K1.
  exact (J19sq_k2_core k1 a2 k2 _ (U.f 5 2) Hk1 K1 Ha Hk2 f52).
Qed.

(** ** The comparisons *)
Theorem beats_J19sq_exact : exists c N, c0 -[ C.tm ]->* c /\ halted C.tm c /\ C.ones c N /\
  forall k1 a2 k2 a3 j,
    Q.iter 2 (Q.ho 0) 10 + 4 = 3 * S (S k1) + 1 ->
    a2 = Q.hoc 0 (S k1) 10 ->
    a2 + 2 * S k1 + 2 = 3 * S (S k2) ->
    a3 = Q.iter 4 (Q.ho k2) (Q.hoc 0 k2 10) ->
    a3 + 2 * S k2 + 2 = 3 * S j ->
    2 * S j + 1 + 1 < N.
Proof.
  destruct C_bound as (c & N & Hrun & Hhalt & Hones & HB).
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  intros k1 a2 k2 a3 j Hk1 Ha2 Hk2 Ha3 Hj.
  rewrite Q_iter in Hk1.
  pose proof (J19sq_count_ub k2 a3 j Ha3 Hj) as H1.
  pose proof (J19sq_k2_ub k1 a2 k2 Hk1 Ha2 Hk2) as H2.
  pose proof (U.f_w2_mono _ _ H2) as H3.
  exact (Nat.le_lt_trans _ _ _ (Nat.le_trans _ _ _ H1 H3) HB).
Qed.

Theorem beats_J19sq_score : exists NQ,
  (exists c, Individual192.Individual192.Permute.Flip.Compute.TM.evstep Q.tm
               Individual192.Individual192.Permute.Flip.Compute.TM.c0 c /\
             Individual192.Individual192.Permute.Flip.Compute.TM.halted Q.tm c /\
             Q.ones c NQ) /\
  exists c N, c0 -[ C.tm ]->* c /\ halted C.tm c /\ C.ones c N /\ NQ + 1 < N.
Proof.
  destruct Q.score_exact as (k1 & a2 & k2 & a3 & j & cQ & Hk1 & Ha2 & Hk2 & Ha3 & Hj & HrunQ & HhaltQ & HonesQ).
  destruct beats_J19sq_exact as (c & N & Hrun & Hhalt & Hones & HB).
  exists (2 * S j + 1). split; [exists cQ; auto |].
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  exact (HB k1 a2 k2 a3 j Hk1 Ha2 Hk2 Ha3 Hj).
Qed.
