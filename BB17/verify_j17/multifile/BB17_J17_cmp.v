(** * J17_champ (BB17_J17_w2_champ.v) beats BB(16) + 1 against J16_w2's EXACT score (BB16_J16_w2.v).

    J16_w2's halting tape holds exactly NJ = 2j + 4 ones, for the k1, q1, a2, j of its [score_exact]
    (G 44 + 4 = 3(k1 + 3), k1 = 3 q1 + 2, a2 = hoc 1 k1 (G 44), a2 + 2(k1 + 1) + 2 = 3(j + 1) + 1); its halt O0 is
    read on a 0, so sigma(J16_w2) = NJ + 1 and BB(17) >= BB(16) + 1 gives a 17-state machine with sigma = NJ + 2
    from it.  J17_champ also halts reading a 0 (O0), so sigma(J17_champ) = N + 1.  Proved here:

      beats_J16_exact : J17_champ halts with N ones and NJ + 1 < N for every k1, q1, a2, j satisfying J16_w2's
                        equations, i.e. sigma(J17_champ) = N + 1 > NJ + 2 = sigma(J16_w2) + 1;
      beats_J16_score : the same, with J16_w2's halting tape (its [score_exact]).

    Method: the generic upper bounds of JZ_UB.v for J16_w2's own definitions h, hc, G, ho, hoc give
    NJ + 1 <= f_w2 Z with Z = k1 + G 44 + 20 <= f_omega^3 (f 14 2), while J17_champ's [sigma_lower_bound] gives
    f_w2 (f_omega^3 (f 14 2)) < N.  The files define iter, f, f_omega, f_wk, f_w2 with the same text; the
    equalities used to move between them are proved below for all arguments. *)

From BB8 Require Import Individual172.
From BB8 Require BB16_J16_w2 BB17_J17_w2_champ JZ_UB.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.

Module J := BB16_J16_w2.
Module K := BB17_J17_w2_champ.
Module U := JZ_UB.
(* JZ_UB's hierarchy is never unfolded here (closed instances must not be reduced): only its equations are used *)
Opaque U.iter U.f U.f_omega U.f_wk U.f_w2.
(* the main files make the hierarchy opaque at their end; the equalities below unfold it for variables only *)
Transparent K.f K.f_omega K.f_wk K.f_w2.

(** ** The hierarchies agree *)
Lemma J_iter : forall {X : Type} n (g : X -> X) x, J.iter n g x = U.iter n g x.
Proof. induction n; intros; [rewrite U.iter_0; reflexivity | rewrite U.iter_S1, <- IHn; reflexivity]. Qed.

Lemma K_iter : forall {X : Type} n (g : X -> X) x, K.iter n g x = U.iter n g x.
Proof. induction n; intros; [rewrite U.iter_0; reflexivity | rewrite U.iter_S1, <- IHn; reflexivity]. Qed.

Lemma K_f : forall k n, K.f k n = U.f k n.
Proof.
  induction k as [| k IH]; intros n; [reflexivity |].
  rewrite K.f_S, U.f_S, K_iter. apply U.iter_ext. exact IH.
Qed.

Lemma K_f_omega : forall n, K.f_omega n = U.f_omega n.
Proof. intros n. rewrite K.f_omega_eq, U.f_omega_eq. apply K_f. Qed.

Lemma K_f_wk : forall k n, K.f_wk k n = U.f_wk k n.
Proof.
  induction k as [| k IH]; intros n.
  - rewrite K.f_wk_0, U.f_wk_0. apply K_f_omega.
  - rewrite K.f_wk_S, U.f_wk_S, K_iter. apply U.iter_ext. exact IH.
Qed.

Lemma K_f_w2 : forall n, K.f_w2 n = U.f_w2 n.
Proof. intros n. rewrite K.f_w2_eq, U.f_w2_eq. apply K_f_wk. Qed.

(** ** J16_w2's level maps satisfy the hypotheses of JZ_UB *)
Lemma J_h_S : forall m x, J.h (S m) x = U.iter (x + 2) (J.h m) 2.
Proof. intros. rewrite J.h_S, J_iter. reflexivity. Qed.

Lemma J_ho_S : forall m a, J.ho (S m) a = U.iter (a + 1) (J.ho m) 5.
Proof. intros. rewrite J.ho_S, J_iter. reflexivity. Qed.

Lemma J_hc_ub : forall n m x, J.hc m n x + 4 <= U.f_omega (m + n + x + 5).
Proof. exact (U.hc_ub J.h J.h_0 J_h_S J.hc J.hc_0 J.hc_S). Qed.

Lemma J_G_ub : forall a, J.G a + 20 <= U.f_omega (a + 20).
Proof.
  intros a. rewrite J.G_eq.
  pose proof (Nat.div_mod a 3 ltac:(lia)) as Ha.
  remember (a / 3) as c eqn:Ec. clear Ec.
  pose proof (J_hc_ub (S c) 0 3) as Hc.
  pose proof (U.f_omega_ge2 (0 + S c + 3 + 5) ltac:(lia)) as H1.
  pose proof (U.f_omega_dbl (0 + S c + 3 + 5) ltac:(lia)) as H2.
  pose proof (U.f_omega_dbl (S (0 + S c + 3 + 5)) ltac:(lia)) as H3.
  pose proof (U.f_omega_mono (S (S (0 + S c + 3 + 5))) (a + 20) ltac:(lia)) as H4.
  lia.
Qed.

Lemma J_ho_ub : forall m a, J.ho m a + 20 <= U.f_wk m (a + 20).
Proof. exact (U.ho_ub J.G 5 J.ho J_G_ub ltac:(lia) J.ho_0 J_ho_S). Qed.

Lemma J_hoc_ub : forall n m a, J.hoc m n a + 20 <= U.f_wk (S (m + n)) (n + a + 20).
Proof. exact (U.hoc_ub J.G 5 J.ho J_G_ub ltac:(lia) J.ho_0 J_ho_S J.hoc J.hoc_0 J.hoc_S). Qed.

Lemma absorb : forall K c y, c <= y -> 1 <= y -> y + c <= U.f_wk K y.
Proof. intros K c y Hc Hy. pose proof (U.f_wk_ge2 K y Hy). lia. Qed.

(** ** J16_w2's exact count, from above *)
Lemma J16_count_ub : forall k1 a2 j,
  a2 = J.hoc 1 k1 (J.G 44) ->
  a2 + 2 * S k1 + 2 = 3 * S j + 1 ->
  2 * j + 4 + 1 <= U.f_w2 (k1 + J.G 44 + 20).
Proof.
  intros k1 a2 j Ha2 Hj.
  pose proof (J_hoc_ub k1 1 (J.G 44)) as Ha. rewrite <- Ha2 in Ha.
  replace (S (1 + k1)) with (S (S k1)) in Ha by lia.
  remember (J.G 44) as g eqn:Eg. clear Eg.
  remember (k1 + g + 20) as Z eqn:EZ.
  pose proof (U.iter_wk_le (S (S k1)) 2 Z Z ltac:(lia) ltac:(lia)) as H2.
  rewrite !U.iter_S1, U.iter_0 in H2.
  pose proof (U.f_wk_ge2 (S (S k1)) Z ltac:(lia)) as G1.
  pose proof (absorb (S (S k1)) (2 * k1) (U.f_wk (S (S k1)) Z) ltac:(lia) ltac:(lia)) as HX.
  pose proof (U.f_wk_le_w2 (S (S (S k1))) Z ltac:(lia) ltac:(lia)) as H3.
  lia.
Qed.

Lemma J16_Z_ub : forall k1, J.G 44 + 4 = 3 * (k1 + 3) ->
  k1 + J.G 44 + 20 <= U.iter 3 U.f_omega (U.f 14 2).
Proof.
  intros k1 Hk.
  pose proof (J_G_ub 44) as HG. replace (44 + 20) with 64 in HG by lia.
  pose proof K.f14_2_ge as H14. rewrite K_f in H14.
  rewrite !U.iter_S1, U.iter_0.
  remember (U.f 14 2) as x eqn:Ex. clear Ex.
  pose proof (U.f_omega_ge2 (U.f_omega 64) ltac:(pose proof (U.f_omega_id 64); lia)) as H1.
  pose proof (U.f_omega_mono 64 x H14) as H2.
  pose proof (U.f_omega_mono (U.f_omega 64) (U.f_omega x) H2) as H3.
  pose proof (U.f_omega_id (U.f_omega (U.f_omega x))) as H4.
  lia.
Qed.

(** ** The comparisons *)
Lemma K_bound : exists c N, c0 -[ K.tm ]->* c /\ halted K.tm c /\ K.ones c N /\
  U.f_w2 (U.iter 3 U.f_omega (U.f 14 2)) < N.
Proof.
  destruct K.sigma_lower_bound as (c & N & Hrun & Hhalt & Hones & _ & HB).
  rewrite K_f, K_iter, (U.iter_ext K.f_omega U.f_omega K_f_omega), K_f_w2 in HB.
  exists c, N. auto.
Qed.

Theorem beats_J16_exact : exists c N, c0 -[ K.tm ]->* c /\ halted K.tm c /\ K.ones c N /\
  forall k1 q1 a2 j,
    J.G 44 + 4 = 3 * (k1 + 3) ->
    k1 = 3 * q1 + 2 ->
    a2 = J.hoc 1 k1 (J.G 44) ->
    a2 + 2 * S k1 + 2 = 3 * S j + 1 ->
    2 * j + 4 + 1 < N.
Proof.
  destruct K_bound as (c & N & Hrun & Hhalt & Hones & HB).
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  intros k1 q1 a2 j Hk Hq Ha2 Hj.
  pose proof (J16_count_ub k1 a2 j Ha2 Hj) as H1.
  pose proof (J16_Z_ub k1 Hk) as H2.
  pose proof (U.f_w2_mono _ _ H2) as H3.
  exact (Nat.le_lt_trans _ _ _ (Nat.le_trans _ _ _ H1 H3) HB).
Qed.

Theorem beats_J16_score : exists NJ,
  (exists c, Individual162.Individual162.Permute.Flip.Compute.TM.evstep J.tm
               Individual162.Individual162.Permute.Flip.Compute.TM.c0 c /\
             Individual162.Individual162.Permute.Flip.Compute.TM.halted J.tm c /\
             J.ones c NJ) /\
  exists c N, c0 -[ K.tm ]->* c /\ halted K.tm c /\ K.ones c N /\ NJ + 1 < N.
Proof.
  destruct J.score_exact as (k1 & q1 & a2 & j & cJ & Hk & Hq & Ha2 & Hj & HrunJ & HhaltJ & HonesJ).
  destruct beats_J16_exact as (c & N & Hrun & Hhalt & Hones & HB).
  exists (2 * j + 4). split; [exists cJ; auto |].
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  exact (HB k1 q1 a2 j Hk Hq Ha2 Hj).
Qed.
