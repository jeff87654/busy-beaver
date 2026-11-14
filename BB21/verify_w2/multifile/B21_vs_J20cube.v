(** * B21 (BB(21), Racheline) beats BB(20) + 1, against J20_cube's EXACT score.

    J20_cube (BB20/verify_j20cube, BB20_J20_w2_cube.v, Argon): halts reading a 0 (T0), with exactly
      NJ = 2(j + 1) + 1 ones, for the k1, a2, k2, a3, k3, a4, j of its [score_exact]:
        (ho 0)^2 10 + 4 = 3(k1 + 2) + 1,  a2 = hoc 0 (k1 + 1) 10,  a2 + 2(k1 + 1) + 2 = 3(k2 + 2),
        a3 = hoc 0 k2 10,  a3 + 2(k2 + 1) + 2 = 3(k3 + 1) + 2,  a4 = (ho k3)^4 (hoc 0 k3 10),  a4 + 2(k3 + 1) + 2 = 3(j + 1);
      sigma(J20_cube) = NJ + 1, and BB(20) + 1 (a 21-state machine) reaches NJ + 2.
    B21 (BB21/verify_w2, BB21_B21_w2.v): halts with N ones, sigma(B21) = N + 1, and
      sigma_lower_bound_wsq3 : f_(w^2)^3 (4^^341) < N.

    Proved here:
      B21_beats_J20cube_exact : B21 halts with N ones and NJ + 1 < N for every k1 .. j satisfying J20_cube's equations,
                                i.e. sigma(B21) = N + 1 > NJ + 2 = sigma(J20_cube) + 1;
      B21_beats_J20cube_score : the same, with J20_cube's halting tape (its [score_exact]).

    Method.  The generic upper bounds of JZ_UB.v (BB18/verify_r18c, also BB20/verify_j20cube; byte-identical) for
    J20_cube's level maps give
      NJ + 1 <= f_w2 (k3 + 30),  k3 + 30 <= f_w2 (k2 + 30),  k2 + 30 <= f_w2 (f_w2 (f_5 2))   (f_w2 = f_(w*2)),
    so NJ + 1 <= f_(w*2)^4 (f_5 2).  With BB_FGH_wa.v's hierarchy (f_wa 2 0 = f_(w*2), f_wsq = f_(w^2)):
      f_(w*2)^4 (x) <= f_(w*2+1)(T) <= f_(w*3)(T) <= f_(w^2)(T)   for x <= T, T >= 4   (key4),
      f_5 2 <= f_(w^2)(t)   for t >= 5   (f52_le_U),
    and T = f_(w^2)(4^^341) gives NJ + 1 <= f_(w^2)^2 (4^^341) <= f_(w^2)^3 (4^^341) < N.
    Closed huge instances are never matched, rewritten or handed to a conversion: every rewrite/change below acts on
    variables only, and the closed instances enter by exact application. *)

From BB8 Require Import Individual212.
From BB8 Require Individual202.
From BB8 Require BB21_B21_absdef BB21_B21_score BB21_B21_w2 BB_FGH_wa BB_FGH_wa2 BB20_J20_w2_cube JZ_UB.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

Module A := BB21_B21_absdef.
Module Sc := BB21_B21_score.
Module W := BB21_B21_w2.
Module F := BB_FGH_wa.
Module F2 := BB_FGH_wa2.
Module C := BB20_J20_w2_cube.
Module U := JZ_UB.

(** ** JZ_UB's hierarchy is BB_FGH_wa's (variables only) *)
Lemma U_iter : forall {X : Type} n (g : X -> X) x, U.iter n g x = A.iter n g x.
Proof. induction n; intros; [reflexivity | rewrite U.iter_S1, IHn; reflexivity]. Qed.

Lemma U_f : forall k n, U.f k n = F.f k n.
Proof.
  induction k as [| k IH]; intros n; [reflexivity |].
  rewrite U.f_S, U_iter. change (F.f (S k) n) with (A.iter n (F.f k) n). apply F.iter_ext. exact IH.
Qed.

Lemma U_f_wk : forall k n, U.f_wk k n = F.f_wa 1 k n.
Proof.
  induction k as [| k IH]; intros n.
  - rewrite U.f_wk_0, U.f_omega_eq, U_f. reflexivity.
  - rewrite U.f_wk_S, F.f_wa_S, U_iter. apply F.iter_ext. exact IH.
Qed.

Lemma U_f_w2 : forall n, U.f_w2 n = F.f_wa 2 0 n.
Proof. intros n. rewrite U.f_w2_eq, F.f_wa_lim. apply U_f_wk. Qed.

(** ** f_(w*2)^4 below f_(w^2) *)
Lemma key4 : forall x T, x <= T -> 4 <= T ->
  F.f_wa 2 0 (F.f_wa 2 0 (F.f_wa 2 0 (F.f_wa 2 0 x))) <= F.f_wsq T.
Proof.
  intros x T Hx HT.
  change (F.f_wa 2 0 (F.f_wa 2 0 (F.f_wa 2 0 (F.f_wa 2 0 x)))) with (A.iter 4 (F.f_wa 2 0) x).
  pose proof (F.iter_mono_arg (F.f_wa 2 0) (F.f_wa_mono 2 0) 4 x T Hx) as M1.
  pose proof (F.iter_mono_cnt (F.f_wa 2 0) (F.f_wa_id 2 0) 4 T T HT) as M2.
  rewrite <- (F.f_wa_S 2 0 T) in M2.
  pose proof (F.f_wa_b_mono 2 1 T T ltac:(lia) ltac:(lia)) as M3.
  rewrite <- (F.f_wa_lim 2 T) in M3.
  pose proof (F.f_wa_a_mono 3 T T ltac:(lia) ltac:(lia)) as M4.
  unfold F.f_wsq. lia.
Qed.

Lemma f52_le_U : forall t, 5 <= t -> U.f 5 2 <= F.f_wsq t.
Proof.
  intros t Ht. pose proof (U_f 5 2) as E.
  pose proof (proj2 (F.good_f 5) 2 t ltac:(lia)) as M1.
  pose proof (F.f_wa_b_mono 0 5 t t Ht ltac:(lia)) as M2.
  change (F.f_wa 0 5 t) with (F.f 5 t) in M2.
  pose proof (F.f_wa_a_mono 1 t t ltac:(lia) ltac:(lia)) as M3.
  change (F.f_wa 1 0 t) with (F.f_wa 0 t t) in M3.
  unfold F.f_wsq. lia.
Qed.

Lemma tet_ge5 : forall n, 5 <= Sc.tet (S (S n)).
Proof.
  intros n. change (Sc.tet (S (S n))) with (4 ^ (4 ^ Sc.tet n)).
  pose proof (Sc.tet_pos n) as P.
  assert (A1 : 4 ^ 1 <= 4 ^ Sc.tet n) by (apply Nat.pow_le_mono_r; lia).
  change (4 ^ 1) with 4 in A1.
  assert (A2 : 4 ^ 2 <= 4 ^ (4 ^ Sc.tet n)) by (apply Nat.pow_le_mono_r; lia).
  change (4 ^ 2) with 16 in A2. lia.
Qed.

(** the comparison, for an abstract X (= f_5 2) and T (= 4^^341) *)
Lemma core : forall X T N k2 k3 j,
  5 <= T -> X <= F.f_wsq T ->
  k2 + 30 <= U.f_w2 (U.f_w2 X) -> k3 + 30 <= U.f_w2 (k2 + 30) -> 2 * S j + 1 + 1 <= U.f_w2 (k3 + 30) ->
  A.iter 3 F.f_wsq T < N -> 2 * S j + 1 + 1 < N.
Proof.
  intros X T N k2 k3 j HT HX H3 H2 H1 HB.
  rewrite (U_f_w2 X) in H3. rewrite !U_f_w2 in H1, H2, H3.
  pose proof (F.f_wa_mono 2 0 _ _ H2) as M1.
  pose proof (F.f_wa_mono 2 0 _ _ H3) as M2.
  pose proof (F.f_wa_mono 2 0 _ _ M2) as M3.
  pose proof (F2.fwsq_ge T) as G1.
  pose proof (key4 X (F.f_wsq T) HX ltac:(lia)) as K.
  pose proof (F2.fwsq_ge (F.f_wsq (F.f_wsq T))) as G2.
  change (A.iter 3 F.f_wsq T) with (F.f_wsq (F.f_wsq (F.f_wsq T))) in HB.
  lia.
Qed.

(** ** J20_cube's level maps (as BB20/verify_j20cube's BB20_J20cube_cmp.v does for J19_sq) *)
Lemma C_iter : forall {X : Type} n (g : X -> X) x, C.iter n g x = U.iter n g x.
Proof. induction n; intros; [rewrite U.iter_0; reflexivity | rewrite U.iter_S1, <- IHn; reflexivity]. Qed.

(* the main file makes its hierarchy opaque at its end; C_f unfolds it for variables only *)
Transparent C.f.
Lemma C_f : forall k n, C.f k n = U.f k n.
Proof.
  induction k as [| k IH]; intros n; [reflexivity |].
  rewrite C.f_S, U.f_S, C_iter. apply U.iter_ext. exact IH.
Qed.
Opaque C.f.

(* JZ_UB's hierarchy is never unfolded below (closed instances must not be reduced): only its equations are used *)
Opaque U.iter U.f U.f_omega U.f_wk U.f_w2.

Lemma absorb : forall K c y, c <= y -> 1 <= y -> y + c <= U.f_wk K y.
Proof. intros K c y Hc Hy. pose proof (U.f_wk_ge2 K y Hy). lia. Qed.

Lemma side_30 : forall k, k + 10 + 20 <= k + 30.  Proof. intros; lia. Qed.
Lemma side_31 : forall k, S k + 10 + 20 <= k + 31.  Proof. intros; lia. Qed.

Lemma C_h_S : forall m x, C.h (S m) x = U.iter (x + 2) (C.h m) 2.
Proof. intros. rewrite C.h_S, C_iter. reflexivity. Qed.

Lemma C_ho_S : forall m a, C.ho (S m) a = U.iter (a + 1) (C.ho m) 6.
Proof. intros. rewrite C.ho_S, C_iter. reflexivity. Qed.

Lemma C_hc_ub : forall n m x, C.hc m n x + 4 <= U.f_omega (m + n + x + 5).
Proof. exact (U.hc_ub C.h C.h_0 C_h_S C.hc C.hc_0 C.hc_S). Qed.

Lemma C_Gcy0 : forall c, C.Gcy c 0 = C.G0 c.  Proof. reflexivity. Qed.
Lemma C_Gcy1 : forall c, C.Gcy c 1 = 3 * c + 5.  Proof. reflexivity. Qed.
Lemma C_Gcy2 : forall c, C.Gcy c 2 = C.G0 c + 2.  Proof. reflexivity. Qed.

Lemma C_G0_ub : forall c, C.G0 c + 22 <= U.f_omega (c + 13).
Proof.
  intros c. rewrite C.G0_eq.
  pose proof (C_hc_ub c 1 6) as Hc.
  pose proof (U.f_omega_ge2 (1 + c + 6 + 5) ltac:(lia)) as H2.
  pose proof (U.f_omega_dbl (1 + c + 6 + 5) ltac:(lia)) as H3.
  replace (S (1 + c + 6 + 5)) with (c + 13) in H3 by lia. lia.
Qed.

Lemma C_G_ub : forall a, C.G a + 20 <= U.f_omega (a + 20).
Proof.
  intros a.
  pose proof (Nat.div_mod a 3 ltac:(lia)) as Ha. pose proof (Nat.mod_upper_bound a 3 ltac:(lia)) as Hy.
  remember (a / 3) as c eqn:Ec. remember (a mod 3) as y eqn:Ey. clear Ec Ey. subst a.
  rewrite (C.G_cy c y Hy).
  destruct y as [| [| [| y]]]; [| | | lia].
  - rewrite C_Gcy0. pose proof (C_G0_ub c). pose proof (U.f_omega_mono (c + 13) (3 * c + 0 + 20) ltac:(lia)). lia.
  - rewrite C_Gcy1. pose proof (U.f_omega_ge2 (3 * c + 1 + 20) ltac:(lia)). lia.
  - rewrite C_Gcy2. pose proof (C_G0_ub c). pose proof (U.f_omega_mono (c + 13) (3 * c + 2 + 20) ltac:(lia)). lia.
Qed.

Lemma C_iter_ho_ub : forall p m a, U.iter p (C.ho m) a + 20 <= U.f_wk (S m) (p + a + 20).
Proof. exact (U.iter_ho_ub C.G 6 C.ho C_G_ub ltac:(lia) C.ho_0 C_ho_S). Qed.

Lemma C_hoc_ub_le : forall n m a K z, S (m + n) <= K -> n + a + 20 <= z -> C.hoc m n a + 20 <= U.f_wk K z.
Proof. exact (U.hoc_ub_le C.G 6 C.ho C_G_ub ltac:(lia) C.ho_0 C_ho_S C.hoc C.hoc_0 C.hoc_S). Qed.

Lemma C_iter_ho_ub_le : forall p m a K z, S m <= K -> p + a + 20 <= z -> U.iter p (C.ho m) a + 20 <= U.f_wk K z.
Proof. exact (U.iter_ho_ub_le C.G 6 C.ho C_G_ub ltac:(lia) C.ho_0 C_ho_S). Qed.

Lemma f52 : 64 <= U.f 5 2.
Proof. pose proof C.f5_2_ge as H. pose proof (C_f 5 2) as E. lia. Qed.

(** ** J20_cube's exact count, from above.  (No tactic here matches or converts a hypothesis that holds a closed
    instance of the level maps.) *)
Lemma count_core : forall k3 a4 j b,
  b + 20 <= U.f_wk (S k3) (k3 + 30) ->
  a4 + 20 <= U.f_wk (S k3) (4 + b + 20) ->
  a4 + 2 * S k3 + 2 = 3 * S j ->
  2 * S j + 1 + 1 <= U.f_w2 (k3 + 30).
Proof.
  intros k3 a4 j b Hb Ha Hj.
  pose proof (U.f_wk_ge2 (S k3) (k3 + 30) ltac:(lia)) as G1.
  pose proof (U.iter_wk_le (S k3) 4 (k3 + 30) (k3 + 30) ltac:(lia) ltac:(lia)) as H4.
  rewrite !U.iter_S1, U.iter_0 in H4.
  pose proof (absorb (S k3) 4 (U.f_wk (S k3) (k3 + 30)) ltac:(lia) ltac:(lia)) as HX4.
  pose proof (U.f_wk_mono (S k3) (4 + b + 20) (U.f_wk (S k3) (U.f_wk (S k3) (k3 + 30))) ltac:(lia)) as H1.
  pose proof (U.f_wk_ge2 (S k3) (U.f_wk (S k3) (k3 + 30)) ltac:(lia)) as G2.
  pose proof (U.f_wk_ge2 (S k3) (U.f_wk (S k3) (U.f_wk (S k3) (k3 + 30))) ltac:(lia)) as G3.
  pose proof (absorb (S k3) (2 * k3 + 6) (U.f_wk (S k3) (U.f_wk (S k3) (U.f_wk (S k3) (k3 + 30)))) ltac:(lia) ltac:(lia)) as HW.
  pose proof (U.f_wk_le_w2 (S (S k3)) (k3 + 30) ltac:(lia) ltac:(lia)) as H5.
  lia.
Qed.

Lemma J20_count_ub : forall k3 a4 j,
  a4 = C.iter 4 (C.ho k3) (C.hoc 0 k3 10) ->
  a4 + 2 * S k3 + 2 = 3 * S j ->
  2 * S j + 1 + 1 <= U.f_w2 (k3 + 30).
Proof.
  intros k3 a4 j Ha4 Hj. rewrite C_iter in Ha4.
  pose proof (C_hoc_ub_le k3 0 10 (S k3) (k3 + 30) (le_n _) (side_30 k3)) as Hb.
  pose proof (C_iter_ho_ub 4 k3 (C.hoc 0 k3 10)) as Ha. rewrite <- Ha4 in Ha.
  exact (count_core k3 a4 j (C.hoc 0 k3 10) Hb Ha Hj).
Qed.

Lemma k3_core : forall k2 a3 k3,
  a3 + 20 <= U.f_wk (S k2) (k2 + 30) ->
  a3 + 2 * S k2 + 2 = 3 * S k3 + 2 ->
  k3 + 30 <= U.f_w2 (k2 + 30).
Proof.
  intros k2 a3 k3 Ha Hk3.
  pose proof (U.f_wk_ge2 (S k2) (k2 + 30) ltac:(lia)) as G1.
  pose proof (U.f_wk_le_w2 (S k2) (k2 + 30) ltac:(lia) ltac:(lia)) as H5.
  lia.
Qed.

Lemma J20_k3_ub : forall k2 a3 k3,
  a3 = C.hoc 0 k2 10 ->
  a3 + 2 * S k2 + 2 = 3 * S k3 + 2 ->
  k3 + 30 <= U.f_w2 (k2 + 30).
Proof.
  intros k2 a3 k3 Ha3 Hk3.
  pose proof (C_hoc_ub_le k2 0 10 (S k2) (k2 + 30) (le_n _) (side_30 k2)) as Ha. rewrite <- Ha3 in Ha.
  exact (k3_core k2 a3 k3 Ha Hk3).
Qed.

Lemma k2_core : forall k1 a2 k2 I z,
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

Lemma J20_k2_ub : forall k1 a2 k2,
  U.iter 2 (C.ho 0) 10 + 4 = 3 * S (S k1) + 1 ->
  a2 = C.hoc 0 (S k1) 10 ->
  a2 + 2 * S k1 + 2 = 3 * S (S k2) ->
  k2 + 30 <= U.f_w2 (U.f_w2 (U.f 5 2)).
Proof.
  intros k1 a2 k2 Hk1 Ha2 Hk2.
  pose proof (C_hoc_ub_le (S k1) 0 10 (S (S k1)) (k1 + 31) (le_n _) (side_31 k1)) as Ha. rewrite <- Ha2 in Ha.
  pose proof (C_iter_ho_ub_le 2 0 10 1 32 (le_n _) (le_n _)) as K1.
  exact (k2_core k1 a2 k2 _ (U.f 5 2) Hk1 K1 Ha Hk2 f52).
Qed.

(** ** The comparisons *)
Theorem B21_beats_J20cube_exact : exists c N, c0 -[ W.tm ]->* c /\ halted W.tm c /\ Sc.onesN c N /\
  forall k1 a2 k2 a3 k3 a4 j,
    C.iter 2 (C.ho 0) 10 + 4 = 3 * S (S k1) + 1 ->
    a2 = C.hoc 0 (S k1) 10 -> a2 + 2 * S k1 + 2 = 3 * S (S k2) ->
    a3 = C.hoc 0 k2 10 -> a3 + 2 * S k2 + 2 = 3 * S k3 + 2 ->
    a4 = C.iter 4 (C.ho k3) (C.hoc 0 k3 10) -> a4 + 2 * S k3 + 2 = 3 * S j ->
    2 * S j + 1 + 1 < N.
Proof.
  destruct W.sigma_lower_bound_wsq3 as (c & N & Hrun & Hhalt & Hones & HB).
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  intros k1 a2 k2 a3 k3 a4 j Hk1 Ha2 Hk2 Ha3 Hk3 Ha4 Hj.
  rewrite C_iter in Hk1.
  pose proof (J20_count_ub k3 a4 j Ha4 Hj) as H1.
  pose proof (J20_k3_ub k2 a3 k3 Ha3 Hk3) as H2.
  pose proof (J20_k2_ub k1 a2 k2 Hk1 Ha2 Hk2) as H3.
  exact (core (U.f 5 2) (Sc.tet 341) N k2 k3 j (tet_ge5 339) (f52_le_U (Sc.tet 341) (tet_ge5 339)) H3 H2 H1 HB).
Qed.

Theorem B21_beats_J20cube_score : exists NJ,
  (exists c, Individual202.Individual202.Permute.Flip.Compute.TM.evstep C.tm
               Individual202.Individual202.Permute.Flip.Compute.TM.c0 c /\
             Individual202.Individual202.Permute.Flip.Compute.TM.halted C.tm c /\
             C.ones c NJ) /\
  exists c N, c0 -[ W.tm ]->* c /\ halted W.tm c /\ Sc.onesN c N /\ NJ + 1 < N.
Proof.
  destruct C.score_exact as (k1 & a2 & k2 & a3 & k3 & a4 & j & cJ & Hk1 & Ha2 & Hk2 & Ha3 & Hk3 & Ha4 & Hj & HrunJ & HhaltJ & HonesJ).
  destruct B21_beats_J20cube_exact as (c & N & Hrun & Hhalt & Hones & HB).
  exists (2 * S j + 1). split; [exists cJ; auto |].
  exists c, N. split; [exact Hrun |]. split; [exact Hhalt |]. split; [exact Hones |].
  exact (HB k1 a2 k2 a3 k3 a4 j Hk1 Ha2 Hk2 Ha3 Hk3 Ha4 Hj).
Qed.

Print Assumptions B21_beats_J20cube_exact.
Print Assumptions B21_beats_J20cube_score.
