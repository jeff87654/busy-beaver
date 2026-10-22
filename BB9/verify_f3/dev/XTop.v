(** * XTop.v : the top of X's run, from the blank tape to the first cascade moment (bb9_f3_coq).

    X differs from C04 only at its two top-level exhaustions (the far-left E0 reads 0 on its left and X takes
    K0 = 0RC, f3_0RC's I0).  The run (y1-fable's REPORT section 7; B = Bx, C04's level-0 accumulator):
      c0 -->* Kt(1^11; 1; 3B+2; 0)                                         (Abs.run_to_exhaustion, as in C04)
         -->+ [frame 1, D1, D(6B-2), D13, D1^4 | 1 ; 2], t = 3            (P1 = XREB1, exhaustion #1)
         -->* [frame 1, D1^7 | 1 ; 3 Rpp + 2], t = 3                       (two clears, CDPx at depth 4 and 5)
         -->+ Kt(1^(12 Rpp + 10) ++ [7]; 1; 2; 3)                           (P2 = XREB2, the frame-1 exhaustion)
         -->* Kt(1^(12 Rpp + 11); 1; 3 R2x + 2; 3)                          (clear of the digit 2)
         -->+ D0f 4 (36 Rpp + 38) 2 1 (6 R2x) blank                         (P3 = XTOPENTRY, exhaustion #2)
         -->+ D0f 7 (3 J + 2) (12 R2x + 11) 0 (J + 6) blank                 (XTOP1, sub-step c = 4; 5 J = 36 Rpp + 14)
         -->+ D0f 10 (S L1x) (12 R2x + 8) (J + 6) _ (1 >> blank)            (C04's step_stop: STOP, clear, ENTRY)
    with Rpp = 16 (mod 50) (arrow residues), so that every division is exact and L1x is odd and = 1 (mod 3).
    The result is [reach_topX : reachF Pmx L1x]; from there C04's cascade and endgame apply unchanged. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs Lift Orbit Step Fin.
From XDev Require G_xreb1 G_xreb2 G_xtop.
Opaque U arrow.

Local Open Scope nat_scope.

(** ** The constants *)
Definition e1 : side := S1 >> const S0.
Definition R1x : nat := iter 4 (U 4) O.
Definition Rpp : nat := iter (2 * Bx - 1) (U 5) R1x.
Definition R2x : nat := iter 2 (U (12 * Rpp + 10)) O.

(** ** Residues: 2 U j x + 4 is a tower 2^(2^(2^h)), h >= 2, hence = 36 (mod 100) *)
Lemma arrow_ge2 : forall k m, 1 <= k -> 1 <= m -> 2 <= arrow k 2 m.
Proof.
  intros k m Hk Hm. destruct (Nat.eq_dec m 1) as [-> | Hm1].
  - rewrite arrow_one. lia.
  - pose proof (arrow_gt_arg k m Hk ltac:(lia)). lia.
Qed.

Lemma arrow_tower : forall k n, 2 <= k -> 4 <= n -> exists h, 2 <= h /\ arrow k 2 n = 2 ^ (2 ^ (2 ^ h)).
Proof.
  induction k as [| k IH]; intros n Hk Hn; [lia |].
  destruct (Nat.eq_dec k 1) as [-> | Hk1].
  - exists (2 ^ arrow 2 2 (n - 4)). split.
    + assert (H1 : 1 <= arrow 2 2 (n - 4)).
      { destruct (n - 4) as [| m]; [rewrite arrow_S0; lia | pose proof (arrow_ge2 2 (S m) ltac:(lia) ltac:(lia)); lia]. }
      pose proof (Nat.pow_le_mono_r 2 1 _ ltac:(lia) H1). simpl in *. lia.
    + replace n with (S (S (S (S (n - 4))))) at 1 by lia.
      rewrite !arrow_SS, !arrow_1_pow. reflexivity.
  - replace n with (S (n - 1)) by lia. rewrite arrow_SS.
    apply IH; [lia |].
    pose proof (arrow_gt_arg (S k) (n - 1) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma pow16_mod20 : forall m, 1 <= m -> 16 ^ m mod 20 = 16.
Proof.
  induction m as [| m IH]; intro Hm; [lia |].
  destruct (Nat.eq_dec m 0) as [-> | Hm0]; [reflexivity |].
  rewrite Nat.pow_succ_r', Nat.mul_mod, IH by lia. reflexivity.
Qed.

Lemma pow76_mod100 : forall q, 1 <= q -> 76 ^ q mod 100 = 76.
Proof.
  induction q as [| q IH]; intro Hq; [lia |].
  destruct (Nat.eq_dec q 0) as [-> | Hq0]; [reflexivity |].
  rewrite Nat.pow_succ_r', Nat.mul_mod, IH by lia. reflexivity.
Qed.

Lemma pow2_20_mod100 : (2 ^ 20) mod 100 = 76.
Proof.
  change 20 with (10 + 10). rewrite Nat.pow_add_r, Nat.mul_mod by lia.
  change (2 ^ 10 mod 100) with 24. reflexivity.
Qed.

Lemma pow2_16_mod100 : (2 ^ 16) mod 100 = 36.
Proof.
  change 16 with (8 + 8). rewrite Nat.pow_add_r, Nat.mul_mod by lia.
  change (2 ^ 8 mod 100) with 56. reflexivity.
Qed.

Lemma pow2_20q_mod100 : forall q, 1 <= q -> (2 ^ 20) ^ q mod 100 = 76.
Proof.
  induction q as [| q IH]; intro Hq; [lia |].
  destruct (Nat.eq_dec q 0) as [-> | Hq0].
  - rewrite Nat.pow_1_r. exact pow2_20_mod100.
  - rewrite Nat.pow_succ_r', Nat.mul_mod, pow2_20_mod100, IH by lia. reflexivity.
Qed.

Lemma pow2_e16_mod100 : forall e, e mod 20 = 16 -> 2 ^ e mod 100 = 36.
Proof.
  intros e He. rewrite (Nat.div_mod_eq e 20), He, Nat.pow_add_r, Nat.pow_mul_r.
  rewrite Nat.mul_mod, pow2_16_mod100 by lia.
  destruct (e / 20) as [| q].
  - reflexivity.
  - rewrite pow2_20q_mod100 by lia. reflexivity.
Qed.

Lemma tower_mod100 : forall h, 2 <= h -> 2 ^ (2 ^ (2 ^ h)) mod 100 = 36.
Proof.
  intros h Hh. apply pow2_e16_mod100.
  assert (E : 2 ^ h = 4 * 2 ^ (h - 2)).
  { replace h with (2 + (h - 2)) at 1 by lia. rewrite Nat.pow_add_r. reflexivity. }
  rewrite E, Nat.pow_mul_r. change (2 ^ 4) with 16. apply pow16_mod20.
  pose proof (Nat.pow_nonzero 2 (h - 2) ltac:(lia)). lia.
Qed.

Lemma U_mod50 : forall j x, 1 <= j -> U j x mod 50 = 16.
Proof.
  intros j x Hj. pose proof (U_closed j x) as E.
  destruct (arrow_tower (S j) (2 * x + 4) ltac:(lia) ltac:(lia)) as [h [Hh E2]].
  pose proof (tower_mod100 h Hh) as M. rewrite <- E2, <- E in M.
  pose proof (Nat.div_mod_eq (2 * U j x + 4) 100) as D1.
  pose proof (Nat.div_mod_eq (U j x) 50) as D2. pose proof (Nat.mod_upper_bound (U j x) 50 ltac:(lia)).
  set (u := U j x) in *. clearbody u. lia.
Qed.

Lemma Rpp_mod50 : Rpp mod 50 = 16.
Proof.
  unfold Rpp. pose proof Bx_ge6.
  replace (2 * Bx - 1) with (S (2 * Bx - 2)) by lia. cbn [iter]. apply U_mod50. lia.
Qed.

(** ** P1: exhaustion #1 (XREB1, a = 3B - 3) and the two clears *)
Lemma lft_rep : forall n, lft (repeat 1%nat n) = [S1;S0;S1]^^n *> lft [].
Proof. intro n. rewrite <- (app_nil_r (repeat 1%nat n)) at 1. apply lft_ones. Qed.

Lemma tokd_far : tokd (2 * Bx - 1) = 4 + 2 * (3 * Bx - 3).
Proof. pose proof Bx_ge6. unfold tokd. lia. Qed.

Lemma xreb1 : Kg (repeat O 11) [] O Bx 0 -->+ Kgx (repeat O 4 ++ [4; 2 * Bx - 1; 0]) [] O O 3 e1.
Proof.
  pose proof Bx_ge6 as HB.
  refine (prog_eq _ _ _ _ _ _ (G_xreb1.XREB1 (3 * Bx - 3))).
  - unfold Kg, Kt. rewrite map_rep0, app_nil_r.
    replace (3 * Bx + 2) with (5 + (3 * Bx - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * Bx - 3)). reflexivity.
  - unfold Kgx. cbn [map app repeat]. rewrite tokd_far. unfold Kx, e1. cbn [lftx].
    rewrite (pow_add [S0;S1] 4 (2 * (3 * Bx - 3))), <- (pow0101 (3 * Bx - 3)). reflexivity.
Qed.

Lemma clears1 : Kgx (repeat O 4 ++ [4; 2 * Bx - 1; 0]) [] O O 3 e1 -->* Kgx (repeat O 7) [] O Rpp 3 e1.
Proof.
  assert (He : good e1) by (left; eexists; reflexivity).
  eapply evstep_trans; [apply (CDPx 4 4 [2 * Bx - 1; 0] [] O 3 e1 He) |].
  eapply evstep_trans; [apply (CDPx 5 (2 * Bx - 1) [0] [] (iter 4 (U 4) O) 3 e1 He) |].
  apply evstep_refl.
Qed.

(** ** P2: the frame-1 exhaustion (XREB2, c = 3 R) and the clear of the digit 2 *)
Lemma xreb2 : forall R, Kgx (repeat O 7) [] O R 3 e1 -->+ Kg (repeat O (12 * R + 10) ++ [2]) [] O O 3.
Proof.
  intro R. refine (prog_eq _ _ _ _ _ _ (G_xreb2.XREB2 (3 * R))).
  - unfold Kgx, Kx, e1. cbn [map app repeat lftx].
    replace (3 * R + 2) with (2 + 3 * R) by lia. rewrite (pow_add [S0;S1] 2 (3 * R)). reflexivity.
  - unfold Kg, Kt. rewrite (map_rep (12 * R + 10) [2]), map_single, app_nil_r.
    change (tokd 2) with 7%nat. rewrite lft_ones.
    replace (12 * R + 10) with (10 + 4 * (3 * R)) by lia.
    rewrite (pow_add [S1;S0;S1] 10 (4 * (3 * R))), (pow_mul [S1;S0;S1] 4 (3 * R)). reflexivity.
Qed.

Lemma clear2 : forall R, Kg (repeat O (12 * R + 10) ++ [2]) [] O O 3 -->*
  Kg (repeat O (S (12 * R + 10))) [] O (iter 2 (U (12 * R + 10)) O) 3.
Proof.
  intro R. rewrite <- (app_nil_r (repeat O (S (12 * R + 10)))) at 1. exact (CDP (12 * R + 10) 2 [] [] O 3).
Qed.

(** ** P3: exhaustion #2 (XTOPENTRY with N = 12 R + 6 and its R = 3 R2) and the first sub-step (XTOP1) *)
Lemma xte : forall R R2, 0 < R2 ->
  Kg (repeat O (S (12 * R + 10))) [] O R2 3 -->+ D0f 4 (36 * R + 38) 2 1 (6 * R2) (const S0).
Proof.
  intros R R2 HR2. refine (prog_eq _ _ _ _ _ _ (G_xtop.XTOPENTRY (12 * R + 6) (3 * R2) ltac:(lia))).
  - unfold Kg, Kt. rewrite map_rep0, app_nil_r, lft_rep.
    replace (S (12 * R + 10)) with (5 + (12 * R + 6)) by lia.
    replace (3 * R2 + 2) with (2 + 3 * R2) by lia.
    rewrite (pow_add [S1;S0;S1] 5 (12 * R + 6)), (pow_add [S0;S1] 2 (3 * R2)). reflexivity.
  - unfold D0f. replace (36 * R + 38) with (3 * (12 * R + 6) + 20) by lia.
    replace (6 * R2) with (2 * (3 * R2)) by lia.
    rewrite (pow_add [S1] (3 * (12 * R + 6)) 20), (pow_mul [S1] 3 (12 * R + 6)), <- (pow0101 (3 * R2)). reflexivity.
Qed.

Lemma xt1 : forall J t y, D0f t (5 * J + 24) 2 1 y (const S0) -->+ D0f (3 + t) (3 * J + 2) (2 * y + 11) 0 (J + 6) (const S0).
Proof.
  intros J t y. refine (prog_eq _ _ _ _ _ _ (G_xtop.XTOP1 J t y)).
  - unfold D0f. rewrite (pow_add [S1] (5 * J) 24), (pow_mul [S1] 5 J). reflexivity.
  - unfold D0f. replace (2 * y + 11) with (11 + 2 * y) by lia. replace (J + 6) with (6 + J) by lia.
    rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 3 t), (pow_add [S1] (3 * J) 2), (pow_mul [S1] 3 J), (pow_add [S0;S0;S1] 11 (2 * y)),
      (pow_mul [S0;S0;S1] 2 y), (pow_add [S0;S1] 6 J). reflexivity.
Qed.

(** ** The cascade start *)
Definition Jx : nat := (36 * Rpp + 14) / 5.
Definition ix : nat := (Jx - 13) / 5.
Definition L1x : nat := 9 * ix + 4.
Definition Pmx : nat := 12 * R2x + 8 - L1x.

Lemma x_vals : exists q, Rpp = 50 * q + 16 /\ Jx = 360 * q + 118 /\ ix = 72 * q + 21 /\ L1x = 648 * q + 193.
Proof.
  pose proof Rpp_mod50 as M. pose proof (Nat.div_mod_eq Rpp 50) as D.
  exists (Rpp / 50). set (q := Rpp / 50) in *.
  assert (ER : Rpp = 50 * q + 16) by lia.
  assert (EJ : Jx = 360 * q + 118) by (unfold Jx; apply div5_eq; lia).
  assert (Ei : ix = 72 * q + 21) by (unfold ix; rewrite EJ; apply div5_eq; lia).
  split; [exact ER |]. split; [exact EJ |]. split; [exact Ei |]. unfold L1x. lia.
Qed.

Lemma R2x_ge : 24 * Rpp + 26 <= R2x.
Proof.
  unfold R2x. cbn [iter]. pose proof (U0_ge (12 * Rpp + 10)). pose proof (U_lin (12 * Rpp + 10) (U (12 * Rpp + 10) O)).
  lia.
Qed.

Lemma L1x_props : 60 <= L1x /\ L1x mod 2 = 1 /\ L1x mod 3 = 1.
Proof.
  destruct x_vals as [q [_ [_ [_ EL]]]]. rewrite EL. split; [lia |]. split.
  - apply (mod_of _ 2 (324 * q + 96)); lia.
  - apply (mod_of _ 3 (216 * q + 64)); lia.
Qed.

Lemma Pmx_ge : 100 <= Pmx.
Proof. destruct x_vals as [q [ER [_ [_ EL]]]]. pose proof R2x_ge. unfold Pmx. lia. Qed.

Lemma reach_D0_top : c0 -->* D0f 7 (3 * Jx + 2) (12 * R2x + 11) 0 (Jx + 6) (const S0).
Proof.
  destruct x_vals as [q [ER [EJ _]]].
  eapply evstep_trans; [apply run_to_exhaustion |].
  eapply evstep_trans; [apply progress_evstep, xreb1 |].
  eapply evstep_trans; [apply clears1 |].
  eapply evstep_trans; [apply progress_evstep, xreb2 |].
  eapply evstep_trans; [apply clear2 |].
  change (iter 2 (U (12 * Rpp + 10)) O) with R2x.
  eapply evstep_trans; [apply progress_evstep, xte; pose proof R2x_ge; lia |].
  replace (36 * Rpp + 38) with (5 * Jx + 24) by lia.
  eapply evstep_trans; [apply progress_evstep, xt1 |].
  replace (2 * (6 * R2x) + 11) with (12 * R2x + 11) by lia. apply evstep_refl.
Qed.

Theorem reach_topX : reachF Pmx L1x.
Proof.
  destruct x_vals as [q [ER [EJ [Ei EL]]]]. pose proof R2x_ge as HR.
  destruct (step_stop ix (12 * R2x + 11) 0 7 (Jx + 6) (const S0) ltac:(lia) ltac:(lia)) as [R HS].
  exists (3 + 7), (12 * R2x + 11 - 3), (Jx + 6), (9 + 6 * R), ([S0;S1]^^0 *> S1 >> const S0).
  split; [| split; [lia | split; [unfold Pmx; lia | exists [S1]; reflexivity]]].
  eapply evstep_trans; [exact reach_D0_top |].
  replace (3 * Jx + 2) with (5 * (3 * ix + 2) + 31) by lia.
  replace (S L1x) with (3 * (3 * ix + 2) - 1) by (unfold L1x; lia).
  apply progress_evstep, HS.
Qed.
