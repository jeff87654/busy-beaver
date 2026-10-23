(** * HTop.v : the top of X3's run, from the blank tape to the first cascade moment (BB9/verify_h003).

    X3 (Base.v) simulates h003.  Its top level is a chain of five rebuilding tops (../1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC.md) and
    the exit (sec. 5):
      Tp K R t  := Kg (repeat O K) [] O R t          (= Kt(1^K;1;3R+2;t), right after the clear of Top(K))
      TopC K t  := Kg (repeat O (K-1) ++ [2]) [] O O t   (the CL moment Top(K), view "0*2 7 1*K")
      T1 (K = 5k+11): Tp K R t -->+ TopC (12R+9k+27) (3+t)                   (G_t1_T1a, G_t1_T1b)
      T3 (K = 5k+13): -> CL "0 1 (6R+1) (3k+13) 1*(3k+5)" (G_tops_P3), two clears, PB (HPhB.pb)
      T4 (K = 5k+14): -> CL "0 1 (6R+5) 2 00 (3k+10) 1*(3k+3)" (G_tops_P4), clear, G_tops_P4b, two clears, PB
      TX (K = 10h+15): Tp K R t -->+ D0f (1+t) (3K-1) 2 1 (6R+3) blank (G_tops_TXa), then the sub-step at P = 2 (G_xt1.XTOP1, run 5J+24)
    The real orbit: Tp 11 Bx 0 -> Top(K0), K0 = 12Bx+27 = 4 (mod 5) -> T4 -> T3 -> T1 -> T1 -> TX, with the
    residues of HArith (every accumulator = rho mod Mres, Res.v).  The result [reach_topH : reachF PmH L1H] is the
    start of C04's cascade (Fin.v), from where f3's generalised endgame applies unchanged. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List ZArith.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs KStep Lift HPhB Res HArith.
From XDev Require G_t1_T1a1 G_t1_T1a2a G_t1_YR G_t1_YE G_t1_T1b G_tops_P3 G_tops_P4 G_tops_P4b G_tops_TXa G_xt1.
Opaque U arrow.

Local Open Scope nat_scope.

(** ** The far ends *)
Definition f4 (R : nat) : side := S0 >> S0 >> lftx [2; 6 * R + 5; 1] e1.

Lemma good_e1 : good e1.
Proof. left. eexists. reflexivity. Qed.
Lemma good_f4 : forall R, good (f4 R).
Proof. intro R. right. eexists. reflexivity. Qed.

Definition Tp (K R t : nat) : Q * tape := Kg (repeat O K) [] O R t.
Definition TopC (K t : nat) : Q * tape := Kg (repeat O (K - 1) ++ [2]) [] O O t.

Lemma Tp_Kx : forall K R t, Tp K R t = Kx (repeat 1 K) 1 (3 * R + 2) t e11.
Proof. intros. unfold Tp, Kg. rewrite map_rep0, app_nil_r. rewrite Kt_Kx. reflexivity. Qed.

Lemma TopC_Kx : forall K t, 1 <= K -> TopC K t = Kx (repeat 1 (K - 1) ++ [7]) 1 2 t e11.
Proof.
  intros K t HK. unfold TopC, Kg. rewrite map_rep, app_nil_r, Kt_Kx. reflexivity.
Qed.

Lemma top_clear : forall K t, 1 <= K -> TopC K t -->* Tp K (iter 2 (U (K - 1)) O) t.
Proof.
  intros K t HK. unfold TopC, Tp.
  eapply evstep_trans; [apply (CDP (K - 1) 2 [] [] O t) |].
  replace (S (K - 1)) with K by lia. rewrite app_nil_r. apply evstep_refl.
Qed.

(** ** The generated phases restated on Kx *)
(** T1a in pieces: T1a1 (to the moment M1), T1a2a (to the far-left transfer loop Yc x m t with the merged token
    x = 2a+3k+18), the loop (YR, by induction), its end (YE). *)
Definition Yc (n m t : nat) : Q * tape :=
  (S1 >> const S0) {{A}}> (S1 >> [S1;S0]^^n *> S0 >> [S1;S0;S1]^^m *> S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> S0 >> S0 >>
    [S1;S0;S0;S1;S1;S1;S0;S0]^^t *> S1 >> S0 >> S0 >> S1 >> S0 >> S1 >> const S0).

Lemma yr : forall n m t, Yc (n + 2) m t -->+ Yc (n + 1) (m + 2) t.
Proof.
  intros n m t. refine (prog_eq _ _ _ _ _ _ (G_t1_YR.YR m n t)).
  - unfold Yc. replace (n + 2) with (2 + n) by lia. rewrite (pow_add [S1;S0] 2 n). reflexivity.
  - unfold Yc. replace (n + 1) with (1 + n) by lia. replace (m + 2) with (2 + m) by lia.
    rewrite (pow_add [S1;S0] 1 n), (pow_add [S1;S0;S1] 2 m). reflexivity.
Qed.

Lemma yloop : forall n m t, Yc (n + 1) m t -->* Yc 1 (m + 2 * n) t.
Proof.
  induction n as [| n IH]; intros m t.
  - replace (m + 2 * 0) with m by lia. apply evstep_refl.
  - replace (S n + 1) with (n + 2) by lia.
    eapply evstep_trans; [apply progress_evstep, yr |].
    replace (m + 2 * S n) with ((m + 2) + 2 * n) by lia. apply IH.
Qed.

Lemma ye : forall m t, Yc 1 (m + 6) t -->+ Kx (repeat 1 (m + 1) ++ [3]) 1 2 (3 + t) e1.
Proof.
  intros m t. refine (prog_eq _ _ _ _ _ _ (G_t1_YE.YE m t)).
  - unfold Yc. replace (m + 6) with (6 + m) by lia. rewrite (pow_add [S1;S0;S1] 6 m). reflexivity.
  - unfold Kx, e1. rewrite lftx_app, lftx_rep. cbn [lftx].
    rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 3 t).
    replace (m + 1) with (1 + m) by lia. rewrite (pow_add [S1;S0;S1] 1 m). reflexivity.
Qed.

Lemma t1a : forall k R t, 1 <= R ->
  Kx (repeat 1 (5 * k + 11)) 1 (3 * R + 2) t e11 -->+ Kx (repeat 1 (12 * R + 9 * k + 27) ++ [3]) 1 2 (3 + t) e1.
Proof.
  intros k R t HR. set (a := 3 * R - 3).
  assert (H1 : Kx (repeat 1 (5 * k + 11)) 1 (3 * R + 2) t e11 -->+ Yc (2 * a + 3 * k + 18) (3 * k + 10) t).
  { eapply progress_trans; [| refine (prog_eq _ _ _ _ _ _ (G_t1_T1a2a.T1a2a a k t)); [reflexivity |] ].
    - refine (prog_eq _ _ _ _ _ _ (G_t1_T1a1.T1a1 a k t)); [| reflexivity].
      unfold Kx, e11, a. rewrite lftx_rep. cbn [lftx lft].
      replace (3 * R + 2) with (5 + (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * R - 3)).
      replace (5 * k + 11) with (11 + 5 * k) by lia. rewrite (pow_add [S1;S0;S1] 11 (5 * k)), (pow_mul [S1;S0;S1] 5 k).
      reflexivity.
    - unfold Yc. replace (2 * a + 3 * k + 18) with (18 + (2 * a + 3 * k)) by lia.
      rewrite (pow_add [S1;S0] 18 (2 * a + 3 * k)), (pow_add [S1;S0] (2 * a) (3 * k)), (pow_mul [S1;S0] 2 a),
        (pow_mul [S1;S0] 3 k).
      replace (3 * k + 10) with (10 + 3 * k) by lia. rewrite (pow_add [S1;S0;S1] 10 (3 * k)), (pow_mul [S1;S0;S1] 3 k).
      reflexivity. }
  eapply progress_evstep_trans; [exact H1 |].
  replace (2 * a + 3 * k + 18) with ((2 * a + 3 * k + 17) + 1) by lia.
  eapply evstep_trans; [apply yloop |].
  replace (3 * k + 10 + 2 * (2 * a + 3 * k + 17)) with ((12 * R + 9 * k + 26) + 6) by (unfold a; lia).
  replace (12 * R + 9 * k + 27) with ((12 * R + 9 * k + 26) + 1) by lia.
  apply progress_evstep, ye.
Qed.

Lemma t1b : forall n t, 5 <= n -> Kx (repeat 1 (S n) ++ [3]) 1 2 t e1 -->+ Kx (repeat 1 n ++ [7]) 1 2 t e11.
Proof.
  intros n t Hn. refine (prog_eq _ _ _ _ _ _ (G_t1_T1b.T1b (n - 5) t)).
  - unfold Kx, e1. rewrite lftx_app, lftx_rep. cbn [lftx].
    replace (S n) with (6 + (n - 5)) by lia. rewrite (pow_add [S1;S0;S1] 6 (n - 5)). reflexivity.
  - unfold Kx, e11. rewrite lftx_app, lftx_rep. cbn [lftx lft].
    replace n with (5 + (n - 5)) at 1 by lia. rewrite (pow_add [S1;S0;S1] 5 (n - 5)). reflexivity.
Qed.

Lemma p3 : forall k R t, 1 <= R ->
  Kx (repeat 1 (5 * k + 13)) 1 (3 * R + 2) t e11 -->+
  Kx (repeat 1 (3 * k + 4) ++ [3 * k + 13; 6 * R + 1; 1]) 1 2 (3 + t) e1.
Proof.
  intros k R t HR. refine (prog_eq _ _ _ _ _ _ (G_tops_P3.P3 (3 * R - 3) k t)).
  - unfold Kx, e11. rewrite lftx_rep. cbn [lftx lft].
    replace (3 * R + 2) with (5 + (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * R - 3)).
    replace (5 * k + 13) with (13 + 5 * k) by lia. rewrite (pow_add [S1;S0;S1] 13 (5 * k)), (pow_mul [S1;S0;S1] 5 k).
    reflexivity.
  - unfold Kx, e1. rewrite lftx_app, lftx_rep. cbn [lftx].
    rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 3 t).
    replace (3 * k + 4) with (4 + 3 * k) by lia. rewrite (pow_add [S1;S0;S1] 4 (3 * k)), (pow_mul [S1;S0;S1] 3 k).
    replace (3 * k + 13) with (13 + 3 * k) by lia. rewrite (pow_add [S0;S1] 13 (3 * k)), (pow_mul [S0;S1] 3 k).
    replace (6 * R + 1) with (7 + 2 * (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 7 (2 * (3 * R - 3))), <- (pow0101 (3 * R - 3)).
    reflexivity.
Qed.

Lemma p4 : forall k R t, 1 <= R ->
  Kx (repeat 1 (5 * k + 14)) 1 (3 * R + 2) t e11 -->+ Kx (repeat 1 (3 * k + 2) ++ [3 * k + 10]) 1 2 (3 + t) (f4 R).
Proof.
  intros k R t HR. refine (prog_eq _ _ _ _ _ _ (G_tops_P4.P4 (3 * R - 3) k t)).
  - unfold Kx, e11. rewrite lftx_rep. cbn [lftx lft].
    replace (3 * R + 2) with (5 + (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * R - 3)).
    replace (5 * k + 14) with (14 + 5 * k) by lia. rewrite (pow_add [S1;S0;S1] 14 (5 * k)), (pow_mul [S1;S0;S1] 5 k).
    reflexivity.
  - unfold Kx, f4, e1. rewrite lftx_app, lftx_rep. cbn [lftx].
    rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 3 t).
    replace (3 * k + 2) with (2 + 3 * k) by lia. rewrite (pow_add [S1;S0;S1] 2 (3 * k)), (pow_mul [S1;S0;S1] 3 k).
    replace (3 * k + 10) with (10 + 3 * k) by lia. rewrite (pow_add [S0;S1] 10 (3 * k)), (pow_mul [S0;S1] 3 k).
    replace (6 * R + 5) with (11 + 2 * (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 11 (2 * (3 * R - 3))), <- (pow0101 (3 * R - 3)).
    reflexivity.
Qed.

Lemma p4b : forall k R Rb t, 1 <= R -> 1 <= Rb ->
  Kx (repeat 1 (k + 3)) 1 (3 * Rb + 2) t (f4 R) -->+ Kx (repeat 1 (k + 1) ++ [6 * Rb + 10; 6 * R + 4; 1]) 1 2 t e1.
Proof.
  intros k R Rb t HR HRb. refine (prog_eq _ _ _ _ _ _ (G_tops_P4b.P4b (3 * R - 3) (3 * Rb - 3) k t)).
  - unfold Kx, f4, e1. rewrite lftx_rep. cbn [lftx].
    replace (3 * Rb + 2) with (5 + (3 * Rb - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * Rb - 3)).
    replace (k + 3) with (3 + k) by lia. rewrite (pow_add [S1;S0;S1] 3 k).
    replace (6 * R + 5) with (11 + 2 * (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 11 (2 * (3 * R - 3))), <- (pow0101 (3 * R - 3)).
    reflexivity.
  - unfold Kx, e1. rewrite lftx_app, lftx_rep. cbn [lftx].
    replace (k + 1) with (1 + k) by lia. rewrite (pow_add [S1;S0;S1] 1 k).
    replace (6 * Rb + 10) with (16 + 2 * (3 * Rb - 3)) by lia. rewrite (pow_add [S0;S1] 16 (2 * (3 * Rb - 3))), <- (pow0101 (3 * Rb - 3)).
    replace (6 * R + 4) with (10 + 2 * (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 10 (2 * (3 * R - 3))), <- (pow0101 (3 * R - 3)).
    reflexivity.
Qed.

Lemma txa : forall k R t, 1 <= R ->
  Kx (repeat 1 (5 * k + 15)) 1 (3 * R + 2) t e11 -->+ D0f (1 + t) (15 * k + 44) 2 1 (6 * R + 3) (const S0).
Proof.
  intros k R t HR. refine (prog_eq _ _ _ _ _ _ (G_tops_TXa.TXa (3 * R - 3) k t)).
  - unfold Kx, e11. rewrite lftx_rep. cbn [lftx lft].
    replace (3 * R + 2) with (5 + (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * R - 3)).
    replace (5 * k + 15) with (15 + 5 * k) by lia. rewrite (pow_add [S1;S0;S1] 15 (5 * k)), (pow_mul [S1;S0;S1] 5 k).
    reflexivity.
  - unfold D0f. rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 1 t).
    rewrite (pow_add [S1] (15 * k) 44), (pow_mul [S1] 15 k).
    replace (6 * R + 3) with (9 + 2 * (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 9 (2 * (3 * R - 3))), <- (pow0101 (3 * R - 3)).
    reflexivity.
Qed.

Lemma top1 : forall J t y, D0f t (5 * J + 24) 2 1 y (const S0) -->+ D0f (3 + t) (3 * J + 2) (2 * y + 11) 0 (J + 6) (const S0).
Proof.
  intros J t y. refine (prog_eq _ _ _ _ _ _ (G_xt1.XTOP1 J t y)).
  - unfold D0f. rewrite (pow_add [S1] (5 * J) 24), (pow_mul [S1] 5 J). reflexivity.
  - unfold D0f. replace (2 * y + 11) with (11 + 2 * y) by lia. replace (J + 6) with (6 + J) by lia.
    rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 3 t), (pow_add [S1] (3 * J) 2), (pow_mul [S1] 3 J), (pow_add [S0;S0;S1] 11 (2 * y)),
      (pow_mul [S0;S0;S1] 2 y), (pow_add [S0;S1] 6 J). reflexivity.
Qed.

(** ** The tops on Kg *)
Lemma Kgx_eq : forall ds suf a b t e, Kgx ds suf a b t e = Kx (map tokd ds ++ suf) (3 * a + 1) (3 * b + 2) t e.
Proof. reflexivity. Qed.

Lemma acc_pos : forall v j B, 1 <= v -> 1 <= iter v (U j) B.
Proof.
  intros [| v] j B Hv; [lia |]. cbn [iter]. pose proof (U_lin j (iter v (U j) B)). lia.
Qed.

Theorem T1 : forall k R t, 1 <= R -> Tp (5 * k + 11) R t -->+ TopC (12 * R + 9 * k + 27) (3 + t).
Proof.
  intros k R t HR. rewrite Tp_Kx, TopC_Kx by lia.
  eapply progress_trans; [apply t1a, HR |].
  replace (12 * R + 9 * k + 27) with (S (12 * R + 9 * k + 27 - 1)) at 1 by lia. apply t1b. lia.
Qed.

Definition Rb3 (k : nat) : nat := iter (k + 4) (U (3 * k + 4)) O.
Definition Rc3 (k R : nat) : nat := iter (2 * R) (U (3 * k + 5)) (Rb3 k).

Theorem T3 : forall k R t, 1 <= R -> 2 <= k -> Tp (5 * k + 13) R t -->+ TopC (12 * Rc3 k R + 3 * k + 11) (3 + t).
Proof.
  intros k R t HR Hk. rewrite Tp_Kx.
  eapply progress_evstep_trans; [apply p3, HR |].
  assert (E1 : Kx (repeat 1 (3 * k + 4) ++ [3 * k + 13; 6 * R + 1; 1]) 1 2 (3 + t) e1 =
               Kgx (repeat O (3 * k + 4) ++ [k + 4; 2 * R; O]) [] O O (3 + t) e1).
  { rewrite Kgx_eq, map_rep, app_nil_r. cbn [map]. unfold tokd.
    replace (3 * (k + 4) + 1) with (3 * k + 13) by lia. replace (3 * (2 * R) + 1) with (6 * R + 1) by lia. reflexivity. }
  rewrite E1.
  eapply evstep_trans; [apply (CDPx (3 * k + 4) (k + 4) [2 * R; O] [] O (3 + t) e1 good_e1) |].
  replace (S (3 * k + 4)) with (3 * k + 5) by lia. fold (Rb3 k).
  eapply evstep_trans; [apply (CDPx (3 * k + 5) (2 * R) [O] [] (Rb3 k) (3 + t) e1 good_e1) |].
  fold (Rc3 k R).
  assert (E2 : Kgx (repeat O (S (3 * k + 5)) ++ [O]) [] O (Rc3 k R) (3 + t) e1 =
               Kx (repeat 1 (3 * k + 6) ++ [1]) 1 (3 * Rc3 k R + 2) (3 + t) e1).
  { rewrite Kgx_eq, map_rep, app_nil_r. replace (S (3 * k + 5)) with (3 * k + 6) by lia. reflexivity. }
  rewrite E2, TopC_Kx by lia.
  assert (HRc : 1 <= Rc3 k R) by (unfold Rc3; apply acc_pos; lia).
  replace (12 * Rc3 k R + 3 * k + 11 - 1) with (12 * Rc3 k R + (3 * k + 6) + 4) by lia.
  apply progress_evstep, pb; lia.
Qed.

Definition Rb4 (k : nat) : nat := iter (k + 3) (U (3 * k + 2)) O.
Definition Rc4 (k : nat) : nat := iter (2 * Rb4 k + 3) (U (3 * k + 1)) O.
Definition Rd4 (k R : nat) : nat := iter (2 * R + 1) (U (3 * k + 2)) (Rc4 k).

Theorem T4 : forall k R t, 1 <= R -> 3 <= k -> Tp (5 * k + 14) R t -->+ TopC (12 * Rd4 k R + 3 * k + 8) (3 + t).
Proof.
  intros k R t HR Hk. rewrite Tp_Kx.
  eapply progress_evstep_trans; [apply p4, HR |].
  assert (E1 : Kx (repeat 1 (3 * k + 2) ++ [3 * k + 10]) 1 2 (3 + t) (f4 R) =
               Kgx (repeat O (3 * k + 2) ++ [k + 3]) [] O O (3 + t) (f4 R)).
  { rewrite Kgx_eq, map_rep, app_nil_r. cbn [map]. unfold tokd. replace (3 * (k + 3) + 1) with (3 * k + 10) by lia. reflexivity. }
  rewrite E1.
  eapply evstep_trans; [apply (CDPx (3 * k + 2) (k + 3) [] [] O (3 + t) (f4 R) (good_f4 R)) |].
  fold (Rb4 k).
  assert (HRb : 1 <= Rb4 k) by (unfold Rb4; apply acc_pos; lia).
  assert (E2 : Kgx (repeat O (S (3 * k + 2)) ++ []) [] O (Rb4 k) (3 + t) (f4 R) =
               Kx (repeat 1 ((3 * k) + 3)) 1 (3 * Rb4 k + 2) (3 + t) (f4 R)).
  { rewrite Kgx_eq, !app_nil_r, map_rep0. replace (S (3 * k + 2)) with (3 * k + 3) by lia. reflexivity. }
  rewrite E2.
  eapply evstep_trans; [apply progress_evstep, (p4b (3 * k) R (Rb4 k) (3 + t) HR HRb) |].
  assert (E3 : Kx (repeat 1 (3 * k + 1) ++ [6 * Rb4 k + 10; 6 * R + 4; 1]) 1 2 (3 + t) e1 =
               Kgx (repeat O (3 * k + 1) ++ [2 * Rb4 k + 3; 2 * R + 1; O]) [] O O (3 + t) e1).
  { rewrite Kgx_eq, map_rep, app_nil_r. cbn [map]. unfold tokd.
    replace (3 * (2 * Rb4 k + 3) + 1) with (6 * Rb4 k + 10) by lia. replace (3 * (2 * R + 1) + 1) with (6 * R + 4) by lia.
    reflexivity. }
  rewrite E3.
  eapply evstep_trans; [apply (CDPx (3 * k + 1) (2 * Rb4 k + 3) [2 * R + 1; O] [] O (3 + t) e1 good_e1) |].
  fold (Rc4 k). replace (S (3 * k + 1)) with (3 * k + 2) by lia.
  eapply evstep_trans; [apply (CDPx (3 * k + 2) (2 * R + 1) [O] [] (Rc4 k) (3 + t) e1 good_e1) |].
  fold (Rd4 k R).
  assert (HRd : 1 <= Rd4 k R) by (unfold Rd4; apply acc_pos; lia).
  assert (E4 : Kgx (repeat O (S (3 * k + 2)) ++ [O]) [] O (Rd4 k R) (3 + t) e1 =
               Kx (repeat 1 (3 * k + 3) ++ [1]) 1 (3 * Rd4 k R + 2) (3 + t) e1).
  { rewrite Kgx_eq, map_rep, app_nil_r. replace (S (3 * k + 2)) with (3 * k + 3) by lia. reflexivity. }
  rewrite E4, TopC_Kx by lia.
  replace (12 * Rd4 k R + 3 * k + 8 - 1) with (12 * Rd4 k R + (3 * k + 3) + 4) by lia.
  apply progress_evstep, pb; lia.
Qed.

Theorem TX : forall h R t, 1 <= R ->
  Tp (10 * h + 15) R t -->+ D0f (4 + t) (18 * h + 14) (12 * R + 17) 0 (6 * h + 10) (const S0).
Proof.
  intros h R t HR. rewrite Tp_Kx. replace (10 * h + 15) with (5 * (2 * h) + 15) by lia.
  eapply progress_trans; [apply txa, HR |].
  replace (15 * (2 * h) + 44) with (5 * (6 * h + 4) + 24) by lia.
  replace (4 + t) with (3 + (1 + t)) by lia. replace (18 * h + 14) with (3 * (6 * h + 4) + 2) by lia.
  replace (12 * R + 17) with (2 * (6 * R + 3) + 11) by lia. replace (6 * h + 10) with (6 * h + 4 + 6) by lia.
  apply top1.
Qed.

(** ** The real orbit *)
Definition K0 : nat := 12 * Bx + 27.
Definition Ra0 : nat := iter 2 (U (K0 - 1)) O.
Definition k0 : nat := (K0 - 14) / 5.
Definition Rd0 : nat := Rd4 k0 Ra0.
Definition K1 : nat := 12 * Rd0 + 3 * k0 + 8.
Definition Ra1 : nat := iter 2 (U (K1 - 1)) O.
Definition k1 : nat := (K1 - 13) / 5.
Definition Rc1 : nat := Rc3 k1 Ra1.
Definition K2 : nat := 12 * Rc1 + 3 * k1 + 11.
Definition Ra2 : nat := iter 2 (U (K2 - 1)) O.
Definition k2 : nat := (K2 - 11) / 5.
Definition K3 : nat := 12 * Ra2 + 9 * k2 + 27.
Definition Ra3 : nat := iter 2 (U (K3 - 1)) O.
Definition k3 : nat := (K3 - 11) / 5.
Definition K4 : nat := 12 * Ra3 + 9 * k3 + 27.
Definition Ra4 : nat := iter 2 (U (K4 - 1)) O.
Definition hx : nat := (K4 - 15) / 10.

Lemma div_exact : forall a d q r, 0 < d -> a = d * q + r -> (a - r) / d = q.
Proof.
  intros a d q r Hd ->. replace (d * q + r - r) with (q * d) by lia. apply Nat.div_mul. lia.
Qed.

Lemma pos2 : forall K, 1 <= iter 2 (U K) O.
Proof. intro K. apply acc_pos. lia. Qed.

Lemma res2 : forall K, 3 <= K -> (Z.of_nat (iter 2 (U (K - 1)) O) mod Mres = rho)%Z.
Proof. intros K HK. apply iter_U_res; lia. Qed.

Lemma orbit_vals : K0 = 5 * k0 + 14 /\ K1 = 5 * k1 + 13 /\ K2 = 5 * k2 + 11 /\ K3 = 5 * k3 + 11 /\ K4 = 10 * hx + 15 /\
  1000 <= k0 /\ 1000 <= k1 /\ 1000 <= k2 /\ 1000 <= k3 /\ 1000 <= hx.
Proof.
  pose proof (pos2 (K0 - 1)) as P0. fold Ra0 in P0.
  pose proof (pos2 (K1 - 1)) as P1. fold Ra1 in P1.
  assert (HB : (Z.of_nat Bx mod Mres = rho)%Z) by exact Bx_res.
  assert (H1 : (Z.of_nat Rd0 mod Mres = rho)%Z) by (unfold Rd0, Rd4; apply iter_U_res; lia).
  assert (H2 : (Z.of_nat Rc1 mod Mres = rho)%Z) by (unfold Rc1, Rc3; apply iter_U_res; lia).
  assert (H3 : (Z.of_nat Ra2 mod Mres = rho)%Z) by (unfold Ra2; apply res2; unfold K2; lia).
  assert (H4 : (Z.of_nat Ra3 mod Mres = rho)%Z) by (unfold Ra3; apply res2; unfold K3; lia).
  destruct (h_arith Bx Rd0 Rc1 Ra2 Ra3 HB H1 H2 H3 H4) as [a0 [a1 [a2 [a3 [a4 [E0 [E1 [E2 [E3 [E4 [B0 [B1 [B2 [B3 B4]]]]]]]]]]]]]].
  clear HB H1 H2 H3 H4.
  assert (F0 : k0 = a0) by (unfold k0, K0; apply div_exact; lia).
  assert (F1 : k1 = a1) by (unfold k1, K1; apply div_exact; lia).
  assert (F2 : k2 = a2) by (unfold k2, K2; apply div_exact; lia).
  assert (F3 : k3 = a3) by (unfold k3, K3; apply div_exact; lia).
  assert (F4 : hx = a4) by (unfold hx, K4; apply div_exact; lia).
  unfold K0, K1, K2, K3, K4. repeat split; lia.
Qed.

(** ** The run to the first cascade moment *)
Lemma clear_to : forall K t K' R', K' = K -> R' = iter 2 (U (K - 1)) O -> 1 <= K -> TopC K' t -->* Tp K R' t.
Proof. intros K t K' R' -> -> HK. apply top_clear, HK. Qed.

Theorem reach_D0_top : c0 -->* D0f 19 (18 * hx + 14) (12 * Ra4 + 17) 0 (6 * hx + 10) (const S0).
Proof.
  destruct orbit_vals as [E0 [E1 [E2 [E3 [E4 [B0 [B1 [B2 [B3 B4]]]]]]]]].
  pose proof (pos2 (K0 - 1)) as P0. fold Ra0 in P0.
  pose proof (pos2 (K1 - 1)) as P1. fold Ra1 in P1.
  pose proof (pos2 (K2 - 1)) as P2. fold Ra2 in P2.
  pose proof (pos2 (K3 - 1)) as P3. fold Ra3 in P3.
  pose proof (pos2 (K4 - 1)) as P4. fold Ra4 in P4.
  pose proof Bx_ge6 as HB.
  eapply evstep_trans; [apply run_to_exhaustion |].
  change (Kg (repeat O 11) [] O Bx 0) with (Tp (5 * 0 + 11) Bx 0).
  eapply evstep_trans; [apply progress_evstep, T1; lia |].
  eapply evstep_trans; [apply (clear_to K0 3); [unfold K0; lia | reflexivity | lia] |].
  fold Ra0. rewrite E0.
  eapply evstep_trans; [apply progress_evstep, T4; lia |].
  eapply evstep_trans; [apply (clear_to K1 6); [unfold K1, Rd0; lia | reflexivity | lia] |].
  fold Ra1. rewrite E1.
  eapply evstep_trans; [apply progress_evstep, T3; lia |].
  eapply evstep_trans; [apply (clear_to K2 9); [unfold K2, Rc1; lia | reflexivity | lia] |].
  fold Ra2. rewrite E2.
  eapply evstep_trans; [apply progress_evstep, T1; lia |].
  eapply evstep_trans; [apply (clear_to K3 12); [unfold K3; lia | reflexivity | lia] |].
  fold Ra3. rewrite E3.
  eapply evstep_trans; [apply progress_evstep, T1; lia |].
  eapply evstep_trans; [apply (clear_to K4 15); [unfold K4; lia | reflexivity | lia] |].
  fold Ra4. rewrite E4.
  apply progress_evstep, TX. lia.
Qed.
