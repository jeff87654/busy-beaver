(** * C7Phases.v : the generated X' machine lemmas of C7's rebuild phases, restated on Kx / M1 (BB9/verify_c7).

    Far ends: e11 = the frame 11 (lft []), e1 = a single 1, eC = 00 D7 D1 e11 (after phase C), eD = D0 e11 (the
    counter), eE = 00 D2 D0 blank (counter end).  M1n: see below. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs KStep.
From XDev Require G_pa1 G_pa2 G_pd G_r30 G_e2 G_e3.
Opaque U arrow.
Local Open Scope nat_scope.

Definition e11 : side := lft [].
Definition e1 : side := S1 >> const S0.
Definition eC : side := S0 >> S0 >> lftx [7; 1] e11.
Definition eD : side := lftx [0] e11.
Definition eE : side := S0 >> S0 >> lftx [2; 0] (const S0).

(** M1n x t = 1001001 (11111001)^t 00 (100)^24 1 (001)^x 1100111 (nearest-first): PA1's target (the old c = x + 26). *)
Definition M1n (x t : nat) : Q * tape :=
  (S1 >> S0 >> S0 >> S1 >> S0 >> S0 >> S1 >> [S1;S1;S1;S1;S1;S0;S0;S1]^^t *> S0 >> S0 >> [S1;S0;S0]^^24 *> S1 >> [S0;S0;S1]^^x *>
   S1 >> S1 >> S0 >> S0 >> S1 >> S1 >> S1 >> const S0) {{B}}> const S0.

(** Phase A, part 1: the far-left transfer loop.  Kt(1^n;1;3R+2;t) -->+ M1n (9R+n-20) t. *)
Lemma pa1 : forall R n t, 1 <= R -> 11 <= n -> Kx (repeat 1 n) 1 (3 * R + 2) t e11 -->+ M1n (9 * R + n - 20) t.
Proof.
  intros R n t HR Hn. refine (prog_eq _ _ _ _ _ _ (G_pa1.PA1 (3 * R - 3) (n - 11) t)).
  - unfold Kx, e11. rewrite lftx_rep. cbn [lft].
    replace (3 * R + 2) with (5 + (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * R - 3)).
    replace n with (11 + (n - 11)) at 1 by lia. rewrite (pow_add [S1;S0;S1] 11 (n - 11)). reflexivity.
  - unfold M1n. replace (9 * R + n - 20) with ((n - 11) + 3 * (3 * R - 3)) by lia.
    rewrite (pow_add [S0;S0;S1] (n - 11) (3 * (3 * R - 3))), (pow_mul [S0;S0;S1] 3 (3 * R - 3)). reflexivity.
Qed.

(** Phase A, part 2 (x = 0 mod 5): M1n (5j) t -->+ CL [frame 1 | 1, K+5, 1^(K-1)] at t+2, K = 3j+14. *)
Lemma pa2 : forall j t, M1n (5 * j) t -->+ Kx (repeat 1 (3 * j + 12) ++ [3 * j + 19; 1]) 1 2 (2 + t) e1.
Proof.
  intros j t. refine (prog_eq _ _ _ _ _ _ (G_pa2.PA2 j t)).
  - unfold M1n. rewrite (pow_mul [S0;S0;S1] 5 j). reflexivity.
  - unfold Kx, e1. rewrite lftx_app, lftx_rep. cbn [lftx].
    rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 2 t).
    replace (3 * j + 12) with (12 + 3 * j) by lia. rewrite (pow_add [S1;S0;S1] 12), (pow_mul [S1;S0;S1] 3 j).
    replace (3 * j + 19) with (19 + 3 * j) by lia. rewrite (pow_add [S0;S1] 19), (pow_mul [S0;S1] 3 j). reflexivity.
Qed.

(** Phase C, part 2 (x = 2 mod 5): M1n (5j+2) t -->+ CL [frame 11 | 1, 7, 00, K-12, 1^K] at t+2, K = 3j+22. *)
Lemma pc2 : forall j t, M1n (5 * j + 2) t -->+ Kx (repeat 1 (3 * j + 21) ++ [3 * j + 10]) 1 2 (2 + t) eC.
Proof.
  intros j t. refine (prog_eq _ _ _ _ _ _ (G_pa2.PC2 j t)).
  - unfold M1n. replace (5 * j + 2) with (2 + 5 * j) by lia.
    rewrite (pow_add [S0;S0;S1] 2), (pow_mul [S0;S0;S1] 5 j). reflexivity.
  - unfold Kx, eC, e11. rewrite lftx_app, lftx_rep. cbn [lftx lft].
    rewrite (pow_add [S0;S0;S1;S1;S1;S1;S1;S1] 2 t).
    replace (3 * j + 21) with (21 + 3 * j) by lia. rewrite (pow_add [S1;S0;S1] 21), (pow_mul [S1;S0;S1] 3 j).
    replace (3 * j + 10) with (10 + 3 * j) by lia. rewrite (pow_add [S0;S1] 10), (pow_mul [S0;S1] 3 j). reflexivity.
Qed.

(** Phase D: Kx(1^K;1;3R+2;t;eC) -->+ CL [D0 e11 | 6R+12, 7, 1^(K-3)]. *)
Lemma pd : forall R K t, 1 <= R -> 20 <= K ->
  Kx (repeat 1 K) 1 (3 * R + 2) t eC -->+ Kx (repeat 1 (K - 3) ++ [7; 6 * R + 12]) 1 2 t eD.
Proof.
  intros R K t HR HK. refine (prog_eq _ _ _ _ _ _ (G_pd.PD (3 * R - 3) (K - 20) t)).
  - unfold Kx, eC, e11. rewrite lftx_rep. cbn [lftx lft].
    replace (3 * R + 2) with (5 + (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * R - 3)).
    replace K with (20 + (K - 20)) at 1 by lia. rewrite (pow_add [S1;S0;S1] 20 (K - 20)). reflexivity.
  - unfold Kx, eD, e11. rewrite lftx_app, lftx_rep. cbn [lftx lft].
    replace (K - 3) with (17 + (K - 20)) by lia. rewrite (pow_add [S1;S0;S1] 17 (K - 20)).
    replace (6 * R + 12) with (18 + 2 * (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 18), <- (pow0101 (3 * R - 3)).
    reflexivity.
Qed.

(** The counter's last borrow (token 3 -> 0): Kx(1^(N+1) ++ [3];1;3R+2;t;eD) -->+ Kx(1^N ++ [6R+7; 0];1;2;t;eD). *)
Lemma r30 : forall R N t, 1 <= R -> 5 <= N ->
  Kx (repeat 1 (S N) ++ [3]) 1 (3 * R + 2) t eD -->+ Kx (repeat 1 N ++ [6 * R + 7; 0]) 1 2 t eD.
Proof.
  intros R N t HR HN. refine (prog_eq _ _ _ _ _ _ (G_r30.R30 (3 * R - 3) (N - 5) t)).
  - unfold Kx, eD, e11. rewrite lftx_app, lftx_rep. cbn [lftx lft].
    replace (3 * R + 2) with (5 + (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * R - 3)).
    replace (S N) with (6 + (N - 5)) by lia. rewrite (pow_add [S1;S0;S1] 6 (N - 5)). reflexivity.
  - unfold Kx, eD, e11. rewrite lftx_app, lftx_rep. cbn [lftx lft].
    replace N with (5 + (N - 5)) at 1 by lia. rewrite (pow_add [S1;S0;S1] 5 (N - 5)).
    replace (6 * R + 7) with (13 + 2 * (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 13), <- (pow0101 (3 * R - 3)).
    reflexivity.
Qed.

(** Counter end, exhaustion 2: Kx(1^N;1;3R+2;t;D0 D0 e11) -->+ Kx(1^(N-1) ++ [6R+4];1;2;t;eE). *)
Lemma e2 : forall R N t, 1 <= R -> 6 <= N ->
  Kx (repeat 1 N) 1 (3 * R + 2) t (lftx [0] eD) -->+ Kx (repeat 1 (N - 1) ++ [6 * R + 4]) 1 2 t eE.
Proof.
  intros R N t HR HN. refine (prog_eq _ _ _ _ _ _ (G_e2.E2 (3 * R - 3) (N - 6) t)).
  - unfold Kx, eD, e11. rewrite lftx_rep. cbn [lftx lft].
    replace (3 * R + 2) with (5 + (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * R - 3)).
    replace N with (6 + (N - 6)) at 1 by lia. rewrite (pow_add [S1;S0;S1] 6 (N - 6)). reflexivity.
  - unfold Kx, eE. rewrite lftx_app, lftx_rep. cbn [lftx].
    replace (N - 1) with (5 + (N - 6)) by lia. rewrite (pow_add [S1;S0;S1] 5 (N - 6)).
    replace (6 * R + 4) with (10 + 2 * (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 10), <- (pow0101 (3 * R - 3)).
    reflexivity.
Qed.

(** Counter end, exhaustion 3 (the far frame is gone): Kx(1^N;1;3R+2;t;eE) -->+ Kx(1^(N-2) ++ [6R+10];1;2;t;blank). *)
Lemma e3 : forall R N t, 1 <= R -> 6 <= N ->
  Kx (repeat 1 N) 1 (3 * R + 2) t eE -->+ Kx (repeat 1 (N - 2) ++ [6 * R + 10]) 1 2 t (const S0).
Proof.
  intros R N t HR HN. refine (prog_eq _ _ _ _ _ _ (G_e3.E3 (3 * R - 3) (N - 6) t)).
  - unfold Kx, eE. rewrite lftx_rep. cbn [lftx].
    replace (3 * R + 2) with (5 + (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 5 (3 * R - 3)).
    replace N with (6 + (N - 6)) at 1 by lia. rewrite (pow_add [S1;S0;S1] 6 (N - 6)). reflexivity.
  - unfold Kx. rewrite lftx_app, lftx_rep. cbn [lftx].
    replace (N - 2) with (4 + (N - 6)) by lia. rewrite (pow_add [S1;S0;S1] 4 (N - 6)).
    replace (6 * R + 10) with (16 + 2 * (3 * R - 3)) by lia. rewrite (pow_add [S0;S1] 16), <- (pow0101 (3 * R - 3)).
    reflexivity.
Qed.
