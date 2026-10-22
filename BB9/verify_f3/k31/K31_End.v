(** * K31_End.v : the key-31 endgame, abstractly.

    From the D0 moment at sketch key 31 (my L = 32):
      D0f t 32 P s y l  -->+  [ell,s,y,4,5,2,6,5 | K ; 2]                    (AbsE1, K = P - 20)
                        -->+  [ell,s,y,4,5,2,6,2,7 | K-1 ; 2]                 (the borrow, R3f)
                        -->*  [ell,s,y,4,5,2,6,2 | K ; 3 R_E + 2]             (ESC clear, R_E = iter 2 (U (K-1)) 0)
                        -->+  E2 form by rho = K mod 5 (K = 5w + 15 + rho)   (AE2_rho)
                        -->*  counters / X1, X3, X4 / one- and two-digit clears (COUNT, CLR, CLR2d)
                        -->+  halt (H reading 1)                              (AH0)
    and the halting tape has at least 6 R_l + 2 ones with R_l >= R_E (rho = 2: R_l = R_E, from the surviving token 6R_E+1).
    Kx / lftx far side: e0 = 1 >> l (the D0f far side), G = [5;4;y;s] the tokens in front of it. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs Lift Step.
From XK31 Require Import K31_Abs K31_Mach.
Opaque U arrow.

(** The halting configurations of the routes. *)
Definition Hc (d s : nat) (G : list nat) (l : side) (R n t : nat) : Q * tape :=
  (1 >> [0;1]^^d *> 1 >> [0;1]^^s *> lftx G (1 >> l)) <{{J}} HR R n t.

Lemma Hc_halted : forall d s G l R n t, halted tm (Hc d s G l R n t).
Proof. intros. reflexivity. Qed.

Lemma Hc_ones : forall d s G Ll R n t,
  exists N, ones (Hc d s G (Ll *> const 0) R n t) N /\ 6 * R + d + 12 <= N.
Proof.
  intros d s G Ll R n t.
  set (Lw := [0;1]^^d ++ [1] ++ [0;1]^^s ++ encl G ++ [1] ++ Ll).
  set (Rw := [1;1;1;1;0;1;0;1;0] ++ [1;0;1;0;1;0;1;0;1;0;1;0]^^R ++ [0;1;0;1;1;0;1;1] ++ [0;1;1]^^n ++
             [1;1;0;0;1;0;0;1]^^t ++ [0;1]).
  exists (count1 Lw + 1 + count1 Rw). split.
  - exists J, Lw, Rw, 1. split; [| reflexivity].
    unfold Hc, HR, Lw, Rw. rewrite lftx_encl. rewrite !Str_app_assoc. reflexivity.
  - unfold Lw, Rw. rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

(** Up to the post-ESC exhaustion: [F,2,6,2 | K ; 3 R_E + 2]. *)
Definition RE (P : nat) : nat := iter 2 (U (P - 21)) O.

Lemma k31_esc : forall P s t y l, 24 <= P ->
  D0f t 32 P s y l -->* Kx (repeat 1%nat (P - 20) ++ [2;6;2])%nat 1 (3 * RE P + 2) (9 + t) (lftx [5;4;y;s]%nat (1 >> l)).
Proof.
  intros P s t y l HP.
  eapply evstep_trans; [apply progress_evstep, (AbsE1 P s t y l HP) |].
  replace (P - 20) with (S (P - 21)) by lia.
  eapply evstep_trans; [apply progress_evstep, (Kx_R3f (P - 21) 2 [6;2;5;4;y;s]%nat 2 (9 + t) (1 >> l) ltac:(lia)) |].
  eapply evstep_trans; [apply (CLR (P - 21) 2 [2;6;2;5;4;y;s]%nat (9 + t) (1 >> l)) |].
  unfold RE. replace ([2;6;2;5;4;y;s])%nat with ([2;6;2] ++ [5;4;y;s])%nat by reflexivity.
  rewrite app_assoc, (Kx_app (repeat 1%nat (S (P - 21)) ++ [2;6;2])%nat [5;4;y;s]%nat). apply evstep_refl.
Qed.

(** ** The five routes from E2's start (K = 5w + 15 + rho zeros, accumulator 3R+2, R = R_E). *)
Lemma COUNT0 : forall c n suf t e,
  Kx (repeat 1%nat (S n) ++ (3 * c) :: suf) 1 2 t e -->* Kx (repeat 1%nat (S n) ++ 0%nat :: suf) 1 (3 * iter c (U (S n)) O + 2) t e.
Proof. intros. exact (COUNT c n O suf t e). Qed.

(** accumulators of the routes *)
Definition Ra1 (w : nat) : nat := iter (w + 3) (U (3 * w + 2)) O.
Definition Rb1 (w R : nat) : nat := iter (2 * R + 2) (U (S (3 * w + 1))) (iter (2 * Ra1 w + 3) (U (3 * w + 1)) O).
Definition Rx3 (w : nat) : nat := iter (w + 4) (U (S (3 * w + 3))) O.
Definition Ry3 (w R : nat) : nat := iter (2 * R + 1) (U (S (3 * w + 3))) (iter (2 * Rx3 w + 3) (U (3 * w + 3)) O).

(** rho = 0: one counter from 2R+w+7, then the halt *)
Lemma route0 : forall w R t G l,
  Kx (repeat 1%nat (5 * w + 15) ++ [2;6;2])%nat 1 (3 * R + 2) t (lftx G (1 >> l)) -->*
  Hc 0 2 G l (iter (2 * R + w + 7) (U (S (3 * w + 2))) O) (S (3 * w + 2)) (3 + t).
Proof.
  intros w R t G l.
  eapply evstep_trans; [apply progress_evstep, AE2_0 |].
  replace (6 * R + 3 * w + 21) with (3 * (2 * R + w + 7)) by lia.
  replace (3 * w + 3) with (S (3 * w + 2)) by lia.
  eapply evstep_trans; [apply COUNT0 |].
  unfold Hc. apply progress_evstep, (AH0 (S (3 * w + 2)) _ 0 2 (3 + t) (lftx G (1 >> l))).
Qed.

(** rho = 1: clear 3w+10, X1, two-digit clear, one counter step, halt *)
Lemma route1 : forall w R t G0 l,
  Kx (repeat 1%nat (5 * w + 16) ++ [2;6;2])%nat 1 (3 * R + 2) t (lftx (5 :: G0)%nat (1 >> l)) -->*
  Hc 1 5 G0 l (iter 1 (U (S (S (3 * w + 1)))) (Rb1 w R)) (S (S (3 * w + 1))) (3 + t).
Proof.
  intros w R t G0 l.
  eapply evstep_trans; [apply progress_evstep, AE2_1 |].
  replace (3 * w + 10) with (tokd (w + 3)) by (unfold tokd; lia).
  eapply evstep_trans; [apply CLR |].
  fold (Ra1 w). rewrite app_nil_r.
  replace (S (3 * w + 2)) with (S (S (3 * w + 1))) by lia.
  replace (6 * R + 8) with (S (6 * R + 7)) by lia.
  eapply evstep_trans; [apply progress_evstep,
    (AX1 (3 * w + 1) (Ra1 w) (6 * R + 7) (3 + t) (lftx [3;2]%nat (lftx (5 :: G0)%nat (1 >> l)))) |].
  replace (6 * Ra1 w + 10) with (tokd (2 * Ra1 w + 3)) by (unfold tokd; lia).
  replace (6 * R + 7) with (tokd (2 * R + 2)) by (unfold tokd; lia).
  eapply evstep_trans; [apply CLR2d |].
  fold (Rb1 w R). rewrite app_nil_r, <- Kx_app.
  eapply evstep_trans; [apply (COUNT 1 (S (3 * w + 1)) (Rb1 w R) [2]%nat (3 + t)) |].
  change (lftx (5 :: G0)%nat (1 >> l)) with (lftx [5]%nat (lftx G0 (1 >> l))).
  rewrite <- Kx_app, <- app_assoc.
  unfold Hc. apply progress_evstep, (AH0 (S (S (3 * w + 1))) _ 1 5 (3 + t) (lftx G0 (1 >> l))).
Qed.

(** rho = 2: one counter from w+5 behind the token 6R+1, halt in that token (it survives: 6R ones) *)
Lemma route2 : forall w R t G l,
  Kx (repeat 1%nat (5 * w + 17) ++ [2;6;2])%nat 1 (3 * R + 2) t (lftx G (1 >> l)) -->*
  Hc (6 * R) 4 (2 :: G)%nat l (iter (w + 5) (U (S (3 * w + 5))) O) (S (3 * w + 5)) (3 + t).
Proof.
  intros w R t G l.
  eapply evstep_trans; [apply progress_evstep, AE2_2 |].
  replace (3 * w + 15) with (3 * (w + 5)) by lia.
  replace (3 * w + 6) with (S (3 * w + 5)) by lia.
  eapply evstep_trans; [apply COUNT0 |].
  replace (6 * R + 1) with (S (6 * R)) by lia.
  replace (0%nat :: [S (6 * R); 4; 2])%nat with ([0; S (6 * R); 4] ++ [2])%nat by reflexivity.
  rewrite app_assoc, Kx_app.
  unfold Hc. apply progress_evstep, (AH0 (S (3 * w + 5)) _ (6 * R) 4 (3 + t) (lftx (2 :: G)%nat (1 >> l))).
Qed.

(** rho = 3: counter from w+4 (z2 beyond), X3, two-digit clear, one counter step, halt *)
Lemma route3 : forall w R t G0 l,
  Kx (repeat 1%nat (5 * w + 18) ++ [2;6;2])%nat 1 (3 * R + 2) t (lftx (5 :: G0)%nat (1 >> l)) -->*
  Hc 1 5 G0 l (iter 1 (U (S (S (3 * w + 3)))) (Ry3 w R)) (S (S (3 * w + 3))) (3 + t).
Proof.
  intros w R t G0 l.
  eapply evstep_trans; [apply progress_evstep, AE2_3 |].
  replace (3 * w + 12) with (3 * (w + 4)) by lia.
  replace (3 * w + 4) with (S (3 * w + 3)) by lia.
  eapply evstep_trans; [apply COUNT0 |].
  fold (Rx3 w).
  replace (6 * R + 6) with (2 + (6 * R + 4)) by lia.
  eapply evstep_trans; [apply progress_evstep,
    (AX3 (3 * w + 3) (Rx3 w) (6 * R + 4) (3 + t) (lftx [3;2]%nat (lftx (5 :: G0)%nat (1 >> l)))) |].
  replace (6 * Rx3 w + 10) with (tokd (2 * Rx3 w + 3)) by (unfold tokd; lia).
  replace (6 * R + 4) with (tokd (2 * R + 1)) by (unfold tokd; lia).
  eapply evstep_trans; [apply CLR2d |].
  fold (Ry3 w R). rewrite app_nil_r, <- Kx_app.
  eapply evstep_trans; [apply (COUNT 1 (S (3 * w + 3)) (Ry3 w R) [2]%nat (3 + t)) |].
  change (lftx (5 :: G0)%nat (1 >> l)) with (lftx [5]%nat (lftx G0 (1 >> l))).
  rewrite <- Kx_app, <- app_assoc.
  unfold Hc. apply progress_evstep, (AH0 (S (S (3 * w + 3))) _ 1 5 (3 + t) (lftx G0 (1 >> l))).
Qed.

(** rho = 4: counter from w+4 (z2 beyond), X4, the nested counter from 2 R' + 2R + 6, halt *)
Lemma route4 : forall w R t G l,
  Kx (repeat 1%nat (5 * w + 19) ++ [2;6;2])%nat 1 (3 * R + 2) t (lftx G (1 >> l)) -->*
  Hc 0 2 G l (iter (2 * Rx3 w + 2 * R + 6) (U (S (3 * w + 2))) O) (S (3 * w + 2)) (3 + t).
Proof.
  intros w R t G l.
  eapply evstep_trans; [apply progress_evstep, AE2_4 |].
  replace (3 * w + 12) with (3 * (w + 4)) by lia.
  replace (3 * w + 4) with (S (3 * w + 3)) by lia.
  eapply evstep_trans; [apply COUNT0 |].
  fold (Rx3 w).
  eapply evstep_trans; [apply progress_evstep,
    (AX4 (3 * w + 3) (Rx3 w) (6 * R + 7) (3 + t) (lftx [2]%nat (lftx G (1 >> l)))) |].
  replace (6 * Rx3 w + (6 * R + 7) + 11) with (3 * (2 * Rx3 w + 2 * R + 6)) by lia.
  replace (3 * w + 3) with (S (3 * w + 2)) by lia.
  rewrite <- Kx_app, <- app_assoc.
  eapply evstep_trans; [apply COUNT0 |].
  unfold Hc. apply progress_evstep, (AH0 (S (3 * w + 2)) _ 0 2 (3 + t) (lftx G (1 >> l))).
Qed.

(** ** The key-31 endgame *)
Theorem k31_end : forall t P s y l, 35 <= P ->
  exists c Rl, D0f t 32 P s y l -->* c /\ halted tm c /\ iter 2 (U (P - 21)) O <= Rl /\
    (forall Ll, l = Ll *> const 0 -> exists N, ones c N /\ 6 * Rl + 2 <= N).
Proof.
  intros t P s y l HP.
  pose proof (k31_esc P s t y l ltac:(lia)) as HE.
  fold (RE P). set (R := RE P) in *.
  destruct (split_mod (P - 35) 5 ltac:(lia)) as [w [rho [Hrho Hw]]].
  destruct rho as [|[|[|[|[|rho]]]]]; [| | | | | lia].
  - (* rho = 0 *)
    replace (P - 20) with (5 * w + 15) in HE by lia.
    eexists. exists (iter (2 * R + w + 7) (U (S (3 * w + 2))) O). split; [| split; [| split]].
    + eapply evstep_trans; [exact HE | apply route0].
    + apply Hc_halted.
    + pose proof (iter_ge_count (2 * R + w + 7) (S (3 * w + 2)) O). lia.
    + intros Ll ->.
      destruct (Hc_ones 0 2 [5;4;y;s]%nat Ll (iter (2 * R + w + 7) (U (S (3 * w + 2))) O) (S (3 * w + 2)) (3 + (9 + t)))
        as [N [HN HB]]. exists N. split; [exact HN | lia].
  - (* rho = 1 *)
    replace (P - 20) with (5 * w + 16) in HE by lia.
    eexists. exists (iter 1 (U (S (S (3 * w + 1)))) (Rb1 w R)). split; [| split; [| split]].
    + eapply evstep_trans; [exact HE | exact (route1 w R (9 + t) [4;y;s]%nat l)].
    + apply Hc_halted.
    + pose proof (iter_ge_start 1 (S (S (3 * w + 1))) (Rb1 w R)).
      pose proof (iter_ge_count (2 * R + 2) (S (3 * w + 1)) (iter (2 * Ra1 w + 3) (U (3 * w + 1)) O)).
      unfold Rb1 in *. lia.
    + intros Ll ->.
      destruct (Hc_ones 1 5 [4;y;s]%nat Ll (iter 1 (U (S (S (3 * w + 1)))) (Rb1 w R)) (S (S (3 * w + 1))) (3 + (9 + t)))
        as [N [HN HB]]. exists N. split; [exact HN | lia].
  - (* rho = 2: the bound comes from the surviving token 6 R_E + 1 *)
    replace (P - 20) with (5 * w + 17) in HE by lia.
    eexists. exists R. split; [| split; [| split]].
    + eapply evstep_trans; [exact HE | apply route2].
    + apply Hc_halted.
    + lia.
    + intros Ll ->.
      destruct (Hc_ones (6 * R) 4 [2;5;4;y;s]%nat Ll (iter (w + 5) (U (S (3 * w + 5))) O) (S (3 * w + 5)) (3 + (9 + t)))
        as [N [HN HB]]. exists N. split; [exact HN | lia].
  - (* rho = 3 *)
    replace (P - 20) with (5 * w + 18) in HE by lia.
    eexists. exists (iter 1 (U (S (S (3 * w + 3)))) (Ry3 w R)). split; [| split; [| split]].
    + eapply evstep_trans; [exact HE | exact (route3 w R (9 + t) [4;y;s]%nat l)].
    + apply Hc_halted.
    + pose proof (iter_ge_start 1 (S (S (3 * w + 3))) (Ry3 w R)).
      pose proof (iter_ge_count (2 * R + 1) (S (3 * w + 3)) (iter (2 * Rx3 w + 3) (U (3 * w + 3)) O)).
      unfold Ry3 in *. lia.
    + intros Ll ->.
      destruct (Hc_ones 1 5 [4;y;s]%nat Ll (iter 1 (U (S (S (3 * w + 3)))) (Ry3 w R)) (S (S (3 * w + 3))) (3 + (9 + t)))
        as [N [HN HB]]. exists N. split; [exact HN | lia].
  - (* rho = 4: the nested counter *)
    replace (P - 20) with (5 * w + 19) in HE by lia.
    eexists. exists (iter (2 * Rx3 w + 2 * R + 6) (U (S (3 * w + 2))) O). split; [| split; [| split]].
    + eapply evstep_trans; [exact HE | apply route4].
    + apply Hc_halted.
    + pose proof (iter_ge_count (2 * Rx3 w + 2 * R + 6) (S (3 * w + 2)) O). lia.
    + intros Ll ->.
      destruct (Hc_ones 0 2 [5;4;y;s]%nat Ll (iter (2 * Rx3 w + 2 * R + 6) (U (S (3 * w + 2))) O) (S (3 * w + 2))
        (3 + (9 + t))) as [N [HN HB]]. exists N. split; [exact HN | lia].
Qed.

Print Assumptions k31_end.
