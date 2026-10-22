(** * C7Score.v : the fast-growing bounds along C7's chain (BB9/verify_c7), with Score.v (f, f_omega, S1_core).
    With a = 12 Bx + 27 (= 6 * 2^^13 3 + 3, M8's argument):
      f_omega a <= R2 (level D3 > a),  f_omega^2 a < R3 (level 3j2+12 >= R2 + 2),
      f_omega^3 a < R4 (level D5 >= 12 R3),  f_omega^4 a < R5 (level 3j3+21 >= R4 + 2),  R5 <= R10. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XScore Require Import Score.   (* first: C7Top's R2 etc. must shadow Score's *)
From XL Require Import Individual112.   (* again: S1 is the symbol, not Score.S1 *)
From XDev Require Import Base G_rules Abs KStep C7Count C7Top.
Opaque U arrow f_omega.
Local Open Scope nat_scope.

Lemma fw_le_U0 : forall a K, S a <= K -> f_omega a <= U K 0.
Proof.
  intros a K H. pose proof (fomega_le_U a) as H1. pose proof (sc_U0_ge a) as H2.
  pose proof (sc_U_mono a a (U a 0) ltac:(lia)) as H3. rewrite <- U_S0 in H3.
  pose proof (sc_U_mono2 (S a) K 0 0 H (le_n 0)). lia.
Qed.

Lemma U_iter_count : forall n j x, x + n <= iter n (U j) x.
Proof. intros. apply sc_iter_count. intro a. pose proof (sc_U_lin j a). lia. Qed.

Lemma R5_le_R10 : forall j3, R5 j3 <= R10 j3.
Proof.
  intro j3. unfold R10, cend, R9.
  set (N := 3 * j3 + 19).
  pose proof (U_iter_count (2 * R5 j3 + 3) (S N) 0) as A.
  set (r9 := iter (2 * R5 j3 + 3) (U (S N)) 0) in *.
  pose proof (sc_U_lin (S N) r9) as B1. pose proof (sc_U_lin (S N) (U (S N) r9)) as B2.
  pose proof (U_iter_count (2 * U (S N) (U (S N) r9) + 1) N 0) as C.
  set (r11 := iter (2 * U (S N) (U (S N) r9) + 1) (U N) 0) in *.
  pose proof (U_iter_count (2 * r11 + 3) (N - 1) 0). lia.
Qed.

Lemma chain_bound : forall j1 j2 j3,
  9 * Bx = 5 * j1 + 9 -> 9 * R2 j1 + 12 * R1 j1 + 3 * j1 + 17 = 5 * j2 + 19 ->
  9 * R4 j2 + 12 * R3 j2 + 3 * j2 + 17 = 5 * j3 + 21 -> 1000 <= j1 ->
  f_omega (f_omega (12 * Bx + 27)) < R3 j2 /\ f_omega (f_omega (f_omega (f_omega (12 * Bx + 27)))) < R5 j3.
Proof.
  intros j1 j2 j3 E1 E2 E3 Hj1.
  set (a := 12 * Bx + 27).
  assert (HR1 : 3 * j1 + 14 <= R1 j1) by (unfold R1; pose proof (C7Top.iter_U_ge (j1 + 6) (3 * j1 + 12) 0 ltac:(lia)); lia).
  (* f_omega a <= R2 *)
  assert (A1 : f_omega a <= R2 j1).
  { unfold R2.
    pose proof (fw_le_U0 a (D3 j1) ltac:(unfold a, D3; lia)). 
    pose proof (Score.iter_U_ge 2 (D3 j1) 0 ltac:(lia)). lia. }
  (* f_omega^2 a < R3 *)
  assert (A2 : f_omega (f_omega a) < R3 j2).
  { pose proof (S1_core a (3 * j2 + 12) ltac:(lia)).
    pose proof (Score.iter_U_ge (j2 + 6) (3 * j2 + 12) 0 ltac:(lia)). unfold R3. lia. }
  (* f_omega^3 a < R4 *)
  assert (A3 : f_omega (f_omega (f_omega a)) < R4 j2).
  { pose proof (S1_core (f_omega a) (D5 j2) ltac:(unfold D5; lia)).
    pose proof (Score.iter_U_ge 2 (D5 j2) 0 ltac:(lia)). unfold R4. lia. }
  split; [exact A2 |].
  pose proof (S1_core (f_omega (f_omega a)) (3 * j3 + 21) ltac:(lia)).
  pose proof (Score.iter_U_ge (j3 + 3) (3 * j3 + 21) 0 ltac:(lia)). unfold R5. lia.
Qed.
