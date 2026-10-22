(** * C7Score5.v : five f_omega levels along C7's chain, starting at the clear R1 (BB9/verify_c7).
    R1 = iter (j1+6) (U (3 j1 + 12)) 0 is a clear at a depth linear in Bx (5 j1 = 9 Bx - 9), so for any y with
    y + 1 <= 3 j1 + 12:
      f_omega y <= R1,  f_omega^2 y < R2 (depth D3 >= 12 R1),  f_omega^3 y < R3 (depth 3j2+12 >= R2 + 2),
      f_omega^4 y < R4 (depth D5 >= 12 R3),  f_omega^5 y < R5 (depth 3j3+21 >= R4 + 2).
    Instances: y = 4 Bx + 8 (= 2 * 2^^13 3) and y = f_omega 12 (<= Bx, by f (k+2) x <= U k x). *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XScore Require Import Score.   (* first: C7Top's R2 etc. must shadow Score's *)
From XL Require Import Individual112.   (* again: S1 is the symbol, not Score.S1 *)
From XDev Require Import Base G_rules Abs KStep C7Count C7Top C7Score.
Opaque U arrow.
Local Open Scope nat_scope.

(** ** f_omega 12 <= Bx *)
Transparent f f_omega.

Lemma iter_S_add : forall n x, iter n S x = n + x.
Proof. induction n; intros x; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

(** Two levels lower: f (k+2) x <= U k x (base f 2 x <= U 0 x = dbl (2x+2) 0, dbl iterating x -> 2x+2). *)
Lemma dbl_iter : forall a b, dbl a b = iter a (fun z => 2 * z + 2) b.
Proof.
  induction a as [| a IH]; intros b; [reflexivity |].
  rewrite iter_S'. cbn [dbl]. apply IH.
Qed.

Lemma fSS_le_U : forall k x, f (S (S k)) x <= U k x.
Proof.
  induction k as [| k IH]; intros n.
  - rewrite f_S, U_0, dbl_iter. set (g := fun z => 2 * z + 2).
    assert (Hg : forall a, a + 1 <= g a) by (intro a; unfold g; lia).
    assert (Hm : forall a b, a <= b -> g a <= g b) by (intros a b H; unfold g; lia).
    assert (H1 : iter n (f 1) n <= iter n g n).
    { apply sc_iter_dom; [| exact Hm]. intro a. rewrite f_S. change (f 0) with S. rewrite iter_S_add. unfold g. lia. }
    assert (H2 : n <= iter (n + 2) g 0) by (pose proof (sc_iter_count g Hg (n + 2) 0); lia).
    assert (H3 : iter n g n <= iter n g (iter (n + 2) g 0)) by (apply sc_iter_mono_x; [exact Hm | exact H2]).
    rewrite <- sc_iter_add in H3. replace (n + (n + 2)) with (2 * n + 2) in H3 by lia. lia.
  - rewrite f_S, U_S.
    assert (Hg : forall a, a + 1 <= U k a) by (intro a; pose proof (sc_U_lin k a); lia).
    assert (H1 : iter n (f (S (S k))) n <= iter n (U k) n) by (apply sc_iter_dom; [exact IH | exact (sc_U_mono k)]).
    assert (H2 : n <= iter (n + 2) (U k) 0) by (pose proof (sc_iter_count (U k) Hg (n + 2) 0); lia).
    assert (H3 : iter n (U k) n <= iter n (U k) (iter (n + 2) (U k) 0))
      by (apply sc_iter_mono_x; [exact (sc_U_mono k) | exact H2]).
    rewrite <- sc_iter_add in H3. replace (n + (n + 2)) with (2 * n + 2) in H3 by lia. lia.
Qed.

Lemma fw12_le_Bx : f_omega 12 <= Bx.
Proof.
  change (f_omega 12) with (f 12 12). pose proof (fSS_le_U 10 12) as H1.
  pose proof (sc_U0_ge 10) as H2. pose proof (sc_U_mono 10 12 (U 10 0) ltac:(lia)) as H3.
  rewrite Bx_def. lia.
Qed.

Opaque f f_omega.

(** ** The chain *)
Lemma chain5 : forall y j1 j2 j3,
  9 * Bx = 5 * j1 + 9 -> 9 * R2 j1 + 12 * R1 j1 + 3 * j1 + 17 = 5 * j2 + 19 ->
  9 * R4 j2 + 12 * R3 j2 + 3 * j2 + 17 = 5 * j3 + 21 -> 1000 <= j1 -> y + 1 <= 3 * j1 + 12 ->
  f_omega (f_omega (f_omega (f_omega (f_omega y)))) < R5 j3.
Proof.
  intros y j1 j2 j3 E1 E2 E3 Hj1 Hy.
  (* f_omega y <= R1 *)
  assert (A1 : f_omega y <= R1 j1).
  { unfold R1. pose proof (fw_le_U0 y (3 * j1 + 12) ltac:(lia)).
    pose proof (Score.iter_U_ge (j1 + 6) (3 * j1 + 12) 0 ltac:(lia)). lia. }
  (* f_omega^2 y < R2 *)
  assert (A2 : f_omega (f_omega y) < R2 j1).
  { pose proof (S1_core y (D3 j1) ltac:(unfold D3; lia)).
    pose proof (Score.iter_U_ge 2 (D3 j1) 0 ltac:(lia)). unfold R2. lia. }
  (* f_omega^3 y < R3 *)
  assert (A3 : f_omega (f_omega (f_omega y)) < R3 j2).
  { pose proof (S1_core (f_omega y) (3 * j2 + 12) ltac:(lia)).
    pose proof (Score.iter_U_ge (j2 + 6) (3 * j2 + 12) 0 ltac:(lia)). unfold R3. lia. }
  (* f_omega^4 y < R4 *)
  assert (A4 : f_omega (f_omega (f_omega (f_omega y))) < R4 j2).
  { pose proof (S1_core (f_omega (f_omega y)) (D5 j2) ltac:(unfold D5; lia)).
    pose proof (Score.iter_U_ge 2 (D5 j2) 0 ltac:(lia)). unfold R4. lia. }
  (* f_omega^5 y < R5 *)
  pose proof (S1_core (f_omega (f_omega (f_omega y))) (3 * j3 + 21) ltac:(lia)).
  pose proof (Score.iter_U_ge (j3 + 3) (3 * j3 + 21) 0 ltac:(lia)). unfold R5. lia.
Qed.

Lemma chain5_arrow : forall j1 j2 j3,
  9 * Bx = 5 * j1 + 9 -> 9 * R2 j1 + 12 * R1 j1 + 3 * j1 + 17 = 5 * j2 + 19 ->
  9 * R4 j2 + 12 * R3 j2 + 3 * j2 + 17 = 5 * j3 + 21 -> 1000 <= j1 ->
  f_omega (f_omega (f_omega (f_omega (f_omega (4 * Bx + 8))))) < R5 j3 /\
  f_omega (f_omega (f_omega (f_omega (f_omega (f_omega 12))))) < R5 j3.
Proof.
  intros j1 j2 j3 E1 E2 E3 Hj1. pose proof Bx_ge6. pose proof fw12_le_Bx.
  split; apply (chain5 _ j1 j2 j3 E1 E2 E3 Hj1); lia.
Qed.

Print Assumptions chain5_arrow.
