(** FGH comparison lemmas for the omega^2 bounds (B21, W2PR). *)
From Coq Require Import Lia PeanoNat.
From BB8 Require Import BB21_B21_absdef BB_FGH_wa.
Set Default Goal Selector "!".

Lemma iter_S_add : forall n y, iter n S y = n + y.
Proof. induction n; intros y; cbn [iter]; [lia | rewrite IHn; lia]. Qed.

Lemma f1_eq : forall y, f 1 y = y + y.
Proof. intros y. change (f 1 y) with (iter y S y). apply iter_S_add. Qed.

Lemma f2_ge : forall y, 2 <= y -> 4 * y <= f 2 y.
Proof.
  intros y Hy. change (f 2 y) with (iter y (f 1) y).
  pose proof (iter_mono_cnt (f 1) (proj1 (good_f 1)) 2 y y Hy) as H.
  cbn [iter] in H. rewrite !f1_eq in H. lia.
Qed.

Lemma fwa_dbl : forall n y, 1 <= n -> 2 <= y -> 2 * y + 2 <= f_wa n 0 y.
Proof.
  intros n y Hn Hy. pose proof (f_wa_a_mono 1 n y Hn ltac:(lia)) as A.
  change (f_wa 1 0 y) with (f_wa 0 y y) in A.
  pose proof (f_wa_b_mono 0 2 y y Hy ltac:(lia)) as B. change (f_wa 0 2 y) with (f 2 y) in B.
  pose proof (f2_ge y Hy). lia.
Qed.

Lemma fwsq_S : forall n, 1 <= n -> 2 * f_wsq n + 2 <= f_wsq (S n).
Proof.
  intros n Hn. unfold f_wsq. rewrite f_wa_lim.
  pose proof (f_wa_b_mono n 1 (S n) (S n) ltac:(lia) ltac:(lia)) as A.
  rewrite (f_wa_S n 0 (S n)) in A.
  pose proof (iter_mono_cnt (f_wa n 0) (proj1 (good_f_wa n 0)) 2 (S n) (S n) ltac:(lia)) as B.
  change (iter 2 (f_wa n 0) (S n)) with (f_wa n 0 (f_wa n 0 (S n))) in B.
  set (z := f_wa n 0 (S n)) in *.
  assert (Z1 : f_wa n 0 n <= z) by (apply f_wa_mono; lia).
  assert (Z2 : S n <= z) by apply f_wa_id.
  pose proof (fwa_dbl n z Hn ltac:(lia)). lia.
Qed.

Lemma fwsq_3 : forall n, 1 <= n -> 8 * f_wsq n + 14 <= f_wsq (n + 3).
Proof.
  intros n Hn. pose proof (fwsq_S n Hn). pose proof (fwsq_S (S n) ltac:(lia)). pose proof (fwsq_S (S (S n)) ltac:(lia)).
  replace (n + 3) with (S (S (S n))) by lia. lia.
Qed.

Lemma fwsq_ge : forall n, n <= f_wsq n.
Proof. intros. apply f_wa_id. Qed.

(** J20's lower bound f_(w*2)(f_(w+2)^2(f_10 2)) is below f_wsq (f_wsq T) once T >= 10 *)
Lemma J20_le : forall T, 10 <= T -> f_wa 2 0 (f_wa 1 2 (f_wa 1 2 (f 10 2))) <= f_wsq (f_wsq T).
Proof.
  intros T HT.
  assert (A0 : f 10 2 <= f_wa 1 2 T).
  { pose proof (f_wa_b_mono 1 0 2 T ltac:(lia) ltac:(lia)) as P. change (f_wa 1 0 T) with (f_wa 0 T T) in P.
    pose proof (f_wa_b_mono 0 10 T T ltac:(lia) ltac:(lia)) as Q.
    pose proof (proj2 (good_f 10) 2 T ltac:(lia)) as R. change (f_wa 0 10 T) with (f 10 T) in Q.
    change (f_wa 0 T T) with (f T T) in P, Q. lia. }
  assert (A : f_wa 1 2 (f_wa 1 2 (f 10 2)) <= f_wa 2 0 T).
  { rewrite f_wa_lim.
    pose proof (f_wa_b_mono 1 3 T T ltac:(lia) ltac:(lia)) as P. rewrite (f_wa_S 1 2 T) in P.
    pose proof (iter_mono_cnt (f_wa 1 2) (proj1 (good_f_wa 1 2)) 3 T T ltac:(lia)) as Q. cbn [iter] in Q.
    pose proof (f_wa_mono 1 2 _ _ A0) as R1. pose proof (f_wa_mono 1 2 _ _ R1) as R2. lia. }
  set (F := f_wsq T).
  assert (B : f_wa 2 0 T <= F) by (apply f_wa_a_mono; lia).
  assert (HF : T <= F) by apply fwsq_ge.
  transitivity (f_wa 2 0 F); [apply f_wa_mono; lia |].
  unfold f_wsq at 1. apply f_wa_a_mono; lia.
Qed.

(** one refill between phases: from a phase end with B0min >= f_wsq V (V >= Y + 3) the next phase has
    S k blocks with 4 * S k >= J-acc > B0min, so k >= f_wsq Y + 3 *)
Lemma chain_step : forall Y V B J k, 1 <= Y -> Y + 3 <= V -> f_wsq V <= B -> B + 1 <= J -> J <= 4 * S k ->
  f_wsq Y + 3 <= k.
Proof.
  intros Y V B J k HY HV HB HJ Hk. pose proof (fwsq_3 Y HY) as P. pose proof (f_wsq_mono _ _ HV) as M.
  set (F := f_wsq Y) in *. set (F3 := f_wsq (Y + 3)) in *. set (FV := f_wsq V) in *. lia.
Qed.

(** the last phase: B0min >= f_wsq V with V >= Y + 3 gives J-acc >= 2 f_wsq Y + 3 *)
Lemma chain_last : forall Y V B J, 1 <= Y -> Y + 3 <= V -> f_wsq V <= B -> B + 1 <= J -> 2 * f_wsq Y + 3 <= J.
Proof.
  intros Y V B J HY HV HB HJ. pose proof (fwsq_3 Y HY) as P. pose proof (f_wsq_mono _ _ HV) as M.
  set (F := f_wsq Y) in *. set (F3 := f_wsq (Y + 3)) in *. set (FV := f_wsq V) in *. lia.
Qed.

Lemma iter_fwsq_ge : forall i T, T <= iter i f_wsq T.
Proof. intros. apply iter_ge_id. exact fwsq_ge. Qed.
