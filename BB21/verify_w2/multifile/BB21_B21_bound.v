(** B21: the omega^2 lower bound.  sigma > f_wsq (f_wsq (4^^341))  (f_wsq = f_(omega^2)), which beats
    J20's f_(omega*2)(f_(omega+2)^2(f_10 2)).
    Phases 4, 5 and 6 each apply f_wsq (BB21_B21_qnt4.phi_loop_q / phase_from_work_q): sigma > f_wsq^3 (4^^341). *)
From BB8 Require Import Individual212.
From BB8 Require Import BB21_B21_absdef BB21_B21_tm BB21_B21_sim BB21_B21_grow BB21_B21_steps BB21_B21_inv
  BB21_B21_proc BB21_B21_phase BB21_B21_run BB21_B21_score.
From BB8 Require Import BB_FGH_wa BB_FGH_wa2 BB21_B21_qnt BB21_B21_qnt2 BB21_B21_qnt3 BB21_B21_qnt4.
From BB8 Require BB20_JZ20.
From Coq Require Import Lia PeanoNat List Bool.
Import ListNotations.
Set Default Goal Selector "!".
Local Open Scope nat_scope.

Lemma iter_succ : forall (g : nat -> nat) n x, iter (S n) g x = g (iter n g x).
Proof. reflexivity. Qed.
Lemma iter_zero : forall (g : nat -> nat) x, iter 0 g x = x.
Proof. reflexivity. Qed.

Lemma end_growth : forall s, PhaseEnd s -> B0min s + 1 <= jacc s.
Proof.
  intros s [I [_ [_ Hd]]]. exact (proj1 (jacc_ge_B0min s I (deep_not_pure s I Hd))).
Qed.

Theorem abstract_final_q : forall T, 1 <= T -> 64 * T <= J3 ->
  exists s, star refill21 S3 (enc s) /\ PhaseEnd s /\ jacc s mod 4 = 2 /\ 2 * iter 3 f_wsq T + 3 <= jacc s.
Proof.
  intros T HT HJ.
  destruct N4_form as [a [HJ3 HN4]].
  (* phase 4 *)
  destruct (two_to_phi_q refill21 (N4 - 1) s4 INV_s4 eq_refl eq_refl) as [s4a [St4a [I4a [Hf4a [Hu4a [Hd4a [Hl4a _]]]]]]].
  destruct (phi_loop_q refill21 (N4 - 1) s4a I4a Hf4a Hu4a Hd4a) as [s4e [St4e [E4 [Hl4e HB4]]]].
  assert (L4 : length (es s4e) = 16 * a + 4) by (rewrite Hl4e, Hl4a; simpl; lia).
  destruct (jacc_end_form s4e E4) as [q4 Hj4]. rewrite L4 in Hj4.
  assert (M4 : jacc s4e mod 4 = 0) by (rewrite Hj4; replace (64 * q4 + 20 + 2 * (16 * a + 4)) with (4 * (16 * q4 + 8 * a + 7) + 0) by lia; apply mod4_form; lia).
  assert (K4 : jacc s4e / 4 = S (16 * q4 + 8 * a + 6)) by (rewrite Hj4; replace (64 * q4 + 20 + 2 * (16 * a + 4)) with (4 * S (16 * q4 + 8 * a + 6)) by lia; apply div4).
  pose proof (end_growth s4e E4) as J4.
  destruct (es s4e) as [| e4 es4] eqn:Ees4; [simpl in L4; lia |].
  destruct (refill_next s4e e4 es4 E4 Ees4 M4) as [s5 [St5 [I5 [Hw5 [Hu5 [Hl5 _]]]]]].
  rewrite K4 in Hu5.
  (* phase 5 *)
  destruct (phase_from_work_q refill21 _ s5 I5 Hw5 Hu5) as [s5e [St5e [E5 [Hl5e HB5]]]].
  assert (L5 : length (es s5e) = 24 * a + 16 * q4 + 10) by (rewrite Hl5e, Hl5; simpl in L4; lia).
  destruct (jacc_end_form s5e E5) as [q5 Hj5]. rewrite L5 in Hj5.
  assert (M5 : jacc s5e mod 4 = 0) by (rewrite Hj5; replace (64 * q5 + 20 + 2 * (24 * a + 16 * q4 + 10)) with (4 * (16 * q5 + 12 * a + 8 * q4 + 10) + 0) by lia; apply mod4_form; lia).
  assert (K5 : jacc s5e / 4 = S (16 * q5 + 12 * a + 8 * q4 + 9)) by (rewrite Hj5; replace (64 * q5 + 20 + 2 * (24 * a + 16 * q4 + 10)) with (4 * S (16 * q5 + 12 * a + 8 * q4 + 9)) by lia; apply div4).
  pose proof (end_growth s5e E5) as J5.
  destruct (es s5e) as [| e5 es5] eqn:Ees5; [simpl in L5; lia |].
  destruct (refill_next s5e e5 es5 E5 Ees5 M5) as [s6 [St6 [I6 [Hw6 [Hu6 [Hl6 _]]]]]].
  rewrite K5 in Hu6.
  (* phase 6 *)
  destruct (phase_from_work_q refill21 _ s6 I6 Hw6 Hu6) as [s6e [St6e [E6 [Hl6e HB6]]]].
  assert (L6 : length (es s6e) = 36 * a + 24 * q4 + 16 * q5 + 19) by (rewrite Hl6e, Hl6; simpl in L5; lia).
  destruct (jacc_end_form s6e E6) as [q6 Hj6]. rewrite L6 in Hj6.
  assert (M6 : jacc s6e mod 4 = 2).
  { rewrite Hj6. replace (64 * q6 + 20 + 2 * (36 * a + 24 * q4 + 16 * q5 + 19)) with (4 * (16 * q6 + 18 * a + 12 * q4 + 8 * q5 + 14) + 2) by lia.
    apply mod4_form. lia. }
  pose proof (end_growth s6e E6) as J6.
  exists s6e. split; [| split; [exact E6 | split; [exact M6 |]]].
  - econstructor; [exact S3_step |].
    replace ([1; 1; 1; 1; 4; 1] :: repeat [2] (J3 / 4)) with (enc s4) by (rewrite enc_s4; reflexivity).
    eapply (star_trans refill21); [exact St4a |]. eapply (star_trans refill21); [exact St4e |].
    econstructor; [exact St5 |]. eapply (star_trans refill21); [exact St5e |].
    econstructor; [exact St6 |]. exact St6e.
  - (* growth: phases 4, 5, 6 each apply f_wsq *)
    set (k4 := N4 - 1) in *. set (k5 := 16 * q4 + 8 * a + 6) in *. set (k6 := 16 * q5 + 12 * a + 8 * q4 + 9) in *.
    pose proof (i_min s4a I4a) as m4. pose proof (i_min s5 I5) as m5. pose proof (i_min s6 I6) as m6.
    pose proof (PhiR_fwsq k4 (length (es s4a)) (B0min s4a) ltac:(unfold k4; lia) ltac:(lia)) as G4.
    pose proof (PhiR_fwsq k5 (S (length (es s5))) (B0min s5) ltac:(unfold k5; lia) ltac:(lia)) as G5.
    pose proof (PhiR_fwsq k6 (S (length (es s6))) (B0min s6) ltac:(unfold k6; lia) ltac:(lia)) as G6.
    assert (Ha : T <= a) by lia.
    pose proof (fwsq_ge T) as Y1. pose proof (fwsq_ge (f_wsq T)) as Y2.
    assert (C4 : f_wsq T + 3 <= k5)
      by (apply (chain_step T k4 (B0min s4e) (jacc s4e) k5); [lia | unfold k4; lia | lia | lia | rewrite Hj4; unfold k5; lia]).
    assert (C5 : f_wsq (f_wsq T) + 3 <= k6)
      by (apply (chain_step (f_wsq T) k5 (B0min s5e) (jacc s5e) k6); [lia | lia | lia | lia | rewrite Hj5; unfold k6; lia]).
    rewrite !iter_succ, iter_zero. apply (chain_last (f_wsq (f_wsq T)) k6 (B0min s6e)); [lia | lia | lia | lia].
Qed.

Lemma tet_ge : forall n, n <= tet n.
Proof.
  induction n; [simpl; lia |]. change (tet (S n)) with (4 ^ tet n).
  assert (tet n < 4 ^ tet n) by (apply Nat.pow_gt_lin_r; lia). lia.
Qed.

Close Scope nat_scope.

(** sigma = N + 1 (the halting transition writes one more 1) *)
Theorem sigma_lower_bound_wsq3 : exists c N, c0 -[ tm ]->* c /\ halted tm c /\ onesN c N /\
  (iter 3 f_wsq (tet 341) < N)%nat.
Proof.
  destruct (abstract_final_q (tet 341) (tet_pos 341) J3_tet) as [s [Hs [E [Hm HJ]]]].
  destruct (end_to_halt s E Hm) as [c [N [Hc [Hh [Ho HN]]]]].
  exists c, N. split; [| split; [exact Hh | split; [exact Ho |]]].
  - follow boot. follow (star_sim _ _ (star_conv' _ _ Hs)). exact Hc.
  - set (X := iter 3 f_wsq (tet 341)) in *. clearbody X. lia.
Qed.

(** the wiki's claim *)
Theorem sigma_lower_bound_wsq : exists c N, c0 -[ tm ]->* c /\ halted tm c /\ onesN c N /\
  (f_wsq (f_wsq (tet 341)) < N)%nat.
Proof.
  destruct sigma_lower_bound_wsq3 as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  pose proof (fwsq_ge (f_wsq (f_wsq (tet 341)))) as G. rewrite !iter_succ, iter_zero in H4.
  set (X := f_wsq (f_wsq (tet 341))) in *. clearbody X. lia.
Qed.

Theorem beats_J20_bound : exists c N, c0 -[ tm ]->* c /\ halted tm c /\ onesN c N /\
  (BB20_JZ20.f_w2 (BB20_JZ20.f_wk 2 (BB20_JZ20.f_wk 2 (BB20_JZ20.f 10 2))) < N)%nat.
Proof.
  destruct sigma_lower_bound_wsq as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  rewrite f_JZ, (f_wk_JZ 2 (BB_FGH_wa.f 10 2)), f_wk_JZ, f_w2_JZ.
  pose proof (tet_ge 341) as Ht. pose proof (J20_le (tet 341) ltac:(lia)) as H.
  set (X := f_wsq (f_wsq (tet 341))) in *. clearbody X. lia.
Qed.
