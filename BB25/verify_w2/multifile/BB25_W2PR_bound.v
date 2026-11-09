(** W2PR: the omega^2 lower bound.  Phases 4..8 each apply f_wsq = f_(omega^2) (BB21_B21_qnt4, generic in the
    refill rule):  sigma > f_wsq^5 (4^^341). *)
From BB8 Require Import Individual252.
From BB8 Require Import BB21_B21_absdef BB25_W2PR_tm BB25_W2PR_sim BB21_B21_grow BB21_B21_steps BB21_B21_inv
  BB21_B21_proc BB21_B21_phase BB25_W2PR_run BB25_W2PR_score.
From BB8 Require Import BB_FGH_wa BB_FGH_wa2 BB21_B21_qnt BB21_B21_qnt2 BB21_B21_qnt3 BB21_B21_qnt4.
From BB8 Require BB21_B21_run BB21_B21_score.
From Coq Require Import Lia PeanoNat List Bool.
Import ListNotations.
Set Default Goal Selector "!".
Local Open Scope nat_scope.

Lemma end_growthW : forall s, PhaseEnd s -> B0min s + 1 <= jacc s.
Proof.
  intros s [I [_ [_ Hd]]]. exact (proj1 (jacc_ge_B0min s I (deep_not_pure s I Hd))).
Qed.

Lemma iter5 : forall (g : nat -> nat) x, iter 5 g x = g (g (g (g (g x)))).
Proof. reflexivity. Qed.
Lemma iter3 : forall (g : nat -> nat) x, iter 3 g x = g (g (g x)).
Proof. reflexivity. Qed.

Theorem abstract_finalW_q : forall T, 1 <= T -> 64 * T <= BB21_B21_run.J3 ->
  exists s, BB21_B21_proc.star refillW BB21_B21_run.S3 (enc s) /\ PhaseEnd s /\ jacc s mod 8 = 6 /\
    2 * f_wsq (f_wsq (f_wsq (f_wsq (f_wsq T)))) + 3 <= jacc s.
Proof.
  intros T HT T3.
  pose proof (Nat.div_mod BB21_B21_run.J3 256 ltac:(lia)) as HJ3. rewrite J3_mod256 in HJ3.
  remember (BB21_B21_run.J3 / 256) as a eqn:Ea. clear Ea.
  assert (HN4 : BB21_B21_run.N4 = 64 * a + 21).
  { unfold BB21_B21_run.N4. rewrite HJ3. replace (256 * a + 84) with (4 * (64 * a + 21)) by lia. apply BB21_B21_run.div4. }
  (* phase 4 *)
  destruct (two_to_phi_q refillW (BB21_B21_run.N4 - 1) BB21_B21_run.s4 BB21_B21_run.INV_s4 eq_refl eq_refl)
    as [s4a [St4a [I4a [Hf4a [Hu4a [Hd4a [Hl4a _]]]]]]].
  destruct (phi_loop_q refillW (BB21_B21_run.N4 - 1) s4a I4a Hf4a Hu4a Hd4a) as [s4e [St4e [E4 [Hl4e HB4]]]].
  assert (L4 : length (es s4e) = 64 * a + 20) by (rewrite Hl4e, Hl4a; simpl; lia).
  destruct (jacc_end256 s4e E4) as [q4 Hj4]. rewrite L4 in Hj4. pose proof (end_growthW s4e E4) as J4.
  assert (M4 : jacc s4e mod 4 = 0) by (rewrite Hj4; replace (256 * q4 + 84 + 2 * (64 * a + 20)) with (4 * (64 * q4 + 32 * a + 31) + 0) by lia; apply BB21_B21_run.mod4_form; lia).
  assert (N4' : jacc s4e mod 8 <> 6) by (rewrite Hj4; replace (256 * q4 + 84 + 2 * (64 * a + 20)) with (8 * (32 * q4 + 16 * a + 15) + 4) by lia; rewrite mod8_form; lia).
  assert (K4 : jacc s4e / 4 = S (64 * q4 + 32 * a + 30)) by (rewrite Hj4; replace (256 * q4 + 84 + 2 * (64 * a + 20)) with (4 * S (64 * q4 + 32 * a + 30)) by lia; apply BB21_B21_run.div4).
  destruct (es s4e) as [| e4 es4] eqn:Ees4; [simpl in L4; lia |].
  destruct (refill_next4 s4e e4 es4 E4 Ees4 M4 N4') as [s5 [St5 [I5 [Hw5 [Hu5 Hl5]]]]]. rewrite K4 in Hu5.
  (* phase 5 *)
  destruct (phase_from_work_q refillW _ s5 I5 Hw5 Hu5) as [s5e [St5e [E5 [Hl5e HB5]]]].
  assert (L5 : length (es s5e) = 96 * a + 64 * q4 + 50) by (rewrite Hl5e, Hl5; simpl in L4; lia).
  destruct (jacc_end256 s5e E5) as [q5 Hj5]. rewrite L5 in Hj5. pose proof (end_growthW s5e E5) as J5.
  assert (M5 : jacc s5e mod 4 = 0) by (rewrite Hj5; replace (256 * q5 + 84 + 2 * (96 * a + 64 * q4 + 50)) with (4 * (64 * q5 + 48 * a + 32 * q4 + 46) + 0) by lia; apply BB21_B21_run.mod4_form; lia).
  assert (N5' : jacc s5e mod 8 <> 6) by (rewrite Hj5; replace (256 * q5 + 84 + 2 * (96 * a + 64 * q4 + 50)) with (8 * (32 * q5 + 24 * a + 16 * q4 + 23) + 0) by lia; rewrite mod8_form; lia).
  assert (K5 : jacc s5e / 4 = S (64 * q5 + 48 * a + 32 * q4 + 45)) by (rewrite Hj5; replace (256 * q5 + 84 + 2 * (96 * a + 64 * q4 + 50)) with (4 * S (64 * q5 + 48 * a + 32 * q4 + 45)) by lia; apply BB21_B21_run.div4).
  destruct (es s5e) as [| e5 es5] eqn:Ees5; [simpl in L5; lia |].
  destruct (refill_next4 s5e e5 es5 E5 Ees5 M5 N5') as [s6 [St6 [I6 [Hw6 [Hu6 Hl6]]]]]. rewrite K5 in Hu6.
  (* phase 6 *)
  destruct (phase_from_work_q refillW _ s6 I6 Hw6 Hu6) as [s6e [St6e [E6 [Hl6e HB6]]]].
  assert (L6 : length (es s6e) = 144 * a + 96 * q4 + 64 * q5 + 95) by (rewrite Hl6e, Hl6; simpl in L5; lia).
  destruct (jacc_end256 s6e E6) as [q6 Hj6]. rewrite L6 in Hj6. pose proof (end_growthW s6e E6) as J6.
  assert (M6 : jacc s6e mod 8 = 2) by (rewrite Hj6; replace (256 * q6 + 84 + 2 * (144 * a + 96 * q4 + 64 * q5 + 95)) with (8 * (32 * q6 + 36 * a + 24 * q4 + 16 * q5 + 34) + 2) by lia; apply mod8_form; lia).
  assert (K6 : (jacc s6e + 2) / 4 = S (64 * q6 + 72 * a + 48 * q4 + 32 * q5 + 68)) by (rewrite Hj6; replace (256 * q6 + 84 + 2 * (144 * a + 96 * q4 + 64 * q5 + 95) + 2) with (4 * S (64 * q6 + 72 * a + 48 * q4 + 32 * q5 + 68)) by lia; apply BB21_B21_run.div4).
  destruct (es s6e) as [| e6 es6] eqn:Ees6; [simpl in L6; lia |].
  destruct (refill_nextV s6e e6 es6 E6 Ees6 M6) as [s7 [St7 [I7 [Hw7 [Hu7 Hl7]]]]]. rewrite K6 in Hu7.
  (* phase 7 *)
  destruct (phase_from_work_q refillW _ s7 I7 Hw7 Hu7) as [s7e [St7e [E7 [Hl7e HB7]]]].
  assert (L7 : length (es s7e) = 216 * a + 144 * q4 + 96 * q5 + 64 * q6 + 163) by (rewrite Hl7e, Hl7; simpl in L6; lia).
  destruct (jacc_end256 s7e E7) as [q7 Hj7]. rewrite L7 in Hj7. pose proof (end_growthW s7e E7) as J7.
  assert (M7 : jacc s7e mod 8 = 2) by (rewrite Hj7; replace (256 * q7 + 84 + 2 * (216 * a + 144 * q4 + 96 * q5 + 64 * q6 + 163)) with (8 * (32 * q7 + 54 * a + 36 * q4 + 24 * q5 + 16 * q6 + 51) + 2) by lia; apply mod8_form; lia).
  assert (K7 : (jacc s7e + 2) / 4 = S (64 * q7 + 108 * a + 72 * q4 + 48 * q5 + 32 * q6 + 102)) by (rewrite Hj7; replace (256 * q7 + 84 + 2 * (216 * a + 144 * q4 + 96 * q5 + 64 * q6 + 163) + 2) with (4 * S (64 * q7 + 108 * a + 72 * q4 + 48 * q5 + 32 * q6 + 102)) by lia; apply BB21_B21_run.div4).
  destruct (es s7e) as [| e7 es7] eqn:Ees7; [simpl in L7; lia |].
  destruct (refill_nextV s7e e7 es7 E7 Ees7 M7) as [s8 [St8 [I8 [Hw8 [Hu8 Hl8]]]]]. rewrite K7 in Hu8.
  (* phase 8 *)
  destruct (phase_from_work_q refillW _ s8 I8 Hw8 Hu8) as [s8e [St8e [E8 [Hl8e HB8]]]].
  assert (L8 : length (es s8e) = 324 * a + 216 * q4 + 144 * q5 + 96 * q6 + 64 * q7 + 265) by (rewrite Hl8e, Hl8; simpl in L7; lia).
  destruct (jacc_end256 s8e E8) as [q8 Hj8]. rewrite L8 in Hj8. pose proof (end_growthW s8e E8) as J8.
  assert (M8 : jacc s8e mod 8 = 6) by (rewrite Hj8; replace (256 * q8 + 84 + 2 * (324 * a + 216 * q4 + 144 * q5 + 96 * q6 + 64 * q7 + 265)) with (8 * (32 * q8 + 81 * a + 54 * q4 + 36 * q5 + 24 * q6 + 16 * q7 + 76) + 6) by lia; apply mod8_form; lia).
  exists s8e. split; [| split; [exact E8 | split; [exact M8 |]]].
  - econstructor; [exact S3_stepW |].
    replace ([1; 1; 1; 1; 4; 1] :: repeat [2] (BB21_B21_run.J3 / 4)) with (enc BB21_B21_run.s4) by (rewrite BB21_B21_run.enc_s4; reflexivity).
    eapply (star_trans refillW); [exact St4a |]. eapply (star_trans refillW); [exact St4e |].
    econstructor; [exact St5 |]. eapply (star_trans refillW); [exact St5e |].
    econstructor; [exact St6 |]. eapply (star_trans refillW); [exact St6e |].
    econstructor; [exact St7 |]. eapply (star_trans refillW); [exact St7e |].
    econstructor; [exact St8 |]. exact St8e.
  - (* growth: phases 4..8 each apply f_wsq *)
    set (k4 := BB21_B21_run.N4 - 1) in *.
    set (k5 := 64 * q4 + 32 * a + 30) in *.
    set (k6 := 64 * q5 + 48 * a + 32 * q4 + 45) in *.
    set (k7 := 64 * q6 + 72 * a + 48 * q4 + 32 * q5 + 68) in *.
    set (k8 := 64 * q7 + 108 * a + 72 * q4 + 48 * q5 + 32 * q6 + 102) in *.
    pose proof (BB21_B21_inv.i_min s4a I4a) as m4. pose proof (BB21_B21_inv.i_min s5 I5) as m5.
    pose proof (BB21_B21_inv.i_min s6 I6) as m6. pose proof (BB21_B21_inv.i_min s7 I7) as m7.
    pose proof (BB21_B21_inv.i_min s8 I8) as m8.
    pose proof (PhiR_fwsq k4 (length (es s4a)) (B0min s4a) ltac:(unfold k4; lia) ltac:(lia)) as G4.
    pose proof (PhiR_fwsq k5 (S (length (es s5))) (B0min s5) ltac:(unfold k5; lia) ltac:(lia)) as G5.
    pose proof (PhiR_fwsq k6 (S (length (es s6))) (B0min s6) ltac:(unfold k6; lia) ltac:(lia)) as G6.
    pose proof (PhiR_fwsq k7 (S (length (es s7))) (B0min s7) ltac:(unfold k7; lia) ltac:(lia)) as G7.
    pose proof (PhiR_fwsq k8 (S (length (es s8))) (B0min s8) ltac:(unfold k8; lia) ltac:(lia)) as G8.
    assert (H4 : T + 3 <= k4) by (unfold k4; lia).
    set (Y1 := f_wsq T). set (Y2 := f_wsq Y1). set (Y3 := f_wsq Y2). set (Y4 := f_wsq Y3).
    assert (Z1 : T <= Y1) by apply fwsq_ge. assert (Z2 : Y1 <= Y2) by apply fwsq_ge.
    assert (Z3 : Y2 <= Y3) by apply fwsq_ge. assert (Z4 : Y3 <= Y4) by apply fwsq_ge.
    assert (C4 : Y1 + 3 <= k5)
      by (apply (chain_step T k4 (B0min s4e) (jacc s4e) k5); [lia | lia | lia | lia | rewrite Hj4; unfold k5; lia]).
    assert (C5 : Y2 + 3 <= k6)
      by (apply (chain_step Y1 k5 (B0min s5e) (jacc s5e) k6); [lia | lia | lia | lia | rewrite Hj5; unfold k6; lia]).
    assert (C6 : Y3 + 3 <= k7)
      by (apply (chain_step Y2 k6 (B0min s6e) (jacc s6e) k7); [lia | lia | lia | lia | rewrite Hj6; unfold k7; lia]).
    assert (C7 : Y4 + 3 <= k8)
      by (apply (chain_step Y3 k7 (B0min s7e) (jacc s7e) k8); [lia | lia | lia | lia | rewrite Hj7; unfold k8; lia]).
    apply (chain_last Y4 k8 (B0min s8e)); [lia | lia | lia | lia].
Qed.

Close Scope nat_scope.

(** sigma = N + 1 *)
Theorem sigma_lower_boundW_wsq : exists c N, c0 -[ tm ]->* c /\ halted tm c /\ onesN c N /\
  (iter 5 f_wsq (tet 341) < N)%nat.
Proof.
  destruct (abstract_finalW_q (tet 341) (tet_pos 341) J3_tet) as [s [Hs [E [Hm HJ]]]].
  destruct (end_to_halt s E Hm) as [c [N [Hc [Hh [Ho HN]]]]].
  exists c, N. split; [| split; [exact Hh | split; [exact Ho |]]].
  - follow boot. follow (star_sim _ _ (star_convW _ _ Hs)). exact Hc.
  - rewrite iter5. set (X := f_wsq (f_wsq (f_wsq (f_wsq (f_wsq (tet 341)))))) in *. clearbody X. lia.
Qed.

(** the two tetration definitions agree *)
Lemma tet_B21 : forall n, BB21_B21_score.tet n = tet n.
Proof. induction n; [reflexivity |]. change (BB21_B21_score.tet (S n)) with (4 ^ BB21_B21_score.tet n)%nat.
  change (tet (S n)) with (4 ^ tet n)%nat. rewrite IHn. reflexivity. Qed.

(** W2PR's proved bound is above B21's (BB21_B21_w2.sigma_lower_bound_wsq3: iter 3 f_wsq (4^^341)) *)
Theorem beats_B21_bound : exists c N, c0 -[ tm ]->* c /\ halted tm c /\ onesN c N /\
  (iter 3 f_wsq (BB21_B21_score.tet 341) < N)%nat.
Proof.
  destruct sigma_lower_boundW_wsq as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  rewrite tet_B21, iter3. rewrite iter5 in H4.
  pose proof (fwsq_ge (f_wsq (f_wsq (tet 341)))) as A. pose proof (fwsq_ge (f_wsq (f_wsq (f_wsq (tet 341))))) as B.
  pose proof (fwsq_ge (f_wsq (f_wsq (f_wsq (f_wsq (tet 341)))))) as C.
  set (X3 := f_wsq (f_wsq (f_wsq (tet 341)))) in *. set (X4 := f_wsq X3) in *. set (X5 := f_wsq X4) in *.
  clearbody X5 X4 X3. lia.
Qed.
