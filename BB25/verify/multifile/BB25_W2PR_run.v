(** W2PR: the abstract run with the mod-8 refill rule: phases 4..8, halt at refill #8. *)
From Coq Require Import Lia PeanoNat List Bool.
From BB8 Require Import BB21_B21_absdef BB21_B21_grow BB21_B21_steps BB21_B21_inv BB21_B21_proc BB21_B21_phase.
From BB8 Require BB21_B21_run.
From BB8 Require Import BB25_W2PR_sim.
Import ListNotations.
Set Default Goal Selector "!".

(** ** residues mod 256 (enough: one bit is lost per phase, 3 bits are needed at refill #8) *)
Lemma mod256_c : forall z a, 3 * z + 13 = 256 * a -> z mod 256 = 81.
Proof.
  intros z a H. pose proof (Nat.div_mod z 256 ltac:(lia)) as Hd. pose proof (Nat.mod_upper_bound z 256 ltac:(lia)) as Hb.
  remember (z mod 256) as r. remember (z / 256) as q. lia.
Qed.

Lemma h_mod256 : forall m x, 2 <= m -> h m x mod 256 = 81.
Proof.
  induction m as [| m IH]; intros x Hm; [lia |].
  destruct m as [| [| m]]; [lia | |].
  - change (h 2 x) with (iter (x + 3) (h 1) 1). pose proof (h1_iter (x + 3)) as E.
    replace (x + 3) with (2 + (x + 1)) in E |- * by lia. rewrite Nat.pow_add_r in E. change (4 ^ 2) with 16 in E.
    apply (mod256_c _ (4 ^ (x + 1))). lia.
  - change (h (S (S (S m))) x) with (iter (x + 3) (h (S (S m))) 1).
    replace (x + 3) with (S (x + 2)) by lia. cbn [iter]. apply IH. lia.
Qed.

Lemma deep_mod256 : forall b, deep b -> eng0 b mod 256 = 81.
Proof. intros b [m [k [-> H]]]. rewrite eng_XS. apply h_mod256. lia. Qed.

Lemma jacc_end256 : forall s, PhaseEnd s -> exists q, jacc s = 256 * q + 84 + 2 * length (es s).
Proof.
  intros s [I [_ [_ Hd]]]. unfold jacc. rewrite eng_eq. pose proof (deep_mod256 _ Hd) as M.
  pose proof (Nat.div_mod (eng0 (b0 s)) 256 ltac:(lia)) as D. rewrite M in D.
  exists (eng0 (b0 s) / 256). lia.
Qed.

Lemma jacc_end_lb : forall s, PhaseEnd s -> h (length (es s) + 2) 0 <= jacc s.
Proof.
  intros s [I [Hf [_ Hd]]]. pose proof (i_chain s I) as Ch. rewrite Hf in Ch. change (lead1 [1]) with 1 in Ch.
  pose proof (chain_len _ _ _ Ch) as Hl. pose proof (LB_big _ (deep_big _ Hd)) as HL.
  unfold LBe in HL. pose proof (h_mono_m (length (es s) + 2) (length (b0 s) - 2) 0 ltac:(lia)).
  unfold jacc. rewrite eng_eq. lia.
Qed.

(** ** the refill steps of W2PR at a phase end *)
Lemma stepW : forall s, PhaseEnd s ->
  astepG refillW (enc s) = refillW (jacc s) (map pred (es s) ++ [length (b0 s) - 1]).
Proof.
  intros s [I [Hf [Hu _]]]. rewrite (astep_enc refillW) by (try apply b0ok_of; try apply (i_es s I); exact I).
  assert (HE : isE (fr s) = false) by (rewrite Hf; reflexivity).
  rewrite (sweep_front refillW _ _ _ _ HE). rewrite Hf, Hu. reflexivity.
Qed.

Lemma halt_endW : forall s, PhaseEnd s -> jacc s mod 8 = 6 -> astepG refillW (enc s) = Halt.
Proof. intros s E H. rewrite (stepW s E). unfold refillW. rewrite H. reflexivity. Qed.

Lemma refill_next4 : forall s e es', PhaseEnd s -> es s = e :: es' -> jacc s mod 4 = 0 -> jacc s mod 8 <> 6 ->
  exists s', astepG refillW (enc s) = Next (enc s') /\ INV s' /\ work (fr s') /\ up s' = repeat [2] (jacc s / 4) /\
    length (es s') = length es'.
Proof.
  intros s e es' E Hes Hm H6. pose proof E as [I [Hf [Hu Hd]]].
  pose proof (jacc_big s I (deep_big _ Hd)) as J16.
  assert (Hq : 1 <= jacc s / 4) by (apply Nat.div_le_lower_bound; lia).
  pose proof (inv_refill s e es' I Hf Hu Hes Hq) as I1.
  pose proof (i_es s I) as Hese. rewrite Hes in Hese. inversion Hese; subst.
  eexists. split; [| split; [exact I1 | split; [| split; [reflexivity | simpl; apply map_length]]]].
  - rewrite (stepW s E). unfold refillW. replace (jacc s mod 8 =? 6) with false by (symmetry; apply Nat.eqb_neq; exact H6).
    replace ((jacc s mod 4 =? 0) && (4 <=? jacc s)) with true by (symmetry; apply andb_true_iff; split; [apply Nat.eqb_eq | apply Nat.leb_le]; lia).
    rewrite Hes. simpl map. destruct e as [| [| e]]; [lia | lia |]. simpl.
    unfold enc. simpl. rewrite restore_es. simpl. try rewrite <- app_assoc. reflexivity.
  - split; [exact (i_frE _ I1) |]. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma refill_nextV : forall s e es', PhaseEnd s -> es s = e :: es' -> jacc s mod 8 = 2 ->
  exists s', astepG refillW (enc s) = Next (enc s') /\ INV s' /\ work (fr s') /\ up s' = repeat [2] ((jacc s + 2) / 4) /\
    length (es s') = length es'.
Proof.
  intros s e es' E Hes Hm. pose proof E as [I [Hf [Hu Hd]]].
  pose proof (jacc_big s I (deep_big _ Hd)) as J16.
  assert (Hq : 1 <= (jacc s + 2) / 4) by (apply Nat.div_le_lower_bound; lia).
  pose proof (i_chain s I) as Ch. rewrite Hf, Hes in Ch. change (lead1 [1]) with 1 in Ch. simpl in Ch.
  pose proof (inv_refill_gen s e es' (e - 2) ((jacc s + 2) / 4) I Hf Hu Hes Hq ltac:(lia) ltac:(lia)) as I1.
  eexists. split; [| split; [exact I1 | split; [| split; [reflexivity | simpl; apply map_length]]]].
  - rewrite (stepW s E). unfold refillW. replace (jacc s mod 8 =? 6) with false by (symmetry; apply Nat.eqb_neq; lia).
    assert (M4 : jacc s mod 4 = 2).
    { rewrite (BB21_B21_run.mod_down (jacc s) 4 2) by lia. change (4 * 2) with 8. rewrite Hm. reflexivity. }
    replace ((jacc s mod 4 =? 0) && (4 <=? jacc s)) with false by (rewrite M4; reflexivity).
    replace ((jacc s mod 8 =? 2) && (10 <=? jacc s)) with true by (symmetry; apply andb_true_iff; split; [apply Nat.eqb_eq | apply Nat.leb_le]; lia).
    rewrite Hes. simpl map. destruct e as [| [| [| e]]]; [lia | lia | lia |]. simpl.
    unfold enc. simpl. rewrite restore_es. simpl. try rewrite <- app_assoc. replace (S (S (S e)) - 2) with (S e) by lia. reflexivity.
  - split; [exact (i_frE _ I1) |]. simpl. rewrite app_length. simpl. lia.
Qed.

(** ** 4^^341 (copied from BB21_B21_score.v, pure arithmetic) *)
Fixpoint tet (n : nat) : nat := match n with Datatypes.O => 1 | S n' => 4 ^ tet n' end.

Lemma h2_ge : forall z, 64 * 4 ^ z <= h 2 z.
Proof.
  intros z. change (h 2 z) with (iter (z + 3) (h 1) 1). pose proof (h1_iter (z + 3)) as E.
  rewrite Nat.pow_add_r in E. change (4 ^ 3) with 64 in E.
  assert (1 <= 4 ^ z) by (pose proof (Nat.pow_le_mono_r 4 0 z ltac:(lia) ltac:(lia)) as P; simpl in P; lia).
  nia.
Qed.

Lemma h2_iter : forall n, 64 * tet (S (S (S n))) <= iter (S (S n)) (h 2) 1.
Proof.
  induction n as [| n IH].
  - cbn [iter]. pose proof (h2_ge (h 2 1)) as A. pose proof (h2_ge 1) as B.
    change (4 ^ 1) with 4 in B.
    assert (C : tet 2 = 256) by reflexivity.
    assert (D : 4 ^ tet 2 <= 4 ^ h 2 1) by (apply Nat.pow_le_mono_r; [lia | rewrite C; lia]).
    change (tet 3) with (4 ^ tet 2). clear C. lia.
  - change (iter (S (S (S n))) (h 2) 1) with (h 2 (iter (S (S n)) (h 2) 1)).
    pose proof (h2_ge (iter (S (S n)) (h 2) 1)) as A.
    change (tet (S (S (S (S n))))) with (4 ^ tet (S (S (S n)))).
    assert (4 ^ tet (S (S (S n))) <= 4 ^ iter (S (S n)) (h 2) 1) by (apply Nat.pow_le_mono_r; lia). lia.
Qed.

Lemma J3_tet : 64 * tet 341 <= BB21_B21_run.J3.
Proof.
  rewrite BB21_B21_run.J3_eq, BB21_B21_run.jacc_s3.
  assert (E : iter 3 (h 1) 1 = 337) by (cbn [iter]; rewrite !h1; reflexivity).
  rewrite E. change (h 3 337) with (iter (337 + 3) (h 2) 1).
  pose proof (h2_iter 338) as H. replace (337 + 3) with (S (S 338)) by lia. lia.
Qed.

Lemma tet_pos : forall n, 1 <= tet n.
Proof. induction n; [simpl; lia |]. change (tet (S n)) with (4 ^ tet n). pose proof (Nat.pow_le_mono_r 4 0 (tet n) ltac:(lia) ltac:(lia)). simpl in H. lia. Qed.


Lemma mod8_form : forall c r, r < 8 -> (8 * c + r) mod 8 = r.
Proof. intros. replace (8 * c + r) with (r + c * 8) by lia. rewrite Nat.Div0.mod_add. apply Nat.mod_small. exact H. Qed.

Lemma J3_mod256 : BB21_B21_run.J3 mod 256 = 84.
Proof.
  rewrite BB21_B21_run.J3_eq, BB21_B21_run.jacc_s3. pose proof (h_mod256 3 (iter 3 (h 1) 1) ltac:(lia)) as M.
  pose proof (Nat.div_mod (h 3 (iter 3 (h 1) 1)) 256 ltac:(lia)) as D. rewrite M in D.
  remember (h 3 (iter 3 (h 1) 1) / 256) as a. clear Heqa. rewrite D.
  replace (256 * a + 81 + 3) with (84 + a * 256) by lia. rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma S3_stepW : astepG refillW BB21_B21_run.S3 = Next ([1; 1; 1; 1; 4; 1] :: repeat [2] (BB21_B21_run.J3 / 4)).
Proof.
  rewrite BB21_B21_run.J3_eq.
  change BB21_B21_run.S3 with (enc BB21_B21_run.s3).
  rewrite (astep_enc refillW).
  - rewrite (sweep_front refillW) by reflexivity.
    change (fr BB21_B21_run.s3) with [1]. change (up BB21_B21_run.s3) with (@nil (list nat)).
    change (es BB21_B21_run.s3) with (@nil nat). change (length (b0 BB21_B21_run.s3) - 1) with 4. unfold refillW.
    pose proof J3_mod256 as M. rewrite BB21_B21_run.J3_eq in M.
    pose proof BB21_B21_run.x3_big as B.
    assert (M8 : jacc BB21_B21_run.s3 mod 8 = 4)
      by (rewrite (BB21_B21_run.mod_down (jacc BB21_B21_run.s3) 8 32) by lia; change (8 * 32) with 256; rewrite M; reflexivity).
    assert (M4 : jacc BB21_B21_run.s3 mod 4 = 0)
      by (rewrite (BB21_B21_run.mod_down (jacc BB21_B21_run.s3) 4 64) by lia; change (4 * 64) with 256; rewrite M; reflexivity).
    replace (jacc BB21_B21_run.s3 mod 8 =? 6) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace ((jacc BB21_B21_run.s3 mod 4 =? 0) && (4 <=? jacc BB21_B21_run.s3)) with true
      by (symmetry; apply andb_true_iff; split; [apply Nat.eqb_eq | apply Nat.leb_le]; lia).
    change (map Init.Nat.pred [] ++ [4]) with [4]. cbv beta iota. cbn [restore rev map app repeat]. reflexivity.
  - exists 1, 1, [4; 1; 2]. split; [reflexivity | unfold nzd; repeat constructor; lia].
  - constructor.
Qed.

(** ** the run: five big phases (4..8), halt at refill #8 *)
Definition Fh (n : nat) : nat := h n 0.

Lemma Fh_step : forall E J k, h (E + 2) 0 <= J -> J <= 4 * k -> E + 1 <= h (E + 1) 0 -> h (E + 1) 0 <= k - 1.
Proof.
  intros E J k H1 H2 _. pose proof (h_S0 (E + 1) ltac:(lia)) as HS. replace (Datatypes.S (E + 1)) with (E + 2) in HS by lia. lia.
Qed.

Lemma step_lb : forall E J k E', h (E + 2) 0 <= J -> J <= 4 * k -> E' = E + k - 1 -> h (E + 1) 0 <= E'.
Proof.
  intros E J k E' H1 H2 H3. pose proof (h_S0 (E + 1) ltac:(lia)) as HS.
  replace (Datatypes.S (E + 1)) with (E + 2) in HS by lia. lia.
Qed.

Lemma Fh_mono : forall a b, a <= b -> Fh a <= h b 0.
Proof. intros. unfold Fh. apply h_mono_m. exact H. Qed.

Theorem abstract_finalW : exists s, BB21_B21_proc.star refillW BB21_B21_run.S3 (enc s) /\ PhaseEnd s /\ jacc s mod 8 = 6 /\
  iter 5 Fh (tet 341) <= h (length (es s) + 1) 0.
Proof.
  pose proof (Nat.div_mod BB21_B21_run.J3 256 ltac:(lia)) as HJ3. rewrite J3_mod256 in HJ3.
  remember (BB21_B21_run.J3 / 256) as a eqn:Ea. clear Ea.
  assert (HN4 : BB21_B21_run.N4 = 64 * a + 21).
  { unfold BB21_B21_run.N4. rewrite HJ3. replace (256 * a + 84) with (4 * (64 * a + 21)) by lia. apply BB21_B21_run.div4. }
  pose proof J3_tet as T3.
  (* phase 4 *)
  destruct (two_to_phi refillW (BB21_B21_run.N4 - 1) BB21_B21_run.s4 BB21_B21_run.INV_s4 eq_refl eq_refl)
    as [s4a [St4a [I4a [Hf4a [Hu4a [Hd4a Hl4a]]]]]].
  destruct (phi_loop refillW (BB21_B21_run.N4 - 1) s4a I4a Hf4a Hu4a Hd4a) as [s4e [St4e [E4 Hl4e]]].
  assert (L4 : length (es s4e) = 64 * a + 20) by (rewrite Hl4e, Hl4a; simpl; lia).
  destruct (jacc_end256 s4e E4) as [q4 Hj4]. rewrite L4 in Hj4. pose proof (jacc_end_lb s4e E4) as B4. rewrite L4 in B4.
  assert (M4 : jacc s4e mod 4 = 0) by (rewrite Hj4; replace (256 * q4 + 84 + 2 * (64 * a + 20)) with (4 * (64 * q4 + 32 * a + 31) + 0) by lia; apply BB21_B21_run.mod4_form; lia).
  assert (N4' : jacc s4e mod 8 <> 6) by (rewrite Hj4; replace (256 * q4 + 84 + 2 * (64 * a + 20)) with (8 * (32 * q4 + 16 * a + 15) + 4) by lia; rewrite mod8_form; lia).
  assert (K4 : jacc s4e / 4 = S (64 * q4 + 32 * a + 30)) by (rewrite Hj4; replace (256 * q4 + 84 + 2 * (64 * a + 20)) with (4 * S (64 * q4 + 32 * a + 30)) by lia; apply BB21_B21_run.div4).
  destruct (es s4e) as [| e4 es4] eqn:Ees4; [simpl in L4; lia |].
  destruct (refill_next4 s4e e4 es4 E4 Ees4 M4 N4') as [s5 [St5 [I5 [Hw5 [Hu5 Hl5]]]]]. rewrite K4 in Hu5.
  (* phase 5 *)
  destruct (phase_from_work refillW _ s5 I5 Hw5 Hu5) as [s5e [St5e [E5 Hl5e]]].
  assert (L5 : length (es s5e) = 96 * a + 64 * q4 + 50) by (rewrite Hl5e, Hl5; simpl in L4; lia).
  destruct (jacc_end256 s5e E5) as [q5 Hj5]. rewrite L5 in Hj5. pose proof (jacc_end_lb s5e E5) as B5. rewrite L5 in B5.
  assert (M5 : jacc s5e mod 4 = 0) by (rewrite Hj5; replace (256 * q5 + 84 + 2 * (96 * a + 64 * q4 + 50)) with (4 * (64 * q5 + 48 * a + 32 * q4 + 46) + 0) by lia; apply BB21_B21_run.mod4_form; lia).
  assert (N5' : jacc s5e mod 8 <> 6) by (rewrite Hj5; replace (256 * q5 + 84 + 2 * (96 * a + 64 * q4 + 50)) with (8 * (32 * q5 + 24 * a + 16 * q4 + 23) + 0) by lia; rewrite mod8_form; lia).
  assert (K5 : jacc s5e / 4 = S (64 * q5 + 48 * a + 32 * q4 + 45)) by (rewrite Hj5; replace (256 * q5 + 84 + 2 * (96 * a + 64 * q4 + 50)) with (4 * S (64 * q5 + 48 * a + 32 * q4 + 45)) by lia; apply BB21_B21_run.div4).
  destruct (es s5e) as [| e5 es5] eqn:Ees5; [simpl in L5; lia |].
  destruct (refill_next4 s5e e5 es5 E5 Ees5 M5 N5') as [s6 [St6 [I6 [Hw6 [Hu6 Hl6]]]]]. rewrite K5 in Hu6.
  (* phase 6 *)
  destruct (phase_from_work refillW _ s6 I6 Hw6 Hu6) as [s6e [St6e [E6 Hl6e]]].
  assert (L6 : length (es s6e) = 144 * a + 96 * q4 + 64 * q5 + 95) by (rewrite Hl6e, Hl6; simpl in L5; lia).
  destruct (jacc_end256 s6e E6) as [q6 Hj6]. rewrite L6 in Hj6. pose proof (jacc_end_lb s6e E6) as B6. rewrite L6 in B6.
  assert (M6 : jacc s6e mod 8 = 2) by (rewrite Hj6; replace (256 * q6 + 84 + 2 * (144 * a + 96 * q4 + 64 * q5 + 95)) with (8 * (32 * q6 + 36 * a + 24 * q4 + 16 * q5 + 34) + 2) by lia; apply mod8_form; lia).
  assert (K6 : (jacc s6e + 2) / 4 = S (64 * q6 + 72 * a + 48 * q4 + 32 * q5 + 68)) by (rewrite Hj6; replace (256 * q6 + 84 + 2 * (144 * a + 96 * q4 + 64 * q5 + 95) + 2) with (4 * S (64 * q6 + 72 * a + 48 * q4 + 32 * q5 + 68)) by lia; apply BB21_B21_run.div4).
  destruct (es s6e) as [| e6 es6] eqn:Ees6; [simpl in L6; lia |].
  destruct (refill_nextV s6e e6 es6 E6 Ees6 M6) as [s7 [St7 [I7 [Hw7 [Hu7 Hl7]]]]]. rewrite K6 in Hu7.
  (* phase 7 *)
  destruct (phase_from_work refillW _ s7 I7 Hw7 Hu7) as [s7e [St7e [E7 Hl7e]]].
  assert (L7 : length (es s7e) = 216 * a + 144 * q4 + 96 * q5 + 64 * q6 + 163) by (rewrite Hl7e, Hl7; simpl in L6; lia).
  destruct (jacc_end256 s7e E7) as [q7 Hj7]. rewrite L7 in Hj7. pose proof (jacc_end_lb s7e E7) as B7. rewrite L7 in B7.
  assert (M7 : jacc s7e mod 8 = 2) by (rewrite Hj7; replace (256 * q7 + 84 + 2 * (216 * a + 144 * q4 + 96 * q5 + 64 * q6 + 163)) with (8 * (32 * q7 + 54 * a + 36 * q4 + 24 * q5 + 16 * q6 + 51) + 2) by lia; apply mod8_form; lia).
  assert (K7 : (jacc s7e + 2) / 4 = S (64 * q7 + 108 * a + 72 * q4 + 48 * q5 + 32 * q6 + 102)) by (rewrite Hj7; replace (256 * q7 + 84 + 2 * (216 * a + 144 * q4 + 96 * q5 + 64 * q6 + 163) + 2) with (4 * S (64 * q7 + 108 * a + 72 * q4 + 48 * q5 + 32 * q6 + 102)) by lia; apply BB21_B21_run.div4).
  destruct (es s7e) as [| e7 es7] eqn:Ees7; [simpl in L7; lia |].
  destruct (refill_nextV s7e e7 es7 E7 Ees7 M7) as [s8 [St8 [I8 [Hw8 [Hu8 Hl8]]]]]. rewrite K7 in Hu8.
  (* phase 8 *)
  destruct (phase_from_work refillW _ s8 I8 Hw8 Hu8) as [s8e [St8e [E8 Hl8e]]].
  assert (L8 : length (es s8e) = 324 * a + 216 * q4 + 144 * q5 + 96 * q6 + 64 * q7 + 265) by (rewrite Hl8e, Hl8; simpl in L7; lia).
  destruct (jacc_end256 s8e E8) as [q8 Hj8]. rewrite L8 in Hj8.
  assert (M8 : jacc s8e mod 8 = 6) by (rewrite Hj8; replace (256 * q8 + 84 + 2 * (324 * a + 216 * q4 + 144 * q5 + 96 * q6 + 64 * q7 + 265)) with (8 * (32 * q8 + 81 * a + 54 * q4 + 36 * q5 + 24 * q6 + 16 * q7 + 76) + 6) by lia; apply mod8_form; lia).
  exists s8e. split; [| split; [exact E8 | split; [exact M8 |]]].
  - econstructor; [exact S3_stepW |].
    replace ([1; 1; 1; 1; 4; 1] :: repeat [2] (BB21_B21_run.J3 / 4)) with (enc BB21_B21_run.s4) by (rewrite BB21_B21_run.enc_s4; reflexivity).
    eapply (star_trans refillW); [exact St4a |]. eapply (star_trans refillW); [exact St4e |].
    econstructor; [exact St5 |]. eapply (star_trans refillW); [exact St5e |].
    econstructor; [exact St6 |]. eapply (star_trans refillW); [exact St6e |].
    econstructor; [exact St7 |]. eapply (star_trans refillW); [exact St7e |].
    econstructor; [exact St8 |]. exact St8e.
  - (* growth: each phase applies Fh at least once *)
    pose proof (tet_pos 341) as Tp.
    assert (G4 : tet 341 <= 64 * a + 20) by lia.
    assert (G5 : h (64 * a + 20 + 1) 0 <= 96 * a + 64 * q4 + 50)
      by (apply (step_lb _ (jacc s4e) (S (64 * q4 + 32 * a + 30))); [exact B4 | lia | lia]).
    assert (G6 : h (96 * a + 64 * q4 + 50 + 1) 0 <= 144 * a + 96 * q4 + 64 * q5 + 95)
      by (apply (step_lb _ (jacc s5e) (S (64 * q5 + 48 * a + 32 * q4 + 45))); [exact B5 | lia | lia]).
    assert (G7 : h (144 * a + 96 * q4 + 64 * q5 + 95 + 1) 0 <= 216 * a + 144 * q4 + 96 * q5 + 64 * q6 + 163)
      by (apply (step_lb _ (jacc s6e) (S (64 * q6 + 72 * a + 48 * q4 + 32 * q5 + 68))); [exact B6 | lia | lia]).
    assert (G8 : h (216 * a + 144 * q4 + 96 * q5 + 64 * q6 + 163 + 1) 0 <= 324 * a + 216 * q4 + 144 * q5 + 96 * q6 + 64 * q7 + 265)
      by (apply (step_lb _ (jacc s7e) (S (64 * q7 + 108 * a + 72 * q4 + 48 * q5 + 32 * q6 + 102))); [exact B7 | lia | lia]).
    rewrite L8. cbn [iter].
    assert (F1 : Fh (tet 341) <= 96 * a + 64 * q4 + 50) by (pose proof (Fh_mono (tet 341) (64 * a + 20 + 1) ltac:(lia)); lia).
    assert (F2 : Fh (Fh (tet 341)) <= 144 * a + 96 * q4 + 64 * q5 + 95) by (pose proof (Fh_mono (Fh (tet 341)) (96 * a + 64 * q4 + 50 + 1) ltac:(lia)); lia).
    assert (F3 : Fh (Fh (Fh (tet 341))) <= 216 * a + 144 * q4 + 96 * q5 + 64 * q6 + 163) by (pose proof (Fh_mono (Fh (Fh (tet 341))) (144 * a + 96 * q4 + 64 * q5 + 95 + 1) ltac:(lia)); lia).
    assert (F4 : Fh (Fh (Fh (Fh (tet 341)))) <= 324 * a + 216 * q4 + 144 * q5 + 96 * q6 + 64 * q7 + 265) by (pose proof (Fh_mono (Fh (Fh (Fh (tet 341)))) (216 * a + 144 * q4 + 96 * q5 + 64 * q6 + 163 + 1) ltac:(lia)); lia).
    apply Fh_mono. lia.
Qed.
