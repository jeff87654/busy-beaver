(** B21: the abstract run from the phase-3 start to the halt (phases 4, 5, 6). *)
From Coq Require Import Lia PeanoNat List Bool.
From BB8 Require Import BB21_B21_absdef BB21_B21_grow BB21_B21_steps BB21_B21_inv BB21_B21_proc BB21_B21_phase.
Import ListNotations.
Set Default Goal Selector "!".

Lemma jacc_end_mod : forall s, PhaseEnd s -> jacc s mod 64 = (20 + 2 * length (es s)) mod 64.
Proof.
  intros s [I [_ [_ Hd]]]. unfold jacc. rewrite eng_eq. pose proof (deep_mod64 _ Hd) as M.
  pose proof (Nat.div_mod (eng0 (b0 s)) 64 ltac:(lia)) as D. rewrite M in D.
  remember (eng0 (b0 s) / 64) as a. rewrite D.
  replace (64 * a + 17 + 3 + 2 * length (es s)) with ((20 + 2 * length (es s)) + a * 64) by lia.
  apply Nat.Div0.mod_add.
Qed.

Lemma refill_next : forall s e es', PhaseEnd s -> es s = e :: es' -> jacc s mod 4 = 0 ->
  exists s', astepG refill21 (enc s) = Next (enc s') /\ INV s' /\ work (fr s') /\ up s' = repeat [2] (jacc s / 4) /\
    length (es s') = length es' /\ 1 <= jacc s / 4.
Proof.
  intros s e es' [I [Hf [Hu Hd]]] Hes Hm.
  pose proof (jacc_big s I (deep_big _ Hd)) as J16.
  assert (Hq : 1 <= jacc s / 4) by (apply Nat.div_le_lower_bound; lia).
  pose proof (inv_refill s e es' I Hf Hu Hes Hq) as I1.
  eexists. split; [| split; [exact I1 | split; [| split; [reflexivity | split; [simpl; apply map_length | exact Hq]]]]].
  - rewrite (step_refill s e es' (b0ok_of s I) (i_es s I) Hf Hu Hes Hm ltac:(lia)). f_equal.
  - split; [exact (i_frE _ I1) |]. simpl. rewrite app_length. simpl. lia.
Qed.

Lemma halt_end : forall s, PhaseEnd s -> jacc s mod 4 = 2 -> astepG refill21 (enc s) = Halt.
Proof. intros s [I [Hf [Hu _]]] Hm. apply (step_halt s (b0ok_of s I) (i_es s I) Hf Hu Hm). Qed.

Lemma mod_down : forall x a b, a <> 0 -> b <> 0 -> x mod a = (x mod (a * b)) mod a.
Proof.
  intros x a b Ha Hb. pose proof (Nat.div_mod x (a * b) ltac:(lia)) as D.
  remember (x / (a * b)) as q. remember (x mod (a * b)) as r. clear Heqq Heqr. rewrite D.
  replace (a * b * q + r) with (r + (b * q) * a) by lia. apply Nat.Div0.mod_add.
Qed.

(** the phase-3 start: [1,1,4,1,2] | [1].  Never let Coq compute engine values on literals: only rewrites. *)
Definition S3 : list (list nat) := [[1; 1; 4; 1; 2]; [1]].
Definition s3 : st := mk [1; 1; 4; 1; 2] [] [1] [].

Lemma eng0_S3 : eng0 [1; 1; 4; 1; 2] = h 3 (iter 3 (h 1) 1).
Proof. reflexivity. Qed.

Lemma jacc_s3 : jacc s3 = h 3 (iter 3 (h 1) 1) + 3.
Proof.
  unfold jacc. rewrite eng_eq. change (b0 s3) with [1; 1; 4; 1; 2]. change (length (es s3)) with 0.
  rewrite eng0_S3. rewrite Nat.mul_0_r, Nat.add_0_r. reflexivity.
Qed.

Lemma x3_mod : jacc s3 mod 64 = 20.
Proof.
  rewrite jacc_s3. pose proof (h_mod64 3 (iter 3 (h 1) 1) ltac:(lia)) as M.
  pose proof (Nat.div_mod (h 3 (iter 3 (h 1) 1)) 64 ltac:(lia)) as D. rewrite M in D.
  remember (h 3 (iter 3 (h 1) 1) / 64) as a. clear Heqa. rewrite D.
  replace (64 * a + 17 + 3) with (20 + a * 64) by lia. rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma x3_big : 100 <= jacc s3.
Proof.
  rewrite jacc_s3. pose proof (hm0_big 3 ltac:(lia)). pose proof (h_mono 3 0 (iter 3 (h 1) 1) ltac:(lia)). lia.
Qed.

(** seal the huge number: the kernel must never unfold it *)
Lemma J3_ex : {j | j = jacc s3}.
Proof. exists (jacc s3). reflexivity. Qed.
Definition J3 : nat := proj1_sig J3_ex.
Lemma J3_eq : J3 = jacc s3.
Proof. exact (proj2_sig J3_ex). Qed.

Lemma J3_mod : J3 mod 64 = 20.
Proof. rewrite J3_eq. exact x3_mod. Qed.

Lemma J3_big : 100 <= J3.
Proof. rewrite J3_eq. exact x3_big. Qed.

Lemma S3_step : astepG refill21 S3 = Next ([1; 1; 1; 1; 4; 1] :: repeat [2] (J3 / 4)).
Proof.
  rewrite J3_eq.
  change S3 with (enc s3).
  rewrite (astep_enc refill21).
  - rewrite (sweep_front refill21) by reflexivity.
    change (fr s3) with [1]. change (up s3) with (@nil (list nat)). change (es s3) with (@nil nat).
    change (length (b0 s3) - 1) with 4. unfold refill21.
    pose proof x3_mod as M. pose proof x3_big as B.
    assert (M4 : jacc s3 mod 4 = 0) by (rewrite (mod_down (jacc s3) 4 16) by lia; change (4 * 16) with 64; rewrite M; reflexivity).
    replace (jacc s3 mod 4 =? 2) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace ((jacc s3 mod 4 =? 0) && (4 <=? jacc s3)) with true
      by (symmetry; apply andb_true_iff; split; [apply Nat.eqb_eq | apply Nat.leb_le]; lia).
    change (map Init.Nat.pred [] ++ [4]) with [4]. cbv beta iota. cbn [restore rev map app repeat]. reflexivity.
  - exists 1, 1, [4; 1; 2]. split; [reflexivity | unfold nzd; repeat constructor; lia].
  - constructor.
Qed.

Lemma jacc_end_form : forall s, PhaseEnd s -> exists q, jacc s = 64 * q + 20 + 2 * length (es s).
Proof.
  intros s [I [_ [_ Hd]]]. unfold jacc. rewrite eng_eq. pose proof (deep_mod64 _ Hd) as M.
  pose proof (Nat.div_mod (eng0 (b0 s)) 64 ltac:(lia)) as D. rewrite M in D.
  exists (eng0 (b0 s) / 64). lia.
Qed.

Lemma div4 : forall c, (4 * c) / 4 = c.
Proof. intros. rewrite Nat.mul_comm. apply Nat.div_mul. lia. Qed.

Lemma mod4_form : forall c r, r < 4 -> (4 * c + r) mod 4 = r.
Proof. intros. replace (4 * c + r) with (r + c * 4) by lia. rewrite Nat.Div0.mod_add. apply Nat.mod_small. exact H. Qed.

(** phase 4 start *)
Definition N4 : nat := J3 / 4.
Definition s4 : st := mk [1; 1; 1; 1; 4; 1] [] [2] (repeat [2] (N4 - 1)).

Lemma N4_form : exists a, J3 = 64 * a + 20 /\ N4 = 16 * a + 5.
Proof.
  pose proof J3_mod as M. pose proof (Nat.div_mod J3 64 ltac:(lia)) as D. rewrite M in D.
  remember (J3 / 64) as a. clear Heqa.
  exists a. split; [exact D |]. unfold N4. rewrite D.
  replace (64 * a + 20) with (4 * (16 * a + 5)) by lia. apply div4.
Qed.

Lemma enc_s4 : enc s4 = [1; 1; 1; 1; 4; 1] :: repeat [2] N4.
Proof.
  destruct N4_form as [a [_ Ha]]. unfold enc, s4. cbn [b0 es fr up]. rewrite Ha.
  replace (16 * a + 5 - 1) with (16 * a + 4) by lia. replace (16 * a + 5) with (S (16 * a + 4)) by lia. reflexivity.
Qed.

Lemma Bound_s4 : 100 <= Bound s4.
Proof.
  unfold Bound. change (B0min s4 + 1) with 6.
  pose proof (LBe_big 6 ltac:(lia)) as H1.
  assert (H2 : 150 <= LBe 6 / 2) by (apply Nat.div_le_lower_bound; lia).
  pose proof (LBe_mono _ _ H2). pose proof (LBe_big 150 ltac:(lia)). lia.
Qed.

Lemma eng_s4 : eng0 [1; 1; 1; 1; 4; 1] = h 4 0.
Proof. exact (eng_41 3). Qed.

Lemma INV_s4 : INV s4.
Proof.
  assert (Hb : big [1; 1; 1; 1; 4; 1]) by (exists 3; right; reflexivity).
  constructor; cbn [b0 es fr up s4].
  - constructor.
  - reflexivity.
  - constructor; [unfold nzd; repeat constructor; lia |].
    apply Forall_forall. intros b H. apply repeat_spec in H. subst. unfold nzd. repeat constructor; lia.
  - right. right. exact Hb.
  - exists [], (N4 - 1). split; [constructor |]. right. reflexivity.
  - simpl. lia.
  - generalize (N4 - 1). intros n.
    induction n as [| n IH]; simpl; [exact Logic.I | split; [left; split; reflexivity | exact IH]].
  - intros _. exact Hb.
  - intros H. discriminate.
  - intros H. discriminate.
  - intros B HB. pose proof Bound_s4. assert (length B = 1).
    { destruct HB as [<- | HB]; [reflexivity | apply repeat_spec in HB; subst; reflexivity]. }
    lia.
  - intros _ B HB. assert (length B = 1).
    { destruct HB as [<- | HB]; [reflexivity | apply repeat_spec in HB; subst; reflexivity]. }
    rewrite eng_s4. pose proof (hm0_big 4 ltac:(lia)). lia.
  - change (B0min s4) with 5. lia.
Qed.

(** ** the run: three big phases, halt at the end of phase 6 *)
Theorem abstract_halt : exists bs, star refill21 S3 bs /\ astepG refill21 bs = Halt.
Proof.
  destruct N4_form as [a [HJ3 HN4]].
  (* phase 4 *)
  destruct (two_to_phi refill21 (N4 - 1) s4 INV_s4 eq_refl eq_refl) as [s4a [St4a [I4a [Hf4a [Hu4a [Hd4a Hl4a]]]]]].
  destruct (phi_loop refill21 (N4 - 1) s4a I4a Hf4a Hu4a Hd4a) as [s4e [St4e [E4 Hl4e]]].
  assert (L4 : length (es s4e) = 16 * a + 4) by (rewrite Hl4e, Hl4a; simpl; lia).
  destruct (jacc_end_form s4e E4) as [q4 Hj4]. rewrite L4 in Hj4.
  assert (M4 : jacc s4e mod 4 = 0) by (rewrite Hj4; replace (64 * q4 + 20 + 2 * (16 * a + 4)) with (4 * (16 * q4 + 8 * a + 7) + 0) by lia; apply mod4_form; lia).
  assert (K4 : jacc s4e / 4 = S (16 * q4 + 8 * a + 6)) by (rewrite Hj4; replace (64 * q4 + 20 + 2 * (16 * a + 4)) with (4 * S (16 * q4 + 8 * a + 6)) by lia; apply div4).
  destruct (es s4e) as [| e4 es4] eqn:Ees4; [simpl in L4; lia |].
  destruct (refill_next s4e e4 es4 E4 Ees4 M4) as [s5 [St5 [I5 [Hw5 [Hu5 [Hl5 _]]]]]].
  rewrite K4 in Hu5.
  (* phase 5 *)
  destruct (phase_from_work refill21 _ s5 I5 Hw5 Hu5) as [s5e [St5e [E5 Hl5e]]].
  assert (L5 : length (es s5e) = 24 * a + 16 * q4 + 10) by (rewrite Hl5e, Hl5; simpl in L4; lia).
  destruct (jacc_end_form s5e E5) as [q5 Hj5]. rewrite L5 in Hj5.
  assert (M5 : jacc s5e mod 4 = 0) by (rewrite Hj5; replace (64 * q5 + 20 + 2 * (24 * a + 16 * q4 + 10)) with (4 * (16 * q5 + 12 * a + 8 * q4 + 10) + 0) by lia; apply mod4_form; lia).
  assert (K5 : jacc s5e / 4 = S (16 * q5 + 12 * a + 8 * q4 + 9)) by (rewrite Hj5; replace (64 * q5 + 20 + 2 * (24 * a + 16 * q4 + 10)) with (4 * S (16 * q5 + 12 * a + 8 * q4 + 9)) by lia; apply div4).
  destruct (es s5e) as [| e5 es5] eqn:Ees5; [simpl in L5; lia |].
  destruct (refill_next s5e e5 es5 E5 Ees5 M5) as [s6 [St6 [I6 [Hw6 [Hu6 [Hl6 _]]]]]].
  rewrite K5 in Hu6.
  (* phase 6 *)
  destruct (phase_from_work refill21 _ s6 I6 Hw6 Hu6) as [s6e [St6e [E6 Hl6e]]].
  assert (L6 : length (es s6e) = 36 * a + 24 * q4 + 16 * q5 + 19) by (rewrite Hl6e, Hl6; simpl in L5; lia).
  destruct (jacc_end_form s6e E6) as [q6 Hj6]. rewrite L6 in Hj6.
  assert (M6 : jacc s6e mod 4 = 2).
  { rewrite Hj6. replace (64 * q6 + 20 + 2 * (36 * a + 24 * q4 + 16 * q5 + 19)) with (4 * (16 * q6 + 18 * a + 12 * q4 + 8 * q5 + 14) + 2) by lia.
    apply mod4_form. lia. }
  exists (enc s6e). split; [| exact (halt_end s6e E6 M6)].
  econstructor; [exact S3_step |].
  replace ([1; 1; 1; 1; 4; 1] :: repeat [2] (J3 / 4)) with (enc s4) by (rewrite enc_s4; reflexivity).
  eapply (star_trans refill21); [exact St4a |]. eapply (star_trans refill21); [exact St4e |].
  econstructor; [exact St5 |]. eapply (star_trans refill21); [exact St5e |].
  econstructor; [exact St6 |]. exact St6e.
Qed.

Theorem abstract_final : exists s, star refill21 S3 (enc s) /\ PhaseEnd s /\ jacc s mod 4 = 2 /\ J3 <= 2 * length (es s) + 20.
Proof.
  destruct N4_form as [a [HJ3 HN4]].
  (* phase 4 *)
  destruct (two_to_phi refill21 (N4 - 1) s4 INV_s4 eq_refl eq_refl) as [s4a [St4a [I4a [Hf4a [Hu4a [Hd4a Hl4a]]]]]].
  destruct (phi_loop refill21 (N4 - 1) s4a I4a Hf4a Hu4a Hd4a) as [s4e [St4e [E4 Hl4e]]].
  assert (L4 : length (es s4e) = 16 * a + 4) by (rewrite Hl4e, Hl4a; simpl; lia).
  destruct (jacc_end_form s4e E4) as [q4 Hj4]. rewrite L4 in Hj4.
  assert (M4 : jacc s4e mod 4 = 0) by (rewrite Hj4; replace (64 * q4 + 20 + 2 * (16 * a + 4)) with (4 * (16 * q4 + 8 * a + 7) + 0) by lia; apply mod4_form; lia).
  assert (K4 : jacc s4e / 4 = S (16 * q4 + 8 * a + 6)) by (rewrite Hj4; replace (64 * q4 + 20 + 2 * (16 * a + 4)) with (4 * S (16 * q4 + 8 * a + 6)) by lia; apply div4).
  destruct (es s4e) as [| e4 es4] eqn:Ees4; [simpl in L4; lia |].
  destruct (refill_next s4e e4 es4 E4 Ees4 M4) as [s5 [St5 [I5 [Hw5 [Hu5 [Hl5 _]]]]]].
  rewrite K4 in Hu5.
  (* phase 5 *)
  destruct (phase_from_work refill21 _ s5 I5 Hw5 Hu5) as [s5e [St5e [E5 Hl5e]]].
  assert (L5 : length (es s5e) = 24 * a + 16 * q4 + 10) by (rewrite Hl5e, Hl5; simpl in L4; lia).
  destruct (jacc_end_form s5e E5) as [q5 Hj5]. rewrite L5 in Hj5.
  assert (M5 : jacc s5e mod 4 = 0) by (rewrite Hj5; replace (64 * q5 + 20 + 2 * (24 * a + 16 * q4 + 10)) with (4 * (16 * q5 + 12 * a + 8 * q4 + 10) + 0) by lia; apply mod4_form; lia).
  assert (K5 : jacc s5e / 4 = S (16 * q5 + 12 * a + 8 * q4 + 9)) by (rewrite Hj5; replace (64 * q5 + 20 + 2 * (24 * a + 16 * q4 + 10)) with (4 * S (16 * q5 + 12 * a + 8 * q4 + 9)) by lia; apply div4).
  destruct (es s5e) as [| e5 es5] eqn:Ees5; [simpl in L5; lia |].
  destruct (refill_next s5e e5 es5 E5 Ees5 M5) as [s6 [St6 [I6 [Hw6 [Hu6 [Hl6 _]]]]]].
  rewrite K5 in Hu6.
  (* phase 6 *)
  destruct (phase_from_work refill21 _ s6 I6 Hw6 Hu6) as [s6e [St6e [E6 Hl6e]]].
  assert (L6 : length (es s6e) = 36 * a + 24 * q4 + 16 * q5 + 19) by (rewrite Hl6e, Hl6; simpl in L5; lia).
  destruct (jacc_end_form s6e E6) as [q6 Hj6]. rewrite L6 in Hj6.
  assert (M6 : jacc s6e mod 4 = 2).
  { rewrite Hj6. replace (64 * q6 + 20 + 2 * (36 * a + 24 * q4 + 16 * q5 + 19)) with (4 * (16 * q6 + 18 * a + 12 * q4 + 8 * q5 + 14) + 2) by lia.
    apply mod4_form. lia. }
  exists s6e. split; [| split; [exact E6 | split; [exact M6 | rewrite L6; lia]]].
  econstructor; [exact S3_step |].
  replace ([1; 1; 1; 1; 4; 1] :: repeat [2] (J3 / 4)) with (enc s4) by (rewrite enc_s4; reflexivity).
  eapply (star_trans refill21); [exact St4a |]. eapply (star_trans refill21); [exact St4e |].
  econstructor; [exact St5 |]. eapply (star_trans refill21); [exact St5e |].
  econstructor; [exact St6 |]. exact St6e.
Qed.
