(** Comparison of M13_19 (BB13_M13_19.v) with the EXACT score of the previous BB(13) entry M13b.

    M13b (BB13/verify_m13b, files BB13_M13b.v and BB13_M13b_bound.v, byte-identical copies here) proves
      BB13_M13b_bound.score_exact :
        exists c, c0 -[ BB13_M13b.tm ]->* c /\ halted BB13_M13b.tm c /\
                  BB13_M13b_bound.ones c (fst pa7 + snd pa7 + 5)
    for the explicit pair pa7 of its 7-round run.  Both machines halt reading a 0 with a halting transition
    that writes a 1, so for both sigma = (ones at the halt) + 1.

    This file proves an UPPER bound on M13b's exact score,
      fst pa7 + snd pa7 + 5 < iter 14 f_omega2 (f_omega 3),
    from the definitions of M13b's maps (W, Kc, Kc_full, Kd_step, Kd_iter, D_reload, pb_K0), and combines it
    with M13_19's sigma_bound (n > iter 19 f_omega2 (f_omega 3)) into
      beats_M13b_exact : M13_19's halting tape holds more ones than M13b's.
    The fast-growing functions are M13_19's (standard: f 0 = S, f (k+1) n = (f k)^n n, f_omega n = f n n,
    f_omega1 n = f_omega^n n, f_omega2 n = f_omega1^n n).  No closed FGH term is ever evaluated: every bound is
    proved for variables and instantiated. *)

From BB8 Require Import Individual132.
From BB8 Require BB13_M13b BB13_M13b_bound.
From BB8 Require Import BB13_M13_19.
From Coq Require Import Lia PeanoNat.

Local Open Scope nat_scope.

(** [dlia] with the facts k * (x / k) <= x for every division by a constant in the goal and the hypotheses. *)
Ltac add_div_facts :=
  repeat match goal with
  | |- context [?x / ?k] =>
      lazymatch goal with
      | _ : k * (x / k) <= x |- _ => fail
      | _ => pose proof (Nat.Div0.mul_div_le x k)
      end
  | H : context [?x / ?k] |- _ =>
      lazymatch goal with
      | _ : k * (x / k) <= x |- _ => fail
      | _ => pose proof (Nat.Div0.mul_div_le x k)
      end
  end.
Ltac dlia := add_div_facts; lia.

(** ** Unfolding lemmas for the hierarchy (stated for variables only) *)

Transparent f_omega f_omega1 f_omega2.
Lemma cmp_Fw_unf : forall n, f_omega n = f n n. Proof. reflexivity. Qed.
Lemma cmp_F1_unf : forall n, f_omega1 n = iter n f_omega n. Proof. reflexivity. Qed.
Lemma cmp_F2_unf : forall n, f_omega2 n = iter n f_omega1 n. Proof. reflexivity. Qed.
Opaque f f_omega f_omega1 f_omega2.

(** The two files define [iter] with the same text. *)
Lemma cmp_iter_M : forall (X : Type) n (g : X -> X) x, BB13_M13b.iter n g x = iter n g x.
Proof.
  intros X n g x. induction n as [| n IH]; cbn [BB13_M13b.iter iter]; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

(** ** Generic facts *)

Lemma cmp_iter_diag : forall g, (forall a b, a <= b -> g a <= g b) -> (forall a, a <= g a) ->
  forall n x m, n <= m -> x <= m -> iter n g x <= iter m g m.
Proof.
  intros g Hm Hid n x m Hn Hx.
  transitivity (iter n g m); [apply iter_mono_x; assumption |].
  apply iter_mono_n; assumption.
Qed.

Lemma cmp_f2_4x : forall n, 2 <= n -> 4 * n <= f 2 n.
Proof.
  intros n Hn. rewrite (f_S 1 n).
  transitivity (iter 2 (f 1) n).
  - cbn [iter]. rewrite !f1. dlia.
  - apply iter_mono_n; [apply f_id | exact Hn].
Qed.

Lemma cmp_Fw3 : 192 <= f_omega 3.
Proof.
  rewrite cmp_Fw_unf, (f_S 2 3). cbn [iter].
  pose proof (cmp_f2_4x 3 ltac:(dlia)) as H1.
  pose proof (cmp_f2_4x (f 2 3) ltac:(dlia)) as H2.
  pose proof (cmp_f2_4x (f 2 (f 2 3)) ltac:(dlia)) as H3.
  dlia.
Qed.

Lemma cmp_G1 : forall x k, 8 <= x -> k <= 8 -> x + f_omega (x + k) <= iter 3 f_omega x.
Proof.
  intros x k Hx Hk. cbn [iter].
  pose proof (f_omega_dbl x ltac:(dlia)) as H1.
  pose proof (f_omega_mono (x + k) (f_omega x) ltac:(dlia)) as H2.
  pose proof (f_omega_id (f_omega x)) as H3.
  pose proof (f_omega_dbl (f_omega (f_omega x)) ltac:(dlia)) as H4.
  dlia.
Qed.

Lemma cmp_G3 : forall x, 3 <= x -> iter 3 f_omega x <= f_omega1 x.
Proof. intros x Hx. rewrite cmp_F1_unf. apply iter_mono_n; [apply f_omega_id | exact Hx]. Qed.

Lemma cmp_F1_8x : forall x, 3 <= x -> 8 * x <= f_omega1 x.
Proof.
  intros x Hx. transitivity (iter 3 f_omega x); [| apply cmp_G3; exact Hx].
  cbn [iter].
  pose proof (f_omega_dbl x ltac:(dlia)) as H1.
  pose proof (f_omega_dbl (f_omega x) ltac:(dlia)) as H2.
  pose proof (f_omega_dbl (f_omega (f_omega x)) ltac:(dlia)) as H3.
  dlia.
Qed.

Lemma cmp_F1_F2 : forall x, 1 <= x -> f_omega1 x <= f_omega2 x.
Proof.
  intros x Hx. rewrite cmp_F2_unf. change (f_omega1 x) with (iter 1 f_omega1 x).
  apply iter_mono_n; [apply f_omega1_id | exact Hx].
Qed.

Lemma cmp_it_F1_F2 : forall n t, 8 <= t -> n <= 7 * t -> iter n f_omega1 t <= f_omega2 (f_omega2 t).
Proof.
  intros n t Ht Hn.
  transitivity (f_omega2 (7 * t)).
  - rewrite (cmp_F2_unf (7 * t)). apply cmp_iter_diag; [exact f_omega1_mono | exact f_omega1_id | dlia | dlia].
  - apply f_omega2_mono.
    pose proof (cmp_F1_8x t ltac:(dlia)). pose proof (cmp_F1_F2 t ltac:(dlia)). dlia.
Qed.

(** ** Upper bounds for M13b's maps, in the size measure p + a *)

Definition sz (x : nat * nat) : nat := fst x + snd x.

(** Used instead of [unfold sz] on closed pairs: the kernel must never be asked to convert [sz pa] and
    [fst pa + snd pa] for a closed [pa], since it may then compute [pa]. *)
Lemma cmp_sz : forall x, sz x = fst x + snd x.
Proof. reflexivity. Qed.

Lemma cmp_W_aux : forall j b, BB13_M13b.W j b + 3 <= f (S j) (b + 3).
Proof.
  induction j as [| j IH]; intros b.
  - rewrite BB13_M13b.W_0, f1. dlia.
  - rewrite BB13_M13b.W_S, cmp_iter_M.
    assert (Hi : forall i, iter i (BB13_M13b.W j) 2 + 3 <= iter i (f (S j)) 5).
    { induction i as [| i IHi]; cbn [iter]; [dlia |].
      specialize (IH (iter i (BB13_M13b.W j) 2)).
      pose proof (f_mono (S j) _ _ IHi). dlia. }
    transitivity (iter (S b) (f (S j)) 5); [exact (Hi (S b)) |].
    rewrite (f_S (S j) (b + 3)).
    assert (E : iter (b + 3) (f (S j)) (b + 3) = iter (S b) (f (S j)) (iter 2 (f (S j)) (b + 3))).
    { rewrite <- iter_add. f_equal. dlia. }
    rewrite E. apply iter_mono_x; [intros u v Huv; apply f_mono; exact Huv |].
    cbn [iter].
    pose proof (f_gt (S j) (b + 3) ltac:(dlia)).
    pose proof (f_gt (S j) (f (S j) (b + 3)) ltac:(dlia)). dlia.
Qed.

Lemma cmp_W : forall j b, BB13_M13b.W j b <= f_omega (j + b + 4).
Proof.
  intros j b. pose proof (cmp_W_aux j b) as H0.
  pose proof (f_level_mono (b + 3) (S j) (b + 3) ltac:(dlia)) as H1.
  replace (b + 3 + S j) with (j + b + 4) in H1 by dlia.
  pose proof (f_mono (j + b + 4) (b + 3) (j + b + 4) ltac:(dlia)) as H2.
  rewrite cmp_Fw_unf. dlia.
Qed.

(** From here on, M13b's W is used only through cmp_W: no closed W term is ever unfolded. *)
Opaque BB13_M13b.W.

Lemma cmp_Kc : forall p a t, p + a <= t -> 8 <= t -> sz (BB13_M13b.Kc (p, a)) <= iter 3 f_omega t.
Proof.
  intros p a t Hs Ht. rewrite BB13_M13b_bound.Kc_unfold. unfold sz; cbn [fst snd].
  pose proof (cmp_W (p - 1) 1).
  pose proof (f_omega_mono (p - 1 + 1 + 4) (t + 4) ltac:(dlia)).
  pose proof (cmp_G1 t 4 ltac:(dlia) ltac:(dlia)). dlia.
Qed.

Lemma cmp_Kc_it : forall n pa t, sz pa <= t -> 8 <= t ->
  sz (BB13_M13b.iter n BB13_M13b.Kc pa) <= iter (3 * n) f_omega t.
Proof.
  induction n as [| n IH]; intros pa t Hs Ht.
  - cbn [BB13_M13b.iter]. rewrite Nat.mul_0_r. cbn [iter]. exact Hs.
  - cbn [BB13_M13b.iter].
    specialize (IH pa t Hs Ht).
    destruct (BB13_M13b.iter n BB13_M13b.Kc pa) as [p a] eqn:E.
    try rewrite E in IH. unfold sz in IH; cbn [fst snd] in IH.
    pose proof (iter_ge f_omega f_omega_id (3 * n) t).
    replace (3 * S n) with (3 + 3 * n) by dlia. rewrite iter_add.
    apply cmp_Kc; dlia.
Qed.

Lemma cmp_Kc_full : forall pb t, sz pb <= t -> 8 <= t -> sz (BB13_M13b.Kc_full pb) <= iter 2 f_omega1 t.
Proof.
  intros [p b] t Hs Ht. unfold sz in Hs; cbn [fst snd] in Hs.
  rewrite BB13_M13b_bound.Kc_full_unfold.
  assert (H0 : sz (p - 1, BB13_M13b.W (p - 1) 3) <= iter 3 f_omega t).
  { unfold sz; cbn [fst snd].
    pose proof (cmp_W (p - 1) 3).
    pose proof (f_omega_mono (p - 1 + 3 + 4) (t + 6) ltac:(dlia)).
    pose proof (cmp_G1 t 6 ltac:(dlia) ltac:(dlia)). dlia. }
  assert (Ht0 : 8 <= iter 3 f_omega t) by (pose proof (iter_ge f_omega f_omega_id 3 t); dlia).
  pose proof (cmp_Kc_it (b / 2) _ _ H0 Ht0) as H1.
  rewrite <- iter_add in H1.
  eapply Nat.le_trans; [exact H1 |].
  transitivity (f_omega1 (2 * t)).
  - rewrite (cmp_F1_unf (2 * t)). apply cmp_iter_diag; [exact f_omega_mono | exact f_omega_id | dlia | dlia].
  - cbn [iter]. apply f_omega1_mono. pose proof (cmp_F1_8x t ltac:(dlia)). dlia.
Qed.

Lemma cmp_Kd_step : forall pb t, sz pb <= t -> 8 <= t -> sz (BB13_M13b.Kd_step pb) <= iter 3 f_omega1 t.
Proof.
  intros pb t Hs Ht. rewrite BB13_M13b_bound.Kd_step_unfold.
  pose proof (cmp_Kc_full pb t Hs Ht) as H1.
  destruct (BB13_M13b.Kc_full pb) as [p a] eqn:E.
  try rewrite E in H1. unfold sz in H1 |- *; cbn [fst snd] in H1 |- *.
  assert (HT : 8 <= iter 2 f_omega1 t) by (pose proof (iter_ge f_omega1 f_omega1_id 2 t); dlia).
  pose proof (cmp_W p (a + 4)).
  pose proof (f_omega_mono (p + (a + 4) + 4) (iter 2 f_omega1 t + 8) ltac:(dlia)).
  pose proof (cmp_G1 (iter 2 f_omega1 t) 8 ltac:(dlia) ltac:(dlia)).
  pose proof (cmp_G3 (iter 2 f_omega1 t) ltac:(dlia)).
  change (iter 3 f_omega1 t) with (f_omega1 (iter 2 f_omega1 t)).
  dlia.
Qed.

Lemma cmp_Kd_iter : forall m pb t, sz pb <= t -> 8 <= t ->
  sz (BB13_M13b.Kd_iter m pb) <= iter (3 * m) f_omega1 t.
Proof.
  intros m pb t Hs Ht. rewrite BB13_M13b_bound.Kd_iter_unfold.
  induction m as [| m IH].
  - cbn [BB13_M13b.iter]. rewrite Nat.mul_0_r. cbn [iter]. exact Hs.
  - cbn [BB13_M13b.iter]. replace (3 * S m) with (3 + 3 * m) by dlia. rewrite iter_add.
    apply cmp_Kd_step; [exact IH |].
    pose proof (iter_ge f_omega1 f_omega1_id (3 * m) t). dlia.
Qed.

Lemma cmp_D_reload : forall pa t, sz pa <= t -> 8 <= t -> sz (BB13_M13b.D_reload pa) <= f_omega1 t.
Proof.
  intros [p a] t Hs Ht. unfold sz in Hs; cbn [fst snd] in Hs.
  rewrite BB13_M13b_bound.D_reload_unfold. unfold sz; cbn [fst snd].
  pose proof (cmp_W (p - 1) 0).
  pose proof (f_omega_mono (p - 1 + 0 + 4) (t + 4) ltac:(dlia)).
  pose proof (cmp_G1 t 4 ltac:(dlia) ltac:(dlia)).
  pose proof (cmp_G3 t ltac:(dlia)). dlia.
Qed.

Definition C0 : nat := iter 3 f_omega 20.

Lemma cmp_pbK0 : sz BB13_M13b.pb_K0 <= C0.
Proof.
  rewrite BB13_M13b_bound.pb_K0_unfold. unfold sz, C0; cbn [fst snd].
  pose proof (cmp_W 8 8) as H1. change (8 + 8 + 4) with 20 in H1.
  pose proof (cmp_G1 20 0 ltac:(dlia) ltac:(dlia)) as H2. change (20 + 0) with 20 in H2.
  (* keep the closed term W 8 8 abstract, so that no tactic tries to compute it *)
  revert H1. generalize (BB13_M13b.W 8 8). intros w H1. dlia.
Qed.

Lemma cmp_C0_8 : 8 <= C0.
Proof. unfold C0. pose proof (iter_ge f_omega f_omega_id 3 20). dlia. Qed.

(** ** The two kinds of half-round of M13b, each bounded by two applications of f_omega2 *)

Lemma cmp_stageA : forall pa t, sz pa <= t -> 8 <= t ->
  sz (BB13_M13b.Kd_iter (snd pa / 6 + 1) (BB13_M13b.D_reload pa)) <= f_omega2 (f_omega2 t).
Proof.
  intros pa t Hs Ht.
  pose proof (cmp_D_reload pa t Hs Ht) as H1.
  assert (H8 : 8 <= f_omega1 t) by (pose proof (f_omega1_id t); dlia).
  pose proof (cmp_Kd_iter (snd pa / 6 + 1) _ _ H1 H8) as H2.
  change (f_omega1 t) with (iter 1 f_omega1 t) in H2. rewrite <- iter_add in H2.
  eapply Nat.le_trans; [exact H2 |]. apply cmp_it_F1_F2; [exact Ht |].
  unfold sz in Hs. dlia.
Qed.

Lemma cmp_stageB : forall c t, C0 <= t -> c <= t ->
  sz (BB13_M13b.Kc_full (BB13_M13b.Kd_iter c BB13_M13b.pb_K0)) <= f_omega2 (f_omega2 t).
Proof.
  intros c t HC Hc.
  pose proof cmp_pbK0. pose proof cmp_C0_8.
  pose proof (cmp_Kd_iter c BB13_M13b.pb_K0 t ltac:(dlia) ltac:(dlia)) as H1.
  assert (H8 : 8 <= iter (3 * c) f_omega1 t) by (pose proof (iter_ge f_omega1 f_omega1_id (3 * c) t); dlia).
  pose proof (cmp_Kc_full _ _ H1 H8) as H2.
  rewrite <- iter_add in H2.
  eapply Nat.le_trans; [exact H2 |]. apply cmp_it_F1_F2; dlia.
Qed.

(** ** The 7-round run of M13b *)

(** Closed terms of the hierarchy are never converted with [change]: Coq's conversion would unfold them.
    Iterates are regrouped with these two equations instead. *)
Lemma cmp_iter_1 : forall (g : nat -> nat) x, g x = iter 1 g x.
Proof. reflexivity. Qed.

Lemma cmp_iter_iter : forall (g : nat -> nat) a b x, iter a g (iter b g x) = iter (a + b) g x.
Proof. intros. rewrite iter_add. reflexivity. Qed.

Definition B0 : nat := f_omega2 (f_omega 3).

Lemma cmp_B0 : C0 <= B0 /\ sz BB13_M13b.pa1 <= B0.
Proof.
  pose proof cmp_Fw3 as H3.
  split.
  - unfold C0, B0.
    pose proof (cmp_G3 20 ltac:(dlia)).
    pose proof (f_omega1_mono 20 (f_omega 3) ltac:(dlia)).
    pose proof (cmp_F1_F2 (f_omega 3) ltac:(dlia)). dlia.
  - rewrite BB13_M13b.pa1_def, BB13_M13b.pb1_1_def, BB13_M13b.pb1_0_def.
    pose proof (cmp_D_reload (8, 4) 12 ltac:(unfold sz; cbn [fst snd]; dlia) ltac:(dlia)) as H1.
    assert (H8 : 8 <= f_omega1 12) by (pose proof (f_omega1_id 12); dlia).
    pose proof (cmp_Kd_step _ _ H1 H8) as H2.
    assert (H8' : 8 <= iter 3 f_omega1 (f_omega1 12))
      by (pose proof (iter_ge f_omega1 f_omega1_id 3 (f_omega1 12)); dlia).
    pose proof (cmp_Kc_full _ _ H2 H8') as H4.
    rewrite (cmp_iter_1 f_omega1 12), !cmp_iter_iter in H4.
    eapply Nat.le_trans; [exact H4 |].
    unfold B0. rewrite (cmp_F2_unf (f_omega 3)).
    apply cmp_iter_diag; [exact f_omega1_mono | exact f_omega1_id | dlia | dlia].
Qed.

Lemma cmp_B0_eq : B0 = f_omega2 (f_omega 3).
Proof. reflexivity. Qed.

Opaque B0 C0.

Lemma cmp_C0_k : forall k, C0 <= iter k f_omega2 B0.
Proof.
  intros k. destruct cmp_B0 as [HC _]. pose proof (iter_ge f_omega2 f_omega2_id k B0). dlia.
Qed.

Lemma cmp_stepA : forall k pa, sz pa <= iter (2 * k) f_omega2 B0 ->
  sz (BB13_M13b.Kd_iter (snd pa / 6 + 1) (BB13_M13b.D_reload pa)) <= iter (2 * S k) f_omega2 B0.
Proof.
  intros k pa H. replace (2 * S k) with (2 + 2 * k) by dlia. rewrite iter_add. cbn [iter].
  apply cmp_stageA; [exact H |]. pose proof (cmp_C0_k (2 * k)). pose proof cmp_C0_8. dlia.
Qed.

Lemma cmp_stepB : forall k c, c <= iter (2 * k) f_omega2 B0 ->
  sz (BB13_M13b.Kc_full (BB13_M13b.Kd_iter c BB13_M13b.pb_K0)) <= iter (2 * S k) f_omega2 B0.
Proof.
  intros k c H. replace (2 * S k) with (2 + 2 * k) by dlia. rewrite iter_add. cbn [iter].
  apply cmp_stageB; [apply cmp_C0_k | exact H].
Qed.

Lemma cmp_pa7 : sz BB13_M13b.pa7 <= iter (2 * 6) f_omega2 B0.
Proof.
  destruct cmp_B0 as [_ H1].
  assert (H1' : sz BB13_M13b.pa1 <= iter (2 * 0) f_omega2 B0) by (rewrite Nat.mul_0_r; cbn [iter]; exact H1).
  assert (H2 : sz BB13_M13b.pb2 <= iter (2 * 1) f_omega2 B0).
  { rewrite BB13_M13b.pb2_def, BB13_M13b.pb2_0_def. exact (cmp_stepA 0 _ H1'). }
  assert (H3 : sz BB13_M13b.pa3 <= iter (2 * 2) f_omega2 B0).
  { rewrite BB13_M13b.pa3_def, BB13_M13b.pb3_1_def, BB13_M13b.d3_def.
    apply (cmp_stepB 1). rewrite cmp_sz in H2. dlia. }
  assert (H4 : sz BB13_M13b.pb4 <= iter (2 * 3) f_omega2 B0).
  { rewrite BB13_M13b.pb4_def, BB13_M13b.pb4_0_def. exact (cmp_stepA 2 _ H3). }
  assert (H5 : sz BB13_M13b.pa5 <= iter (2 * 4) f_omega2 B0).
  { rewrite BB13_M13b.pa5_def, BB13_M13b.pb5_1_def, BB13_M13b.d5_def.
    apply (cmp_stepB 3). rewrite cmp_sz in H4. dlia. }
  assert (H6 : sz BB13_M13b.pb6 <= iter (2 * 5) f_omega2 B0).
  { rewrite BB13_M13b.pb6_def, BB13_M13b.pb6_0_def. exact (cmp_stepA 4 _ H5). }
  rewrite BB13_M13b.pa7_def, BB13_M13b.pb7_1_def, BB13_M13b.d7_def.
  apply (cmp_stepB 5). rewrite cmp_sz in H6. dlia.
Qed.

(** The last step, for variables (no local definitions in the proof term). *)
Lemma cmp_final : forall s x y, s <= x -> 3 <= x -> f_omega2 x <= y -> s + 5 < y.
Proof.
  intros s x y Hs Hx Hy. pose proof (cmp_F1_8x x Hx). pose proof (cmp_F1_F2 x ltac:(dlia)). dlia.
Qed.

Lemma cmp_s1 : fst BB13_M13b.pa7 + snd BB13_M13b.pa7 <= iter (2 * 6 + 1) f_omega2 (f_omega 3).
Proof.
  pose proof cmp_pa7 as H. rewrite cmp_sz, cmp_B0_eq in H.
  rewrite (cmp_iter_1 f_omega2 (f_omega 3)), cmp_iter_iter in H. exact H.
Qed.

Lemma cmp_s2 : 3 <= iter (2 * 6 + 1) f_omega2 (f_omega 3).
Proof.
  pose proof cmp_Fw3. pose proof (iter_ge f_omega2 f_omega2_id (2 * 6 + 1) (f_omega 3)). dlia.
Qed.

Lemma cmp_s3 : f_omega2 (iter (2 * 6 + 1) f_omega2 (f_omega 3)) <= iter 19 f_omega2 (f_omega 3).
Proof.
  rewrite (cmp_iter_1 f_omega2 (iter (2 * 6 + 1) f_omega2 (f_omega 3))), cmp_iter_iter.
  apply iter_mono_n; [exact f_omega2_id | dlia].
Qed.

Lemma cmp_score_M13b : fst BB13_M13b.pa7 + snd BB13_M13b.pa7 + 5 < iter 19 f_omega2 (f_omega 3).
Proof. exact (cmp_final _ _ _ cmp_s1 cmp_s2 cmp_s3). Qed.

(** ** The comparison *)

Theorem beats_M13b_exact :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
  fst BB13_M13b.pa7 + snd BB13_M13b.pa7 + 5 < n.
Proof.
  destruct sigma_bound as (c & n & H1 & H2 & H3 & H4).
  exists c, n. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof cmp_score_M13b. dlia.
Qed.

(** The same, together with M13b's exact-score theorem: the number NM of ones on M13b's halting tape is
    smaller than the number of ones on M13_19's halting tape. *)
Theorem beats_M13b_score :
  exists NM,
    (exists c, c0 -[ BB13_M13b.tm ]->* c /\ halted BB13_M13b.tm c /\ BB13_M13b_bound.ones c NM) /\
    (exists c n, c0 -[ tm ]->* c /\ halted tm c /\ ones c n /\ NM < n).
Proof.
  exists (fst BB13_M13b.pa7 + snd BB13_M13b.pa7 + 5).
  split; [exact BB13_M13b_bound.score_exact | exact beats_M13b_exact].
Qed.

Print Assumptions beats_M13b_exact.
Print Assumptions beats_M13b_score.
