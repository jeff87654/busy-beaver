(** Comparison of M14_fw3 (BB14_M14_fw3.v) with the EXACT score of the previous BB(14) entry M14_31.

    M14_31 (BB14/verify_m14_31, file BB14_M14_31.v, byte-identical copy here) proves
      BB14_M14_31.score_exact :
        exists c, c0 -[ BB14_M14_31.tm ]->* c /\ halted BB14_M14_31.tm c /\
                  BB14_M14_31.ones c (fst pa32 + snd pa32 + 4)
    for the explicit pair pa32 of its 32-round run.  M14_31 halts reading a 1 (sigma = ones at the halt);
    M14_fw3 halts reading a 0 with a halting transition that writes a 1 (sigma = ones at the halt + 1).

    This file proves an UPPER bound on M14_31's exact score,
      fst pa32 + snd pa32 + 4 < iter 64 f_omega2 (f_omega 3) <= f_omega3 (f_omega 3),
    from the definitions of M14_31's maps (W, Kc, Kc_full, Kd_step, Kd_iter, D_reload, pb_K0 and the eight round
    maps), and combines it with M14_fw3's sigma_bound (n > f_omega3 (f_omega 3)) into
      beats_M14_31_exact : M14_fw3's halting tape holds more ones than M14_31's.
    The fast-growing functions are M14_fw3's (standard: f 0 = S, f (k+1) n = (f k)^n n, f_omega n = f n n,
    f_omega1 n = f_omega^n n, f_omega2 n = f_omega1^n n, f_omega3 n = f_omega2^n n).  No closed FGH term is
    ever evaluated: every bound is proved for variables and instantiated. *)

From BB8 Require Import Individual142.
From BB8 Require BB14_M14_31.
From BB8 Require Import BB14_M14_fw3.
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

Transparent f_omega f_omega1 f_omega2 f_omega3.
Lemma cmp_Fw_unf : forall n, f_omega n = f n n. Proof. reflexivity. Qed.
Lemma cmp_F1_unf : forall n, f_omega1 n = iter n f_omega n. Proof. reflexivity. Qed.
Lemma cmp_F2_unf : forall n, f_omega2 n = iter n f_omega1 n. Proof. reflexivity. Qed.
Lemma cmp_F3_unf : forall n, f_omega3 n = iter n f_omega2 n. Proof. reflexivity. Qed.
Opaque f f_omega f_omega1 f_omega2 f_omega3.

(** The two files define [iter] with the same text. *)
Lemma cmp_iter_M : forall (X : Type) n (g : X -> X) x, BB14_M14_31.iter n g x = iter n g x.
Proof.
  intros X n g x. induction n as [| n IH]; cbn [BB14_M14_31.iter iter]; [reflexivity |].
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

(** ** Upper bounds for M14_31's maps, in the size measure p + a *)

Definition sz (x : nat * nat) : nat := fst x + snd x.

(** Used instead of [unfold sz] on closed pairs: the kernel must never be asked to convert [sz pa] and
    [fst pa + snd pa] for a closed [pa], since it may then compute [pa]. *)
Lemma cmp_sz : forall x, sz x = fst x + snd x.
Proof. reflexivity. Qed.

Lemma cmp_W_aux : forall j b, BB14_M14_31.W j b + 3 <= f (S j) (b + 3).
Proof.
  induction j as [| j IH]; intros b.
  - rewrite BB14_M14_31.W_0, f1. dlia.
  - rewrite BB14_M14_31.W_S, cmp_iter_M.
    assert (Hi : forall i, iter i (BB14_M14_31.W j) 2 + 3 <= iter i (f (S j)) 5).
    { induction i as [| i IHi]; cbn [iter]; [dlia |].
      specialize (IH (iter i (BB14_M14_31.W j) 2)).
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

Lemma cmp_W : forall j b, BB14_M14_31.W j b <= f_omega (j + b + 4).
Proof.
  intros j b. pose proof (cmp_W_aux j b) as H0.
  pose proof (f_level_mono (b + 3) (S j) (b + 3) ltac:(dlia)) as H1.
  replace (b + 3 + S j) with (j + b + 4) in H1 by dlia.
  pose proof (f_mono (j + b + 4) (b + 3) (j + b + 4) ltac:(dlia)) as H2.
  rewrite cmp_Fw_unf. dlia.
Qed.

(** From here on, M14_31's W is used only through cmp_W: no closed W term is ever unfolded. *)
Opaque BB14_M14_31.W.

Lemma cmp_Kc : forall p a t, p + a <= t -> 8 <= t -> sz (BB14_M14_31.Kc (p, a)) <= iter 3 f_omega t.
Proof.
  intros p a t Hs Ht. rewrite BB14_M14_31.Kc_unfold. unfold sz; cbn [fst snd].
  pose proof (cmp_W (p - 1) 1).
  pose proof (f_omega_mono (p - 1 + 1 + 4) (t + 4) ltac:(dlia)).
  pose proof (cmp_G1 t 4 ltac:(dlia) ltac:(dlia)). dlia.
Qed.

Lemma cmp_Kc_it : forall n pa t, sz pa <= t -> 8 <= t ->
  sz (BB14_M14_31.iter n BB14_M14_31.Kc pa) <= iter (3 * n) f_omega t.
Proof.
  induction n as [| n IH]; intros pa t Hs Ht.
  - cbn [BB14_M14_31.iter]. rewrite Nat.mul_0_r. cbn [iter]. exact Hs.
  - cbn [BB14_M14_31.iter].
    specialize (IH pa t Hs Ht).
    destruct (BB14_M14_31.iter n BB14_M14_31.Kc pa) as [p a] eqn:E.
    try rewrite E in IH. unfold sz in IH; cbn [fst snd] in IH.
    pose proof (iter_ge f_omega f_omega_id (3 * n) t).
    replace (3 * S n) with (3 + 3 * n) by dlia. rewrite iter_add.
    apply cmp_Kc; dlia.
Qed.

Lemma cmp_Kc_full : forall pb t, sz pb <= t -> 8 <= t -> sz (BB14_M14_31.Kc_full pb) <= iter 2 f_omega1 t.
Proof.
  intros [p b] t Hs Ht. unfold sz in Hs; cbn [fst snd] in Hs.
  rewrite BB14_M14_31.Kc_full_unfold.
  assert (H0 : sz (p - 1, BB14_M14_31.W (p - 1) 3) <= iter 3 f_omega t).
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

Lemma cmp_Kd_step : forall pb t, sz pb <= t -> 8 <= t -> sz (BB14_M14_31.Kd_step pb) <= iter 3 f_omega1 t.
Proof.
  intros pb t Hs Ht. rewrite BB14_M14_31.Kd_step_unfold.
  pose proof (cmp_Kc_full pb t Hs Ht) as H1.
  destruct (BB14_M14_31.Kc_full pb) as [p a] eqn:E.
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
  sz (BB14_M14_31.Kd_iter m pb) <= iter (3 * m) f_omega1 t.
Proof.
  intros m pb t Hs Ht. rewrite BB14_M14_31.Kd_iter_unfold.
  induction m as [| m IH].
  - cbn [BB14_M14_31.iter]. rewrite Nat.mul_0_r. cbn [iter]. exact Hs.
  - cbn [BB14_M14_31.iter]. replace (3 * S m) with (3 + 3 * m) by dlia. rewrite iter_add.
    apply cmp_Kd_step; [exact IH |].
    pose proof (iter_ge f_omega1 f_omega1_id (3 * m) t). dlia.
Qed.

Lemma cmp_D_reload : forall pa t, sz pa <= t -> 8 <= t -> sz (BB14_M14_31.D_reload pa) <= f_omega1 t.
Proof.
  intros [p a] t Hs Ht. unfold sz in Hs; cbn [fst snd] in Hs.
  rewrite BB14_M14_31.D_reload_unfold. unfold sz; cbn [fst snd].
  pose proof (cmp_W (p - 1) 0).
  pose proof (f_omega_mono (p - 1 + 0 + 4) (t + 4) ltac:(dlia)).
  pose proof (cmp_G1 t 4 ltac:(dlia) ltac:(dlia)).
  pose proof (cmp_G3 t ltac:(dlia)). dlia.
Qed.

Definition C0 : nat := iter 3 f_omega 20.

Lemma cmp_pbK0 : sz BB14_M14_31.pb_K0 <= C0.
Proof.
  rewrite BB14_M14_31.pb_K0_unfold. unfold sz, C0; cbn [fst snd].
  pose proof (cmp_W 8 8) as H1. change (8 + 8 + 4) with 20 in H1.
  pose proof (cmp_G1 20 0 ltac:(dlia) ltac:(dlia)) as H2. change (20 + 0) with 20 in H2.
  (* keep the closed term W 8 8 abstract, so that no tactic tries to compute it *)
  revert H1. generalize (BB14_M14_31.W 8 8). intros w H1. dlia.
Qed.

Lemma cmp_C0_8 : 8 <= C0.
Proof. unfold C0. pose proof (iter_ge f_omega f_omega_id 3 20). dlia. Qed.

(** ** The round maps of M14_31, each bounded by two applications of f_omega2 *)

Lemma cmp_A0 : forall m pa t, sz pa <= t -> 8 <= t -> m <= t ->
  sz (BB14_M14_31.Kd_iter m (BB14_M14_31.D_reload pa)) <= f_omega2 (f_omega2 t).
Proof.
  intros m pa t Hs Ht Hm.
  pose proof (cmp_D_reload pa t Hs Ht) as H1.
  assert (H8 : 8 <= f_omega1 t) by (pose proof (f_omega1_id t); dlia).
  pose proof (cmp_Kd_iter m _ _ H1 H8) as H2.
  change (f_omega1 t) with (iter 1 f_omega1 t) in H2. rewrite <- iter_add in H2.
  eapply Nat.le_trans; [exact H2 |]. apply cmp_it_F1_F2; dlia.
Qed.

Lemma cmp_A1 : forall m pa t, sz pa <= t -> 8 <= t -> m <= t ->
  sz (BB14_M14_31.Kc_full (BB14_M14_31.Kd_iter m (BB14_M14_31.D_reload pa))) <= f_omega2 (f_omega2 t).
Proof.
  intros m pa t Hs Ht Hm.
  pose proof (cmp_D_reload pa t Hs Ht) as H1.
  assert (H8 : 8 <= f_omega1 t) by (pose proof (f_omega1_id t); dlia).
  pose proof (cmp_Kd_iter m _ _ H1 H8) as H2.
  assert (H8' : 8 <= iter (3 * m) f_omega1 (f_omega1 t))
    by (pose proof (iter_ge f_omega1 f_omega1_id (3 * m) (f_omega1 t)); dlia).
  pose proof (cmp_Kc_full _ _ H2 H8') as H3.
  change (f_omega1 t) with (iter 1 f_omega1 t) in H3. rewrite <- !iter_add in H3.
  eapply Nat.le_trans; [exact H3 |]. apply cmp_it_F1_F2; dlia.
Qed.

Lemma cmp_B0 : forall c t, C0 <= t -> c <= t ->
  sz (BB14_M14_31.Kd_iter c BB14_M14_31.pb_K0) <= f_omega2 (f_omega2 t).
Proof.
  intros c t HC Hc.
  pose proof cmp_pbK0. pose proof cmp_C0_8.
  pose proof (cmp_Kd_iter c BB14_M14_31.pb_K0 t ltac:(dlia) ltac:(dlia)) as H1.
  eapply Nat.le_trans; [exact H1 |]. apply cmp_it_F1_F2; dlia.
Qed.

Lemma cmp_B1 : forall c t, C0 <= t -> c <= t ->
  sz (BB14_M14_31.Kc_full (BB14_M14_31.Kd_iter c BB14_M14_31.pb_K0)) <= f_omega2 (f_omega2 t).
Proof.
  intros c t HC Hc.
  pose proof cmp_pbK0. pose proof cmp_C0_8.
  pose proof (cmp_Kd_iter c BB14_M14_31.pb_K0 t ltac:(dlia) ltac:(dlia)) as H1.
  assert (H8 : 8 <= iter (3 * c) f_omega1 t) by (pose proof (iter_ge f_omega1 f_omega1_id (3 * c) t); dlia).
  pose proof (cmp_Kc_full _ _ H1 H8) as H2.
  rewrite <- iter_add in H2.
  eapply Nat.le_trans; [exact H2 |]. apply cmp_it_F1_F2; dlia.
Qed.

Definition round_ok (R : nat * nat -> nat * nat) : Prop :=
  forall x t, sz x <= t -> C0 <= t -> sz (R x) <= f_omega2 (f_omega2 t).

Transparent BB14_M14_31.D2_round BB14_M14_31.D1_round BB14_M14_31.K0_z0_round BB14_M14_31.K1_z0_round
  BB14_M14_31.K2_z0_round BB14_M14_31.K0_z1_round BB14_M14_31.K1_z1_round BB14_M14_31.K2_z1_round.

Lemma ok_D2 : round_ok BB14_M14_31.D2_round.
Proof.
  intros x t Hs HC. pose proof cmp_C0_8. unfold BB14_M14_31.D2_round.
  apply cmp_A0; [exact Hs | dlia | unfold sz in Hs; dlia].
Qed.

Lemma ok_D1 : round_ok BB14_M14_31.D1_round.
Proof.
  intros x t Hs HC. pose proof cmp_C0_8. unfold BB14_M14_31.D1_round.
  apply cmp_A1; [exact Hs | dlia | unfold sz in Hs; dlia].
Qed.

Lemma ok_K0_z0 : round_ok BB14_M14_31.K0_z0_round.
Proof. intros x t Hs HC. unfold BB14_M14_31.K0_z0_round. apply cmp_B0; [exact HC | unfold sz in Hs; dlia]. Qed.
Lemma ok_K0_z1 : round_ok BB14_M14_31.K0_z1_round.
Proof. intros x t Hs HC. unfold BB14_M14_31.K0_z1_round. apply cmp_B0; [exact HC | unfold sz in Hs; dlia]. Qed.
Lemma ok_K1_z0 : round_ok BB14_M14_31.K1_z0_round.
Proof. intros x t Hs HC. unfold BB14_M14_31.K1_z0_round. apply cmp_B1; [exact HC | unfold sz in Hs; dlia]. Qed.
Lemma ok_K2_z0 : round_ok BB14_M14_31.K2_z0_round.
Proof. intros x t Hs HC. unfold BB14_M14_31.K2_z0_round. apply cmp_B1; [exact HC | unfold sz in Hs; dlia]. Qed.
Lemma ok_K1_z1 : round_ok BB14_M14_31.K1_z1_round.
Proof. intros x t Hs HC. unfold BB14_M14_31.K1_z1_round. apply cmp_B1; [exact HC | unfold sz in Hs; dlia]. Qed.
Lemma ok_K2_z1 : round_ok BB14_M14_31.K2_z1_round.
Proof. intros x t Hs HC. unfold BB14_M14_31.K2_z1_round. apply cmp_B1; [exact HC | unfold sz in Hs; dlia]. Qed.

Opaque BB14_M14_31.D2_round BB14_M14_31.D1_round BB14_M14_31.K0_z0_round BB14_M14_31.K1_z0_round
  BB14_M14_31.K2_z0_round BB14_M14_31.K0_z1_round BB14_M14_31.K1_z1_round BB14_M14_31.K2_z1_round.

(** ** The 32-round run of M14_31 *)

(** Closed terms of the hierarchy are never converted with [change]: Coq's conversion would unfold them.
    Iterates are regrouped with these two equations instead. *)
Lemma cmp_iter_1 : forall (g : nat -> nat) x, g x = iter 1 g x.
Proof. reflexivity. Qed.

Lemma cmp_iter_0 : forall (g : nat -> nat) x, iter 0 g x = x.
Proof. reflexivity. Qed.

Lemma cmp_iter_iter : forall (g : nat -> nat) a b x, iter a g (iter b g x) = iter (a + b) g x.
Proof. intros. rewrite iter_add. reflexivity. Qed.

Definition B0 : nat := f_omega2 (f_omega 3).

Lemma cmp_B0_C0 : C0 <= B0.
Proof.
  pose proof cmp_Fw3. unfold C0, B0.
  pose proof (cmp_G3 20 ltac:(dlia)).
  pose proof (f_omega1_mono 20 (f_omega 3) ltac:(dlia)).
  pose proof (cmp_F1_F2 (f_omega 3) ltac:(dlia)). dlia.
Qed.

Lemma cmp_pa1 : sz BB14_M14_31.pa1 <= iter (2 * 0) f_omega2 B0.
Proof.
  pose proof cmp_Fw3. pose proof cmp_pbK0. pose proof cmp_C0_8.
  rewrite BB14_M14_31.pa1_def.
  pose proof (cmp_Kc_full BB14_M14_31.pb_K0 C0 ltac:(dlia) ltac:(dlia)) as Hk1.
  assert (Hk2 : C0 <= f_omega1 20) by (unfold C0; apply cmp_G3; dlia).
  pose proof (iter_mono_x f_omega1 f_omega1_mono 2 C0 (f_omega1 20) Hk2) as Hk3.
  rewrite (cmp_iter_1 f_omega1 20), cmp_iter_iter in Hk3.
  eapply Nat.le_trans; [exact Hk1 |]. eapply Nat.le_trans; [exact Hk3 |].
  rewrite Nat.mul_0_r, cmp_iter_0. unfold B0. rewrite (cmp_F2_unf (f_omega 3)).
  apply cmp_iter_diag; [exact f_omega1_mono | exact f_omega1_id | dlia | dlia].
Qed.

Lemma cmp_B0_eq : B0 = f_omega2 (f_omega 3).
Proof. reflexivity. Qed.

Opaque B0 C0.

Lemma cmp_C0_k : forall k, C0 <= iter k f_omega2 B0.
Proof.
  intros k. pose proof cmp_B0_C0. pose proof (iter_ge f_omega2 f_omega2_id k B0). dlia.
Qed.

Lemma cmp_next : forall R, round_ok R -> forall k x,
  sz x <= iter (2 * k) f_omega2 B0 -> sz (R x) <= iter (2 * S k) f_omega2 B0.
Proof.
  intros R HR k x Hx.
  replace (2 * S k) with (2 + 2 * k) by dlia. rewrite iter_add. cbn [iter].
  apply HR; [exact Hx | apply cmp_C0_k].
Qed.

Lemma cmp_pb2 : sz BB14_M14_31.pb2 <= iter (2 * 1) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb2_def. exact (cmp_next _ ok_D2 0 _ cmp_pa1). Qed.
Lemma cmp_pb3 : sz BB14_M14_31.pb3 <= iter (2 * 2) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb3_def. exact (cmp_next _ ok_K0_z0 1 _ cmp_pb2). Qed.
Lemma cmp_pa4 : sz BB14_M14_31.pa4 <= iter (2 * 3) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa4_def. exact (cmp_next _ ok_K2_z1 2 _ cmp_pb3). Qed.
Lemma cmp_pb5 : sz BB14_M14_31.pb5 <= iter (2 * 4) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb5_def. exact (cmp_next _ ok_D2 3 _ cmp_pa4). Qed.
Lemma cmp_pb6 : sz BB14_M14_31.pb6 <= iter (2 * 5) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb6_def. exact (cmp_next _ ok_K0_z0 4 _ cmp_pb5). Qed.
Lemma cmp_pb7 : sz BB14_M14_31.pb7 <= iter (2 * 6) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb7_def. exact (cmp_next _ ok_K0_z1 5 _ cmp_pb6). Qed.
Lemma cmp_pa8 : sz BB14_M14_31.pa8 <= iter (2 * 7) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa8_def. exact (cmp_next _ ok_K2_z0 6 _ cmp_pb7). Qed.
Lemma cmp_pb9 : sz BB14_M14_31.pb9 <= iter (2 * 8) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb9_def. exact (cmp_next _ ok_D2 7 _ cmp_pa8). Qed.
Lemma cmp_pa10 : sz BB14_M14_31.pa10 <= iter (2 * 9) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa10_def. exact (cmp_next _ ok_K2_z1 8 _ cmp_pb9). Qed.
Lemma cmp_pb11 : sz BB14_M14_31.pb11 <= iter (2 * 10) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb11_def. exact (cmp_next _ ok_D2 9 _ cmp_pa10). Qed.
Lemma cmp_pa12 : sz BB14_M14_31.pa12 <= iter (2 * 11) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa12_def. exact (cmp_next _ ok_K2_z0 10 _ cmp_pb11). Qed.
Lemma cmp_pb13 : sz BB14_M14_31.pb13 <= iter (2 * 12) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb13_def. exact (cmp_next _ ok_D2 11 _ cmp_pa12). Qed.
Lemma cmp_pa14 : sz BB14_M14_31.pa14 <= iter (2 * 13) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa14_def. exact (cmp_next _ ok_K1_z1 12 _ cmp_pb13). Qed.
Lemma cmp_pa15 : sz BB14_M14_31.pa15 <= iter (2 * 14) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa15_def. exact (cmp_next _ ok_D1 13 _ cmp_pa14). Qed.
Lemma cmp_pb16 : sz BB14_M14_31.pb16 <= iter (2 * 15) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb16_def. exact (cmp_next _ ok_D2 14 _ cmp_pa15). Qed.
Lemma cmp_pa17 : sz BB14_M14_31.pa17 <= iter (2 * 16) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa17_def. exact (cmp_next _ ok_K1_z1 15 _ cmp_pb16). Qed.
Lemma cmp_pa18 : sz BB14_M14_31.pa18 <= iter (2 * 17) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa18_def. exact (cmp_next _ ok_D1 16 _ cmp_pa17). Qed.
Lemma cmp_pb19 : sz BB14_M14_31.pb19 <= iter (2 * 18) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb19_def. exact (cmp_next _ ok_D2 17 _ cmp_pa18). Qed.
Lemma cmp_pb20 : sz BB14_M14_31.pb20 <= iter (2 * 19) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb20_def. exact (cmp_next _ ok_K0_z1 18 _ cmp_pb19). Qed.
Lemma cmp_pa21 : sz BB14_M14_31.pa21 <= iter (2 * 20) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa21_def. exact (cmp_next _ ok_K2_z0 19 _ cmp_pb20). Qed.
Lemma cmp_pb22 : sz BB14_M14_31.pb22 <= iter (2 * 21) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb22_def. exact (cmp_next _ ok_D2 20 _ cmp_pa21). Qed.
Lemma cmp_pa23 : sz BB14_M14_31.pa23 <= iter (2 * 22) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa23_def. exact (cmp_next _ ok_K1_z1 21 _ cmp_pb22). Qed.
Lemma cmp_pa24 : sz BB14_M14_31.pa24 <= iter (2 * 23) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa24_def. exact (cmp_next _ ok_D1 22 _ cmp_pa23). Qed.
Lemma cmp_pb25 : sz BB14_M14_31.pb25 <= iter (2 * 24) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb25_def. exact (cmp_next _ ok_D2 23 _ cmp_pa24). Qed.
Lemma cmp_pa26 : sz BB14_M14_31.pa26 <= iter (2 * 25) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa26_def. exact (cmp_next _ ok_K2_z1 24 _ cmp_pb25). Qed.
Lemma cmp_pb27 : sz BB14_M14_31.pb27 <= iter (2 * 26) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb27_def. exact (cmp_next _ ok_D2 25 _ cmp_pa26). Qed.
Lemma cmp_pa28 : sz BB14_M14_31.pa28 <= iter (2 * 27) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa28_def. exact (cmp_next _ ok_K2_z0 26 _ cmp_pb27). Qed.
Lemma cmp_pb29 : sz BB14_M14_31.pb29 <= iter (2 * 28) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb29_def. exact (cmp_next _ ok_D2 27 _ cmp_pa28). Qed.
Lemma cmp_pa30 : sz BB14_M14_31.pa30 <= iter (2 * 29) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa30_def. exact (cmp_next _ ok_K2_z1 28 _ cmp_pb29). Qed.
Lemma cmp_pb31 : sz BB14_M14_31.pb31 <= iter (2 * 30) f_omega2 B0.
Proof. rewrite BB14_M14_31.pb31_def. exact (cmp_next _ ok_D2 29 _ cmp_pa30). Qed.
Lemma cmp_pa32 : sz BB14_M14_31.pa32 <= iter (2 * 31) f_omega2 B0.
Proof. rewrite BB14_M14_31.pa32_def. exact (cmp_next _ ok_K1_z0 30 _ cmp_pb31). Qed.

(** The last step, for variables (no local definitions in the proof term). *)
Lemma cmp_final : forall s x y, s <= x -> 3 <= x -> f_omega2 x <= y -> s + 4 < y.
Proof.
  intros s x y Hs Hx Hy. pose proof (cmp_F1_8x x Hx). pose proof (cmp_F1_F2 x ltac:(dlia)). dlia.
Qed.

Lemma cmp_score_M14_31 : fst BB14_M14_31.pa32 + snd BB14_M14_31.pa32 + 4 < f_omega3 (f_omega 3).
Proof.
  pose proof cmp_pa32 as H. rewrite cmp_sz, cmp_B0_eq in H.
  rewrite (cmp_iter_1 f_omega2 (f_omega 3)), cmp_iter_iter in H.
  apply (cmp_final _ _ _ H).
  - pose proof cmp_Fw3. pose proof (iter_ge f_omega2 f_omega2_id (2 * 31 + 1) (f_omega 3)). dlia.
  - rewrite (cmp_iter_1 f_omega2 (iter (2 * 31 + 1) f_omega2 (f_omega 3))), cmp_iter_iter.
    rewrite (cmp_F3_unf (f_omega 3)). apply iter_mono_n; [exact f_omega2_id |].
    pose proof cmp_Fw3. dlia.
Qed.

(** ** The comparison *)

Theorem beats_M14_31_exact :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
  fst BB14_M14_31.pa32 + snd BB14_M14_31.pa32 + 4 < n.
Proof.
  destruct sigma_bound as (c & n & H1 & H2 & H3 & H4).
  exists c, n. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof cmp_score_M14_31. dlia.
Qed.

(** The same, together with M14_31's exact-score theorem: the number N31 of ones on M14_31's halting tape is
    smaller than the number of ones on M14_fw3's halting tape. *)
Theorem beats_M14_31_score :
  exists N31,
    (exists c, c0 -[ BB14_M14_31.tm ]->* c /\ halted BB14_M14_31.tm c /\ BB14_M14_31.ones c N31) /\
    (exists c n, c0 -[ tm ]->* c /\ halted tm c /\ ones c n /\ N31 < n).
Proof.
  exists (fst BB14_M14_31.pa32 + snd BB14_M14_31.pa32 + 4).
  split; [exact BB14_M14_31.score_exact | exact beats_M14_31_exact].
Qed.

Print Assumptions beats_M14_31_exact.
Print Assumptions beats_M14_31_score.
