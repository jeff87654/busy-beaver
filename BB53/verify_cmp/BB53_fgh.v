(** * BB53_fgh: the BB(5,3) machine's bounds restated with the STANDARD fast-growing hierarchy.

    Argon's Local.BB53_bound.sigma_exceeds_f_omega2 proves
        f_omega (knuth 8 2 3) < sigma  /\  f_omega (f_omega 7) < sigma
    with a home-made f_omega n = 2 ^n n (Knuth arrows).  Here f_omega is replaced by the standard f_omega of the
    published Ord.v (busy-beaver BB31/BB33 verify/multifile, logical root BB8): FGH omega n = f_n(n) with
    f_0 = S, f_(k+1)(n) = f_k^n(n)  (Ord.fin_fgh, Ord.FGH_omega).

    Key lemma (fin_fgh_le_knuth): for k >= 1 and x >= 4,  f_(k+1)(x) <= 2 ^k (3x);  hence for n >= 4,
    f_omega(n) <= 2 ^n n (FGH_omega_le_home).  It fails at n = 3 (f_3(3) = f_2(f_2(24)) > 2^(4*10^8) > 2 ^3 3 = 2^^4 = 65536),
    which does not matter here: every argument below is >= 7.

      Theorem sigma_exceeds_FGH :
        FGH omega (knuth 8 2 3) < sigma  /\  FGH omega (FGH omega 7) < sigma.

    i.e. sigma > f_omega(2 ^8 3) and sigma > f_omega(f_omega(7)) in the standard hierarchy. *)

From BB8 Require Import Ord.
From Local Require BB53_run BB53_bound.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

Module L := Local.BB53_bound.

Lemma iter_infl : forall (f : nat -> nat), (forall y, y <= f y) -> forall j x, x <= Nat.iter j f x.
Proof.
  intros f Hf j x. induction j as [|j IH]; [simpl; lia|].
  rewrite Nat.iter_succ. eapply Nat.le_trans; [exact IH | apply Hf].
Qed.

Lemma fin_ge : forall k x, x <= fin_fgh k x.
Proof.
  induction k as [|k IH]; intros x; cbn [fin_fgh]; [lia|]. apply iter_infl. exact IH.
Qed.

Lemma iter_fin0 : forall j y, Nat.iter j (fin_fgh 0) y = j + y.
Proof. induction j as [|j IH]; intros y; [reflexivity|]. rewrite Nat.iter_succ, IH. reflexivity. Qed.

Lemma fin1 : forall y, fin_fgh 1 y = 2 * y.
Proof. intros y. change (fin_fgh 1 y) with (Nat.iter y (fin_fgh 0) y). rewrite iter_fin0. lia. Qed.

Lemma iter_fin1 : forall j x, Nat.iter j (fin_fgh 1) x = 2 ^ j * x.
Proof.
  induction j as [|j IH]; intros x; [simpl; lia|].
  rewrite Nat.iter_succ, IH, fin1, Nat.pow_succ_r', Nat.mul_assoc. reflexivity.
Qed.

Lemma fin2_le : forall x, fin_fgh 2 x <= L.knuth 1 2 (3 * x).
Proof.
  intros x. rewrite L.knuth_1_pow.
  change (fin_fgh 2 x) with (Nat.iter x (fin_fgh 1) x). rewrite iter_fin1.
  pose proof (Nat.pow_gt_lin_r 2 x ltac:(lia)) as H1.
  assert (H2 : 2 ^ x * x <= 2 ^ x * 2 ^ x) by (apply Nat.mul_le_mono_l; lia).
  rewrite <- Nat.pow_add_r in H2.
  assert (H3 : 2 ^ (x + x) <= 2 ^ (3 * x)) by (apply Nat.pow_le_mono_r; lia).
  exact (Nat.le_trans _ _ _ H2 H3).
Qed.

Lemma three_le_pow2 : forall y, 4 <= y -> 3 * y <= 2 ^ y.
Proof.
  intros y Hy. induction Hy as [|y Hy IH]; [simpl; lia|].
  rewrite Nat.pow_succ_r'. pose proof (Nat.pow_gt_lin_r 2 y ltac:(lia)). lia.
Qed.

Lemma knuth_ge_3y : forall k y, 1 <= k -> 4 <= y -> 3 * y <= L.knuth k 2 y.
Proof.
  intros k y Hk Hy.
  pose proof (L.knuth_mono_k 1 k y Hk ltac:(lia)) as H. rewrite L.knuth_1_pow in H.
  pose proof (three_le_pow2 y Hy). lia.
Qed.

Lemma iter_knuth_mono : forall L n x y, x <= y -> Nat.iter n (L.knuth L 2) x <= Nat.iter n (L.knuth L 2) y.
Proof.
  intros L0 n. induction n as [|n IH]; intros x y H; [exact H|].
  cbn [Nat.iter]. apply L.knuth_mono_b. apply IH. exact H.
Qed.

(** f_(k+1)(x) <= 2 ^k (3x) for k >= 1, x >= 4 *)
Theorem fin_fgh_le_knuth : forall k x, 1 <= k -> 4 <= x -> fin_fgh (S k) x <= L.knuth k 2 (3 * x).
Proof.
  intros k. induction k as [|k IHk]; intros x Hk Hx; [lia|].
  destruct k as [|k'].
  - apply fin2_le.
  - assert (HI : forall j, Nat.iter j (fin_fgh (S (S k'))) x <= Nat.iter (2 * j) (L.knuth (S k') 2) x).
    { induction j as [|j IHj]; [apply Nat.eq_le_incl; reflexivity|].
      replace (2 * S j) with (S (S (2 * j))) by lia. rewrite !Nat.iter_succ.
      assert (Ha : 4 <= Nat.iter j (fin_fgh (S (S k'))) x)
        by (pose proof (iter_infl _ (fin_ge (S (S k'))) j x); lia).
      assert (Hinf : forall y, y <= L.knuth (S k') 2 y) by (intro y; pose proof (L.knuth_ge_2b (S k') y); lia).
      assert (Hb : 4 <= Nat.iter (2 * j) (L.knuth (S k') 2) x)
        by (pose proof (iter_infl _ Hinf (2 * j) x); lia).
      eapply Nat.le_trans; [apply IHk; [lia | exact Ha]|].
      apply L.knuth_mono_b.
      eapply Nat.le_trans; [apply Nat.mul_le_mono_l; exact IHj|].
      apply knuth_ge_3y; [lia | exact Hb]. }
    change (fin_fgh (S (S (S k'))) x) with (Nat.iter x (fin_fgh (S (S k'))) x).
    eapply Nat.le_trans; [apply HI|].
    assert (Hx2 : x <= L.knuth (S (S k')) 2 x) by (pose proof (L.knuth_ge_2b (S (S k')) x); lia).
    eapply Nat.le_trans; [apply iter_knuth_mono; exact Hx2|].
    rewrite (L.knuth_S0 (S k') x), (L.knuth_S0 (S k') (3 * x)).
    rewrite <- L.iter_add. replace (2 * x + x) with (3 * x) by lia. lia.
Qed.

Lemma tet_ge : forall m, 3 <= m -> 3 * m + 3 <= L.knuth 2 2 m.
Proof.
  intros m Hm. induction Hm as [|m Hm IH].
  - change (L.knuth 2 2 3) with 16. lia.
  - rewrite (L.knuth_S 1 2 m). pose proof (L.knuth_ge_2b 1 (L.knuth 2 2 m)). lia.
Qed.

(** The standard f_omega is below the home-made one from n = 4 on. *)
Theorem FGH_omega_le_home : forall n, 4 <= n -> FGH omega n <= L.f_omega n.
Proof.
  intros n Hn. rewrite FGH_omega, L.f_omega_def.
  destruct n as [|m]; [lia|].
  pose proof (fin_fgh_le_knuth m (S m) ltac:(lia) Hn) as H1.
  rewrite (L.knuth_S m 2 m).
  eapply Nat.le_trans; [exact H1|]. apply L.knuth_mono_b.
  pose proof (L.knuth_mono_k 2 (S m) m ltac:(lia) ltac:(lia)).
  pose proof (tet_ge m ltac:(lia)). lia.
Qed.

Theorem sigma_exceeds_FGH :
  FGH omega (L.knuth 8 2 3) < Local.BB53_run.sigma /\ FGH omega (FGH omega 7) < Local.BB53_run.sigma.
Proof.
  destruct L.sigma_exceeds_f_omega2 as [H1 H2].
  pose proof L.knuth8_3_ge_7 as H83.
  split.
  - pose proof (FGH_omega_le_home (L.knuth 8 2 3) ltac:(lia)). lia.
  - pose proof (FGH_omega_le_home 7 ltac:(lia)) as H7.
    assert (Hge : 7 <= FGH omega 7) by (rewrite FGH_omega; apply fin_ge).
    pose proof (FGH_omega_le_home (FGH omega 7) ltac:(lia)) as H8.
    pose proof (L.f_omega_mono (FGH omega 7) (L.f_omega 7) ltac:(lia) H7) as H9.
    lia.
Qed.

Print Assumptions FGH_omega_le_home.
Print Assumptions sigma_exceeds_FGH.
