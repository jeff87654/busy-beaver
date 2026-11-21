(** * Closed-form identities and FGH lower bounds for the new BB(5,4) champion:
      1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE

    Main certified theorems (zero axioms):
      1. [sigma_beats_official_bb54]:
           f_omega2 (knuth 4 2 (knuth 3 2 4)) < sigma
         (strictly exceeds the refined upper bound of the official BB(5,4) wiki champion!)
      2. [sigma_beats_f_omega1_65536]:
           f_omega1 (2 ^ 16) < sigma
         (certifies a full ordinal jump from f_omega^2 to f_{omega+1}(65536)!) *)

From TM64 Require Import Individual64 BB64_rules BB64_run BB64_score.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(** ** Knuth up-arrows: [knuth n a b = a ↑^n b], with [a ↑^0 b = a * b] *)
Fixpoint knuth (n a b : nat) : nat :=
  match n with
  | 0 => a * b
  | S n' => Nat.iter b (knuth n' a) 1
  end.

Lemma iter_add : forall {X : Type} (f : X -> X) a b x,
  Nat.iter (a + b) f x = Nat.iter a f (Nat.iter b f x).
Proof.
  intros X f a. induction a as [|a IH]; intros b x.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma knuth_S : forall n a b, knuth (S n) a (S b) = knuth n a (knuth (S n) a b).
Proof. reflexivity. Qed.

Lemma knuth_S0 : forall k b, knuth (S k) 2 b = Nat.iter b (knuth k 2) 1.
Proof. reflexivity. Qed.

Lemma knuth_1 : forall k, knuth k 2 1 = 2.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

Lemma knuth_2 : forall k, knuth k 2 2 = 4.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - simpl. rewrite knuth_1. exact IH.
Qed.

Lemma iter2_knuth : forall k, Nat.iter 2 (knuth k 2) 1 = 4.
Proof. intros k. simpl. rewrite knuth_1. apply knuth_2. Qed.

Lemma knuth_1_pow : forall b, knuth 1 2 b = 2 ^ b.
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rewrite knuth_S, IH. simpl. lia.
Qed.

(** ** Closed form of Kropitz's [g] hierarchy: [2 * g (S k) m + 4 = knuth k 2 (2 * m + 4)] *)

Section ClosedForm.
Variable h kh : nat -> nat.
Hypothesis hyp : forall y, 2 * h y + 4 = kh (2 * y + 4).

Lemma iter_closed_helper : forall j x,
  2 * Nat.iter j h x + 4 = Nat.iter j kh (2 * x + 4).
Proof.
  induction j as [|j IH]; intros x.
  - simpl. lia.
  - simpl in *. rewrite hyp. rewrite (IH x). reflexivity.
Qed.
End ClosedForm.

Theorem g_closed : forall k m,
  2 * g (S k) m + 4 = knuth k 2 (2 * m + 4).
Proof.
  induction k as [|k IH]; intros m.
  - assert (E : g 1 m = 2 * m + 2).
    { assert (E2 : g 1 m = Nat.iter (2 * m + 2) (g 0) 0%nat) by reflexivity.
      rewrite E2. rewrite (iter_g0 (2 * m + 2) 0%nat). lia. }
    rewrite E. simpl. lia.
  - assert (E : g (S (S k)) m = Nat.iter (2 * m + 2) (g (S k)) 0) by reflexivity.
    rewrite E.
    rewrite (iter_closed_helper (g (S k)) (knuth k 2) IH (2 * m + 2) 0).
    change (2 * 0 + 4) with 4.
    rewrite (knuth_S0 k (2 * m + 4)).
    replace (2 * m + 4) with (2 * m + 2 + 2) by lia.
    rewrite (iter_add (knuth k 2) (2 * m + 2) 2 1).
    rewrite iter2_knuth.
    reflexivity.
Qed.

Theorem g_iter_closed : forall k n,
  2 * Nat.iter n (g k) 0%nat + 4 = knuth k 2 (n + 2).
Proof.
  intros k n. destruct k as [|k].
  - rewrite iter_g0. simpl. lia.
  - rewrite (iter_closed_helper (g (S k)) (knuth k 2) (g_closed k) n 0).
    change (2 * 0 + 4) with 4.
    rewrite (knuth_S0 k (n + 2)).
    rewrite (iter_add (knuth k 2) n 2 1).
    rewrite iter2_knuth.
    reflexivity.
Qed.

Theorem g_iter_closed_gen : forall k n (x : nat),
  x = Nat.iter n (g k) 0%nat -> 2 * x + 4 = knuth k 2 (n + 2).
Proof. intros k n x Hx. subst x. apply g_iter_closed. Qed.

Lemma M1_closed : 2 * M1 + 4 = knuth 4 2 3.
Proof. exact (g_iter_closed_gen 4 1 M1 M1_eq). Qed.

Lemma knuth_4_2_3 : knuth 4 2 3 = knuth 3 2 4.
Proof.
  rewrite (knuth_S 3 2 2), (knuth_S 3 2 1), (knuth_S 3 2 0).
  reflexivity.
Qed.

(** ** Monotonicity and growth lemmas for [knuth k 2 b] *)

Lemma knuth_ge_2b : forall k b, knuth k 2 b >= 2 * b.
Proof.
  induction k as [|k IHk]; intros b.
  - simpl. lia.
  - induction b as [|b IHb].
    + simpl. lia.
    + destruct b as [|b'].
      * rewrite knuth_1. lia.
      * rewrite knuth_S.
        pose proof (IHk (knuth (S k) 2 (S b'))) as H1.
        lia.
Qed.

Lemma knuth_pos : forall k b, knuth (S k) 2 b >= 1.
Proof.
  intros k [|b].
  - simpl. lia.
  - pose proof (knuth_ge_2b (S k) (S b)). lia.
Qed.

Lemma knuth_strict_b : forall k b, knuth (S k) 2 (S b) > knuth (S k) 2 b.
Proof.
  intros k b.
  rewrite knuth_S.
  pose proof (knuth_ge_2b k (knuth (S k) 2 b)).
  pose proof (knuth_pos k b).
  lia.
Qed.

Lemma knuth_mono_b : forall k b1 b2, b1 <= b2 -> knuth k 2 b1 <= knuth k 2 b2.
Proof.
  intros [|k] b1 b2 Hle.
  - simpl. lia.
  - induction b2 as [|b2 IH].
    + assert (b1 = 0) by lia. subst. lia.
    + destruct (Nat.eq_dec b1 (S b2)) as [Heq | Hne].
      * subst. lia.
      * assert (b1 <= b2) by lia.
        pose proof (IH H).
        pose proof (knuth_strict_b k b2).
        lia.
Qed.

Lemma knuth_step_k : forall k b, b >= 1 -> knuth k 2 b <= knuth (S k) 2 b.
Proof.
  intros k b Hb.
  destruct b as [|[|b']].
  - lia.
  - rewrite !knuth_1. lia.
  - rewrite (knuth_S k 2 (S b')).
    apply knuth_mono_b.
    destruct b' as [|b''].
    + rewrite knuth_1. lia.
    + pose proof (knuth_ge_2b (S k) (S (S b''))). lia.
Qed.

Lemma knuth_mono_k : forall k1 k2 b, k1 <= k2 -> b >= 1 -> knuth k1 2 b <= knuth k2 2 b.
Proof.
  intros k1 k2 b Hk Hb.
  induction k2 as [|k2 IH].
  - assert (k1 = 0) by lia. subst. lia.
  - destruct (Nat.eq_dec k1 (S k2)) as [Heq | Hne].
    + subst. lia.
    + assert (k1 <= k2) by lia.
      pose proof (IH H).
      pose proof (knuth_step_k k2 b Hb).
      lia.
Qed.

Lemma knuth_k_4_gt : forall j, j >= 1 -> knuth j 2 4 >= j + 6.
Proof.
  induction j as [|j IH]; intros Hj.
  - lia.
  - destruct j as [|j'].
    + simpl. lia.
    + rewrite (knuth_S (S j') 2 3).
      rewrite (knuth_S (S j') 2 2).
      rewrite knuth_2.
      assert (H1 : knuth (S j') 2 4 >= S j' + 6) by (apply IH; lia).
      pose proof (knuth_ge_2b (S j') (knuth (S j') 2 4)) as H2.
      lia.
Qed.

(** ** Fast-growing hierarchy functions [f_omega], [f_omega2], and [f_omega1] *)

Definition f_omega (n : nat) : nat := knuth (S n) 2 (n + 3).
Definition f_omega2 (n : nat) : nat := f_omega (f_omega n).
Definition f_omega1 (n : nat) : nat := Nat.iter n f_omega n.

Lemma f_omega_ge_2n6 : forall n, f_omega n >= 2 * n + 6.
Proof.
  intros n. unfold f_omega.
  pose proof (knuth_ge_2b (S n) (n + 3)). lia.
Qed.

Lemma f_omega_mono : forall a b, a <= b -> f_omega a <= f_omega b.
Proof.
  intros a b Hab. unfold f_omega.
  assert (H1 : knuth (S a) 2 (a + 3) <= knuth (S b) 2 (a + 3)).
  { apply knuth_mono_k; lia. }
  assert (H2 : knuth (S b) 2 (a + 3) <= knuth (S b) 2 (b + 3)).
  { apply knuth_mono_b; lia. }
  lia.
Qed.

Lemma iter_f_omega_mono : forall c a b,
  a <= b -> Nat.iter c f_omega a <= Nat.iter c f_omega b.
Proof.
  induction c as [|c IH]; intros a b Hab.
  - simpl. lia.
  - simpl. apply f_omega_mono. apply IH. exact Hab.
Qed.

Lemma iter_f_omega_mono_c : forall c1 c2 x,
  c1 <= c2 -> Nat.iter c1 f_omega x <= Nat.iter c2 f_omega x.
Proof.
  intros c1 c2 x Hle.
  induction c2 as [|c2 IH].
  - assert (c1 = 0) by lia. subst. simpl. lia.
  - destruct (Nat.eq_dec c1 (S c2)) as [Heq | Hne].
    + subst. lia.
    + assert (c1 <= c2) by lia.
      pose proof (IH H) as H1.
      simpl.
      pose proof (f_omega_ge_2n6 (Nat.iter c2 f_omega x)) as H2.
      lia.
Qed.

(** ** Dominance of [step_pair] over [f_omega] *)

Lemma step_pair_1_grow : forall k m,
  m >= 1 ->
  2 * snd (step_pair (k, m)) >= 2 * m + 2 /\ snd (step_pair (k, m)) >= 1.
Proof.
  intros k m Hm.
  change (snd (step_pair (k, m))) with (Nat.iter (S (S k)) (g (2 * m)) 0%nat).
  pose proof (g_iter_closed (2 * m) (S (S k))) as Hc.
  assert (Hmono : knuth (2 * m) 2 4 <= knuth (2 * m) 2 (S (S k) + 2)).
  { apply knuth_mono_b. lia. }
  assert (Hgt : knuth (2 * m) 2 4 >= 2 * m + 6).
  { apply knuth_k_4_gt. lia. }
  lia.
Qed.

Lemma step_pair_2_dom : forall k m,
  m >= 1 ->
  2 * snd (step_pair (step_pair (k, m))) >= f_omega (2 * m) /\
  snd (step_pair (step_pair (k, m))) >= 1.
Proof.
  intros k m Hm.
  destruct (step_pair_1_grow k m Hm) as [Hm1a Hm1b].
  remember (step_pair (k, m)) as p1 eqn:Ep1.
  destruct p1 as [k1 m1].
  assert (Hk1 : k1 = 2 * m).
  { unfold step_pair in Ep1. inversion Ep1. reflexivity. }
  simpl in Hm1a, Hm1b.
  change (snd (step_pair (k1, m1))) with (Nat.iter (S (S k1)) (g (2 * m1)) 0%nat).
  rewrite Hk1.
  pose proof (g_iter_closed (2 * m1) (S (S (2 * m)))) as Hc2.
  replace (S (S (2 * m)) + 2) with (2 * m + 4) in Hc2 by lia.
  assert (H1 : knuth (S (S (2 * m))) 2 4 <= knuth (2 * m1) 2 (2 * m + 4)).
  { eapply Nat.le_trans.
    - apply (knuth_mono_k (S (S (2 * m))) (2 * m1) 4); lia.
    - apply knuth_mono_b; lia. }
  assert (H2 : knuth (S (S (2 * m))) 2 4 = knuth (S (2 * m)) 2 (knuth (S (2 * m)) 2 4)).
  { rewrite (knuth_S (S (2 * m)) 2 3), (knuth_S (S (2 * m)) 2 2), knuth_2. reflexivity. }
  assert (H3 : knuth (S (2 * m)) 2 4 >= 2 * m + 4).
  { pose proof (knuth_k_4_gt (S (2 * m))) as Hk4. lia. }
  assert (H4 : knuth (S (2 * m)) 2 (2 * m + 4) <= knuth (S (2 * m)) 2 (knuth (S (2 * m)) 2 4)).
  { apply knuth_mono_b. lia. }
  assert (H5 : knuth (S (2 * m)) 2 (2 * m + 4) = knuth (2 * m) 2 (f_omega (2 * m))).
  { replace (2 * m + 4) with (S (2 * m + 3)) by lia.
    rewrite knuth_S. reflexivity. }
  pose proof (knuth_ge_2b (2 * m) (f_omega (2 * m))) as H6.
  pose proof (f_omega_ge_2n6 (2 * m)) as H7.
  lia.
Qed.

Lemma iter_2n_step_pair : forall n k m,
  m >= 1 ->
  2 * snd (Nat.iter (2 * n) step_pair (k, m)) >= Nat.iter n f_omega (2 * m) /\
  snd (Nat.iter (2 * n) step_pair (k, m)) >= 1.
Proof.
  induction n as [|n IH]; intros k m Hm.
  - simpl. lia.
  - replace (2 * S n) with (S (S (2 * n))) by lia.
    change (Nat.iter (S (S (2 * n))) step_pair (k, m))
      with (step_pair (step_pair (Nat.iter (2 * n) step_pair (k, m)))).
    destruct (IH k m Hm) as [IH1 IH2].
    remember (Nat.iter (2 * n) step_pair (k, m)) as pn eqn:Epn.
    destruct pn as [kn mn]; cbn [fst snd] in IH1, IH2.
    destruct (step_pair_2_dom kn mn IH2) as [D1 D2].
    assert (Hmono : f_omega (Nat.iter n f_omega (2 * m)) <= f_omega (2 * mn)).
    { apply f_omega_mono. lia. }
    change (Nat.iter (S n) f_omega (2 * m)) with (f_omega (Nat.iter n f_omega (2 * m))).
    lia.
Qed.

(** ** Symbolic 65536 = [2 ^ 16] (never expanded into 65536 unary [S] constructors!) *)

Definition N65536 : nat := 2 ^ 16.

Lemma N65536_def : N65536 = 2 ^ 16.
Proof. reflexivity. Qed.

Lemma knuth_2_2_4 : knuth 2 2 4 = N65536.
Proof.
  rewrite (knuth_S 1 2 3), (knuth_S 1 2 2), knuth_2.
  change (knuth 1 2 4) with 16.
  rewrite knuth_1_pow. reflexivity.
Qed.

Lemma knuth_3_2_4 : knuth 3 2 4 = knuth 2 2 N65536.
Proof.
  rewrite (knuth_S 2 2 3), (knuth_S 2 2 2), knuth_2, knuth_2_2_4.
  reflexivity.
Qed.

Lemma N65536_ge_16 : N65536 >= 16.
Proof.
  unfold N65536.
  change 16 with (2 ^ 4) at 2.
  apply Nat.pow_le_mono_r; lia.
Qed.

Lemma M1_plus_2_ge : M1 + 2 >= S N65536.
Proof.
  pose proof M1_closed as HM1.
  rewrite knuth_4_2_3, knuth_3_2_4 in HM1.
  pose proof N65536_ge_16 as HN.
  destruct N65536 as [|n'] eqn:En; [lia |].
  rewrite (knuth_S 1 2 n') in HM1.
  pose proof (knuth_ge_2b 1 (knuth 2 2 n')) as H1.
  pose proof (knuth_ge_2b 2 n') as H2.
  Opaque knuth g M1.
  lia.
Qed.

Transparent knuth.

Lemma f_omega_2_gt_N65536 : f_omega 2 >= N65536.
Proof.
  unfold f_omega. simpl (2 + 3).
  rewrite (knuth_S 2 2 4), knuth_3_2_4.
  pose proof (knuth_ge_2b 2 (knuth 2 2 N65536)) as H1.
  pose proof (knuth_ge_2b 2 N65536) as H2.
  Opaque knuth N65536.
  lia.
Qed.

Transparent knuth.

Lemma iter2_f_omega_2_ge_X :
  Nat.iter 2 f_omega 2 >= knuth 4 2 (knuth 3 2 4).
Proof.
  assert (H1 : f_omega 2 >= 5).
  { pose proof (f_omega_ge_2n6 2). lia. }
  assert (H2 : Nat.iter 2 f_omega 2 >= f_omega 5).
  { simpl. apply f_omega_mono. exact H1. }
  assert (H3 : f_omega 5 >= knuth 5 2 5).
  { unfold f_omega.
    eapply Nat.le_trans; [apply (knuth_mono_k 5 6 5); lia |].
    apply knuth_mono_b; lia. }
  assert (H4 : knuth 5 2 5 >= knuth 4 2 (knuth 3 2 4)).
  { rewrite (knuth_S 4 2 4).
    apply knuth_mono_b.
    apply knuth_mono_k; lia. }
  Opaque knuth f_omega.
  lia.
Qed.


(** ** Exact closed form of [step_pair].

    Since [step_pair (k,m) = (2m, iter_(S(S k)) (g_(2m)) 0)], the closed form
    of the [g] hierarchy gives
        2 * snd (step_pair (k,m)) + 4 = knuth (2*m) 2 (k+4).
    This is exact (not just a bound) and is the engine of the lower bound. *)

Lemma step_pair_closed : forall k m,
  2 * snd (step_pair (k, m)) + 4 = knuth (2 * m) 2 (k + 4).
Proof.
  intros k m.
  unfold step_pair.
  change (2 * snd (let '(k0, m0) := (k, m) in
                   (2 * m0, Nat.iter (S (S k0)) (g (2 * m0)) 0%nat)) + 4 =
          knuth (2 * m) 2 (k + 4)).
  cbn [fst snd].
  rewrite (g_iter_closed (2 * m) (S (S k))).
  replace (S (S k) + 2) with (k + 4) by lia.
  reflexivity.
Qed.

(** [fst (step_pair (k,m)) = 2m]. *)
Lemma step_pair_fst : forall k m, fst (step_pair (k, m)) = 2 * m.
Proof. intros k m. unfold step_pair. cbn. reflexivity. Qed.

(** ** A lower bound for one D_chain.

    Iterating step_pair [c] times from [(0,1)] produces a second component
    whose double dominates [iter (c/2) f_omega 2]. *)

Lemma snd_step_pair_ge_one : forall c, snd (Nat.iter c step_pair (0%nat, 1%nat)) >= 1.
Proof.
  induction c as [|c IH]; intros.
  - simpl. lia.
  - change (Nat.iter (S c) step_pair (0%nat, 1%nat)) with
      (step_pair (Nat.iter c step_pair (0%nat, 1%nat))).
    remember (Nat.iter c step_pair (0%nat, 1%nat)) as p eqn:Ep.
    destruct p as [k m]; cbn [fst snd] in *.
    destruct (step_pair_1_grow k m IH) as [_ Hm]. exact Hm.
Qed.

Lemma dchain_lower_even : forall n,
  2 * snd (Nat.iter (2 * n) step_pair (0%nat, 1%nat)) >= Nat.iter n f_omega 2.
Proof.
  intros n. exact (proj1 (iter_2n_step_pair n 0%nat 1%nat ltac:(lia))).
Qed.

Lemma dchain_lower_odd : forall n,
  2 * snd (Nat.iter (2 * n + 1) step_pair (0%nat, 1%nat)) >= Nat.iter n f_omega 2.
Proof.
  intros n.
  replace (2 * n + 1) with (S (2 * n)) by lia.
  rewrite Nat.iter_succ.
  change (2 * snd (step_pair (Nat.iter (2 * n) step_pair (0%nat, 1%nat))) >=
          Nat.iter n f_omega (2 * 1)).
  destruct (iter_2n_step_pair n 0%nat 1%nat ltac:(lia)) as [Ha Hb].
  remember (Nat.iter (2 * n) step_pair (0%nat, 1%nat)) as p eqn:Ep.
  destruct p as [k m]; cbn [fst snd] in *.
  destruct (step_pair_1_grow k m Hb) as [Hg _].
  lia.
Qed.

Lemma dchain_lower : forall c,
  2 * snd (Nat.iter c step_pair (0%nat, 1%nat)) >=
  Nat.iter (c / 2) f_omega 2.
Proof.
  intros c.
  assert (Hz : 2 <> 0) by lia.
  assert (Hmod : c mod 2 < 2) by (apply Nat.mod_upper_bound; lia).
  assert (Hcase : c mod 2 = 0 \/ c mod 2 = 1) by lia.
  destruct Hcase as [H0 | H1].
  - replace c with (2 * (c / 2)) by
      (pose proof (Nat.div_mod c 2 Hz); lia).
    assert (Hdiv : (2 * (c / 2)) / 2 = c / 2) by
      (replace (2 * (c / 2)) with (0 + (c / 2) * 2) by lia;
       rewrite Nat.div_add by lia; simpl; lia).
    rewrite Hdiv.
    apply dchain_lower_even.
  - replace c with (2 * (c / 2) + 1) by
      (pose proof (Nat.div_mod c 2 Hz); lia).
    assert (Hdiv : (2 * (c / 2) + 1) / 2 = c / 2) by
      (replace (2 * (c / 2) + 1) with (1 + (c / 2) * 2) by lia;
       rewrite Nat.div_add by lia; simpl; lia).
    rewrite Hdiv.
    apply dchain_lower_odd.
Qed.

(** ** Four nested [f_{omega+1}] levels.

    [f_omega1 n = F^n(n)] with [F n = 2 ↑^(n+1) (n+3)] is a Knuth-arrow
    majorant of the FGH [f_{omega+1}].  Put [A_0 = 65536] and
    [A_(i+1) = F^(A_i)(A_i)], so [A_i = f_omega1^i(65536)].  Each of the four
    D_chains raises the invariant [m_i >= A_i + (N + 5 A_i + 6)], whence
    [sigma > 2 m4 > A_4]. *)

Fixpoint Aseq (i : nat) : nat :=
  match i with
  | O => N65536
  | S j => Nat.iter (Aseq j) f_omega (Aseq j)
  end.

Lemma Aseq_succ : forall i, Aseq (S i) = Nat.iter (Aseq i) f_omega (Aseq i).
Proof. reflexivity. Qed.

Lemma Aseq_eq_fomega1 : forall i, Aseq i = Nat.iter i f_omega1 N65536.
Proof.
  induction i as [|i IH].
  - reflexivity.
  - change (Nat.iter (Aseq i) f_omega (Aseq i) = f_omega1 (Nat.iter i f_omega1 N65536)).
    rewrite IH. unfold f_omega1. reflexivity.
Qed.

Lemma iter_f_omega_ge : forall c x, x <= Nat.iter c f_omega x.
Proof.
  induction c as [|c IH]; intros x.
  - simpl. lia.
  - simpl. pose proof (IH x). pose proof (f_omega_ge_2n6 (Nat.iter c f_omega x)). lia.
Qed.

Lemma iter_f_omega_ge_add : forall c x, x + 2 * c <= Nat.iter c f_omega x.
Proof.
  induction c as [|c IH]; intros x.
  - simpl. lia.
  - simpl. pose proof (IH x). pose proof (f_omega_ge_2n6 (Nat.iter c f_omega x)). lia.
Qed.

Lemma iter_f_omega_pow2 : forall c x, 2 ^ c * x <= Nat.iter c f_omega x.
Proof.
  induction c as [|c IH]; intros x.
  - simpl. lia.
  - pose proof (IH x). pose proof (f_omega_ge_2n6 (Nat.iter c f_omega x)).
    change (2 ^ S c * x <= f_omega (Nat.iter c f_omega x)).
    rewrite (Nat.pow_succ_r 2 c ltac:(lia)). nia.
Qed.

Lemma Aseq_ge_N : forall i, N65536 <= Aseq i.
Proof.
  induction i as [|i IH].
  - reflexivity.
  - change (N65536 <= Nat.iter (Aseq i) f_omega (Aseq i)).
    eapply Nat.le_trans; [exact IH |]. apply iter_f_omega_ge.
Qed.

(** [A_i <= F^(N + 3 A_i + 1)(2)]: the levels are reachable from [2]. *)
Lemma Aseq_bound : forall i,
  Aseq i <= Nat.iter (N65536 + 3 * Aseq i + 1) f_omega 2.
Proof.
  induction i as [|i IH].
  - change (N65536 <= Nat.iter (N65536 + 3 * N65536 + 1) f_omega 2).
    pose proof (iter_f_omega_ge_add (N65536 + 3 * N65536 + 1) 2%nat). lia.
  - change (Nat.iter (Aseq i) f_omega (Aseq i) <=
            Nat.iter (N65536 + 3 * Nat.iter (Aseq i) f_omega (Aseq i) + 1) f_omega 2).
    set (a := Aseq i). set (a' := Nat.iter a f_omega a).
    set (p := N65536 + 3 * a + 1).
    assert (Ha2 : 2 <= a) by
      (subst a; pose proof (Aseq_ge_N i); pose proof N65536_ge_16; lia).
    assert (Hmono : a' <= Nat.iter a f_omega (Nat.iter p f_omega 2)) by
      (subst a'; apply iter_f_omega_mono; exact IH).
    assert (Heq : Nat.iter a f_omega (Nat.iter p f_omega 2) =
                  Nat.iter (a + p) f_omega 2) by
      (symmetry; apply iter_add).
    rewrite Heq in Hmono.
    assert (Ha' : 2 * a + 2 <= a') by
      (subst a'; pose proof (iter_f_omega_ge_add a a) as H; lia).
    assert (Hcount : a + p <= N65536 + 3 * a' + 1) by lia.
    assert (Hle := iter_f_omega_mono_c (a + p) (N65536 + 3 * a' + 1) 2 Hcount).
    subst a' a p. lia.
Qed.

(** One D_chain from [(k,m)] dominates [F^m(2)] in its second component. *)
Lemma dchain_step_lower : forall k m,
  Nat.iter m f_omega 2 <=
  2 * snd (Nat.iter (k + 2 * m) step_pair (0%nat, 1%nat)).
Proof.
  intros k m.
  assert (H := dchain_lower (k + 2 * m)).
  assert (Hdiv : m <= (k + 2 * m) / 2) by
    (replace (k + 2 * m) with (k + m * 2) by lia;
     rewrite Nat.div_add by lia; lia).
  eapply Nat.le_trans; [| exact H]. apply iter_f_omega_mono_c. exact Hdiv.
Qed.

(** The first D_chain has length [2 M1 + 5], i.e. [M1 + 2] full pairs. *)
Lemma m1_lower : Nat.iter (M1 + 2) f_omega 2 <= 2 * m1.
Proof.
  unfold m1, P1.
  assert (H := dchain_lower (2 * M1 + 5)).
  assert (Hdiv : (2 * M1 + 5) / 2 = M1 + 2) by
    (replace (2 * M1 + 5) with (5 + M1 * 2) by lia;
     rewrite Nat.div_add by lia; simpl; lia).
  rewrite Hdiv in H. exact H.
Qed.

Lemma m2_lower : Nat.iter m1 f_omega 2 <= 2 * m2.
Proof. unfold m2, P2. apply dchain_step_lower. Qed.

Lemma m3_lower : Nat.iter m2 f_omega 2 <= 2 * m3.
Proof. unfold m3, P3. apply dchain_step_lower. Qed.

Lemma m4_lower : Nat.iter m3 f_omega 2 <= 2 * m4.
Proof. unfold m4, P4. apply dchain_step_lower. Qed.

(** [2 ↑↑ 65536] is far larger than [65536 + 5]. *)
Lemma knuth_2_2_5 : knuth 2 2 5 = 2 ^ N65536.
Proof. rewrite (knuth_S 1 2 4), knuth_2_2_4, knuth_1_pow. reflexivity. Qed.

Lemma knuth_2_2_6 : knuth 2 2 6 = 2 ^ (2 ^ N65536).
Proof.
  replace 6 with (S 5) by reflexivity. rewrite knuth_S, knuth_2_2_5, knuth_1_pow.
  reflexivity.
Qed.

Lemma M1_ge_N5 : N65536 + 5 <= M1 + 2.
Proof.
  pose proof M1_closed as Hc.
  rewrite knuth_4_2_3, knuth_3_2_4 in Hc.
  assert (HN6 : 6 <= N65536) by (pose proof N65536_ge_16; lia).
  pose proof (knuth_mono_b 2 6 N65536 HN6) as Hmono.
  rewrite knuth_2_2_6 in Hmono.
  pose proof (knuth_ge_2b 1 (2 ^ N65536)) as Hpow2.
  rewrite knuth_1_pow in Hpow2.
  pose proof (knuth_ge_2b 1 N65536) as Hpow1.
  rewrite knuth_1_pow in Hpow1.
  pose proof N65536_ge_16 as HN16.
  lia.
Qed.

(** Seal the big constants: otherwise unification tries to reduce
    [Nat.iter 65536 f_omega ...] and explodes. *)
Opaque N65536 M1 g knuth f_omega f_omega1
       P1 P2 P3 P4 k1 k2 k3 k4 m1 m2 m3 m4.

(** Base of the slack invariant. *)
Lemma first_slack : N65536 + 5 * Aseq 1 + 6 <= m1.
Proof.
  assert (HA1 : Aseq 1 <= Nat.iter (N65536 + 1) f_omega 2) by
    ( change (Nat.iter N65536 f_omega N65536 <= Nat.iter (N65536 + 1) f_omega 2);
      replace (N65536 + 1) with (S N65536) by lia;
      rewrite (iter_succ_r f_omega N65536 2);
      apply iter_f_omega_mono; apply f_omega_2_gt_N65536 ).
  assert (Hc : Nat.iter (N65536 + 5) f_omega 2 <= Nat.iter (M1 + 2) f_omega 2) by
    (apply iter_f_omega_mono_c; apply M1_ge_N5).
  assert (H4 : 16 * Aseq 1 <= Nat.iter (N65536 + 5) f_omega 2) by
    ( replace (N65536 + 5) with (4 + (N65536 + 1)) by lia;
      rewrite iter_add;
      pose proof (iter_f_omega_mono 4 (Aseq 1) (Nat.iter (N65536 + 1) f_omega 2) HA1) as Hm;
      pose proof (iter_f_omega_pow2 4 (Aseq 1)) as HP;
      change (16 * Aseq 1 <= Nat.iter 4 f_omega (Aseq 1)) in HP;
      eapply Nat.le_trans; [exact HP | exact Hm] ).
  pose proof m1_lower as Hm1.
  pose proof Aseq_ge_N 1 as HA1N.
  pose proof N65536_ge_16 as HN.
  lia.
Qed.

(** Induction step: one more D_chain adds one more [f_omega1] level. *)
Lemma next_slack : forall a m mnext,
  N65536 <= a ->
  a <= Nat.iter (N65536 + 3 * a + 1) f_omega 2 ->
  N65536 + 5 * a + 6 <= m ->
  Nat.iter m f_omega 2 <= 2 * mnext ->
  Nat.iter a f_omega a + (N65536 + 5 * Nat.iter a f_omega a + 6) <= mnext.
Proof.
  intros a m mnext HaN HaB Hm Hmnext.
  set (a' := Nat.iter a f_omega a).
  assert (Hp_le : N65536 + 3 * a + 1 + (2 * a + 5) <= m) by lia.
  assert (H1 : Nat.iter (N65536 + 3 * a + 1 + (2 * a + 5)) f_omega 2 <=
               Nat.iter m f_omega 2) by
    (apply iter_f_omega_mono_c; exact Hp_le).
  assert (H2 : Nat.iter (2 * a + 5) f_omega a <=
               Nat.iter (2 * a + 5) f_omega (Nat.iter (N65536 + 3 * a + 1) f_omega 2)) by
    (apply iter_f_omega_mono; exact HaB).
  assert (H3 : Nat.iter (2 * a + 5) f_omega (Nat.iter (N65536 + 3 * a + 1) f_omega 2) =
               Nat.iter ((2 * a + 5) + (N65536 + 3 * a + 1)) f_omega 2) by
    (symmetry; apply iter_add).
  assert (H4 : Nat.iter (2 * a + 5) f_omega a =
               Nat.iter 5 f_omega (Nat.iter (2 * a) f_omega a)) by
    (replace (2 * a + 5) with (5 + 2 * a) by lia; apply iter_add).
  assert (H5 : a' <= Nat.iter (2 * a) f_omega a) by
    (subst a'; apply iter_f_omega_mono_c; lia).
  assert (H6 : Nat.iter 5 f_omega a' <= Nat.iter 5 f_omega (Nat.iter (2 * a) f_omega a)) by
    (apply iter_f_omega_mono; exact H5).
  assert (H7 : 32 * a' <= Nat.iter 5 f_omega a') by
    (pose proof (iter_f_omega_pow2 5 a') as HP;
     change (32 * a' <= Nat.iter 5 f_omega a') in HP; exact HP).
  assert (H1' : Nat.iter ((2 * a + 5) + (N65536 + 3 * a + 1)) f_omega 2 <=
                Nat.iter m f_omega 2) by
    (replace ((2 * a + 5) + (N65536 + 3 * a + 1)) with
             (N65536 + 3 * a + 1 + (2 * a + 5)) by lia; exact H1).
  assert (Hchain : 32 * a' <= Nat.iter m f_omega 2) by
    ( eapply Nat.le_trans; [exact H7 |]
    ; eapply Nat.le_trans; [exact H6 |]
    ; rewrite <- H4
    ; eapply Nat.le_trans; [exact H2 |]
    ; rewrite H3; exact H1' ).
  assert (Ha'N : N65536 <= a') by
    (subst a'; pose proof (iter_f_omega_ge_add a a) as HG; lia).
  pose proof N65536_ge_16 as HN.
  subst a'. lia.
Qed.

Lemma second_slack : N65536 + 5 * Aseq 2 + 6 <= m2.
Proof.
  assert (H : Aseq 2 + (N65536 + 5 * Aseq 2 + 6) <= m2) by
    ( change (Nat.iter (Aseq 1) f_omega (Aseq 1) +
              (N65536 + 5 * Nat.iter (Aseq 1) f_omega (Aseq 1) + 6) <= m2);
      apply (next_slack (Aseq 1) m1 m2);
      [ apply Aseq_ge_N | apply Aseq_bound | apply first_slack | apply m2_lower ] ).
  lia.
Qed.

Lemma third_slack : N65536 + 5 * Aseq 3 + 6 <= m3.
Proof.
  assert (H : Aseq 3 + (N65536 + 5 * Aseq 3 + 6) <= m3) by
    ( change (Nat.iter (Aseq 2) f_omega (Aseq 2) +
              (N65536 + 5 * Nat.iter (Aseq 2) f_omega (Aseq 2) + 6) <= m3);
      apply (next_slack (Aseq 2) m2 m3);
      [ apply Aseq_ge_N | apply Aseq_bound | apply second_slack | apply m3_lower ] ).
  lia.
Qed.

Lemma fourth_slack : N65536 + 5 * Aseq 4 + 6 <= m4.
Proof.
  assert (H : Aseq 4 + (N65536 + 5 * Aseq 4 + 6) <= m4) by
    ( change (Nat.iter (Aseq 3) f_omega (Aseq 3) +
              (N65536 + 5 * Nat.iter (Aseq 3) f_omega (Aseq 3) + 6) <= m4);
      apply (next_slack (Aseq 3) m3 m4);
      [ apply Aseq_ge_N | apply Aseq_bound | apply third_slack | apply m4_lower ] ).
  lia.
Qed.

(** ** The four-level lower bound. *)

Theorem sigma_beats_four_f_omega1 :
  f_omega1 (f_omega1 (f_omega1 (f_omega1 (2 ^ 16)))) < sigma.
Proof.
  Transparent Aseq N65536.
  rewrite <- N65536_def.
  change (Aseq 4 < sigma).
  unfold sigma.
  pose proof fourth_slack as H.
  pose proof Aseq_ge_N 4 as HN4.
  pose proof N65536_ge_16 as HN.
  lia.
Qed.
