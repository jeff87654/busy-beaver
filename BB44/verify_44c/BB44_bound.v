(** * Exact closed-form score and lower-bound proof for the new BB(4,4) TNF champion:
      1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD

    Main certified theorems (zero axioms):
      1. [sigma_exact_closed_form]:
           sigma = knuth (2 ^ 16 - 4) 2 6 + (2 ^ 16 - 4)
         (i.e. exact sigma = 2 ↑^65532 6 + 65532!)
      2. [sigma_beats_official_bb44]:
           knuth 509 2 3 + 510 < sigma
         (strictly exceeds Loader3229's official BB(4,4) wiki champion 2 ↑^509 3 + 510!) *)

From Local Require Import Individual44 BB44_rules BB44_run.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

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

(** ** Monotonicity of [knuth] *)

Lemma knuth_ge_2b : forall k b, knuth k 2 b >= 2 * b.
Proof.
  induction k as [|k IHk]; intros b.
  - simpl. lia.
  - induction b as [|b IHb].
    + simpl. lia.
    + destruct b as [|b'].
      * rewrite knuth_1. lia.
      * rewrite knuth_S.
        pose proof (IHk (knuth (S k) 2 (S b'))). lia.
Qed.

Lemma knuth_pos : forall k b, knuth (S k) 2 b >= 1.
Proof.
  intros k [|b]; [simpl; lia |].
  pose proof (knuth_ge_2b (S k) (S b)). lia.
Qed.

Lemma knuth_strict_b : forall k b, knuth (S k) 2 (S b) > knuth (S k) 2 b.
Proof.
  intros k b. rewrite knuth_S.
  pose proof (knuth_ge_2b k (knuth (S k) 2 b)).
  pose proof (knuth_pos k b). lia.
Qed.

Lemma knuth_mono_b : forall k b1 b2, b1 <= b2 -> knuth k 2 b1 <= knuth k 2 b2.
Proof.
  intros [|k] b1 b2 Hle; [simpl; lia |].
  induction b2 as [|b2 IH].
  - assert (b1 = 0) by lia. subst. lia.
  - destruct (Nat.eq_dec b1 (S b2)) as [Heq | Hne]; [subst; lia |].
    assert (b1 <= b2) by lia.
    pose proof (IH H). pose proof (knuth_strict_b k b2). lia.
Qed.

Lemma knuth_step_k : forall k b, b >= 1 -> knuth k 2 b <= knuth (S k) 2 b.
Proof.
  intros k [|[|b']] Hb; [lia | rewrite !knuth_1; lia |].
  rewrite (knuth_S k 2 (S b')).
  apply knuth_mono_b.
  destruct b' as [|b'']; [rewrite knuth_1; lia |].
  pose proof (knuth_ge_2b (S k) (S (S b''))). lia.
Qed.

Lemma knuth_mono_k : forall k1 k2 b, k1 <= k2 -> b >= 1 -> knuth k1 2 b <= knuth k2 2 b.
Proof.
  intros k1 k2 b Hk Hb.
  induction k2 as [|k2 IH]; [assert (k1 = 0) by lia; subst; lia |].
  destruct (Nat.eq_dec k1 (S k2)) as [Heq | Hne]; [subst; lia |].
  assert (k1 <= k2) by lia.
  pose proof (IH H). pose proof (knuth_step_k k2 b Hb). lia.
Qed.

(** ** Exact closed-form score: [sigma = 2 ↑^65532 6 + 65532] *)

Definition N65536 : nat := 2 ^ 16.
Lemma N65536_def : N65536 = 2 ^ 16. Proof. reflexivity. Qed.

Lemma g30_closed : 2 * g30 + 4 = N65536.
Proof.
  pose proof (g_iter_closed_gen 3 1 g30 g30_eq) as H.
  change (1 + 2) with 3 in H.
  rewrite (knuth_S 2 2 2), knuth_2 in H.
  rewrite (knuth_S 1 2 3), (knuth_S 1 2 2), knuth_2 in H.
  change (knuth 1 2 4) with 16 in H.
  rewrite knuth_1_pow in H.
  exact H.
Qed.

Lemma N65536_ge_1024 : N65536 >= 1024.
Proof.
  unfold N65536.
  change 1024 with (2 ^ 10).
  apply Nat.pow_le_mono_r; lia.
Qed.

Lemma M44_final_closed : 2 * M44_final + 4 = knuth (2 * g30) 2 6.
Proof.
  exact (g_iter_closed_gen (2 * g30) 4 M44_final M44_final_eq).
Qed.

Opaque g knuth N65536 g30 M44_final.

Lemma two_g30_eq : 2 * g30 = 2 ^ 16 - 4.
Proof.
  rewrite <- N65536_def.
  pose proof g30_closed as H.
  lia.
Qed.

Theorem sigma_exact_closed_form :
  sigma = knuth (2 ^ 16 - 4) 2 6 + (2 ^ 16 - 4).
Proof.
  unfold sigma.
  pose proof M44_final_closed as HM.
  assert (HS : 2 * M44_final + 2 * g30 + 4 = (2 * M44_final + 4) + 2 * g30) by lia.
  rewrite HS, HM, two_g30_eq.
  reflexivity.
Qed.

Theorem sigma_beats_official_bb44 :
  knuth 509 2 3 + 510 < sigma.
Proof.
  unfold sigma.
  pose proof M44_final_closed as HM.
  pose proof g30_closed as HG.
  pose proof N65536_ge_1024 as HN.
  assert (Hg509 : 509 <= 2 * g30) by lia.
  assert (Hk1 : knuth 509 2 3 <= knuth (2 * g30) 2 3).
  { apply knuth_mono_k; lia. }
  assert (Hk2 : knuth (2 * g30) 2 3 <= knuth (2 * g30) 2 6).
  { apply knuth_mono_b; lia. }
  lia.
Qed.

Theorem bb44_new_champion_main :
  halts tm c0 /\
  c0 -[ tm ]->* c_final /\
  halted tm c_final /\
  length final_cells = sigma /\
  (forall y, List.In y final_cells -> y <> S0) /\
  sigma = knuth (2 ^ 16 - 4) 2 6 + (2 ^ 16 - 4) /\
  knuth 509 2 3 + 510 < sigma.
Proof.
  split; [exact bb44_halts |].
  split; [exact reaches_final |].
  split; [exact final_halted |].
  split; [exact final_cells_count |].
  split; [exact final_cells_all_nonblank |].
  split; [exact sigma_exact_closed_form | exact sigma_beats_official_bb44].
Qed.
