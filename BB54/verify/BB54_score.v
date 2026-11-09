(** * Score of the BB(5,4) champion 1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ

    Main results ([knuth n a b] is [a] with [n] Knuth up-arrows applied to [b],
    so [knuth 2 10 65533] is [10 ↑↑ 65533] and [knuth 4 10 x] is [10 ↑^4 x]):

      bb54_main : the machine reaches the Ligocki configuration
                  B(5, 0, g_4(0)) [3 1] 0^inf from the blank tape, and the
                  tape of that configuration carries
                  sigma = 2 * g_4(0) + 8 = (2 ↑^4 3) + 4 = (2 ↑↑ 65536) + 4
                  nonzero symbols.  This [sigma] is an intermediate count,
                  not the sigma of the machine: that is [sigma_final] of
                  BB54_halt.v, and halting is [bb54_halts] there;
      g_closed  : 2 * g_(k+1)(m) + 4 = knuth k 2 (2m+4)   (closed form of the g hierarchy)
      g_iter_closed : 2 * g_k^n(0) + 4 = knuth k 2 (n + 2)
      f_omega   : f_w n = 2 ↑^(n+1) (n+3)  (an upper bound for F_w(n))
      target    : the number claimed on the wiki, f_w^2 (10 ↑^4 10 ↑↑ 65533).

    No large number is ever evaluated: [knuth 4 2 3], [f_omega] and the sealed
    [g40] stay symbolic throughout.

    What is *not* proved in Coq: any comparison of the machine's sigma
    with the wiki's bound [f_w^2 (10 ↑^4 10 ↑↑ 65533)]; it is a hand
    calculation in ../README.md ("The size of σ"). *)

From TM54 Require Import Individual54 BB54_rules BB54_run.
From Coq Require Import Lia PeanoNat.
From Coq.micromega Require Import ZifyNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(** ** Knuth up-arrows: [knuth n a b = a ↑^n b], with [a ↑^0 b = a * b] *)
Fixpoint knuth (n a b : nat) : nat :=
  match n with
  | 0 => a * b
  | S n' => Nat.iter b (knuth n' a) 1
  end.

Lemma iter_add : forall (f : nat -> nat) a b x,
  Nat.iter (a + b) f x = Nat.iter a f (Nat.iter b f x).
Proof.
  induction a as [|a IH]; intros b x.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma knuth_S : forall n a b, knuth (S n) a (S b) = knuth n a (knuth (S n) a b).
Proof. reflexivity. Qed.

Lemma knuth_S0 : forall k b, knuth (S k) 2 b = Nat.iter b (knuth k 2) 1.
Proof. reflexivity. Qed.

(** The coincidence 2 ↑^k 2 = 4 for all k, on which the closed form rests. *)
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

Lemma knuth_step4 : forall k j, Nat.iter (j + 2) (knuth k 2) 1 = Nat.iter j (knuth k 2) 4.
Proof.
  intros k j. rewrite (iter_add (knuth k 2) j 2 1). rewrite iter2_knuth. reflexivity.
Qed.

(** ** The closed form of the g hierarchy: 2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4) *)

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
  - (* k = 0:  g 1 m = 2m+2 *)
    assert (E : g 1 m = 2 * m + 2).
    { assert (E2 : g 1 m = Nat.iter (2 * m + 2) (g 0) 0%nat) by reflexivity.
      rewrite E2. rewrite (iter_g0 (2 * m + 2) 0%nat). lia. }
    rewrite E. simpl. lia.
  - (* k -> S k *)
    assert (E : g (S (S k)) m = Nat.iter (2 * m + 2) (g (S k)) 0) by reflexivity.
    rewrite E.
    rewrite (iter_closed_helper (g (S k)) (knuth k 2) IH (2 * m + 2) 0).
    change (2 * 0 + 4) with 4.
    rewrite (knuth_S0 k (2 * m + 4)).
    replace (2 * m + 4) with (2 * m + 2 + 2) by lia.
    rewrite (iter_add (knuth k 2) (2 * m + 2) 2 1).
    rewrite iter2_knuth.
    reflexivity.
Qed.

(** Corollary (Ligocki): 2 g_k^n(0) + 4 = 2 ↑^k (n + 2) *)
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

(** The same statement with the number abstracted.  This is the bridge used to
    instantiate the closed form with the sealed [g40] of BB54_run.v without
    ever evaluating it. *)
Theorem g_iter_closed_gen : forall k n (x : nat),
  x = Nat.iter n (g k) 0%nat -> 2 * x + 4 = knuth k 2 (n + 2).
Proof. intros k n x Hx. subst x. apply g_iter_closed. Qed.

(** [g40 = g_4(0)] satisfies the closed form with k = 4, n = 1:
    [2 * g40 + 4 = 2 ↑^4 3 = 2 ↑^3 4 = 2 ↑↑ 65536]. *)
Lemma g40_closed : 2 * g40 + 4 = knuth 4 2 3.
Proof. exact (g_iter_closed_gen 4 1 g40 g40_eq). Qed.

(** ** The exact cell count of the intermediate configuration [c_score]:
    [sigma = (2 ↑^3 4) + 4 = (2 ↑↑ 65536) + 4]. *)
Theorem sigma_eq : sigma = knuth 4 2 3 + 4.
Proof.
  unfold sigma.
  assert (H : 2 * g40 + 4 = knuth 4 2 3) by exact g40_closed.
  lia.
Qed.

(** ** The fast-growing function at [omega], and the number claimed on the
    wiki's Champions page.

    [f_omega n = 2 ↑^(n+1) (n+3)] is a Knuth-arrow function, not the
    fast-growing hierarchy's f_w; it is an upper bound for the
    hierarchy [F_{k+1}(n) = F_k^{n+3}(n)], [F_w(n) = F_n(n)].

    The wiki claims for the BB(5,4) champion a runtime larger than
    [f_w^2 (10 ↑^4 10 ↑↑ 65533)]; [target] is that number. *)
Definition f_omega (n : nat) : nat := knuth (S n) 2 (n + 3).

Definition f_omega2 (n : nat) : nat := f_omega (f_omega n).

(** [10 ↑↑ 65533] and [10 ↑^4 (10 ↑↑ 65533)]. *)
Definition tower65533 : nat := knuth 2 10 65533.
Definition target : nat := f_omega2 (knuth 4 10 tower65533).

(** The score that the run of BB54_run.v certifies. *)
Theorem bb54_main :
  c0 -->* c_score /\
  length score_cells = sigma /\
  sigma = knuth 4 2 3 + 4.
Proof.
  split; [exact reaches_score |]. split; [exact score_cells_count |].
  exact sigma_eq.
Qed.

(** The level-4 descent of the run has the closed form [2 ↑^3 4]. *)
Theorem sigma_level_4 : 2 * g40 + 4 = knuth 4 2 3.
Proof. exact g40_closed. Qed.
