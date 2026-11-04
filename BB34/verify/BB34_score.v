(** * Score of the BB(3,4) champion 1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC *)

(** Main results ([knuth 15 2 5] is 2 with 15 Knuth up-arrows applied to 5):
      bb34_main : the machine halts from the blank tape, with the exact halting
                  configuration (A reading the 2 after 3^(2 g15 + 1) 2^16), and
                  sigma = 2 * g15 + 18.
      g_closed  : 2 * g_(k+1)(m) + 4 = knuth k 2 (2m+4)   (closed form of the g hierarchy)
      sigma_eq  : sigma = knuth 15 2 5 + 14 = (2 ↑^15 5) + 14.
    No large number is ever evaluated: [knuth 15 2 5] and the sealed [g15]
    stay symbolic throughout. *)

From TM34 Require Import Individual34 BB34_rules BB34_run.
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
    instantiate the closed form with the sealed [g15] of BB34_run.v without
    ever evaluating it. *)
Theorem g_iter_closed_gen : forall k n (x : nat),
  x = Nat.iter n (g k) 0%nat -> 2 * x + 4 = knuth k 2 (n + 2).
Proof. intros k n x Hx. subst x. apply g_iter_closed. Qed.

(** [g15 = g_15^3(0)] satisfies the closed form with k = 15, n = 3:
    2 * g15 + 4 = 2 ↑^15 5. *)
Lemma g15_closed : 2 * g15 + 4 = knuth 15 2 5.
Proof. exact (g_iter_closed_gen 15 3 g15 g15_eq). Qed.

(** A generic score lemma: if the "3"-block of the final tape is [2x+1], the
    final tape has [2x+18] nonzero symbols, i.e. [K+14] when [2x+4 = K]. *)
Lemma score_generic : forall (x K : nat),
  2 * x + 4 = K -> 2 * x + 18 = K + 14.
Proof. intros x K H. lia. Qed.

(** ** The exact score: sigma = (2 ↑^15 5) + 14 *)
Theorem sigma_eq : sigma = knuth 15 2 5 + 14.
Proof.
  unfold sigma.
  apply (score_generic g15 (knuth 15 2 5)).
  exact g15_closed.
Qed.

(** ** Main theorem: halting, the exact final tape, and the exact score *)
Theorem bb34_main :
  halts tm c0 /\
  c0 -[ tm ]->* c_final /\
  halted tm c_final /\
  sigma = knuth 15 2 5 + 14.
Proof.
  split; [exact bb34_halts |]. split; [exact reaches_final |].
  split; [exact final_halted | exact sigma_eq].
Qed.

(** The same computation at any level k: the machine started from
    [Bcfg (S k) 3 0 (2 >> const 0)] halts with [2 * Nat.iter 3 (g k) 0 + k + 2]
    nonzero symbols.  At k = 15 this is exactly sigma. *)
Theorem sigma_general : forall k,
  2 * Nat.iter 3 (g k) 0%nat + 4 = knuth k 2 5.
Proof.
  intros k. apply g_iter_closed.
Qed.
