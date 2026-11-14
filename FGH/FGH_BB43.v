(** * FGH_BB43: the BB(4,3) champion's score in the standard fast-growing hierarchy.

    Published files (busy-beaver BB43/verify, logical root TM43, unchanged): BB43, Individual43, BB43_rules, BB43_run,
    BB43_score.  BB43_score.sigma_bounds :
       4 * P (P (P (2^96 - 1))) + 18 < sigma <= 4 * P (P (P (2^96 + 6))) + 18,   P = 2 ^^^ = knuth 3 2,
    for the exact score sigma = 4 e4 + 18 (BB43_run.sigma).  Standard FGH: published Ord.v; KnuthFGH.v (new).

      bb43_fgh : f_4^3(2^94) < sigma < f_4^3(2^96 + 6)       (f_4 = FGH (ofin 4), iterated three times)

    Lemmas lower43 / upper43 are proved for variables (f_4(x) <= 2 ^^^ (3x) and 2 ^^^ (x+2) <= f_4(x), x >= 4). *)

From BB8 Require Import Ord KnuthFGH.
From TM43 Require BB43_run BB43_score.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".

Lemma iter_ext_nat : forall (f h : nat -> nat) n x, (forall y, f y = h y) -> Nat.iter n f x = Nat.iter n h x.
Proof. intros f h n x H. induction n as [|n IH]; [reflexivity|]. rewrite !Nat.iter_succ, IH. apply H. Qed.

Lemma knuth_same : forall n a b, TM43.BB43_score.knuth n a b = kn n a b.
Proof.
  induction n as [|n IH]; intros a b; [reflexivity|].
  change (TM43.BB43_score.knuth (S n) a b) with (Nat.iter b (TM43.BB43_score.knuth n a) 1).
  change (kn (S n) a b) with (Nat.iter b (kn n a) 1).
  apply iter_ext_nat. intro y. apply IH.
Qed.

Lemma nest_same : forall x, TM43.BB43_score.knuth 3 2 (TM43.BB43_score.knuth 3 2 (TM43.BB43_score.knuth 3 2 x))
  = kn 3 2 (kn 3 2 (kn 3 2 x)).
Proof.
  intros x. rewrite (knuth_same 3 2 x), (knuth_same 3 2 (kn 3 2 x)), (knuth_same 3 2 (kn 3 2 (kn 3 2 x))).
  reflexivity.
Qed.

Lemma lower43 : forall M N, 4 <= M -> 3 * M + 3 <= N ->
  Nat.iter 3 (fin_fgh 4) M <= kn 3 2 (kn 3 2 (kn 3 2 N)).
Proof.
  intros M N HM HN.
  change (Nat.iter 3 (fin_fgh 4) M) with (fin_fgh 4 (fin_fgh 4 (fin_fgh 4 M))).
  pose proof (fin_ge 4 M) as g1.
  pose proof (fin_ge 4 (fin_fgh 4 M)) as g2.
  pose proof (fin_upper 3 M ltac:(lia) HM) as h1.
  pose proof (fin_upper 3 (fin_fgh 4 M) ltac:(lia) ltac:(lia)) as h2.
  pose proof (fin_upper 3 (fin_fgh 4 (fin_fgh 4 M)) ltac:(lia) ltac:(lia)) as h3.
  pose proof (quad 3 (3 * M) ltac:(lia)) as q1.
  assert (m1 : fin_fgh 4 (fin_fgh 4 M) <= kn 3 2 (kn 3 2 (3 * M + 2))).
  { eapply Nat.le_trans; [exact h2|]. apply mono_b. lia. }
  pose proof (quad 3 (kn 3 2 (3 * M + 2)) ltac:(lia)) as q2.
  pose proof (plus1 3 (3 * M + 2) ltac:(lia) ltac:(lia)) as p1.
  replace (S (3 * M + 2)) with (3 * M + 3) in p1 by lia.
  eapply Nat.le_trans; [exact h3|].
  apply mono_b.
  apply Nat.le_trans with (m := kn 3 2 (kn 3 2 (3 * M + 2) + 2)); [lia|].
  apply mono_b.
  apply Nat.le_trans with (m := kn 3 2 (3 * M + 3)); [lia|].
  apply mono_b. lia.
Qed.

Lemma upper43 : forall y, 4 <= y -> 4 * kn 3 2 (kn 3 2 (kn 3 2 y)) + 18 < Nat.iter 3 (fin_fgh 4) y.
Proof.
  intros y Hy.
  change (Nat.iter 3 (fin_fgh 4) y) with (fin_fgh 4 (fin_fgh 4 (fin_fgh 4 y))).
  pose proof (fin_ge 4 y) as g1.
  pose proof (fin_ge 4 (fin_fgh 4 y)) as g2.
  pose proof (fin_lower2 2 y Hy) as l1.
  pose proof (fin_lower2 2 (fin_fgh 4 y) ltac:(lia)) as l2.
  pose proof (fin_lower2 2 (fin_fgh 4 (fin_fgh 4 y)) ltac:(lia)) as l3.
  (* P(y+2) >= P y + 3 *)
  pose proof (quad 3 y ltac:(lia)) as q0. pose proof (kn_pos 2 y) as p0.
  (* inner: f (f y) >= P (P y) + 2 *)
  assert (i1 : kn 3 2 (kn 3 2 y) + 2 <= fin_fgh 4 (fin_fgh 4 y)).
  { pose proof (mono_b 3 (kn 3 2 y + 2) (fin_fgh 4 y + 2) ltac:(lia)) as m1.
    pose proof (quad 3 (kn 3 2 y) ltac:(lia)) as q1. pose proof (kn_pos 2 (kn 3 2 y)). lia. }
  pose proof (mono_b 3 (kn 3 2 (kn 3 2 y) + 4) (fin_fgh 4 (fin_fgh 4 y) + 2) ltac:(lia)) as m2.
  pose proof (quad 3 (kn 3 2 (kn 3 2 y)) ltac:(lia)) as q2.
  pose proof (quad 3 (kn 3 2 (kn 3 2 y) + 2) ltac:(lia)) as q3.
  replace (kn 3 2 (kn 3 2 y) + 2 + 2) with (kn 3 2 (kn 3 2 y) + 4) in q3 by lia.
  pose proof (kn_pos 2 (kn 3 2 y)). pose proof (ge_2b 3 (kn 3 2 (kn 3 2 y))). lia.
Qed.

Lemma pow_rel : forall k, 2 ^ S (S k) = 4 * 2 ^ k.
Proof. intros k. rewrite !Nat.pow_succ_r'. lia. Qed.

Lemma four_le_pow : forall k, 2 <= k -> 4 <= 2 ^ k.
Proof.
  intros k Hk. replace k with (S (S (k - 2))) by lia. rewrite pow_rel.
  pose proof (Nat.pow_nonzero 2 (k - 2) ltac:(lia)). lia.
Qed.

Theorem bb43_fgh :
  Nat.iter 3 (FGH (ofin 4)) (2 ^ 94) < TM43.BB43_run.sigma /\
  TM43.BB43_run.sigma < Nat.iter 3 (FGH (ofin 4)) (2 ^ 96 + 6).
Proof.
  (* side facts first, while the context is clean: lia must never see a hypothesis containing 2 ^ 96 *)
  pose proof (four_le_pow 94 ltac:(lia)) as H4.
  pose proof (pow_rel 94) as E.
  rewrite !(iter_ext_nat (FGH (ofin 4)) (fin_fgh 4) 3) by (intro y; apply FGH_fin).
  destruct TM43.BB43_score.sigma_bounds as [Hl Hu].
  rewrite (nest_same (2 ^ 96 - 1)) in Hl. rewrite (nest_same (2 ^ 96 + 6)) in Hu.
  rewrite E in Hl, Hu |- *. clear E.
  revert Hl Hu H4. generalize (2 ^ 94). intros x Hl Hu H4.
  split.
  - pose proof (lower43 x (4 * x - 1) H4 ltac:(lia)). lia.
  - pose proof (upper43 (4 * x + 6) ltac:(lia)). lia.
Qed.

Print Assumptions bb43_fgh.
