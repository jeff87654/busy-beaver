(** * FGH_BB34: the BB(3,4) champion's score in the standard fast-growing hierarchy.

    Published files (busy-beaver BB34/verify at 1e7ead5, logical root TM34, unchanged): BB34, Individual34, BB34_rules,
    BB34_start, BB34_run, BB34_score.  BB34_score.sigma_eq : sigma = knuth 15 2 5 + 14  (sigma = 2 ^15 5 + 14).
    Standard FGH: published Ord.v (fin_fgh k = f_k, FGH (ofin k) = f_k by FGH_fin); KnuthFGH.v (new library).

      bb34_fgh : FGH (ofin 16) 2 < sigma /\ sigma < FGH (ofin 16) 3
    i.e.  f_16(2) < sigma < f_16(3).  Proved for an abstract level (Lemmas f2_le, f3_gt, f3_gt5) and instantiated. *)

From BB8 Require Import Ord KnuthFGH.
From TM34 Require BB34_run BB34_score.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".

Lemma iter_ext_nat : forall (f h : nat -> nat) n x, (forall y, f y = h y) -> Nat.iter n f x = Nat.iter n h x.
Proof. intros f h n x H. induction n as [|n IH]; [reflexivity|]. rewrite !Nat.iter_succ, IH. apply H. Qed.

Lemma knuth_same : forall n a b, TM34.BB34_score.knuth n a b = kn n a b.
Proof.
  induction n as [|n IH]; intros a b; [reflexivity|].
  change (TM34.BB34_score.knuth (S n) a b) with (Nat.iter b (TM34.BB34_score.knuth n a) 1).
  change (kn (S n) a b) with (Nat.iter b (kn n a) 1).
  apply iter_ext_nat. intro y. apply IH.
Qed.

(** f_(n+2)(2) <= 2 ^(n+1) 5 *)
Lemma f2_le : forall n, 1 <= n -> fin_fgh (S (S n)) 2 <= kn (S n) 2 5.
Proof.
  intros n Hn.
  change (fin_fgh (S (S n)) 2) with (fin_fgh (S n) (fin_fgh (S n) 2)).
  assert (Y4 : 4 <= fin_fgh (S n) 2) by (pose proof (fin_lower n 2 ltac:(lia)); rewrite kn_2 in *; lia).
  assert (Y12 : fin_fgh (S n) 2 <= kn n 2 12)
    by (apply Nat.le_trans with (m := fin_fgh (S n) 4); [apply fin_mono; lia | apply fin_upper; lia]).
  eapply Nat.le_trans; [apply fin_upper; [exact Hn | exact Y4]|].
  rewrite (kn_S n 2 4), k4.
  apply mono_b.
  assert (H16 : 16 <= kn n 2 4).
  { pose proof (mono_k 1 n 4 Hn ltac:(lia)) as H. change (kn 1 2 4) with 16 in H. lia. }
  pose proof (quad n 12 Hn) as Q. replace (12 + 2) with 14 in Q by reflexivity.
  pose proof (mono_b n 14 (kn n 2 4) ltac:(lia)). lia.
Qed.

(** 2 ^(n+1) 4 < f_(n+2)(3) *)
Lemma f3_gt : forall n, 1 <= n -> kn (S n) 2 4 < fin_fgh (S (S n)) 3.
Proof.
  intros n Hn. destruct n as [|n']; [lia|].
  change (fin_fgh (S (S (S n'))) 3)
    with (fin_fgh (S (S n')) (fin_fgh (S (S n')) (fin_fgh (S (S n')) 3))).
  rewrite k4.
  assert (A1 : kn (S n') 2 3 <= fin_fgh (S (S n')) 3) by (apply fin_lower; lia).
  assert (A3 : kn (S n') 2 3 >= 6) by (rewrite k3; pose proof (k4_gt n'); lia).
  assert (B1 : kn (S n') 2 5 <= kn (S n') 2 (fin_fgh (S (S n')) 3)) by (apply mono_b; lia).
  pose proof (fin_lower (S n') (fin_fgh (S (S n')) 3) ltac:(lia)) as B2.
  pose proof (strict_b n' 4) as S1.
  assert (C1 : kn (S n') 2 (S (kn (S n') 2 4)) <= kn (S n') 2 (fin_fgh (S (S n')) (fin_fgh (S (S n')) 3)))
    by (apply mono_b; lia).
  pose proof (strict_b n' (kn (S n') 2 4)) as S2.
  pose proof (fin_ge (S (S n')) (fin_fgh (S (S n')) 3)) as G1.
  pose proof (fin_lower (S n') (fin_fgh (S (S n')) (fin_fgh (S (S n')) 3)) ltac:(lia)) as C2.
  lia.
Qed.

(** 2 ^(n+2) 5 + 14 < f_(n+3)(3) *)
Lemma f3_gt5 : forall n, 1 <= n -> kn (S (S n)) 2 5 + 14 < fin_fgh (S (S (S n))) 3.
Proof.
  intros n Hn.
  change (fin_fgh (S (S (S n))) 3)
    with (fin_fgh (S (S n)) (fin_fgh (S (S n)) (fin_fgh (S (S n)) 3))).
  rewrite (kn_S (S n) 2 4), k4.
  pose proof (f3_gt n Hn) as H0.
  pose proof (fin_ge (S (S n)) 3) as Hz3.
  assert (B1 : kn (S n) 2 (S (kn (S n) 2 4)) <= kn (S n) 2 (fin_fgh (S (S n)) 3)) by (apply mono_b; lia).
  pose proof (strict_b n (kn (S n) 2 4)) as S1.
  pose proof (fin_lower (S n) (fin_fgh (S (S n)) 3) ltac:(lia)) as B2.
  assert (C1 : kn (S n) 2 (S (kn (S n) 2 (kn (S n) 2 4)))
               <= kn (S n) 2 (fin_fgh (S (S n)) (fin_fgh (S (S n)) 3))) by (apply mono_b; lia).
  pose proof (dbl (S n) (kn (S n) 2 (kn (S n) 2 4)) ltac:(lia)) as D1.
  pose proof (fin_ge (S (S n)) (fin_fgh (S (S n)) 3)) as Hzz.
  pose proof (fin_lower (S n) (fin_fgh (S (S n)) (fin_fgh (S (S n)) 3)) ltac:(lia)) as C2.
  pose proof (k4_gt (S n)) as K1.
  pose proof (ge_2b (S n) (kn (S n) 2 4)) as K2.
  pose proof (ge_2b (S n) (kn (S n) 2 (kn (S n) 2 4))) as K3.
  lia.
Qed.

Theorem bb34_fgh : FGH (ofin 16) 2 < TM34.BB34_run.sigma /\ TM34.BB34_run.sigma < FGH (ofin 16) 3.
Proof.
  rewrite !FGH_fin, TM34.BB34_score.sigma_eq, (knuth_same 15 2 5).
  split.
  - pose proof (f2_le 14 ltac:(lia)). lia.
  - exact (f3_gt5 13 ltac:(lia)).
Qed.

Print Assumptions bb34_fgh.
