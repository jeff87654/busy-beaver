From BB7 Require Import Individual72 C232_rules1 C232_rules2.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Lemma lpow_double : forall {X : Type} (xs : list X) n, xs^^(n + n) = (xs ++ xs)^^n.
Proof.
  induction n; [reflexivity |].
  rewrite Nat.add_succ_r. simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma lpow_twice : forall {X : Type} (xs : list X) n, xs^^(2 * n) = (xs ++ xs)^^n.
Proof. intros. replace (2 * n) with (n + n) by lia. apply lpow_double. Qed.

Lemma alc : forall {X : Type} (x : X) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof.
  intros. rewrite const_unfold at 1. revert xs. induction n; intros; [reflexivity |].
  simpl. rewrite !Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma rgt_zeros : forall k t, rgt (repeat O k ++ t) = [0]^^(2 * k) *> rgt t.
Proof.
  intros. rewrite lpow_twice. induction k; [reflexivity |].
  simpl repeat. simpl app. simpl rgt. rewrite IHk. reflexivity.
Qed.

Lemma rgt_ones : forall k t, rgt (repeat 1%nat k ++ t) = [1;1;0;0]^^k *> rgt t.
Proof.
  induction k; intros; [reflexivity |].
  simpl repeat. simpl app. simpl rgt. rewrite IHk. reflexivity.
Qed.

Lemma zeros3 : forall k (r : side), [0]^^(S (S (2 * k + 1))) *> r = 0 >> 0 >> 0 >> [0]^^(2 * k) *> r.
Proof. intros. replace (2 * k + 1) with (S (2 * k)) by lia. reflexivity. Qed.

(** R2 and R3 in one statement: k zeros (k <= b) then a nonzero digit *)
Lemma R23 : forall k y t b, k <= b ->
  Kc (repeat O k ++ S y :: t) 0 b -->+
  const 0 {{E}}> 0 >> 1 >> 0 >> 0 >> [1;1;0;0]^^k *> [1]^^(2 * (b + 3 - k)) *> 0 >> 0 >> rgt (y :: t).
Proof.
  intros k y t b Hk. unfold Kc. rewrite rgt_zeros.
  change ([1]^^(2 * O) *> 0 >> 0 >> [0]^^(2 * k) *> rgt (S y :: t))
    with (0 >> 0 >> [0]^^(2 * k) *> rgt (S y :: t)).
  eapply progress_evstep_trans; [apply (START (S (2 * b)) (0 >> [0]^^(2 * k) *> rgt (S y :: t))) |].
  replace (3 + S (2 * b)) with ((2 * k + 1) + S (2 * b + 2 - 2 * k)) by lia.
  rewrite <- zeros3.
  follow (FWS (2 * k + 1) (const 0) (2 * b + 2 - 2 * k) (rgt (S y :: t))).
  replace (S (2 * b + 2 - 2 * k)) with (S (S (2 * b + 1 - 2 * k))) by lia.
  replace (2 * k + 1) with (S (2 * k)) by lia.
  change (rgt (S y :: t)) with ([1]^^(2 * S y) *> 0 >> 0 >> rgt t).
  replace (2 * S y) with (S (S (2 * y))) by lia.
  change ([0;1]^^(S (2 * k)) *> const 0) with (0 >> 1 >> [0;1]^^(2 * k) *> const 0).
  change ([1]^^(S (S (2 * y))) *> 0 >> 0 >> rgt t) with (1 >> 1 >> [1]^^(2 * y) *> 0 >> 0 >> rgt t).
  follow (progress_evstep _ _ _ (TURN ([0;1]^^(2 * k) *> const 0) (2 * b + 1 - 2 * k) ([1]^^(2 * y) *> 0 >> 0 >> rgt t))).
  rewrite lpow_twice. simpl app.
  follow (BWS k (const 0) ([1]^^(5 + (2 * b + 1 - 2 * k)) *> 0 >> 0 >> [1]^^(2 * y) *> 0 >> 0 >> rgt t)).
  follow (progress_evstep _ _ _ (FINB ([1;1;0;0]^^k *> [1]^^(5 + (2 * b + 1 - 2 * k)) *> 0 >> 0 >> [1]^^(2 * y) *> 0 >> 0 >> rgt t))).
  replace (5 + (2 * b + 1 - 2 * k)) with (2 * (b + 3 - k)) by lia.
  finish.
Qed.

Lemma R2 : forall y t b, Kc (S y :: t) 0 b -->+ Kc (y :: t) (b + 3) 0.
Proof.
  intros. pose proof (R23 O y t b ltac:(lia)) as H. simpl repeat in H. simpl app in H.
  replace (b + 3 - O) with (b + 3) in H by lia. unfold Kc. exact H.
Qed.

Lemma R3 : forall k y t b, S k <= b ->
  Kc (repeat O (S k) ++ S y :: t) 0 b -->+ Kc (repeat 1%nat k ++ (b + 2 - k) :: y :: t) 1 0.
Proof.
  intros k y t b Hk. eapply progress_evstep_trans; [apply (R23 (S k) y t b Hk) |].
  unfold Kc. rewrite rgt_ones. simpl rgt.
  replace (b + 3 - S k) with (b + 2 - k) by lia.
  finish.
Qed.

(** ** the halting phase *)
Lemma TURN4 : forall l n,
  (0 >> 0 >> l) <{{F}} [1]^^(S (S n)) *> 0 >> 0 >> 1 >> const 0 -->+ (0 >> l) <{{F}} [1]^^(5 + n) *> const 0.
Proof.
  intros. eapply progress_intro; [prove_step | simpl_tape]. ex.
  follow crB. ex. follow crE. ex. follow crB. ex. follow crF. ex.
Qed.

Lemma FWZ : forall l n,
  (0 >> l) <{{F}} [1]^^(S (S n)) *> const 0 -->+ (0 >> 0 >> 1 >> l) <{{F}} [1]^^(S n) *> const 0.
Proof.
  intros. eapply progress_intro; [prove_step | simpl_tape]. ex.
  follow crB. ex. follow crF. ex.
Qed.

Lemma FWZS : forall j l n,
  (0 >> l) <{{F}} [1]^^(j + S n) *> const 0 -->* (0 >> [0;1]^^j *> l) <{{F}} [1]^^(S n) *> const 0.
Proof.
  induction j; intros.
  - finish.
  - replace (S j + S n) with (j + S (S n)) by lia.
    follow (IHj l (S n)).
    follow (progress_evstep _ _ _ (FWZ ([0;1]^^j *> l) n)). finish.
Qed.

Lemma END2 : forall l, (0 >> 0 >> 1 >> l) <{{F}} 1 >> const 0 -->+ l <{{F}} 1 >> 0 >> 1 >> const 0.
Proof. intros. eapply progress_intro; [prove_step | simpl_tape]. ex. Qed.

Lemma FIN : forall L T, (1 >> 0 >> L) <{{F}} 1 >> 0 >> 1 >> T -->* (1 >> 0 >> 0 >> 1 >> L) {{C}}> 1 >> T.
Proof. intros. ex. Qed.

Definition cfin (k b : nat) : Q * tape :=
  (1 >> 0 >> 0 >> 1 >> [1;0;1;0]^^k *> const 0) {{C}}>
  1 >> 1 >> 0 >> 0 >> [1;1;0;0]^^(b + 1 - k) *> 1 >> const 0.

Lemma cfin_halted : forall k b, halted tm (cfin k b).
Proof. intros. reflexivity. Qed.

Lemma R4x : forall k b, k <= b -> Kc (repeat O k) 0 b -->* cfin k b.
Proof.
  intros k b Hk. unfold Kc. rewrite <- (app_nil_r (repeat O k)), rgt_zeros. simpl rgt.
  change ([1]^^(2 * O) *> 0 >> 0 >> [0]^^(2 * k) *> 1 >> const 0)
    with (0 >> 0 >> [0]^^(2 * k) *> 1 >> const 0).
  follow (progress_evstep _ _ _ (START (S (2 * b)) (0 >> [0]^^(2 * k) *> 1 >> const 0))).
  replace (3 + S (2 * b)) with ((2 * k + 1) + S (2 * b + 2 - 2 * k)) by lia.
  rewrite <- zeros3.
  follow (FWS (2 * k + 1) (const 0) (2 * b + 2 - 2 * k) (1 >> const 0)).
  replace (S (2 * b + 2 - 2 * k)) with (S (S (2 * b + 1 - 2 * k))) by lia.
  replace (2 * k + 1) with (S (2 * k)) by lia.
  change ([0;1]^^(S (2 * k)) *> const 0) with (0 >> 1 >> [0;1]^^(2 * k) *> const 0).
  follow (progress_evstep _ _ _ (TURN4 (1 >> [0;1]^^(2 * k) *> const 0) (2 * b + 1 - 2 * k))).
  replace (5 + (2 * b + 1 - 2 * k)) with ((4 + (2 * b + 1 - 2 * k)) + S O) by lia.
  follow (FWZS (4 + (2 * b + 1 - 2 * k)) (1 >> [0;1]^^(2 * k) *> const 0) 0).
  change ([0;1]^^(4 + (2 * b + 1 - 2 * k)) *> 1 >> [0;1]^^(2 * k) *> const 0)
    with (0 >> 1 >> [0;1]^^(3 + (2 * b + 1 - 2 * k)) *> 1 >> [0;1]^^(2 * k) *> const 0).
  change ([1]^^(S O) *> const 0) with (1 >> const 0).
  follow (progress_evstep _ _ _ (END2 ([0;1]^^(3 + (2 * b + 1 - 2 * k)) *> 1 >> [0;1]^^(2 * k) *> const 0))).
  replace (3 + (2 * b + 1 - 2 * k)) with (2 * (b + 2 - k)) by lia.
  rewrite (lpow_twice [0;1] (b + 2 - k)). simpl app.
  follow (BWS (b + 2 - k) (1 >> [0;1]^^(2 * k) *> const 0) (1 >> const 0)).
  rewrite (lpow_twice [0;1] k). simpl app. rewrite (alc 0 [1;0;1] k). simpl app.
  replace (b + 2 - k) with (S (b + 1 - k)) by lia.
  change ([1;1;0;0]^^(S (b + 1 - k)) *> 1 >> const 0)
    with (1 >> 1 >> 0 >> 0 >> [1;1;0;0]^^(b + 1 - k) *> 1 >> const 0).
  follow (FIN ([1;0;1;0]^^k *> const 0) (1 >> 0 >> 0 >> [1;1;0;0]^^(b + 1 - k) *> 1 >> const 0)).
  unfold cfin. finish.
Qed.
