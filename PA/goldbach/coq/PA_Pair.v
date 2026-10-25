(** * PA_Pair: the dual Cantor pairing  P a b = tri (a+b) + b  of the machine (as zf/m254/logic/coq/Codes254.v). *)
From Coq Require Import Arith Lia.

Fixpoint tri (n : nat) : nat := match n with 0 => 0 | S m => S m + tri m end.

Definition P (a b : nat) : nat := tri (a + b) + b.

Definition unP_step (o : nat * nat) : nat * nat :=
  match o with
  | (S a, b) => (a, S b)
  | (0, b) => (S b, 0)
  end.

Definition unP (z : nat) : nat * nat := Nat.iter z unP_step (0, 0).

Lemma P_unP_step a b : P (fst (unP_step (a, b))) (snd (unP_step (a, b))) = S (P a b).
Proof.
  unfold P. destruct a as [|a]; cbn [unP_step fst snd].
  - rewrite !Nat.add_0_r, !Nat.add_0_l. cbn [tri]. lia.
  - replace (a + S b) with (S a + b) by lia. lia.
Qed.

Lemma P_0 a b : P a b = 0 -> a = 0 /\ b = 0.
Proof. unfold P. destruct (a + b) as [|s] eqn:E; cbn [tri]; intro H; lia. Qed.

Lemma P_pred a b : P a b <> 0 -> exists a' b', P a' b' + 1 = P a b /\ unP_step (a', b') = (a, b).
Proof.
  intro Hn. destruct b as [|b].
  - destruct a as [|a]; [unfold P in Hn; cbn in Hn; lia|].
    exists 0, a. split; [|reflexivity].
    pose proof (P_unP_step 0 a) as H. cbn [unP_step fst snd] in H. lia.
  - exists (S a), b. split; [|reflexivity].
    pose proof (P_unP_step (S a) b) as H. cbn [unP_step fst snd] in H. lia.
Qed.

Lemma unP_P a b : unP (P a b) = (a, b).
Proof.
  remember (P a b) as n eqn:E. revert a b E. induction n as [|n IH]; intros a b E.
  - symmetry in E. destruct (P_0 a b E) as [-> ->]. reflexivity.
  - destruct (P_pred a b ltac:(lia)) as [a' [b' [H1 H2]]].
    change (unP (S n)) with (unP_step (unP n)). rewrite (IH a' b') by lia. exact H2.
Qed.

Lemma P_unP z : P (fst (unP z)) (snd (unP z)) = z.
Proof.
  induction z as [|z IH]; [reflexivity|].
  change (unP (S z)) with (unP_step (unP z)). destruct (unP z) as [a b].
  rewrite P_unP_step. cbn [fst snd] in IH. now rewrite IH.
Qed.

Lemma P_ge_l a b : a <= P a b.
Proof.
  unfold P. assert (forall n, n <= tri n) by (induction n; cbn; lia).
  specialize (H (a + b)). lia.
Qed.

Lemma P_ge_r a b : b <= P a b.
Proof. unfold P. lia. Qed.

Lemma P_inj a b a' b' : P a b = P a' b' -> a = a' /\ b = b'.
Proof. intro H. pose proof (unP_P a b) as E. rewrite H, unP_P in E. now injection E. Qed.

