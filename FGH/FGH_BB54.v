(** * FGH_BB54: the BB(5,4) machine 54-L (1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE)
    in the standard fast-growing hierarchy.

    Files (logical root Local, argon_scout/M54 = published busy-beaver BB54/verify_54l, unchanged): BB54, Individual54,
    BB54_rules, BB54_run, BB54_bound.  BB54_bound.sigma_beats_f_omega1_65536 : f_omega1 (2 ^ 16) < sigma, where
    f_omega n = knuth (S n) 2 (n + 3) = 2 ^(n+1) (n+3) (a Knuth-arrow function) and f_omega1 n = f_omega^n(n).
    Standard FGH: published Ord.v (root BB8); KnuthFGH.v (new).  f_(w+1) = FGH (osucc omega).

      bb54_fgh : FGH (osucc omega) (2 ^ 16) < sigma          i.e.  f_(w+1)(65536) < sigma

    via f_w(n) <= 2 ^(n+1) (n+3) for n >= 4 (KnuthFGH.fw_le_F). *)

From BB8 Require Import Ord KnuthFGH.
From Local Require BB54_run BB54_bound.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".

Lemma iter_ext_nat : forall (f h : nat -> nat) n x, (forall y, f y = h y) -> Nat.iter n f x = Nat.iter n h x.
Proof. intros f h n x H. induction n as [|n IH]; [reflexivity|]. rewrite !Nat.iter_succ, IH. apply H. Qed.

Lemma knuth_same : forall n a b, Local.BB54_bound.knuth n a b = kn n a b.
Proof.
  induction n as [|n IH]; intros a b; [reflexivity|].
  change (Local.BB54_bound.knuth (S n) a b) with (Nat.iter b (Local.BB54_bound.knuth n a) 1).
  change (kn (S n) a b) with (Nat.iter b (kn n a) 1).
  apply iter_ext_nat. intro y. apply IH.
Qed.

Lemma fw_le_F54 : forall y, 4 <= y -> FGH omega y <= Local.BB54_bound.f_omega y.
Proof.
  intros y Hy. change (Local.BB54_bound.f_omega y) with (Local.BB54_bound.knuth (S y) 2 (y + 3)).
  rewrite knuth_same. apply fw_le_F. exact Hy.
Qed.

Lemma iter_le_f_omega1 : forall N, 4 <= N -> Nat.iter N (FGH omega) N <= Local.BB54_bound.f_omega1 N.
Proof.
  intros N HN. unfold Local.BB54_bound.f_omega1.
  exact (it_le_ge1 Local.BB54_bound.f_omega (FGH omega) 4 Local.BB54_bound.f_omega_mono fw_le_F54
           (fun y Hy => Nat.le_trans _ _ _ Hy (FGH_ge omega y nf_omega)) N N HN).
Qed.

Theorem bb54_fgh : FGH (osucc omega) (2 ^ 16) < Local.BB54_run.sigma.
Proof.
  rewrite FGH_osucc by apply nf_omega.
  pose proof Local.BB54_bound.sigma_beats_f_omega1_65536 as H.
  assert (H4 : 4 <= 2 ^ 16) by (apply Nat.le_trans with (m := 2 ^ 2); [apply Nat.le_refl | apply Nat.pow_le_mono_r; lia]).
  pose proof (iter_le_f_omega1 (2 ^ 16) H4) as H2.
  revert H H2. generalize (Local.BB54_bound.f_omega1 (2 ^ 16)) (Nat.iter (2 ^ 16) (FGH omega) (2 ^ 16)).
  intros a b H H2. lia.
Qed.

Print Assumptions bb54_fgh.
