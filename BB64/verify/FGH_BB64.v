(** * FGH_BB64: the BB(6,4) machine
      1RB3LC1LD2RA_2RC1RF2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE_0LC0LB0LD1RZ
    in the standard fast-growing hierarchy.

    BB64_bound proves the Knuth-arrow majorant
      BB64_bound.sigma_beats_four_f_omega1 :
        f_omega1^4(2 ^ 16) < sigma,
    where f_omega n = 2 ^(n+1) (n+3) and f_omega1 n = f_omega^n(n).
    By KnuthFGH.fw_le_F, f_omega majorises the FGH f_omega, hence f_omega1
    majorises f_(omega+1) = FGH (osucc omega), and the majorisation survives
    four iterates:

      bb64_fgh_four : f_(omega+1)^4(65536) < sigma. *)

From BB8 Require Import Ord KnuthFGH.
From TM64 Require Import BB64_score BB64_run BB64_bound.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".

Lemma iter_ext_nat64 : forall (f h : nat -> nat) n x,
  (forall y, f y = h y) -> Nat.iter n f x = Nat.iter n h x.
Proof. intros f h n x H. induction n as [|n IH]; [reflexivity |].
  rewrite !Nat.iter_succ, IH. apply H. Qed.

Lemma knuth_same64 : forall n a b, BB64_bound.knuth n a b = kn n a b.
Proof.
  induction n as [|n IH]; intros a b; [reflexivity |].
  change (BB64_bound.knuth (S n) a b) with
    (Nat.iter b (BB64_bound.knuth n a) 1).
  change (kn (S n) a b) with (Nat.iter b (kn n a) 1).
  apply iter_ext_nat64. intro y. apply IH.
Qed.

Lemma fw_le_F64 : forall y, 4 <= y -> FGH omega y <= BB64_bound.f_omega y.
Proof.
  intros y Hy.
  change (BB64_bound.f_omega y) with (BB64_bound.knuth (S y) 2 (y + 3)).
  rewrite knuth_same64. apply fw_le_F. exact Hy.
Qed.

Lemma f_omega1_mono64 : forall a b,
  a <= b -> BB64_bound.f_omega1 a <= BB64_bound.f_omega1 b.
Proof.
  intros a b Hab. unfold BB64_bound.f_omega1.
  assert (H1 : Nat.iter a BB64_bound.f_omega a <=
               Nat.iter a BB64_bound.f_omega b) by
    (apply BB64_bound.iter_f_omega_mono; exact Hab).
  assert (H2 : Nat.iter a BB64_bound.f_omega b <=
               Nat.iter b BB64_bound.f_omega b) by
    (apply BB64_bound.iter_f_omega_mono_c; exact Hab).
  lia.
Qed.

Lemma iter_le_f_omega1_64 : forall N, 4 <= N ->
  Nat.iter N (FGH omega) N <= BB64_bound.f_omega1 N.
Proof.
  intros N HN. unfold BB64_bound.f_omega1.
  exact (it_le_ge1 BB64_bound.f_omega (FGH omega) 4
           BB64_bound.f_omega_mono fw_le_F64
           (fun y Hy => Nat.le_trans _ _ _ Hy (FGH_ge omega y nf_omega))
           N N HN).
Qed.

Lemma W_le_f1 : forall y, 4 <= y ->
  FGH (osucc omega) y <= BB64_bound.f_omega1 y.
Proof.
  intros y Hy. rewrite FGH_osucc by apply nf_omega.
  apply iter_le_f_omega1_64. exact Hy.
Qed.

Lemma W_ge_4 : forall y, 4 <= y -> 4 <= FGH (osucc omega) y.
Proof.
  intros y Hy. eapply Nat.le_trans; [exact Hy |].
  apply FGH_ge. apply nf_osucc. apply nf_omega.
Qed.

Lemma iter_W_le_iter_f1 : forall i x, 4 <= x ->
  Nat.iter i (FGH (osucc omega)) x <=
  Nat.iter i BB64_bound.f_omega1 x.
Proof.
  intros i x Hx.
  exact (it_le_ge1 BB64_bound.f_omega1 (FGH (osucc omega)) 4
           f_omega1_mono64 W_le_f1 W_ge_4 i x Hx).
Qed.

(** The exact statement requested:  f_(omega+1)^4(65536) < sigma. *)
Theorem bb64_fgh_four :
  Nat.iter 4 (FGH (osucc omega)) (2 ^ 16) < BB64_score.sigma.
Proof.
  assert (H4 : 4 <= 2 ^ 16) by (vm_compute; lia).
  pose proof (iter_W_le_iter_f1 4 (2 ^ 16) H4) as Hmono.
  assert (Hsig : Nat.iter 4 BB64_bound.f_omega1 (2 ^ 16) < BB64_score.sigma) by
    (exact BB64_bound.sigma_beats_four_f_omega1).
  lia.
Qed.

Print Assumptions bb64_fgh_four.
