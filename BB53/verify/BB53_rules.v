(** * Rules for the new BB(5,3) TNF f_omega^2 champion:
      1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB

    Shatters BB(5,3) from finite pentation towers to two nested Ackermann
    cascades: sigma > 2 ↑^(2 ↑^8 3) 4 > f_omega(f_omega(8)). *)

From Local Require Import Individual53.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, L, C)  | A, 2 => Some (1, R, A)
  | B, 0 => Some (1, L, A)  | B, 1 => Some (2, L, C)  | B, 2 => Some (1, R, B)
  | C, 0 => Some (1, L, B)  | C, 1 => Some (1, L, D)  | C, 2 => Some (2, L, C)
  | D, 0 => Some (2, R, E)  | D, 1 => Some (2, L, D)  | D, 2 => Some (1, R, A)
  | E, 0 => None            | E, 1 => Some (2, R, E)  | E, 2 => Some (1, R, B)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma lpow_snoc : forall (x : sym) j r, [x]^^j *> x >> r = [x]^^(S j) *> r.
Proof.
  intros x j. induction j as [|j IH]; intros r.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
Ltac finish_norm := apply evstep_refl'; norm_nat; try (rewrite lpow_snoc); try reflexivity; lia_refl.

Ltac st_tape := autorewrite with tape_pre; simpl.
Ltac st_step := (eapply evstep_step || eapply progress_step); [prove_step | st_tape].

(** ** Elementary sweeps *)

Lemma D_1s : forall j l r,
  ([1]^^j *> l) <{{D}} r -->* l <{{D}} ([2]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (2 >> r)). finish_norm.
Qed.

Lemma A_2s : forall j l r,
  l {{A}}> [2]^^j *> r -->* ([1]^^j *> l) {{A}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH (1 >> l) r). finish_norm.
Qed.

Lemma B_2s : forall j l r,
  l {{B}}> [2]^^j *> r -->* ([1]^^j *> l) {{B}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH (1 >> l) r). finish_norm.
Qed.

Lemma EB_sweep : forall j l r,
  l {{E}}> 2 >> ([2]^^j *> r) -->* ([1]^^(S j) *> l) {{B}}> r.
Proof.
  intros j l r. step. follow (B_2s j (1 >> l) r). finish_norm.
Qed.

Lemma E_1s : forall j l r,
  l {{E}}> 1 >> ([1]^^j *> r) -->* ([2]^^(S j) *> l) {{E}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - step. finish.
  - step. follow (IH (2 >> l) r). finish_norm.
Qed.

Lemma C_2s : forall j l r,
  ([2]^^j *> l) <{{C}} r -->* l <{{C}} ([2]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (2 >> r)). finish_norm.
Qed.

(** ** 3-symbol Pure-Blank Ackermann core (B = A_core, C = B_L, E = B_R, D = C_L, A = C_R) *)

Lemma L1 : forall k l r,
  ([1]^^(S k) *> 2 >> l) <{{C}} r -->* ([1]^^(S k) *> l) <{{C}} (1 >> r).
Proof.
  intros k l r.
  step.
  follow (D_1s k (2 >> l) (1 >> r)).
  step.
  follow (A_2s k (1 >> l) (1 >> r)).
  step.
  finish_norm.
Qed.

Lemma Cor2 : forall k m l r,
  ([1]^^(S k) *> [2]^^m *> l) <{{C}} r -->* ([1]^^(S k) *> l) <{{C}} ([1]^^m *> r).
Proof.
  induction m as [|m IH]; intros l r.
  - finish.
  - follow (L1 k ([2]^^m *> l) r).
    follow (IH l (1 >> r)).
    finish_norm.
Qed.

Definition Bcfg (k n m : nat) (r : Stream sym) : Q * tape :=
  ([1]^^k *> [2]^^(2 * m + 1) *> const 0) {{B}}> ([1]^^n *> r).

Ltac finish_cfg := apply evstep_refl'; unfold Bcfg; norm_nat;
  try (rewrite lpow_snoc); try reflexivity; lia_refl.

Lemma turnaround : forall j m r,
  ([1]^^(S (S j)) *> const 0) <{{C}} ([1]^^m *> r) -->*
  Bcfg (S j) (S m) 0 r.
Proof.
  intros j m r.
  st_step.
  follow (D_1s (S j) (const 0) (1 >> [1]^^m *> r)).
  st_step.
  follow (EB_sweep j (2 >> const 0) (1 >> [1]^^m *> r)).
  finish.
Qed.

Fixpoint g (k m : nat) : nat :=
  match k with
  | O => S m
  | S k' => Nat.iter (2 * m + 2) (g k') 0%nat
  end.

Lemma B_level1_step : forall J r,
  ([1]^^1 *> [2]^^J *> const 0) {{B}}> (1 >> r) -->*
  ([1]^^1 *> [2]^^(J + 2) *> const 0) {{B}}> r.
Proof.
  intros J r.
  st_step.
  follow (Cor2 0 J (const 0) (2 >> r)).
  st_step.
  st_step.
  follow (E_1s J (2 >> const 0) (2 >> r)).
  st_step.
  finish_norm.
Qed.

Lemma B1_step : forall n m r,
  Bcfg 1 (S n) m r -->* Bcfg 1 n (S m) r.
Proof.
  intros n m r.
  unfold Bcfg. simpl ([1]^^(S n) *> r).
  follow (B_level1_step (2 * m + 1) ([1]^^n *> r)).
  finish_norm.
Qed.

Lemma iter_g0 : forall n x, Nat.iter n (g 0) x = x + n.
Proof.
  induction n as [|n IH]; intros x.
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

Lemma iter_succ_r : forall {X : Type} (f : X -> X) n x,
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  intros X f n. induction n as [|n IH]; intros x.
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

Theorem B_rule : forall k n m r,
  Bcfg (S k) n m r -->* Bcfg (S k) 0 (Nat.iter n (g k) m) r.
Proof.
  induction k as [|k IHk].
  - intros n. induction n as [|n IHn]; intros m r.
    + finish.
    + follow (B1_step n m r).
      follow (IHn (S m) r).
      rewrite !iter_g0. finish.
  - intros n. induction n as [|n IHn]; intros m r.
    + finish.
    + st_step.
      follow (Cor2 (S k) (2 * m + 1) (const 0) (2 >> [1]^^n *> r)).
      follow (turnaround k (2 * m + 1) (2 >> [1]^^n *> r)).
      follow (IHk (S (2 * m + 1)) 0%nat (2 >> [1]^^n *> r)).
      assert (E : Nat.iter (S (2 * m + 1)) (g k) 0%nat = g (S k) m).
      { assert (E2 : S (2 * m + 1) = 2 * m + 2) by lia.
        rewrite E2. reflexivity. }
      rewrite E.
      st_step.
      follow (IHn (g (S k) m) r).
      rewrite <- (iter_succ_r (g (S k)) n m). finish.
Qed.

(** ** Outer phase-lifting, K-drain, and halting rules *)

Lemma lift_from_1 : forall J,
  ([1]^^1 *> [2]^^J *> const 0) {{B}}> (const 0) -->*
  ([1]^^(S J) *> [2]^^4 *> const 0) {{B}}> ([1]^^2 *> const 0).
Proof.
  intros J.
  st_step.
  st_step.
  follow (C_2s J (const 0) ([1]^^2 *> const 0)).
  do 3 st_step.
  follow (B_level1_step 0 (1 >> [2]^^J *> [1]^^2 *> const 0)).
  follow (B_level1_step 2 ([2]^^J *> [1]^^2 *> const 0)).
  follow (B_2s J ([1]^^1 *> [2]^^4 *> const 0) ([1]^^2 *> const 0)).
  finish_norm.
Qed.

Lemma even_round : forall j,
  ([1]^^(S (S j)) *> [2]^^4 *> const 0) {{B}}> ([1]^^2 *> const 0) -->*
  Bcfg (S (S j)) 0 (g (S j) (Nat.iter 5 (g j) 0%nat)) (const 0).
Proof.
  intros j.
  st_step.
  follow (Cor2 (S j) 4 (const 0) (2 >> 1 >> const 0)).
  follow (turnaround j 4 (2 >> 1 >> const 0)).
  follow (B_rule j 5 0%nat (2 >> 1 >> const 0)).
  st_step.
  follow (B_rule (S j) 1 (Nat.iter 5 (g j) 0%nat) (const 0)).
  finish_cfg.
Qed.

Lemma K_drain_step : forall k m,
  Bcfg (S (S (S k))) 0 m (const 0) -->*
  Bcfg (S k) 0 (Nat.iter (2 * m + 4) (g k) 0%nat) (const 0).
Proof.
  intros k m.
  st_step.
  st_step.
  follow (Cor2 (S k) (2 * m + 1) (const 0) (1 >> (1 >> const 0))).
  rewrite (lpow_snoc 1 (2 * m + 1) (1 >> const 0)).
  rewrite (lpow_snoc 1 (S (2 * m + 1)) (const 0)).
  follow (turnaround k (S (S (2 * m + 1))) (const 0)).
  assert (E2 : S (S (S (2 * m + 1))) = 2 * m + 4) by lia.
  rewrite E2.
  follow (B_rule k (2 * m + 4) 0%nat (const 0)).
  finish.
Qed.

Fixpoint drain_even (q m : nat) : nat :=
  match q with
  | O => m
  | S q' => drain_even q' (Nat.iter (2 * m + 4) (g (2 * q' + 1)) 0%nat)
  end.

Lemma K_drain_even : forall q m,
  Bcfg (2 * q + 2) 0 m (const 0) -->* Bcfg 2 0 (drain_even q m) (const 0).
Proof.
  induction q as [|q IH]; intros m.
  - finish.
  - assert (Eq1 : 2 * S q + 2 = S (S (S (2 * q + 1)))) by lia.
    rewrite Eq1.
    follow (K_drain_step (2 * q + 1) m).
    assert (Eq2 : S (2 * q + 1) = 2 * q + 2) by lia.
    rewrite Eq2.
    simpl drain_even.
    apply IH.
Qed.

Lemma halt_from_2 : forall m,
  Bcfg 2 0 m (const 0) -->*
  ([2]^^(2 * m + 5) *> const 0) {{E}}> (const 0).
Proof.
  intros m.
  st_step.
  st_step.
  follow (Cor2 0 (2 * m + 1) (const 0) (1 >> (1 >> const 0))).
  st_step.
  st_step.
  follow (E_1s (2 * m + 1) (2 >> const 0) (1 >> (1 >> const 0))).
  do 2 st_step.
  finish_norm.
Qed.

(** ** 6-step blank-tape boot + Round 1 + Lifting #1 *)

Lemma boot53_6 : c0 -->* ([1]^^1 *> const 0) {{B}}> ([1]^^4 *> const 0).
Proof.
  unfold c0.
  do 6 st_step.
  finish_norm.
Qed.

Lemma start53_to_round2 :
  c0 -->* ([1]^^9 *> [2]^^4 *> const 0) {{B}}> ([1]^^2 *> const 0).
Proof.
  follow boot53_6.
  follow (B_level1_step 0 ([1]^^3 *> const 0)).
  follow (B_level1_step 2 ([1]^^2 *> const 0)).
  follow (B_level1_step 4 ([1]^^1 *> const 0)).
  follow (B_level1_step 6 (const 0)).
  follow (lift_from_1 8).
  finish_norm.
Qed.
