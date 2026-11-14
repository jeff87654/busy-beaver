(** * Rules for the new BB(4,4) TNF champion:
      1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD

    Exact score: sigma = 2 ↑^65532 6 + 65532 (vs official record 2 ↑^509 3 + 510). *)

From Local Require Import Individual44.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (3, L, B)  | A, 2 => None            | A, 3 => Some (2, R, A)
  | B, 0 => Some (1, L, C)  | B, 1 => Some (3, R, B)  | B, 2 => Some (1, L, D)  | B, 3 => Some (2, R, A)
  | C, 0 => Some (3, R, B)  | C, 1 => Some (2, L, C)  | C, 2 => Some (1, L, C)  | C, 3 => Some (3, L, C)
  | D, 0 => Some (3, R, B)  | D, 1 => Some (1, L, B)  | D, 2 => Some (3, L, D)  | D, 3 => Some (2, R, D)
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

(** ** Elementary sweeps (D = Kropitz C, C = level lifter) *)

Lemma D_sweep_left : forall j l r,
  ([2]^^j *> l) <{{D}} r -->* l <{{D}} ([3]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (3 >> r)). finish_norm.
Qed.

Lemma D_right_3s : forall j l r,
  l {{D}}> [3]^^j *> r -->* ([2]^^j *> l) {{D}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH (2 >> l) r). finish_norm.
Qed.

Lemma A_3s : forall j l r,
  l {{A}}> [3]^^j *> r -->* ([2]^^j *> l) {{A}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH (2 >> l) r). finish_norm.
Qed.

Lemma B_1s : forall j l r,
  l {{B}}> 1 >> ([1]^^j *> r) -->* ([3]^^(S j) *> l) {{B}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - step. finish.
  - step. follow (IH (3 >> l) r). finish_norm.
Qed.

Lemma BA_sweep : forall j l r,
  l {{B}}> 3 >> ([3]^^j *> r) -->* ([2]^^(S j) *> l) {{A}}> r.
Proof.
  intros j l r. step. follow (A_3s j (2 >> l) r). finish_norm.
Qed.

Lemma C_2s : forall j l r,
  ([2]^^j *> l) <{{C}} r -->* l <{{C}} ([1]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (1 >> r)). finish_norm.
Qed.

Lemma C_3s : forall j l r,
  ([3]^^j *> l) <{{C}} r -->* l <{{C}} ([3]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (3 >> r)). finish_norm.
Qed.

(** ** Kropitz Ackermann core (B = Kropitz B, D = Kropitz C) *)

Lemma L1 : forall k l r,
  ([2]^^(S k) *> 3 >> l) <{{B}} r -->* ([2]^^(S k) *> l) <{{B}} (1 >> r).
Proof.
  intros k l r.
  step.
  follow (D_sweep_left k (3 >> l) (1 >> r)).
  step.
  follow (D_right_3s k (2 >> l) (1 >> r)).
  step.
  finish_norm.
Qed.

Lemma Cor2 : forall k m l r,
  ([2]^^(S k) *> [3]^^m *> l) <{{B}} r -->* ([2]^^(S k) *> l) <{{B}} ([1]^^m *> r).
Proof.
  induction m as [|m IH]; intros l r.
  - finish.
  - follow (L1 k ([3]^^m *> l) r).
    follow (IH l (1 >> r)).
    finish_norm.
Qed.

Definition Bcfg (k n m : nat) (r : Stream sym) : Q * tape :=
  ([2]^^k *> [3]^^(2 * m + 1) *> const 0) {{A}}> ([1]^^n *> r).

Ltac finish_cfg := apply evstep_refl'; unfold Bcfg; norm_nat;
  try (rewrite lpow_snoc); try reflexivity; lia_refl.

Lemma turnaround : forall j m n r,
  ([2]^^(S (S j)) *> const 0) <{{B}} ([1]^^m *> 3 >> [1]^^n *> r) -->*
  Bcfg (S j) (S m) 0 (3 >> [1]^^n *> r).
Proof.
  intros j m n r.
  st_step.
  follow (D_sweep_left (S j) (const 0) (1 >> [1]^^m *> 3 >> [1]^^n *> r)).
  st_step.
  follow (BA_sweep j (3 >> const 0) (1 >> [1]^^m *> 3 >> [1]^^n *> r)).
  finish.
Qed.

Fixpoint g (k m : nat) : nat :=
  match k with
  | O => S m
  | S k' => Nat.iter (2 * m + 2) (g k') 0%nat
  end.

Lemma B1_step : forall n m r,
  Bcfg 1 (S n) m r -->* Bcfg 1 n (S m) r.
Proof.
  intros n m r.
  st_step.
  follow (Cor2 0 (2 * m + 1) (const 0) (3 >> [1]^^n *> r)).
  st_step.
  st_step.
  follow (B_1s (2 * m + 1) (3 >> const 0) (3 >> [1]^^n *> r)).
  st_step.
  finish_cfg.
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
      follow (Cor2 (S k) (2 * m + 1) (const 0) (3 >> [1]^^n *> r)).
      follow (turnaround k (2 * m + 1) n r).
      follow (IHk (S (2 * m + 1)) 0%nat (3 >> [1]^^n *> r)).
      assert (E : Nat.iter (S (2 * m + 1)) (g k) 0%nat = g (S k) m).
      { assert (E2 : S (2 * m + 1) = 2 * m + 2) by lia.
        rewrite E2. reflexivity. }
      rewrite E.
      st_step.
      follow (IHn (g (S k) m) r).
      rewrite <- (iter_succ_r (g (S k)) n m). finish.
Qed.

(** ** 22-step blank-tape startup: [c0 -->* Bcfg 4 1 0 (const 0)] *)

Definition c44_mid12 : Q * tape :=
  ([3]^^4 *> const 0) {{B}}> (const 0).

Lemma start44_12a : c0 -->* c44_mid12.
Proof.
  unfold c0, c44_mid12.
  do 12 st_step.
  finish_norm.
Qed.

Lemma start44_10b : c44_mid12 -->* Bcfg 4 1 0 (const 0).
Proof.
  unfold c44_mid12.
  do 10 st_step.
  finish_cfg.
Qed.

Lemma start44_to_B4 : c0 -->* Bcfg 4 1 0 (const 0).
Proof.
  eapply evstep_trans; [apply start44_12a | apply start44_10b].
Qed.

(** ** Level-lift phase [C_lift]: [Bcfg 4 0 m (const 0) -->* Bcfg (2m+1) 4 0 (2 >> 1 >> const 0)] *)

Theorem C_lift : forall m,
  Bcfg 4 0 m (const 0) -->* Bcfg (S (2 * m)) 4 0 (2 >> (1 >> const 0)).
Proof.
  intros m.
  unfold Bcfg at 1; simpl.
  st_step. st_step. st_step.
  follow (C_2s 4 ([3]^^(2 * m + 1) *> const 0) (2 >> (1 >> const 0))).
  follow (C_3s (2 * m + 1) (const 0) ([1]^^4 *> (2 >> (1 >> const 0)))).
  replace (2 * m + 1) with (S (2 * m)) by lia.
  change ([3]^^(S (2 * m)) *> ([1]^^4 *> (2 >> (1 >> const 0))))
    with (3 >> ([3]^^(2 * m) *> ([1]^^4 *> (2 >> (1 >> const 0))))).
  st_step.
  follow (BA_sweep (2 * m) (3 >> const 0) ([1]^^4 *> (2 >> (1 >> const 0)))).
  finish.
Qed.
