(** * Rules for Argon's BB(4,4) machine 44-B (TNF):
      1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD

    Rows C, D and A1 = 2LC, A2 = 3RA are those of 44-A (BB44A_rules.v): the same Kropitz core, so the core lemmas
    and the B_rule are copied verbatim from BB44A_rules.v (ports of argon_scout/M44).  The 44-B specific phases are
    step_up (A2), phase1, phase2, phase3 and the 77-step start.  The hierarchy g is M44's (BB44_rules.g). *)

From Local Require Import Individual44.
From Local Require BB44_rules.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (2, L, C)  | A, 2 => Some (3, R, A)  | A, 3 => None
  | B, 0 => Some (2, R, C)  | B, 1 => Some (3, L, B)  | B, 2 => Some (2, L, B)  | B, 3 => Some (0, L, C)
  | C, 0 => Some (1, L, B)  | C, 1 => Some (2, R, C)  | C, 2 => Some (3, R, A)  | C, 3 => Some (1, L, D)
  | D, 0 => Some (2, R, C)  | D, 1 => Some (1, L, C)  | D, 2 => Some (3, R, D)  | D, 3 => Some (2, L, D)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation g := BB44_rules.g.

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

Lemma D_sweep_left : forall j l r,
  ([3]^^j *> l) <{{D}} r -->* l <{{D}} ([2]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (2 >> r)). finish_norm.
Qed.

Lemma D_right_2s : forall j l r,
  l {{D}}> [2]^^j *> r -->* ([3]^^j *> l) {{D}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH (3 >> l) r). finish_norm.
Qed.

Lemma A_2s : forall j l r,
  l {{A}}> [2]^^j *> r -->* ([3]^^j *> l) {{A}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH (3 >> l) r). finish_norm.
Qed.

Lemma C_1s : forall j l r,
  l {{C}}> 1 >> ([1]^^j *> r) -->* ([2]^^(S j) *> l) {{C}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - step. finish.
  - step. follow (IH (2 >> l) r). finish_norm.
Qed.

Lemma CA_sweep : forall j l r,
  l {{C}}> 2 >> ([2]^^j *> r) -->* ([3]^^(S j) *> l) {{A}}> r.
Proof.
  intros j l r. step. follow (A_2s j (3 >> l) r). finish_norm.
Qed.

Lemma B_2s : forall j l r,
  ([2]^^j *> l) <{{B}} r -->* l <{{B}} ([2]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (2 >> r)). finish_norm.
Qed.

(** ** Kropitz Ackermann core (C = Kropitz B, D = Kropitz C) *)

Lemma L1 : forall k l r,
  ([3]^^(S k) *> 2 >> l) <{{C}} r -->* ([3]^^(S k) *> l) <{{C}} (1 >> r).
Proof.
  intros k l r.
  step.
  follow (D_sweep_left k (2 >> l) (1 >> r)).
  step.
  follow (D_right_2s k (3 >> l) (1 >> r)).
  step.
  finish_norm.
Qed.

Lemma Cor2 : forall k m l r,
  ([3]^^(S k) *> [2]^^m *> l) <{{C}} r -->* ([3]^^(S k) *> l) <{{C}} ([1]^^m *> r).
Proof.
  induction m as [|m IH]; intros l r.
  - finish.
  - follow (L1 k ([2]^^m *> l) r).
    follow (IH l (1 >> r)).
    finish_norm.
Qed.

Definition Bcfg (k n m : nat) (r : Stream sym) : Q * tape :=
  ([3]^^k *> [2]^^(2 * m + 1) *> const 0) {{A}}> ([1]^^n *> r).

Ltac finish_cfg := apply evstep_refl'; unfold Bcfg; norm_nat;
  try (rewrite lpow_snoc); try reflexivity; lia_refl.

Lemma turnaround : forall j m n r,
  ([3]^^(S (S j)) *> const 0) <{{C}} ([1]^^m *> 2 >> [1]^^n *> r) -->*
  Bcfg (S j) (S m) 0 (2 >> [1]^^n *> r).
Proof.
  intros j m n r.
  st_step.
  follow (D_sweep_left (S j) (const 0) (1 >> [1]^^m *> 2 >> [1]^^n *> r)).
  st_step.
  follow (CA_sweep j (2 >> const 0) (1 >> [1]^^m *> 2 >> [1]^^n *> r)).
  finish.
Qed.

Lemma B1_step : forall n m r,
  Bcfg 1 (S n) m r -->* Bcfg 1 n (S m) r.
Proof.
  intros n m r.
  st_step.
  follow (Cor2 0 (2 * m + 1) (const 0) (2 >> [1]^^n *> r)).
  st_step.
  st_step.
  follow (C_1s (2 * m + 1) (2 >> const 0) (2 >> [1]^^n *> r)).
  st_step.
  finish_cfg.
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
      rewrite !BB44_rules.iter_g0. finish.
  - intros n. induction n as [|n IHn]; intros m r.
    + finish.
    + st_step.
      follow (Cor2 (S k) (2 * m + 1) (const 0) (2 >> [1]^^n *> r)).
      follow (turnaround k (2 * m + 1) n r).
      follow (IHk (S (2 * m + 1)) 0%nat (2 >> [1]^^n *> r)).
      assert (E : Nat.iter (S (2 * m + 1)) (g k) 0%nat = g (S k) m).
      { assert (E2 : S (2 * m + 1) = 2 * m + 2) by lia.
        rewrite E2. reflexivity. }
      rewrite E.
      st_step.
      follow (IHn (g (S k) m) r).
      rewrite <- (iter_succ_r (g (S k)) n m). finish.
Qed.

(** ** The phases of 44-B *)

(** A2 = 3RA: one more 3, the counter reads the next 1. *)
Lemma step_up : forall k m R, Bcfg k 0 m (2 >> 1 >> R) -->* Bcfg (S k) 1 m R.
Proof. intros k m R. unfold Bcfg. st_step. finish. Qed.

(** phase1 (macro steps 67-78): from the blank right end. *)
Theorem phase1 : forall K a,
  Bcfg (S (S (S K))) 0 a (const 0) -->* Bcfg (S K) (2 * a + 2) 0 (0 >> 3 >> 2 >> 1 >> const 0).
Proof.
  intros K a. unfold Bcfg at 1.
  do 6 st_step.
  follow (Cor2 (S K) (2 * a + 1) (const 0) (0 >> 3 >> 2 >> 1 >> const 0)).
  st_step.
  follow (D_sweep_left (S K) (const 0) (1 >> [1]^^(2 * a + 1) *> 0 >> 3 >> 2 >> 1 >> const 0)).
  st_step.
  follow (CA_sweep K (2 >> const 0) (1 >> [1]^^(2 * a + 1) *> 0 >> 3 >> 2 >> 1 >> const 0)).
  finish_cfg.
Qed.

(** phase2 (macro steps 80-91) *)
Theorem phase2 : forall K b R0,
  Bcfg (S (S (S K))) 0 b (0 >> 3 >> R0) -->* Bcfg (S K) (2 * b + 2) 0 (0 >> 2 >> 1 >> R0).
Proof.
  intros K b R0. unfold Bcfg at 1.
  do 6 st_step.
  follow (Cor2 (S K) (2 * b + 1) (const 0) (0 >> 2 >> 1 >> R0)).
  st_step.
  follow (D_sweep_left (S K) (const 0) (1 >> [1]^^(2 * b + 1) *> 0 >> 2 >> 1 >> R0)).
  st_step.
  follow (CA_sweep K (2 >> const 0) (1 >> [1]^^(2 * b + 1) *> 0 >> 2 >> 1 >> R0)).
  finish_cfg.
Qed.

(** phase3 (macro steps 93-105): the level becomes 2c+3. *)
Theorem phase3 : forall c R0,
  Bcfg 2 0 c (0 >> 2 >> 1 >> R0) -->* Bcfg (S (S (2 * c + 1))) 1 0 (3 >> 2 >> 1 >> R0).
Proof.
  intros c R0. unfold Bcfg at 1.
  do 4 st_step.
  follow (Cor2 0 (2 * c + 1) (const 0) (0 >> 3 >> 2 >> 1 >> R0)).
  st_step.
  st_step.
  follow (C_1s (2 * c + 1) (2 >> const 0) (0 >> 3 >> 2 >> 1 >> R0)).
  st_step.
  follow (B_2s (S (2 * c + 1)) (2 >> const 0) (1 >> 3 >> 2 >> 1 >> R0)).
  st_step.
  st_step.
  follow (CA_sweep (S (2 * c + 1)) (2 >> const 0) (1 >> 3 >> 2 >> 1 >> R0)).
  finish_cfg.
Qed.

(** 77 literal steps from the blank tape *)
Lemma start_to_B2 : c0 -->* Bcfg 2 1 0 (2 >> 1 >> 2 >> 1 >> 2 >> 1 >> 2 >> 1 >> const 0).
Proof.
  unfold c0.
  do 77 st_step.
  finish_cfg.
Qed.
