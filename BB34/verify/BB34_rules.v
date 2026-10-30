(** * Rules for the BB(3,4) champion 1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC *)

(** Tape convention (busycoq): [l <{{Q}} r] has the head on [hd l]; [l {{Q}}> r] has the head on
    [hd r].  A left stream is listed from the head outwards, so the Ligocki word
    "0^inf 3^(2m+1) 2^k A> 1^n R" is [(Bcfg k n m r)] with left stream
    [[2]^^k *> [3]^^(2m+1) *> const 0].  The halting transition A2 = 1RZ is [None]. *)

From TM34 Require Import Individual34.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (3, L, B)  | A, 2 => None            | A, 3 => Some (2, R, A)
  | B, 0 => Some (2, L, C)  | B, 1 => Some (3, R, B)  | B, 2 => Some (1, L, C)  | B, 3 => Some (2, R, A)
  | C, 0 => Some (3, R, B)  | C, 1 => Some (1, L, B)  | C, 2 => Some (3, L, C)  | C, 3 => Some (2, R, C)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** ** Stream alignment lemmas *)

Lemma lpow_snoc : forall (x : sym) j r, [x]^^j *> x >> r = [x]^^(S j) *> r.
Proof.
  intros x j. induction j as [|j IH]; intros r.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
Ltac finish_norm := apply evstep_refl'; norm_nat; try (rewrite lpow_snoc); try reflexivity; lia_refl.

(** Individual's [simpl_tape] autorewrites with [tape_post], whose [lpow_add]
    splits blocks like [3^^(2*m+1)] whose exponent is a stuck sum.  We use a
    gentler version that only [simpl]s. *)
Ltac st_tape := autorewrite with tape_pre; simpl.
Ltac st_step := (eapply evstep_step || eapply progress_step); [prove_step | st_tape].


(** ** Elementary sweeps *)

(** C sweeping left over a block of 2s, writing 3s and stopping on the next cell left:
    [([2]^^j *> l) <{{C}} r -->* l <{{C}} ([3]^^j *> r)]. *)
Lemma C_sweep_left : forall j l r,
  ([2]^^j *> l) <{{C}} r -->* l <{{C}} ([3]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (3 >> r)). finish_norm.
Qed.

(** C sweeping right over a block of 3s, writing 2s:
    [l {{C}}> [3]^^j *> r -->* ([2]^^j *> l) {{C}}> r]. *)
Lemma C_right_3s : forall j l r,
  l {{C}}> [3]^^j *> r -->* ([2]^^j *> l) {{C}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH (2 >> l) r). finish_norm.
Qed.

(** A sweeping right over a block of 3s, writing 2s:
    [l {{A}}> [3]^^j *> r -->* ([2]^^j *> l) {{A}}> r]. *)
Lemma A_3s : forall j l r,
  l {{A}}> [3]^^j *> r -->* ([2]^^j *> l) {{A}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH (2 >> l) r). finish_norm.
Qed.

(** B sweeping right over a block of 1s, writing 3s:
    [l {{B}}> 1 >> ([1]^^j *> r) -->* ([3]^^(S j) *> l) {{B}}> r]. *)
Lemma B_1s : forall j l r,
  l {{B}}> 1 >> ([1]^^j *> r) -->* ([3]^^(S j) *> l) {{B}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - step. finish.
  - step. follow (IH (3 >> l) r). finish_norm.
Qed.

(** One B step over a 3 followed by an A sweep:
    [l {{B}}> 3 >> ([3]^^j *> r) -->* ([2]^^(S j) *> l) {{A}}> r]. *)
Lemma BA_sweep : forall j l r,
  l {{B}}> 3 >> ([3]^^j *> r) -->* ([2]^^(S j) *> l) {{A}}> r.
Proof.
  intros j l r. step. follow (A_3s j (2 >> l) r). finish_norm.
Qed.

(** ** Lemma 1 (Ligocki): [3 2^k <B --> 2^k <B 1] in [2k+1] steps for [k >= 1]. *)
Lemma L1 : forall k l r,
  ([2]^^(S k) *> 3 >> l) <{{B}} r -->* ([2]^^(S k) *> l) <{{B}} (1 >> r).
Proof.
  intros k l r.
  step.
  follow (C_sweep_left k (3 >> l) (1 >> r)).
  step.
  follow (C_right_3s k (2 >> l) (1 >> r)).
  step.
  finish_norm.
Qed.

(** ** Corollary 2 (Ligocki): [3^m 2^k <B --> 2^k <B 1^m] for [k >= 1]. *)
Lemma Cor2 : forall k m l r,
  ([2]^^(S k) *> [3]^^m *> l) <{{B}} r -->* ([2]^^(S k) *> l) <{{B}} ([1]^^m *> r).
Proof.
  induction m as [|m IH]; intros l r.
  - finish.
  - follow (L1 k ([3]^^m *> l) r).
    follow (IH l (1 >> r)).
    finish_norm.
Qed.

(** ** The B configurations (Ligocki):
       [B(k, n, m) R = 0^inf  3^(2m+1)  2^k  A>  1^n  R]. *)
Definition Bcfg (k n m : nat) (r : Stream sym) : Q * tape :=
  ([2]^^k *> [3]^^(2 * m + 1) *> const 0) {{A}}> ([1]^^n *> r).

(** [finish_norm] for goals whose target is a [Bcfg] configuration. *)
Ltac finish_cfg := apply evstep_refl'; unfold Bcfg; norm_nat;
  try (rewrite lpow_snoc); try reflexivity; lia_refl.

(** ** The turnaround: [0^inf 2^(k+2) <B 1^m 3 1^n R --> 0^inf 3 2^(k+1) A> 1^(m+1) 3 1^n R]. *)
Lemma turnaround : forall j m n r,
  ([2]^^(S (S j)) *> const 0) <{{B}} ([1]^^m *> 3 >> [1]^^n *> r) -->*
  Bcfg (S j) (S m) 0 (3 >> [1]^^n *> r).
Proof.
  intros j m n r.
  st_step.
  follow (C_sweep_left (S j) (const 0) (1 >> [1]^^m *> 3 >> [1]^^n *> r)).
  st_step.
  follow (BA_sweep j (3 >> const 0) (1 >> [1]^^m *> 3 >> [1]^^n *> r)).
  finish.
Qed.

(** ** The Ackermann-like function: [g_0(m) = m+1], [g_(k+1)(m) = g_k^(2m+2)(0)]. *)
Fixpoint g (k m : nat) : nat :=
  match k with
  | O => S m
  | S k' => Nat.iter (2 * m + 2) (g k') 0%nat
  end.

(** ** Theorem 3 (Ligocki): [B(k+1, n, m) --> B(k+1, 0, g_k^n(m))] for [k >= 0]. *)

(** One step of the base case: [B(1, n+1, m) --> B(1, n, m+1)]. *)
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

Lemma iter_succ_r : forall (f : nat -> nat) n x,
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  induction n as [|n IH]; intros x.
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
      rewrite <- iter_succ_r. finish.
Qed.
