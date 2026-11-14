(** * Rules for Argon's BB(4,4) machine 44-A (TNF):
      1LB2LC3RA0RB_2RC1RZ2LB3LB_1LB2RC3RA1LD_2RC1LC3RD2LD

    The states C and D with A1 = 2LC, A2 = 3RA run Kropitz's 4-symbol Ackermann core (C = Kropitz B,
    D = Kropitz C, symbols 2 and 3 exchanged with respect to argon_scout/M44's 44-C).  The core lemmas and the
    B_rule are those of argon_scout/M44/BB44_rules.v with states and symbols renamed; the level-lift phases
    lift and lift2 are new.  The hierarchy g is M44's (BB44_rules.g), so that M44's closed forms apply. *)

From Local Require Import Individual44.
From Local Require BB44_rules.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1LB2LC3RA0RB_2RC1RZ2LB3LB_1LB2RC3RA1LD_2RC1LC3RD2LD *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, L, B)  | A, 1 => Some (2, L, C)  | A, 2 => Some (3, R, A)  | A, 3 => Some (0, R, B)
  | B, 0 => Some (2, R, C)  | B, 1 => None            | B, 2 => Some (2, L, B)  | B, 3 => Some (3, L, B)
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

Lemma B_3s : forall j l r,
  ([3]^^j *> l) <{{B}} r -->* l <{{B}} ([3]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (3 >> r)). finish_norm.
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

(** ** The two level-lift phases of 44-A *)

(** First lift: the 3-block of the level goes to the right and comes back as the new right context. *)
Theorem lift : forall j M,
  Bcfg (S (S j)) 0 M (const 0) -->* Bcfg (S (2 * M)) 3 0 ([3]^^j *> 1 >> const 0).
Proof.
  intros j M. unfold Bcfg at 1. replace (2 * M + 1) with (S (2 * M)) by lia.
  st_step.
  follow (B_3s (S (S j)) ([2]^^(S (2 * M)) *> const 0) (1 >> const 0)).
  follow (B_2s (S (2 * M)) (const 0) ([3]^^(S (S j)) *> 1 >> const 0)).
  st_step.
  follow (CA_sweep (2 * M) (2 >> const 0) ([3]^^(S (S j)) *> 1 >> const 0)).
  st_step. st_step. st_step.
  follow (Cor2 0 1 ([3]^^(S (2 * M)) *> 2 >> const 0) ([3]^^j *> 1 >> const 0)).
  follow (Cor2 (S (2 * M)) 1 (const 0) (1 >> [3]^^j *> 1 >> const 0)).
  st_step.
  follow (D_sweep_left (S (2 * M)) (const 0) (1 >> 1 >> 1 >> [3]^^j *> 1 >> const 0)).
  st_step.
  follow (CA_sweep (2 * M) (2 >> const 0) (1 >> 1 >> 1 >> [3]^^j *> 1 >> const 0)).
  finish_cfg.
Qed.

(** Later lifts: two 3s of the right context are used up, the counter n becomes 2M+3. *)
Theorem lift2 : forall K j M R0,
  Bcfg (S K) 0 M ([3]^^(S (S j)) *> R0) -->* Bcfg (S K) (2 * M + 3) 0 ([3]^^j *> R0).
Proof.
  intros K j M R0. unfold Bcfg at 1.
  st_step. st_step. st_step.
  follow (Cor2 0 1 ([3]^^(S K) *> [2]^^(2 * M + 1) *> const 0) ([3]^^j *> R0)).
  follow (Cor2 (S K) (2 * M + 1) (const 0) (1 >> [3]^^j *> R0)).
  st_step.
  follow (D_sweep_left (S K) (const 0) (1 >> [1]^^(2 * M + 1) *> 1 >> [3]^^j *> R0)).
  st_step.
  follow (CA_sweep K (2 >> const 0) (1 >> [1]^^(2 * M + 1) *> 1 >> [3]^^j *> R0)).
  finish_cfg.
Qed.

(** The halt: A reads 3 (A3 = 0RB), B reads 1 (B1 = 1RZ, undefined here). *)
Definition c_halt (K M : nat) : Q * tape :=
  (0 >> [3]^^K *> [2]^^(2 * M + 1) *> const 0) {{B}}> (1 >> const 0).

Theorem to_halt : forall K M, Bcfg K 0 M (3 >> 1 >> const 0) -->* c_halt K M.
Proof. intros K M. unfold Bcfg, c_halt. st_step. finish. Qed.

Theorem c_halt_halted : forall K M, halted tm (c_halt K M).
Proof. intros. reflexivity. Qed.

(** 91 literal steps from the blank tape to Bcfg 5 4 0 *)
Lemma start_to_B5 : c0 -->* Bcfg 5 4 0 (const 0).
Proof.
  unfold c0.
  do 91 st_step.
  finish_cfg.
Qed.
