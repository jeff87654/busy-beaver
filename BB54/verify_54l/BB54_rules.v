(** * Rules for the new BB(5,4) f_{omega+1} champion:
      1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE *)

(** Tape convention (busycoq): [l <{{Q}} r] has the head on [hd l]; [l {{Q}}> r] has the head on
    [hd r].  A left stream is listed from the head outwards, so the Ligocki word
    "0^inf 3^(2m+1) 2^k A> 1^n R" is [(Bcfg k n m r)] with left stream
    [[2]^^k *> [3]^^(2m+1) *> const 0].  The halting transition B1 = 1RZ is [None].

    In strict Tree Normal Form (TNF):
      - State C is Kropitz's B, state E is Kropitz's C;
      - State B is the counter-plant / sweep / halt state;
      - State D is the 1-state f_omega stepper. *)

From Local Require Import Individual54.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (3, L, C)  | A, 2 => Some (1, L, D)  | A, 3 => Some (2, R, A)
  | B, 0 => Some (2, R, C)  | B, 1 => None            | B, 2 => Some (2, L, B)  | B, 3 => Some (2, L, B)
  | C, 0 => Some (1, L, D)  | C, 1 => Some (3, R, C)  | C, 2 => Some (1, L, E)  | C, 3 => Some (2, R, A)
  | D, 0 => Some (3, R, C)  | D, 1 => Some (0, L, B)  | D, 2 => Some (1, L, D)  | D, 3 => Some (3, L, D)
  | E, 0 => Some (3, R, C)  | E, 1 => Some (1, L, C)  | E, 2 => Some (3, L, E)  | E, 3 => Some (2, R, E)
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

Lemma block_snoc : forall (c : sym) (p : nat) (x : Stream sym),
  ([c]^^p *> (c >> x)) = ([c]^^(S p) *> x).
Proof.
  intros c p x. apply lpow_snoc.
Qed.

Lemma lpow_cat : forall (c : sym) a b r,
  [c]^^a *> ([c]^^b *> r) = [c]^^(a + b) *> r.
Proof.
  intros c a b r. induction a as [|a IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
Ltac finish_norm := apply evstep_refl'; norm_nat; try (rewrite lpow_snoc); try reflexivity; lia_refl.

Ltac st_tape := autorewrite with tape_pre; simpl.
Ltac st_step := (eapply evstep_step || eapply progress_step); [prove_step | st_tape].

(** ** Elementary sweeps *)

Lemma E_sweep_left : forall j l r,
  ([2]^^j *> l) <{{E}} r -->* l <{{E}} ([3]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (3 >> r)). finish_norm.
Qed.

Lemma E_right_3s : forall j l r,
  l {{E}}> [3]^^j *> r -->* ([2]^^j *> l) {{E}}> r.
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

Lemma C_1s : forall j l r,
  l {{C}}> 1 >> ([1]^^j *> r) -->* ([3]^^(S j) *> l) {{C}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - step. finish.
  - step. follow (IH (3 >> l) r). finish_norm.
Qed.

Lemma CA_sweep : forall j l r,
  l {{C}}> 3 >> ([3]^^j *> r) -->* ([2]^^(S j) *> l) {{A}}> r.
Proof.
  intros j l r. step. follow (A_3s j (2 >> l) r). finish_norm.
Qed.

Lemma B_2s : forall j l r,
  ([2]^^j *> l) <{{B}} r -->* l <{{B}} ([2]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (2 >> r)). finish_norm.
Qed.

Lemma B_3s : forall j l r,
  ([3]^^j *> l) <{{B}} r -->* l <{{B}} ([2]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (2 >> r)). finish_norm.
Qed.

Lemma D_2s : forall j l r,
  ([2]^^j *> l) <{{D}} r -->* l <{{D}} ([1]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (1 >> r)). finish_norm.
Qed.

Lemma D_3s : forall j l r,
  ([3]^^j *> l) <{{D}} r -->* l <{{D}} ([3]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (3 >> r)). finish_norm.
Qed.

(** ** Kropitz Ackermann core (C = Kropitz B, E = Kropitz C) *)

Lemma L1 : forall k l r,
  ([2]^^(S k) *> 3 >> l) <{{C}} r -->* ([2]^^(S k) *> l) <{{C}} (1 >> r).
Proof.
  intros k l r.
  step.
  follow (E_sweep_left k (3 >> l) (1 >> r)).
  step.
  follow (E_right_3s k (2 >> l) (1 >> r)).
  step.
  finish_norm.
Qed.

Lemma Cor2 : forall k m l r,
  ([2]^^(S k) *> [3]^^m *> l) <{{C}} r -->* ([2]^^(S k) *> l) <{{C}} ([1]^^m *> r).
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
  ([2]^^(S (S j)) *> const 0) <{{C}} ([1]^^m *> 3 >> [1]^^n *> r) -->*
  Bcfg (S j) (S m) 0 (3 >> [1]^^n *> r).
Proof.
  intros j m n r.
  st_step.
  follow (E_sweep_left (S j) (const 0) (1 >> [1]^^m *> 3 >> [1]^^n *> r)).
  st_step.
  follow (CA_sweep j (3 >> const 0) (1 >> [1]^^m *> 3 >> [1]^^n *> r)).
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
  follow (C_1s (2 * m + 1) (3 >> const 0) (3 >> [1]^^n *> r)).
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

(** ** Blank-tape startup: 24 steps from [c0] to [Bcfg 5 1 0 (const 0)] *)

Definition c_mid12 : Q * tape :=
  ([3]^^4 *> const 0) {{C}}> (1 >> const 0).

Lemma start_12a : c0 -->* c_mid12.
Proof.
  unfold c0, c_mid12.
  do 12 st_step.
  finish_norm.
Qed.

Lemma start_12b : c_mid12 -->* Bcfg 5 1 0 (const 0).
Proof.
  unfold c_mid12.
  do 13 st_step.
  finish_cfg.
Qed.

Lemma start_to_B5 : c0 -->* Bcfg 5 1 0 (const 0).
Proof.
  eapply evstep_trans; [apply start_12a | apply start_12b].
Qed.

(** ** Phase 2 ([B_sweep]): plant halting marker [0 1 1] on right and convert
    [3^(2m+1) 2^5] into the outer [f_{omega+1}] unary counter [[2]^^(2m+5)]! *)

Theorem B_sweep : forall m,
  Bcfg 5 0 m (const 0) -->*
  Bcfg 1 0 1 ([2]^^(2 * m + 5) *> (0 >> (1 >> (1 >> const 0)))).
Proof.
  intros m.
  unfold Bcfg at 1; simpl.
  st_step. st_step. st_step. st_step. st_step.
  follow (B_2s 5 ([3]^^(2 * m + 1) *> const 0) (0 >> (1 >> (1 >> const 0)))).
  follow (B_3s (2 * m + 1) (const 0) ([2]^^5 *> (0 >> (1 >> (1 >> const 0))))).
  rewrite (lpow_cat 2 (2 * m + 1) 5 (0 >> (1 >> (1 >> const 0)))).
  replace (2 * m + 1 + 5) with (S (2 * m + 5)) by lia.
  change ([2]^^(S (2 * m + 5)) *> (0 >> (1 >> (1 >> const 0))))
    with (2 >> ([2]^^(2 * m + 5) *> (0 >> (1 >> (1 >> const 0))))).
  st_step. st_step. st_step. st_step. st_step.
  follow (B1_step 0 0 ([2]^^(2 * m + 5) *> (0 >> (1 >> (1 >> const 0))))).
  finish.
Qed.

(** ** Phase 3 ([D_step] and [D_chain]): 1-state [f_omega] stepper iterating [c] times *)

Theorem D_step : forall k m r,
  Bcfg (S k) 0 m (2 >> r) -->*
  Bcfg (S (2 * m)) 0 (Nat.iter (S (S k)) (g (2 * m)) 0%nat) r.
Proof.
  intros k m r.
  unfold Bcfg at 1; simpl.
  st_step.
  change (2 >> ([2]^^k *> ([3]^^(2 * m + 1) *> const 0)))
    with ([2]^^(S k) *> ([3]^^(2 * m + 1) *> const 0)).
  follow (D_2s (S k) ([3]^^(2 * m + 1) *> const 0) (1 >> r)).
  rewrite (block_snoc 1 (S k) r).
  follow (D_3s (2 * m + 1) (const 0) ([1]^^(S (S k)) *> r)).
  replace (2 * m + 1) with (S (2 * m)) by lia.
  change ([3]^^(S (2 * m)) *> ([1]^^(S (S k)) *> r))
    with (3 >> ([3]^^(2 * m) *> ([1]^^(S (S k)) *> r))).
  st_step.
  follow (CA_sweep (2 * m) (3 >> const 0) ([1]^^(S (S k)) *> r)).
  follow (B_rule (2 * m) (S (S k)) 0%nat r).
  finish.
Qed.

Definition step_pair (p : nat * nat) : nat * nat :=
  let '(k, m) := p in (2 * m, Nat.iter (S (S k)) (g (2 * m)) 0%nat).

Theorem D_chain : forall c k m r,
  Bcfg (S k) 0 m ([2]^^c *> r) -->*
  Bcfg (S (fst (Nat.iter c step_pair (k, m)))) 0 (snd (Nat.iter c step_pair (k, m))) r.
Proof.
  induction c as [|c IH]; intros k m r.
  - simpl. finish.
  - change ([2]^^(S c) *> r) with (2 >> ([2]^^c *> r)).
    follow (D_step k m ([2]^^c *> r)).
    follow (IH (2 * m) (Nat.iter (S (S k)) (g (2 * m)) 0%nat) r).
    rewrite (iter_succ_r step_pair c (k, m)).
    finish.
Qed.
