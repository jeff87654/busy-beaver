(** * Rules for the BB(7,4) machine 3RD1LE2RA1LF_0LE2LE2RB2RD_1RF1RC2RB0LB_0RC0LD3RC2RA_1RC2LE1LG2RF_0LA0LD3LG1RZ_1LD2RA2LG0RB

    Tape convention (busycoq): [l <{{Q}} r] has the head on [hd l]; [l {{Q}}> r] has the head on
    [hd r].  A left stream is listed from the head outwards, so the configuration
    "0^inf 1^(2m+1) 2^k B> 1^n R" is [(Bcfg k n m r)] with left stream
    [[2]^^k *> [1]^^(2m+1) *> const 0].  The halting transition F2 = 1RZ is [None].

    Four macro rules (all verified by simulation):
      B_rule : Bcfg (S k) n m r -->* Bcfg (S k) 0 (Nat.iter n (g k) m) r
      rule 2 : Bcfg (S (S k)) 0 m (0 >> r) -->* Bcfg (S k) (2*m+2) 0 (0 >> r)
      rule 3 : Bcfg 1 0 m (0 >> 1 >> r) -->* Bcfg (2*m+3) 1 0 (0 >> r)
      halt  : Bcfg 1 0 m (0 >> 2 >> r) halts
    where g 0 m = m+1, g (S k) m = Nat.iter (2m+2) (g k) 0. *)

From TM74 Require Import Individual74.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 3RD1LE2RA1LF_0LE2LE2RB2RD_1RF1RC2RB0LB_0RC0LD3RC2RA_1RC2LE1LG2RF_0LA0LD3LG1RZ_1LD2RA2LG0RB *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (3, R, D)  | A, 1 => Some (1, L, E)  | A, 2 => Some (2, R, A)  | A, 3 => Some (1, L, F)
  | B, 0 => Some (0, L, E)  | B, 1 => Some (2, L, E)  | B, 2 => Some (2, R, B)  | B, 3 => Some (2, R, D)
  | C, 0 => Some (1, R, F)  | C, 1 => Some (1, R, C)  | C, 2 => Some (2, R, B)  | C, 3 => Some (0, L, B)
  | D, 0 => Some (0, R, C)  | D, 1 => Some (0, L, D)  | D, 2 => Some (3, R, C)  | D, 3 => Some (2, R, A)
  | E, 0 => Some (1, R, C)  | E, 1 => Some (2, L, E)  | E, 2 => Some (1, L, G)  | E, 3 => Some (2, R, F)
  | F, 0 => Some (0, L, A)  | F, 1 => Some (0, L, D)  | F, 2 => Some (3, L, G)  | F, 3 => None
  | G, 0 => Some (1, L, D)  | G, 1 => Some (2, R, A)  | G, 2 => Some (2, L, G)  | G, 3 => Some (0, R, B)
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

Lemma hd_lpow_gen : forall (x : sym) n (l : Stream sym), 1 <= n -> Streams.hd ([x]^^n *> l) = x.
Proof. intros x n. destruct n as [|n]; intros l H; [lia | reflexivity]. Qed.

Lemma tl_lpow_gen : forall (x : sym) n (l : Stream sym), 1 <= n ->
  Streams.tl ([x]^^n *> l) = [x]^^(pred n) *> l.
Proof. intros x n. destruct n as [|n]; intros l H; [lia | reflexivity]. Qed.

Ltac norm_hd := repeat progress (rewrite hd_lpow_gen by lia); repeat progress (rewrite tl_lpow_gen by lia).
Ltac st_tape := autorewrite with tape_pre; simpl; norm_hd; simpl.
Ltac st_step := (eapply evstep_step || eapply progress_step); [norm_hd; prove_step | st_tape].

(** ** Elementary sweeps *)

(** E sweeping left over a block of 1s, writing 2s:
    [([1]^^j *> l) <{{E}} r -->* l <{{E}} ([2]^^j *> r)]. *)
Lemma E_left_1s : forall j l r,
  ([1]^^j *> l) <{{E}} r -->* l <{{E}} ([2]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (2 >> r)). finish_norm.
Qed.

(** G sweeping left over a block of 2s:
    [([2]^^j *> l) <{{G}} r -->* l <{{G}} ([2]^^j *> r)]. *)
Lemma G_left_2s : forall j l r,
  ([2]^^j *> l) <{{G}} r -->* l <{{G}} ([2]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (2 >> r)). finish_norm.
Qed.

(** A sweeping right over a block of 2s:
    [l {{A}}> ([2]^^j *> r) -->* ([2]^^j *> l) {{A}}> r]. *)
Lemma A_right_2s : forall j l r,
  l {{A}}> ([2]^^j *> r) -->* ([2]^^j *> l) {{A}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH (2 >> l) r). finish_norm.
Qed.

(** B sweeping right over a block of 2s:
    [l {{B}}> ([2]^^j *> r) -->* ([2]^^j *> l) {{B}}> r]. *)
Lemma B_right_2s : forall j l r,
  l {{B}}> ([2]^^j *> r) -->* ([2]^^j *> l) {{B}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH (2 >> l) r). finish_norm.
Qed.

(** C sweeping right over a block of 1s:
    [l {{C}}> ([1]^^j *> r) -->* ([1]^^j *> l) {{C}}> r]. *)
Lemma C_right_1s : forall j l r,
  l {{C}}> ([1]^^j *> r) -->* ([1]^^j *> l) {{C}}> r.
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH (1 >> l) r). finish_norm.
Qed.

(** ** The EGA loop: moving the 1-block from left to right.

    [B] on a 1 hands over to [E] on the following 2.  The three-step loop
    E2 -> G1 -> A1 moves one 1 from the head-side block to the right stream:

      (2 >> [1]^^(S j) *> l) <{{E}} ([1]^^p *> 2 >> r)
          -->*  (2 >> [1]^^j *> l) <{{E}} ([1]^^(S p) *> 2 >> r). *)

Lemma EGA_cycle : forall j p l r,
  (2 >> ([1]^^(S j) *> l)) <{{E}} ([1]^^p *> 2 >> r) -->*
  (2 >> ([1]^^j *> l)) <{{E}} ([1]^^(S p) *> 2 >> r).
Proof.
  intros j p l r.
  st_step.  (* E2: write 1, move left, state G *)
  st_step.  (* G1: write 2, move right, state A *)
  st_step.  (* A1: write 1, move left, state E *)
  finish_norm.
Qed.

Lemma EGA_sweep : forall j p l r,
  (2 >> ([1]^^j *> l)) <{{E}} ([1]^^p *> 2 >> r) -->*
  (2 >> l) <{{E}} ([1]^^(p + j) *> 2 >> r).
Proof.
  induction j as [|j IH]; intros p l r.
  - replace (p + 0) with p by lia. finish.
  - follow (EGA_cycle j p l r).
    follow (IH (S p) l r).
    replace (p + S j) with (S p + j) by lia.
    finish_norm.
Qed.

(** ** Exit of the EGA loop: the left 1-block is exhausted.  E2 writes a last 1,
    G0/D0 hand over to C, which walks right over the accumulated 1s. *)

Lemma EGA_exit : forall j r,
  (2 >> const 0) <{{E}} ([1]^^j *> 2 >> r) -->*
  (2 >> ([1]^^(S (S j)) *> const 0)) {{B}}> r.
Proof.
  intros j r.
  st_step.  (* E2: write 1, move left, state G; head = hd (const 0) = 0 *)
  st_step.  (* G0: write 1, move left, state D; head = 0 *)
  st_step.  (* D0: write 0, move right, state C *)
  change (((0 >> const 0) {{C}}> ([1]^^(S (S j)) *> 2 >> r)) -->*
    ((2 >> ([1]^^(S (S j)) *> const 0)) {{B}}> r)).
  follow (C_right_1s (S (S j)) (0 >> const 0) (2 >> r)).
  st_step.  (* C2: write 2, move right, state B *)
  apply evstep_refl'.
  simpl. rewrite <- (const_unfold sym S0). reflexivity.
Qed.

(** ** The B configurations: [Bcfg k n m r = 0^inf 1^(2m+1) 2^k B> 1^n r]. *)

Definition Bcfg (k n m : nat) (r : Stream sym) : Q * tape :=
  ([2]^^k *> [1]^^(2 * m + 1) *> const 0) {{B}}> ([1]^^n *> r).

Ltac finish_cfg := apply evstep_refl'; unfold Bcfg; norm_nat;
  try (rewrite lpow_snoc); try reflexivity; lia_refl.

(** ** One step of the base case: [B(1, n+1, m) --> B(1, n, m+1)]. *)

Lemma B1_step : forall n m r,
  Bcfg 1 (S n) m r -->* Bcfg 1 n (S m) r.
Proof.
  intros n m r.
  unfold Bcfg.
  st_step.  (* B1: write 2, move left, state E *)
  st_step.  (* E2: write 1, move left, state G *)
  st_step.  (* G1: write 2, move right, state A *)
  st_step.  (* A1: write 1, move left, state E *)
  assert (Hp : Init.Nat.pred (m + (m + 0) + 1) = m + (m + 0)) by lia.
  rewrite Hp.
  follow (EGA_sweep (m + (m + 0)) 1 (const 0) ([1]^^n *> r)).
  follow (EGA_exit (1 + (m + (m + 0))) ([1]^^n *> r)).
  unfold Bcfg.
  apply evstep_refl'.
  norm_nat; simpl; lia_refl.
Qed.

(** ** The Ackermann-like function: [g_0(m) = m+1], [g_(k+1)(m) = g_k^(2m+2)(0)]. *)

Fixpoint g (k m : nat) : nat :=
  match k with
  | O => S m
  | S k' => Nat.iter (2 * m + 2) (g k') 0%nat
  end.

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

(** ** Exit: walk the 2-block left, then come back through C and B. *)

Lemma EGA_exit_gen : forall j p r,
  (2 >> ([2]^^(S j) *> const 0)) <{{E}} ([1]^^(S p) *> 2 >> r) -->*
  Bcfg (S j) (S (S p)) 0 (2 >> r).
Proof.
  intros j p r.
  st_step.  (* E2 *)
  follow (G_left_2s (S j) (const 0) ([1]^^(S (S p)) *> 2 >> r)).
  st_step.  (* G0 *)
  st_step.  (* D0 *)
  follow (C_right_1s 1 (0 >> const 0) (2 >> [2]^^j *> 1 >> 1 >> [1]^^p *> 2 >> r)).
  st_step.  (* C2 *)
  follow (B_right_2s j (2 >> 1 >> 0 >> const 0) (1 >> 1 >> [1]^^p *> 2 >> r)).
  unfold Bcfg. apply evstep_refl'.
  norm_nat. simpl. rewrite <- (const_unfold sym S0). rewrite !lpow_snoc. reflexivity.
Qed.

(** ** Cycle moving one 1 past a block of 2s (E -> G -> A -> E). *)

Lemma EGAA_cycle : forall j m p l r,
  (2 >> ([2]^^j *> [1]^^(S m) *> l)) <{{E}} ([1]^^p *> 2 >> r) -->*
  (2 >> ([2]^^j *> [1]^^m *> l)) <{{E}} ([1]^^(S p) *> 2 >> r).
Proof.
  intros j m p l r.
  st_step.  (* E2 *)
  destruct j as [|j'].
  - st_step.  (* G1 *)
    st_step.  (* A1 *)
    finish_norm.
  - follow (G_left_2s (S j') ([1]^^(S m) *> l) (1 >> [1]^^p *> 2 >> r)).
    st_step.  (* G1 *)
    follow (A_right_2s (S j') (2 >> [1]^^m *> l) (1 >> [1]^^p *> 2 >> r)).
    st_step.  (* A1 *)
    finish_norm.
Qed.

Lemma EGAA_sweep : forall j m p l r,
  (2 >> ([2]^^j *> [1]^^m *> l)) <{{E}} ([1]^^p *> 2 >> r) -->*
  (2 >> ([2]^^j *> l)) <{{E}} ([1]^^(p + m) *> 2 >> r).
Proof.
  intros j; induction m as [|m IHm]; intros p l r.
  - replace (p + 0) with p by lia. finish.
  - follow (EGAA_cycle j m p l r).
    follow (IHm (S p) l r).
    replace (p + S m) with (S p + m) by lia.
    finish_norm.
Qed.

(** ** The generalised turnaround: from B(k+2, n+1, m) to B(k+1, 2m+2, 0). *)

Lemma turnaround : forall j m n r,
  Bcfg (S (S j)) (S n) m r -->*
  Bcfg (S j) (S (S (2 * m))) 0 (2 >> [1]^^n *> r).
Proof.
  intros j m n r.
  unfold Bcfg.
  st_step.  (* B1 *)
  replace (m + (m + 0) + 1) with (S (2 * m)) by lia.
  follow (EGAA_cycle (S j) (2 * m) 0 (const 0) ([1]^^n *> r)).
  replace (m + (m + 0)) with (2 * m) by lia.
  follow (EGAA_sweep (S j) (2 * m) 1 (const 0) ([1]^^n *> r)).
  assert (HE : 1 + 2 * m = S (2 * m)) by lia.
  rewrite HE.
  follow (EGA_exit_gen j (2 * m) ([1]^^n *> r)).
  unfold Bcfg. finish_cfg.
Qed.

(** ** The main rule: [B(k+1, n, m) -->* B(k+1, 0, g_k^n(m))]. *)

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
    + follow (turnaround k m n r).
      assert (E : Nat.iter (S (S (2 * m))) (g k) 0%nat = g (S k) m).
      { assert (E2 : S (S (2 * m)) = 2 * m + 2) by lia. rewrite E2. reflexivity. }
      follow (IHk (S (S (2 * m))) 0%nat (2 >> [1]^^n *> r)).
      rewrite E.
      st_step.  (* B2: write 2, move right, state B *)
      follow (IHn (g (S k) m) r).
      rewrite <- iter_succ_r. finish.
Qed.

(** ** The same loops with an arbitrary marker symbol in the right stream (used by rule 2). *)

Lemma EGAA_cycle_x : forall j m p l r x,
  (2 >> ([2]^^j *> [1]^^(S m) *> l)) <{{E}} ([1]^^p *> x >> r) -->*
  (2 >> ([2]^^j *> [1]^^m *> l)) <{{E}} ([1]^^(S p) *> x >> r).
Proof.
  intros j m p l r x.
  st_step.  (* E2 *)
  destruct j as [|j'].
  - st_step.  (* G1 *)
    st_step.  (* A1 *)
    finish_norm.
  - follow (G_left_2s (S j') ([1]^^(S m) *> l) (1 >> [1]^^p *> x >> r)).
    st_step.  (* G1 *)
    follow (A_right_2s (S j') (2 >> [1]^^m *> l) (1 >> [1]^^p *> x >> r)).
    st_step.  (* A1 *)
    finish_norm.
Qed.

Lemma EGAA_sweep_x : forall j m p l r x,
  (2 >> ([2]^^j *> [1]^^m *> l)) <{{E}} ([1]^^p *> x >> r) -->*
  (2 >> ([2]^^j *> l)) <{{E}} ([1]^^(p + m) *> x >> r).
Proof.
  intros j; induction m as [|m IHm]; intros p l r x.
  - replace (p + 0) with p by lia. finish.
  - follow (EGAA_cycle_x j m p l r x).
    follow (IHm (S p) l r x).
    replace (p + S m) with (S p + m) by lia.
    finish_norm.
Qed.

Lemma EGA_exit_gen_x : forall j p r x,
  (2 >> ([2]^^(S j) *> const 0)) <{{E}} ([1]^^(S p) *> x >> r) -->*
  Bcfg (S j) (S (S p)) 0 (x >> r).
Proof.
  intros j p r x.
  st_step.  (* E2 *)
  follow (G_left_2s (S j) (const 0) ([1]^^(S (S p)) *> x >> r)).
  st_step.  (* G0 *)
  st_step.  (* D0 *)
  follow (C_right_1s 1 (0 >> const 0) (2 >> [2]^^j *> 1 >> 1 >> [1]^^p *> x >> r)).
  st_step.  (* C2 *)
  follow (B_right_2s j (2 >> 1 >> 0 >> const 0) (1 >> 1 >> [1]^^p *> x >> r)).
  unfold Bcfg. apply evstep_refl'.
  norm_nat. simpl. rewrite <- (const_unfold sym S0). rewrite !lpow_snoc. reflexivity.
Qed.

(** ** Rule 2: [B(k+2, 0, m) x -->* B(k+1, 2m+2, 0) x]. *)

Lemma rule2 : forall j m r,
  Bcfg (S (S j)) 0 m (0 >> r) -->*
  Bcfg (S j) (S (S (2 * m))) 0 (0 >> r).
Proof.
  intros j m r.
  unfold Bcfg.
  st_step.  (* B0 *)
  replace (m + (m + 0) + 1) with (S (2 * m)) by lia.
  follow (EGAA_cycle_x (S j) (2 * m) 0 (const 0) r 0).
  replace (m + (m + 0)) with (2 * m) by lia.
  follow (EGAA_sweep_x (S j) (2 * m) 1 (const 0) r 0).
  assert (HE : 1 + 2 * m = S (2 * m)) by lia.
  rewrite HE.
  follow (EGA_exit_gen_x j (2 * m) r 0).
  unfold Bcfg. finish_cfg.
Qed.

(** ** Rule 3a, phase B: C on the marker 0 with a block of 1s to its left
    turns that block into a block of 2s and returns in state B. *)

Lemma rule3a_phaseB : forall p r,
  1 <= p ->
  (0 >> ([1]^^p *> const 0)) <{{C}} (0 >> r) -->*
  Bcfg p 1 0 (0 >> r).
Proof.
  intros p r Hp.
  st_step.  (* C0: write 1, move right, state F *)
  st_step.  (* F0: write 0, move left, state A *)
  destruct p as [|p'].
  - lia.
  - st_step.  (* A1: write 1, move left, state E *)
    follow (E_left_1s (S p') (const 0) (1 >> 0 >> r)).
    st_step.  (* E0: write 1, move right, state C *)
    st_step.  (* C2: write 2, move right, state B *)
    follow (B_right_2s p' (2 >> 1 >> const 0) (1 >> 0 >> r)).
    unfold Bcfg. apply evstep_refl'. norm_nat. rewrite lpow_snoc. reflexivity.
Qed.

(** ** Rule 3a, phase A: the initial descent leaves C on the 0 marker. *)

Lemma rule3a_phaseA : forall m r,
  Bcfg 1 0 m (0 >> 0 >> r) -->*
  (0 >> ([1]^^(S (S (S (2 * m)))) *> const 0)) <{{C}} (0 >> r).
Proof.
  intros m r.
  unfold Bcfg.
  st_step.  (* B0 *)
  st_step.  (* E2 *)
  st_step.  (* G1 *)
  st_step.  (* A1 *)
  replace (m + (m + 0)) with (2 * m) by lia.
  replace (Init.Nat.pred (2 * m + 1)) with (2 * m) by lia.
  follow (EGAA_sweep_x 0 (2 * m) 1 (const 0) (0 >> r) 0).
  assert (H1 : 1 + 2 * m = S (2 * m)) by lia. rewrite H1.
  st_step.  (* E2 *)
  st_step.  (* G0 *)
  st_step.  (* D0 *)
  follow (C_right_1s (S (S (S (2 * m)))) (0 >> const 0) (0 >> 0 >> r)).
  apply evstep_refl'. simpl.
  rewrite <- (const_unfold sym S0). reflexivity.
Qed.

(** ** Rule 3a: [B(1, 0, m) 0 0 -->* B(2m+3, 1, 0) 0]. *)

Lemma rule3a : forall m r,
  Bcfg 1 0 m (0 >> 0 >> r) -->*
  Bcfg (2 * m + 3) 1 0 (0 >> r).
Proof.
  intros m r.
  replace (2 * m + 3) with (S (S (S (2 * m)))) by lia.
  eapply evstep_trans; [apply rule3a_phaseA |].
  apply rule3a_phaseB. lia.
Qed.

(** ** Halting: [B(1, 0, m) 0 2] halts. *)

Lemma rule_halt : forall m r,
  Bcfg 1 0 m (0 >> 2 >> r) -->*
  (0 >> ([1]^^(S (S (S (2 * m)))) *> const 0)) <{{C}} (2 >> r).
Proof.
  intros m r.
  unfold Bcfg.
  st_step.  (* B0 *)
  st_step.  (* E2 *)
  st_step.  (* G1 *)
  st_step.  (* A1 *)
  replace (m + (m + 0)) with (2 * m) by lia.
  replace (Init.Nat.pred (2 * m + 1)) with (2 * m) by lia.
  follow (EGAA_sweep_x 0 (2 * m) 1 (const 0) (2 >> r) 0).
  assert (H1 : 1 + 2 * m = S (2 * m)) by lia. rewrite H1.
  st_step.  (* E2 *)
  st_step.  (* G0 *)
  st_step.  (* D0 *)
  replace (m + (m + 0)) with (2 * m) by lia.
  follow (C_right_1s (S (S (S (2 * m)))) (0 >> const 0) (0 >> 2 >> r)).
  apply evstep_refl'. simpl.
  rewrite <- (const_unfold sym S0). reflexivity.
Qed.

(** In BB74, F on 2 is NOT a halt (F2 = 3LG); this lemma just reaches it. *)
Lemma reach_F_on_2 : forall m r,
  Bcfg 1 0 m (0 >> 2 >> r) -->*
  (1 >> ([1]^^(S (S (S (2 * m)))) *> const 0)) {{F}}> (2 >> r).
Proof.
  intros m r.
  eapply evstep_trans; [apply rule_halt |].
  st_step.  (* C0: write 1, move right, state F *)
  apply evstep_refl'. reflexivity.
Qed.

(** ** D sweeping left over a block of 1s, writing 0s:
    [([1]^^j *> l) <{{D}} r -->* l <{{D}} ([0]^^j *> r)]. *)
Lemma D_left_1s : forall j l r,
  ([1]^^j *> l) <{{D}} r -->* l <{{D}} ([0]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (0 >> r)). finish_norm.
Qed.

(** ** The fixed 13-step cleanup that closes rule 3b.
    From C on the base 0 with [j+1] zeros to its right, it produces
    [B(2,1,0)] with [j] zeros of tail. *)
Lemma lpow_pred2_eq : forall j r, 2 <= j ->
  0 >> [0]^^(Init.Nat.pred (Init.Nat.pred j)) *> r = [0]^^(j - 1) *> r.
Proof.
  intros j r Hj.
  replace (Init.Nat.pred (Init.Nat.pred j)) with (j - 2) by lia.
  replace (j - 1) with (S (j - 2)) by lia.
  reflexivity.
Qed.

Lemma rule3b_cleanup : forall j r,
  4 <= j ->
  (0 >> const 0) {{C}}> ([0]^^(S j) *> r) -->*
  Bcfg 2 1 0 ([0]^^(j - 1) *> r).
Proof.
  intros j r Hj.
  st_step.  (* C0: write 1, move right, state F *)
  st_step.  (* F0: write 0, move left, state A *)
  st_step.  (* A1: write 1, move left, state E *)
  st_step.  (* E0: write 1, move right, state C *)
  st_step.  (* C1: write 1, move right, state C *)
  st_step.  (* C0: write 1, move right, state F *)
  st_step.  (* F0: write 0, move left, state A *)
  st_step.  (* A1: write 1, move left, state E *)
  st_step.  (* E1: write 2, move left, state E *)
  st_step.  (* E0: write 1, move right, state C *)
  st_step.  (* C2: write 2, move right, state B *)
  st_step.  (* B2: write 2, move right, state B *)
  st_step.  (* B2: write 2, move right, state B *)
  unfold Bcfg. apply evstep_refl'. norm_nat. simpl.
  rewrite lpow_pred2_eq by lia. reflexivity.
Qed.

(** ** Rule 3b, phase A: same descent as rule 3a, but with marker 1. *)
Lemma rule3b_phaseA : forall m r,
  Bcfg 1 0 m (0 >> 1 >> r) -->*
  (0 >> ([1]^^(S (S (S (2 * m)))) *> const 0)) <{{C}} (1 >> r).
Proof.
  intros m r.
  unfold Bcfg.
  st_step.  (* B0 *)
  st_step.  (* E2 *)
  st_step.  (* G1 *)
  st_step.  (* A1 *)
  replace (m + (m + 0)) with (2 * m) by lia.
  replace (Init.Nat.pred (2 * m + 1)) with (2 * m) by lia.
  follow (EGAA_sweep_x 0 (2 * m) 1 (const 0) (1 >> r) 0).
  assert (H1 : 1 + 2 * m = S (2 * m)) by lia. rewrite H1.
  st_step.  (* E2 *)
  st_step.  (* G0 *)
  st_step.  (* D0 *)
  follow (C_right_1s (S (S (S (2 * m)))) (0 >> const 0) (0 >> 1 >> r)).
  apply evstep_refl'. simpl.
  rewrite <- (const_unfold sym S0). reflexivity.
Qed.

(** ** Rule 3b: [B(1, 0, m) 0 1 r -->* B(2, 1, 0) 0^(2m+3) r]. *)
Lemma rule3b : forall m r,
  Bcfg 1 0 m (0 >> 1 >> r) -->*
  Bcfg 2 1 0 ([0]^^(2 * m + 3) *> r).
Proof.
  intros m r.
  eapply evstep_trans; [apply rule3b_phaseA |].
  st_step.  (* C0: write 1, move right, state F *)
  st_step.  (* F1: write 0, move left, state D *)
  follow (D_left_1s (S (S (S (S (2 * m))))) (const 0) (0 >> r)).
  st_step.  (* D0: write 0, move right, state C *)
  replace (m + (m + 0)) with (2 * m) by lia.
  rewrite lpow_snoc.
  change ((0 >> const 0) {{C}}> ([0]^^(S (S (S (S (S (2 * m)))))) *> r) -->*
          Bcfg 2 1 0 ([0]^^(2 * m + 3) *> r)).
  eapply evstep_trans; [apply rule3b_cleanup with (j := S (S (S (S (2 * m))))); lia |].
  unfold Bcfg. apply evstep_refl'. replace (S (S (S (S (2 * m)))) - 1) with (2 * m + 3) by lia. reflexivity.
Qed.

(** ** BB74's halting rule: [B(1, 0, m) 0 3 r] reaches F on the 3 and halts. *)

Lemma rule_halt_x : forall m r x,
  Bcfg 1 0 m (0 >> x >> r) -->*
  (0 >> ([1]^^(S (S (S (2 * m)))) *> const 0)) <{{C}} (x >> r).
Proof.
  intros m r x.
  unfold Bcfg.
  st_step.  (* B0 *)
  st_step.  (* E2 *)
  st_step.  (* G1 *)
  st_step.  (* A1 *)
  replace (m + (m + 0)) with (2 * m) by lia.
  replace (Init.Nat.pred (2 * m + 1)) with (2 * m) by lia.
  follow (EGAA_sweep_x 0 (2 * m) 1 (const 0) (x >> r) 0).
  assert (H1 : 1 + 2 * m = S (2 * m)) by lia. rewrite H1.
  st_step.  (* E2 *)
  st_step.  (* G0 *)
  st_step.  (* D0 *)
  replace (m + (m + 0)) with (2 * m) by lia.
  follow (C_right_1s (S (S (S (2 * m)))) (0 >> const 0) (0 >> x >> r)).
  apply evstep_refl'. simpl.
  rewrite <- (const_unfold sym S0). reflexivity.
Qed.

(** The halt configuration has F reading a 3; [F3 = 1RZ] halts. *)
Lemma halt_from_B : forall m r,
  Bcfg 1 0 m (0 >> 3 >> r) -->*
  (1 >> ([1]^^(S (S (S (2 * m)))) *> const 0)) {{F}}> (3 >> r).
Proof.
  intros m r.
  eapply evstep_trans; [apply (rule_halt_x m r 3) |].
  st_step.  (* C0: write 1, move right, state F; F reads 3 and halts *)
  apply evstep_refl'. reflexivity.
Qed.

(** ** BB74's new 2-marker rule.  F on 2 (F2 = 3LG) drives a loop that moves
    the 3 marker left through the block of 1s, appending one 1 after it per
    cycle.  This is the G/A/F loop: G1 -> A3 -> F2 -> G. *)

Lemma G31_cycle : forall j p l r,
  (([1]^^(S j) *> l) <{{G}} (3 >> [1]^^p *> r)) -->*
  (([1]^^j *> l) <{{G}} (3 >> [1]^^(S p) *> r)).
Proof.
  intros j p l r.
  st_step.  (* G1: write 2, move right, state A *)
  st_step.  (* A3: write 1, move left, state F *)
  st_step.  (* F2: write 3, move left, state G *)
  finish_norm.
Qed.

Lemma G31_sweep : forall j p l r,
  (([1]^^j *> l) <{{G}} (3 >> [1]^^p *> r)) -->*
  (l <{{G}} (3 >> [1]^^(p+j) *> r)).
Proof.
  intros j; induction j as [|j IHj]; intros p l r.
  - replace (p + 0) with p by lia. finish.
  - follow (G31_cycle j p l r).
    follow (IHj (S p) l r).
    replace (S p + j) with (p + S j) by lia.
    finish_norm.
Qed.

(** Reach the G/A/F loop: after F on 2, F2 = 3LG puts G on the 1-block. *)
Lemma rule3c_to_loop : forall m r,
  Bcfg 1 0 m (0 >> 2 >> r) -->*
  ([1]^^(S (S (S (S (2 * m))))) *> const 0) <{{G}} (3 >> r).
Proof.
  intros m r.
  eapply evstep_trans; [apply (reach_F_on_2 m r) |].
  st_step.  (* F2: write 3, move left, state G *)
  finish_norm.
Qed.

(** After the loop: G on the base 0, right = 3 >> [1]^p r.  Four fixed steps
    (G0,D0,C1,C3) give B on a 1 with right = 0 >> [1]^p r. *)
Lemma post3c_A : forall p r, 1 <= p ->
  (const 0) <{{G}} (3 >> [1]^^p *> r) -->*
  (1 >> const 0) <{{B}} (0 >> [1]^^p *> r).
Proof.
  intros p r Hp.
  st_step.  (* G0: write 1, move left, state D *)
  st_step.  (* D0: write 0, move right, state C *)
  st_step.  (* C1: write 1, move right, state C *)
  st_step.  (* C3: write 0, move left, state B *)
  apply evstep_refl'.
  autorewrite with tape_post.
  reflexivity.
Qed.

(** Nine fixed steps: B on 1 -> D on 0 with right = 111 0 [1]^p r. *)
Lemma post3c_B : forall p r, 1 <= p ->
  (1 >> const 0) <{{B}} (0 >> [1]^^p *> r) -->*
  (const 0) <{{D}} (1 >> 1 >> 1 >> 0 >> [1]^^p *> r).
Proof.
  intros p r Hp.
  st_step.  (* B1 *)
  st_step.  (* E0 *)
  st_step.  (* C2 *)
  st_step.  (* B0 *)
  st_step.  (* E2 *)
  st_step.  (* G1 *)
  st_step.  (* A1 *)
  st_step.  (* E2 *)
  st_step.  (* G0 *)
  apply evstep_refl'. autorewrite with tape_post. reflexivity.
Qed.


(** From D on 0 after the fixed descent, sweep C right over three 1s, then
    five fixed steps give D on 1 with [0] followed by the remaining 1-block. *)
Lemma post3c_C : forall p r, 1 <= p ->
  (const 0) <{{D}} (1 >> 1 >> 1 >> 0 >> [1]^^p *> r) -->*
  (0 >> const 0) <{{D}} ([0]^^4 *> (0 >> [1]^^(pred p) *> r)).
Proof.
  intros p r Hp.
  st_step. st_step. st_step. st_step. st_step.
  st_step.  (* F1 *)
  change (([1]^^4 *> (0 >> const 0)) <{{D}} (0 >> [1]^^(pred p) *> r) -->* ((0 >> const 0) <{{D}} ([0]^^4 *> (0 >> [1]^^(pred p) *> r)))).
  follow (D_left_1s 4 (0 >> const 0) (0 >> [1]^^(pred p) *> r)).
  apply evstep_refl'. autorewrite with tape_post. reflexivity.
Qed.

(** The final 14 fixed steps produce B(2,1,0) with tail 000 [1]^(p-1) r. *)
Lemma post3c_D : forall p r, 2 <= p ->
  (0 >> const 0) <{{D}} ([0]^^4 *> (0 >> [1]^^(pred p) *> r)) -->*
  Bcfg 2 1 0 ([0;0;0] *> [1]^^(pred p) *> r).
Proof.
  intros p r Hp.
  st_step. st_step. st_step. st_step. st_step.
  st_step. st_step. st_step. st_step. st_step.
  st_step. st_step. st_step. st_step.
  apply evstep_refl'.
  unfold Bcfg. simpl. reflexivity.
Qed.

(** ** The full rule 3c: [B(1,0,m) 0 2 r -->* B(2,1,0) 0^3 1^(2m+3) r]. *)
Theorem rule3c : forall m r,
  Bcfg 1 0 m (0 >> 2 >> r) -->*
  Bcfg 2 1 0 ([0;0;0] *> [1]^^(2 * m + 3) *> r).
Proof.
  intros m r.
  eapply evstep_trans; [apply (rule3c_to_loop m r) |].
  change (([1]^^(S (S (S (S (2*m))))) *> const 0) <{{G}} (3 >> r) -->*
          (Bcfg 2 1 0 ([0;0;0] *> [1]^^(2 * m + 3) *> r))).
  replace (S (S (S (S (2*m))))) with (2*m + 4) by lia.
  follow (G31_sweep (2*m+4) 0 (const 0) r).
  replace (0 + (2*m+4)) with (2*m+4) by lia.
  follow (post3c_A (2*m+4) r ltac:(lia)).
  follow (post3c_B (2*m+4) r ltac:(lia)).
  follow (post3c_C (2*m+4) r ltac:(lia)).
  follow (post3c_D (2*m+4) r ltac:(lia)).
  apply evstep_refl'. unfold Bcfg. simpl.
  replace (m + (m + 0)) with (2*m) by lia.
  replace (Nat.pred (2 * m + 4)) with (2 * m + 3) by lia.
  reflexivity.
Qed.
