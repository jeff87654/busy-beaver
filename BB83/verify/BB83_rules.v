(** * Rules for the BB(8,3) machine 2LH1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LD0RH_1RC2LE1LG_0LA0LD1RZ_1LD2RA2LG_2RD1LF1LG

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

From TM83 Require Import Individual83.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 2LH1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LD0RH_1RC2LE1LG_0LA0LD1RZ_1LD2RA2LG_2RD1LF1LG *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (2, L, H)  | A, 1 => Some (1, L, E)  | A, 2 => Some (2, R, A)
  | B, 0 => Some (0, L, E)  | B, 1 => Some (2, L, E)  | B, 2 => Some (2, R, B)
  | C, 0 => Some (1, R, F)  | C, 1 => Some (1, R, C)  | C, 2 => Some (2, R, B)
  | D, 0 => Some (0, R, C)  | D, 1 => Some (0, L, D)  | D, 2 => Some (0, R, H)
  | E, 0 => Some (1, R, C)  | E, 1 => Some (2, L, E)  | E, 2 => Some (1, L, G)
  | F, 0 => Some (0, L, A)  | F, 1 => Some (0, L, D)  | F, 2 => None
  | G, 0 => Some (1, L, D)  | G, 1 => Some (2, R, A)  | G, 2 => Some (2, L, G)
  | H, 0 => Some (2, R, D)  | H, 1 => Some (1, L, F)  | H, 2 => Some (1, L, G)
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

Lemma halt_from_B : forall m r,
  Bcfg 1 0 m (0 >> 2 >> r) -->*
  (1 >> ([1]^^(S (S (S (2 * m)))) *> const 0)) {{F}}> (2 >> r).
Proof.
  intros m r.
  eapply evstep_trans; [apply rule_halt |].
  st_step.  (* C0: write 1, move right, state F; F reads 2 and halts *)
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
