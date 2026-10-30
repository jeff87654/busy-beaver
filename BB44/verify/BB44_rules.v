(** * Rules for the BB(4,4) champion 0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC *)

(** Tape convention (busycoq): [l <{{Q}} r] has the head on [hd l]; [l {{Q}}> r] has the head on
    [hd r].  A left stream is listed from the head outwards, so the Ligocki word
    "0^inf 3^(2m+1) 2^k A> 1^n R" is [(Bcfg k n m r)] with left stream
    [[2]^^k *> [3]^^(2m+1) *> const 0].  The halting transition A2 = 1RZ is [None].

    Note on the port from BB(3,4): this machine differs from the BB(3,4) champion
    [1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC] only in the entries A0 (1RB vs 0LB), B0 (2LC vs 1LD)
    and in the extra state D.  All the transitions used by the descent lemmas below --
    A1 = 3LB, A3 = 2RA, B1 = 3RB, B2 = 1LC, B3 = 2RA, C0 = 3RB, C1 = 1LB, C2 = 3LC, C3 = 2RC
    (plus the halting entry A2 = 1RZ) -- are identical in the two machines, so the sweeps, the
    turnaround and the main rule port over unchanged. *)

From TM44 Require Import Individual44.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (0, L, B)  | A, 1 => Some (3, L, B)  | A, 2 => None            | A, 3 => Some (2, R, A)
  | B, 0 => Some (1, L, D)  | B, 1 => Some (3, R, B)  | B, 2 => Some (1, L, C)  | B, 3 => Some (2, R, A)
  | C, 0 => Some (3, R, B)  | C, 1 => Some (1, L, B)  | C, 2 => Some (3, L, C)  | C, 3 => Some (2, R, C)
  | D, 0 => Some (0, R, D)  | D, 1 => Some (2, R, C)  | D, 2 => Some (2, L, B)  | D, 3 => Some (0, R, A)
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

(** ** The two BB(4,4)-specific phases *)

(** The BB(4,4) champion differs from the BB(3,4) one only in A0, B0 and the extra
    state D, so Ligocki's descent (Lemma 1, Corollary 2, the turnaround and
    [B_rule]) ports over unchanged -- but the *start* of the run does not: it
    enters the descent only after two BB(4,4)-specific phases.

    Phase B (below) takes [B(2, 0, m) 0^inf] to [B(1, 2m+2, 0) 0^inf];
    phase D (below) takes [B(1, 0, m) 0^inf] to [B(2m+2, 1, 0) 2 1 3 0^inf].
    Both are stated for a symbolic [m], so the two phases are proved once and
    for all. *)

(** ** Phase B: [B(2, 0, m)] --> [B(1, 2m+2, 0)]

    The head sits on the outermost 2 of the block [2]^2 3^(2m+1); a five-step
    cycle (B2, C2, C3, C3, C1) eats one 3 of the left block and appends one 1
    to the right stream, until the 3-block is gone.  The four steps that follow
    (B2, C2, C0, B3) leave the head on a 1 in state A. *)

Lemma Bloop_step : forall m j,
  ([2]^^2 *> [3]^^(S m) *> const 0) <{{B}} ([1]^^j *> const 0) -->*
  ([2]^^2 *> [3]^^m *> const 0) <{{B}} ([1]^^(S j) *> const 0).
Proof.
  intros m j. st_step. st_step. st_step. st_step. st_step. finish.
Qed.

Lemma Bloop : forall m, forall j,
  ([2]^^2 *> [3]^^m *> const 0) <{{B}} ([1]^^j *> const 0) -->*
  ([2]^^2 *> const 0) <{{B}} ([1]^^(j + m) *> const 0).
Proof.
  induction m as [|m IH]; intros j.
  - replace (j + 0) with j by lia. finish.
  - follow (Bloop_step m j).
    replace (j + S m) with (S j + m) by lia.
    follow (IH (S j)).
    finish.
Qed.

Lemma B_phase : forall m,
  Bcfg 2 0 m (const 0) -->* Bcfg 1 (2*m+2) 0 (const 0).
Proof.
  intros m.
  st_step.
  rewrite <- const_unfold.
  follow (Bloop (2 * m + 1) 0).
  st_step. st_step. st_step. st_step.
  finish_cfg.
Qed.

(** ** Phase D: [B(1, 0, m)] --> [B(2m+2, 1, 0) 2 1 3]

    Six sub-phases, in the order in which the machine meets them:

      D1  the head enters the 3-block through A0 and a three-step cycle
          (B2, C3, C1) eats the block, one 3 at a time, each 3 replaced by a 1
          on the right;
      D2  B2 and C0 set up a run of 1s that the B1 sweep ([B_1s]) turns into 3s;
      D3  B0 enters state D; a three-step cycle (D3, A1, B0) walks left over the
          3-block, one 3 at a time;
      D4  C sweeps right over the 3-block, writing 2s;
      D5  a short detour through states B, D and A, then a C sweep left over the
          2-block, writing 3s;
      D6  C0 and B3 set up a run of 3s that the A3 sweep ([A_3s]) turns into 2s.

    The three-step cycles are the only loops; everything else is a fixed number
    of steps or one of the elementary sweeps of the BB(3,4) development. *)

(** One step of the D1 cycle: consume the nearest 3 of the left block, append a
    1 to the right stream. *)
Lemma D1_step : forall m j,
  (2 >> ([3]^^(S m) *> const 0)) <{{B}} ([1]^^j *> const 0) -->*
  (2 >> ([3]^^m *> const 0)) <{{B}} ([1]^^(S j) *> const 0).
Proof.
  intros m j. st_step. st_step. st_step. finish.
Qed.

Lemma D1_loop : forall m, forall j,
  (2 >> ([3]^^m *> const 0)) <{{B}} ([1]^^j *> const 0) -->*
  (2 >> const 0) <{{B}} ([1]^^(j + m) *> const 0).
Proof.
  induction m as [|m IH]; intros j.
  - replace (j + 0) with j by lia. finish.
  - follow (D1_step m j).
    replace (j + S m) with (S j + m) by lia.
    follow (IH (S j)).
    finish.
Qed.

(** One step of the D3 cycle (D3, A1, B0): move one cell to the left over the
    3-block. *)
Lemma D3_step : forall m j,
  ([3]^^(S (S m)) *> const 0) <{{D}} (1 >> ([3]^^j *> const 0)) -->*
  ([3]^^(S m) *> const 0) <{{D}} (1 >> ([3]^^(S j) *> const 0)).
Proof.
  intros m j. st_step. st_step. st_step. finish.
Qed.

Lemma D3_loop : forall m, forall j,
  ([3]^^(S m) *> const 0) <{{D}} (1 >> ([3]^^j *> const 0)) -->*
  (3 >> const 0) <{{D}} (1 >> ([3]^^(j + m) *> const 0)).
Proof.
  induction m as [|m IH]; intros j.
  - replace (j + 0) with j by lia. finish.
  - follow (D3_step m j).
    replace (j + S m) with (S j + m) by lia.
    follow (IH (S j)).
    finish.
Qed.

(** ** Shape normalisation.

    A block of [c]'s can be written with the extra [c] at its front or at its
    back; both denote the same stream, but Coq only sees them as equal after a
    little rewriting.  This lemma moves the extra [c] from the back to the
    front. *)
Lemma block_snoc : forall (c : sym) (p : nat) (x : Stream sym),
  ([c]^^p *> (c >> x)) = ([c]^^(S p) *> x).
Proof.
  intros c p x.
  change ((([c]^^p *> (Str_app [c] x))) = (([c]^^(S p) *> x))).
  rewrite <- (Str_app_assoc (lpow [c] p) [c] x).
  rewrite (lpow_shift [c] p).
  rewrite (Str_app_assoc [c] (lpow [c] p) x).
  reflexivity.
Qed.

(** Phase D for a symbolic number [p] of 3s in the left block. *)
Lemma D_phase_p : forall p,
  ([2] *> [3]^^p *> const 0) {{A}}> (const 0) -->*
  ([2]^^(S p) *> [3] *> const 0) {{A}}> ([1] *> (2 >> (1 >> (3 >> const 0)))).
Proof.
  intros p.
  (* D1 *)
  st_step.
  rewrite <- const_unfold.
  follow (D1_loop p 0).
  (* D2 *)
  st_step. st_step.
  follow (B_1s p (3 >> const 0) (const 0)).
  st_step.
  rewrite (block_snoc 3 p (const 0)).
  (* D3 *)
  follow (D3_loop (S p) 0).
  st_step. st_step. st_step. st_step.
  (* D4 *)
  st_step.
  follow (C_right_3s (S (S p)) (2 >> (0 >> const 0)) (const 0)).
  (* D5 *)
  st_step. st_step. st_step. st_step. st_step. st_step. st_step.
  rewrite (block_snoc 2 p (0 >> const 0)).
  follow (C_sweep_left (S p) (0 >> const 0) (1 >> (2 >> (1 >> (3 >> const 0))))).
  (* D6 *)
  st_step. st_step.
  follow (A_3s p (2 >> (3 >> const 0)) (1 >> (2 >> (1 >> (3 >> const 0))))).
  rewrite (block_snoc 2 p (3 >> const 0)).
  finish.
Qed.

(** Phase D, in the notation of the configuration family: the machine reaches
    [B(2m+2, 1, 0) 2 1 3 0^inf] from [B(1, 0, m) 0^inf]. *)
Lemma D_phase : forall m,
  Bcfg 1 0 m (const 0) -->* Bcfg (S (2*m+1)) 1 0 (2 >> (1 >> (3 >> const 0))).
Proof.
  intros m.
  apply (D_phase_p (2 * m + 1)).
Qed.
