(** * Rules for the BB(3,5) champion 1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC *)

(** Tape convention (busycoq): [l <{{Q}} r] has the head on [hd l]; [l {{Q}}> r] has the head on
    [hd r].  A left stream is listed from the head outwards, so the Ligocki word
    "0^inf 3^(2m+1) 2^k A> 1^n R" is [(Bcfg k n m r)] with left stream
    [[2]^^k *> [3]^^(2m+1) *> const 0].  The halting transition B4 = 1RZ is [None].

    The BB(3,5) champion agrees with the BB(3,4) champion on the symbols 0..3
    (only A2 differs: 1RZ in BB(3,4), 4LC in BB(3,5)), so every sweep and the
    whole descent of Ligocki's BB(3,4) analysis port over verbatim; the extra
    symbol 4 adds the new rules at the end of this file.

    The three BB(3,5)-specific rules (with the head position made explicit):

      rule 1   B(k, 0, m) 2  -->*  B(k + 2m + 1, 0, 0) 4
      rule 2   B(k, 0, m) 4  -->*  B(k - 1, 2m + 2, 0) 4
      rule 3   B(1, 0, m) 4  -->*  3^(2m+3) B> 4      (and the machine then halts)

    In the Coq notation [Bcfg k n m r] is the configuration
    [0^inf 3^(2m+1) 2^k A> 1^n r], so these read

      rule 1   Bcfg k 0 m (2 >> r)  -->*  Bcfg (k + 2m + 1) 0 0 (4 >> r)
      rule 2   Bcfg k 0 m (4 >> r)  -->*  Bcfg (k - 1) (2m + 2) 0 (4 >> r)
      rule 3   Bcfg 1 0 m (4 >> r)  -->*  ([3]^^(2m+3) *> const 0) {{B}}> (4 >> r)

    Rule 2 needs [k >= 2]; in the Coq statements the parameter is written
    [S k] (as everywhere else in this development) so that the [tl] of a
    block of 2s reduces. *)

From TM35 Require Import Individual35.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (3, L, B)  | A, 2 => Some (4, L, C)  | A, 3 => Some (2, R, A)  | A, 4 => Some (4, L, B)
  | B, 0 => Some (2, L, C)  | B, 1 => Some (3, R, B)  | B, 2 => Some (1, L, C)  | B, 3 => Some (2, R, A)  | B, 4 => None
  | C, 0 => Some (3, R, B)  | C, 1 => Some (1, L, B)  | C, 2 => Some (3, L, C)  | C, 3 => Some (2, R, C)  | C, 4 => Some (4, L, C)
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

(** Individual's [simpl_tape] autorewrites with [tape_pre], whose [lpow_add]
    splits blocks like [3^^(2*m+1)] whose exponent is a stuck sum.  We use a
    gentler version that only [simpl]s. *)
Ltac st_tape := autorewrite with tape_pre; simpl.
Ltac st_step := (eapply evstep_step || eapply progress_step); [prove_step | st_tape].

(** The head and the tail of a block of identical symbols.  [simpl] only reduces
    [hd ([x]^^n *> l)] when [n] is a successor, so for a symbolic [n] these two
    lemmas are the way in. *)
Lemma hd_lpow_gen : forall (x : sym) n (l : Stream sym), 1 <= n -> Streams.hd ([x]^^n *> l) = x.
Proof.
  intros x n. destruct n as [|n]; intros l H.
  - lia.
  - simpl. reflexivity.
Qed.

Lemma tl_lpow_gen : forall (x : sym) n (l : Stream sym), 1 <= n -> Streams.tl ([x]^^n *> l) = [x]^^(pred n) *> l.
Proof.
  intros x n. destruct n as [|n]; intros l H.
  - lia.
  - simpl. reflexivity.
Qed.

(** A block of [c]'s can be written with the extra [c] at its front or at its
    back; both denote the same stream, but Coq only sees them as equal after
    a little rewriting.  This lemma moves the extra [c] from the back to
    the front. *)
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

(** ** The BB(3,5)-specific rules.

    The whole descent of Ligocki's BB(3,4) analysis ports over unchanged, but
    the BB(3,4) champion halted at the configuration [B(k,0,m) 2] (the halting
    transition A2 = 1RZ), whereas the BB(3,5) champion executes A2 = 4LC
    instead and only halts much later, at [B(1,0,m) 4] (the halting
    transition B4 = 1RZ).  Between the two there are three new rules.

    The new rules are proved from the elementary sweeps of the BB(3,4)
    development; the only genuinely new ingredient is the generalised
    turnaround [GT] below, which is [turnaround] with an arbitrary right
    stream. *)

(** The generalised turnaround: the machine walks left over the block of 2s
    (writing 3s), then right over the 3s it has just written (writing 2s),
    and comes to rest on the 1 it wrote on its very first step.  The right
    stream is left untouched, so the right stream of the result is the right
    stream of the source minus its first element.

      [0^inf 2^(k+2) <B R  -->  0^inf 3 2^(k+1) A> 1 R]

    (With [turnaround] above, [R] is [1^m 3 1^n R'] and the head comes to
    rest on the first 1 of the [1^m] block, which is exactly the same
    statement.) *)
Lemma GT : forall j (r : Stream sym),
  ([2]^^(S (S j)) *> const 0) <{{B}} r -->*
  ([2]^^(S j) *> [3]^^1 *> const 0) {{A}}> (1 >> r).
Proof.
  intros j r.
  st_step.
  follow (C_sweep_left (S j) (const 0) (1 >> r)).
  st_step.
  follow (BA_sweep j (3 >> const 0) (1 >> r)).
  finish.
Qed.

(** ** Rule 1: [B(k, 0, m) 2 -->* B(k + 2m + 1, 0, 0) 4].

    The head sits in state A on the 2 that follows the block of 2s; A2 = 4LC
    writes a 4 and moves left, so the head ends up on the rightmost 2 of the
    block, with the 4 immediately to its right.  From there the machine
    alternates between two rounds:

    - "eating" a 3: C sweeps left over the whole block of 2s, writing 3s,
      then sweeps right over them again, writing 2s; the block of 2s grows by
      one and the block of 3s shrinks by one;
    - "growing" a 3: once the block of 3s is empty, the left sweep runs into
      the blank, C0 creates a fresh 3 at the far left, and the right sweep
      writes 2s over the block of 2s again.

    There are [2m+1] eating rounds (the block of 3s has [2m+1] cells) and one
    growing round, so the block of 2s ends up with [k + 2m + 1] cells and the
    block of 3s with one cell. *)

(** One eating round: the block of 3s loses one 3, the block of 2s gains one 2. *)
Lemma StepE : forall u v r,
  ([2]^^u *> [3]^^(S v) *> const 0) {{C}}> (2 >> 4 >> r) -->*
  ([2]^^(S u) *> [3]^^v *> const 0) {{C}}> (2 >> 4 >> r).
Proof.
  intros u v r.
  (* C sweeps left over the block of 2s, writing 3s. *)
  follow (C_sweep_left (S u) ([3]^^(S v) *> const 0) (4 >> r)).
  (* C sweeps right over the 3s it has just written, writing 2s. *)
  follow (C_right_3s (S (S u)) ([3]^^v *> const 0) (4 >> r)).
  (* C4 = 4LC: write the 4 and move left onto the block of 2s again. *)
  st_step.
  finish.
Qed.

(** All the eating rounds: [S v] of them. *)
Lemma StepE_iter : forall u v r,
  ([2]^^u *> [3]^^(S v) *> const 0) {{C}}> (2 >> 4 >> r) -->*
  ([2]^^(u + S v) *> const 0) {{C}}> (2 >> 4 >> r).
Proof.
  intros u v r. revert u r.
  induction v as [|v IH]; intros u r.
  - follow (StepE u 0 r).
    replace (u + S 0) with (S u) by lia.
    finish.
  - follow (StepE u (S v) r).
    follow (IH (S u) r).
    replace (S u + S v) with (u + S (S v)) by lia.
    finish.
Qed.

(** The growing round: the block of 3s is empty, so the left sweep runs into
    the blank and C0 creates a fresh 3 at the far left. *)
Lemma StepN : forall u r,
  ([2]^^u *> const 0) {{C}}> (2 >> 4 >> r) -->*
  ([2]^^(S u) *> [3]^^1 *> const 0) {{A}}> (4 >> r).
Proof.
  intros u r.
  (* C sweeps left over the block of 2s, writing 3s, and runs into the blank. *)
  follow (C_sweep_left (S u) (const 0) (4 >> r)).
  (* C0 = 3RB: write a 3 at the far left and move right. *)
  st_step.
  (* B3 and the A sweep turn the 3s back into 2s. *)
  follow (BA_sweep u (3 >> const 0) (4 >> r)).
  finish.
Qed.

(** ** Rule 1 of the BB(3,5) champion: [B(k,0,m) 2 -->* B(k+2m+1,0,0) 4]. *)
Theorem rule1 : forall k m r,
  Bcfg (S k) 0 m (2 >> r) -->* Bcfg (S k + 2 * m + 1) 0 0 (4 >> r).
Proof.
  intros k m r.
  (* A2 = 4LC: write a 4 and move left onto the block of 2s. *)
  st_step.
  (* The [2m+1] eating rounds. *)
  follow (StepE_iter k (2 * m) r).
  (* The growing round. *)
  follow (StepN (S k + 2 * m) r).
  finish_cfg.
Qed.

(** ** Rule 2 of the BB(3,5) champion: [B(k,0,m) 4 -->* B(k-1,2m+2,0) 4].

    The head sits in state A on the 4 that follows the block of 2s; A4 = 4LB
    writes a 4 and moves left, so the head ends up on the rightmost 2 of the
    block.  Ligocki's Corollary 2 then converts the block of [2m+1] threes
    into [2m+1] ones on the right, and the generalised turnaround [GT] brings
    the head back onto the first of those ones, leaving a single 3 at the far
    left.  The result is [B(k-1, 2m+2, 0) 4]: one 2 fewer on the left, one 3
    instead of [2m+1], and [2m+2] ones on the right. *)
Theorem rule2 : forall k m r,
  Bcfg (S (S k)) 0 m (4 >> r) -->* Bcfg (S k) (2 * m + 2) 0 (4 >> r).
Proof.
  intros k m r.
  (* A4 = 4LB: write a 4 and move left onto the block of 2s. *)
  st_step.
  (* Corollary 2: the block of [2m+1] threes becomes [2m+1] ones on the right. *)
  follow (Cor2 (S k) (2 * m + 1) (const 0) (4 >> r)).
  (* The generalised turnaround. *)
  follow (GT k ([1]^^(2 * m + 1) *> (4 >> r))).
  finish_cfg.
Qed.

(** ** Rule 3 of the BB(3,5) champion: [B(1,0,m) 4 -->* 3^(2m+3) B> 4].

    The head sits in state A on the 4 that follows the single 2; A4 = 4LB
    writes a 4 and moves left onto the 2.  A three-step cycle (B2, C3, C1)
    then eats one 3 of the left block and appends one 1 to the right stream;
    after [2m+1] such cycles the block of 3s is gone and there are [2m+1]
    ones on the right.  The last four steps (B2, C0, and two B1 sweeps) turn
    those ones into 3s and leave the head in state B on the 4, where B4 = 1RZ
    halts the machine. *)
Lemma cycle3 : forall v r,
  ([3]^^(S v) *> const 0) {{B}}> (2 >> r) -->*
  ([3]^^v *> const 0) {{B}}> (2 >> 1 >> r).
Proof.
  intros v r. st_step. st_step. st_step. finish.
Qed.

Lemma cycle3_iter : forall v r,
  ([3]^^(S v) *> const 0) {{B}}> (2 >> r) -->*
  ([3]^^0 *> const 0) {{B}}> (2 >> [1]^^(S v) *> r).
Proof.
  intros v r. revert r.
  induction v as [|v IH]; intros r.
  - follow (cycle3 0 r).
    rewrite <- (block_snoc 1 0 r).
    finish.
  - follow (cycle3 (S v) r).
    follow (IH (1 >> r)).
    rewrite (block_snoc 1 (S v) r).
    finish.
Qed.

(** ** Rule 3 of the BB(3,5) champion. *)
Theorem rule3 : forall m r,
  Bcfg 1 0 m (4 >> r) -->* ([3]^^(2 * m + 3) *> const 0) {{B}}> (4 >> r).
Proof.
  intros m r.
  unfold Bcfg.
  replace (2 * m + 1) with (S (2 * m)) by lia.
  (* A4 = 4LB: write a 4 and move left onto the 2. *)
  st_step.
  (* The [2m+1] three-step cycles. *)
  follow (cycle3_iter (2 * m) (4 >> r)).
  (* B2, C0 and the B1 sweep: the ones on the right become 3s. *)
  st_step. st_step.
  follow (B_1s (S (2 * m)) (3 >> const 0) (4 >> r)).
  replace (S (S (2 * m))) with (2 * m + 2) by lia.
  rewrite (block_snoc 3 (2 * m + 2) (const 0)).
  finish.
Qed.
