(** * Rules for the BB(5,4) champion 1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ *)

(** Tape convention (busycoq): [l <{{Q}} r] has the head on [hd l]; [l {{Q}}> r] has the head on
    [hd r].  A left stream is listed from the head outwards, so the Ligocki word
    "0^inf 3^(2m+1) 2^k A> 1^n R" is [(Bcfg k n m r)] with left stream
    [[2]^^k *> [3]^^(2m+1) *> const 0].  The halting transition E3 = 1RZ is [None].

    This machine is the BB(5,4) champion listed on the wiki's Champions
    page (../tools/explore.py checks its equivalence, under the renaming of
    the states A<->B and of the symbols 2<->3, with the string
    1LD2RA3RB1LC_1LD2LA3RB---_2RA1LA3RC2LC_2RA---2LD2LE_------1RZ1LD).  It differs
    from the BB(3,4) champion in the entries A0, B0, in the extra states D and E,
    and in the fact that the halting entry is E3 rather than A2.

    Every transition used by Ligocki's descent (A1 = 3LB, A3 = 2RA, B1 = 3RB,
    B2 = 1LC, B3 = 2RA, C0 = 3RB, C1 = 1LB, C2 = 3LC, C3 = 2RC) is identical
    in the two machines, so the sweeps, the turnaround and the main rule port
    over unchanged.  What is new is the D/E phase, proved at the end of this
    file: when the machine is in state A on a blank with a block of twos and a
    block of threes to its left, it enters states D and E, and -- depending on
    the parity of the number of twos -- either halts (E3) or continues with
    state D. *)

From TM54 Require Import Individual54.
From Coq Require Import Lia PeanoNat List Ring.
Import ListNotations.
Set Default Goal Selector "!".


(* machine: 1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, L, D)  | A, 1 => Some (3, L, B)  | A, 2 => None            | A, 3 => Some (2, R, A)
  | B, 0 => Some (1, L, D)  | B, 1 => Some (3, R, B)  | B, 2 => Some (1, L, C)  | B, 3 => Some (2, R, A)
  | C, 0 => Some (3, R, B)  | C, 1 => Some (1, L, B)  | C, 2 => Some (3, L, C)  | C, 3 => Some (2, R, C)
  | D, 0 => Some (3, R, B)  | D, 1 => None            | D, 2 => Some (3, L, E)  | D, 3 => Some (3, L, D)
  | E, 0 => None            | E, 1 => None            | E, 2 => Some (1, L, D)  | E, 3 => None
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
       [B(k, n, m) R = 0^inf  3^(2m+1)  2^k  A> 1^n  R].

    The block of threes is written as [2 * m + 1]. *)
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

(** ** The BB(5,4)-specific D/E phase *)

(** State D walks left over a block of threes, writing threes:
    [([3]^^j *> l) <{{D}} r -->* l <{{D}} ([3]^^j *> r)]. *)
Lemma D_sweep_left : forall j l r,
  ([3]^^j *> l) <{{D}} r -->* l <{{D}} ([3]^^j *> r).
Proof.
  induction j as [|j IH]; intros l r.
  - finish.
  - step. follow (IH l (3 >> r)). finish_norm.
Qed.

(** A block of [p] twos followed by one more two is a block of [p+1] twos. *)
Lemma block2_snoc : forall (p : nat) (x : Stream sym),
  ([2]^^p *> (2 >> x)) = ([2]^^(S p) *> x).
Proof.
  intros p x.
  change ((([2]^^p *> (Str_app [2] x))) = (([2]^^(S p) *> x))).
  rewrite <- (Str_app_assoc (lpow [2] p) [2] x).
  rewrite (lpow_shift [2] p).
  rewrite (Str_app_assoc [2] (lpow [2] p) x).
  reflexivity.
Qed.

(** ** The D/E phase.

    The machine is in state A on a blank cell, with two twos and a block of
    [S L] threes to its left:

        0^inf  3^(S L)  2 2  A>  0^inf .

    It writes a 1 on the blank and steps left (A0 = 1LD), then eats the two
    twos from right to left: D2 = 3LE writes a 3, E2 = 1LD writes a 1, and
    the machine alternates between the states D and E.  Because there are two
    twos, the machine arrives in state D on the first three of the block, and
    D3 = 3LD walks it left over the whole block.  D0 = 3RB then writes a three
    on the blank in front of the block, B3 = 2RA rewrites the first three of
    the block as a two, and A3 = 2RA turns the remaining threes into twos.

    The result is the Ligocki configuration [B(S L, 1, 0) 3 1 0^inf]: the
    block of threes has become a block of twos, and the right context has
    grown by "3 1".  The phase takes [2 L + 6] steps. *)
Lemma D_phase_raw : forall L,
  ([2]^^2 *> [3]^^(S L) *> const 0) {{A}}> (const 0) -->*
  ([2]^^(S L) *> 3 >> const 0) {{A}}> (1 >> 3 >> 1 >> const 0).
Proof.
  intros L.
  (* A0 = 1LD: write a 1 on the blank and step left onto the first 2. *)
  st_step.
  (* D2 = 3LE: write a 3 and step left onto the second 2. *)
  st_step.
  (* E2 = 1LD: write a 1 and step left onto the first 3 of the block. *)
  st_step.
  (* D3 = 3LD: walk left over the block of threes. *)
  follow (D_sweep_left (S L) (const 0) (1 >> 3 >> 1 >> const 0)).
  (* D0 = 3RB: write a 3 on the blank in front of the block and step right. *)
  st_step.
  (* B3 = 2RA and A3 = 2RA: the block of threes becomes a block of twos. *)
  follow (BA_sweep L (3 >> const 0) (1 >> 3 >> 1 >> const 0)).
  finish.
Qed.

(** The D/E phase in the configuration family.  The run of the BB(5,4)
    machine reaches [B(2, 0, 2)] -- two twos and a block of five threes --
    and the phase turns it into [B(5, 1, 0) 3 1 0^inf]. *)
Lemma D_phase_2 : Bcfg 2 0 2 (const 0) -->* Bcfg 5 1 0 (3 >> 1 >> const 0).
Proof.
  change (([2]^^2 *> [3]^^5 *> const 0) {{A}}> (const 0) -->*
          ([2]^^5 *> 3 >> const 0) {{A}}> (1 >> 3 >> 1 >> const 0)).
  apply (D_phase_raw 4).
Qed.

(** ** Halting in the D/E phase.

    If the number of twos is odd, the machine arrives in state E on the first
    three of the block, and E3 = 1RZ halts it.  With three twos the machine
    therefore halts in the configuration

        0^inf  3^(S L)  1 3 1  E> 3 1 3 1 0^inf ,

    i.e. with the head on a three in state E. *)
Lemma D_phase_halt : forall L,
  ([2]^^3 *> [3]^^(S L) *> const 0) {{A}}> (const 0) -->*
  (E;; (([3]^^L *> const 0) {{ 3 }} (3 >> 1 >> 3 >> 1 >> const 0))).
Proof.
  intros L.
  (* A0 = 1LD, then the three twos are eaten by D2, E2, D2. *)
  st_step. st_step. st_step. st_step.
  finish.
Qed.

(** The D/E phase entered with a *single* two also halts: A0 = 1LD moves the
    head onto the two, D2 = 3LE moves it onto the first three of the block in
    the state E, where E3 = 1RZ halts the machine. *)
Lemma D_phase_halt_1 : forall L,
  ([2]^^1 *> [3]^^(S L) *> const 0) {{A}}> (const 0) -->*
  (E;; (([3]^^L *> const 0) {{ 3 }} (3 >> 1 >> const 0))).
Proof.
  intros L.
  st_step. st_step.
  finish.
Qed.

(** ** The macro steps of the run

    The run of the BB(5,4) machine is organised in three macro steps, all
    of which are proved here from the elementary sweeps above.

    [macro_descent]  one level down:  B(k,n+1,m,r) -->* B(k-1, 2m+2, 0) (3 1^n r)
    [B1_iter]        the base case:   B(1,n,m,r) -->* B(1, 0, m+n) r
    [a3_step]        the A3 sweep:    B(k,0,m, 3 1^b r) -->* B(k+1, b, m) r

    The descent is Ligocki's turnaround preceded by the A1 and Cor2 steps;
    [B1_iter] is [B1_step] iterated; [a3_step] is a single A3 = 2RA step. *)

(** One level down. *)
Lemma macro_descent : forall k n m r,
  Bcfg (S (S k)) (S n) m r -->* Bcfg (S k) (2 * m + 2) 0 (3 >> [1]^^n *> r).
Proof.
  intros k n m r.
  (* A1 = 3LB: the head writes a three and steps left onto a two. *)
  st_step.
  (* Cor2: the block of threes turns into ones on the right. *)
  follow (Cor2 (S k) (2 * m + 1) (const 0) (3 >> [1]^^n *> r)).
  (* The turnaround. *)
  follow (turnaround k (2 * m + 1) n r).
  finish_cfg.
Qed.

(** The base case, [B1_step] iterated. *)
Lemma B1_iter : forall n m r,
  Bcfg 1 n m r -->* Bcfg 1 0%nat (m + n) r.
Proof.
  induction n as [|n IH]; intros m r.
  - simpl. finish.
  - follow (B1_step n m r).
    replace (m + S n)%nat with (S m + n)%nat by lia.
    apply IH.
Qed.

(** The A3 sweep: the head reads a three, writes a two and steps right. *)
Lemma a3_step : forall k m b r,
  Bcfg k 0%nat m (3 >> [1]^^b *> r) -->* Bcfg (S k) b m r.
Proof.
  intros k m b r.
  st_step.
  finish_cfg.
Qed.

(** ** The long chain

    In the main regime the machine sits in the configuration

        B(2, n, m) [3 ...]

    with a huge [n].  One macro cycle lowers [n] by one and doubles [m];
    after [n] cycles the machine is in

        B(2, 0, 2^n (m+2) - 2) [3 ...] .

    This is the step that makes the run grow so fast: the [m] parameter --
    and with it the size of the block of threes on the tape -- is
    exponentiated once per unit of [n]. *)
Lemma chain_step : forall n m r,
  Bcfg 2 (S n) m (3 >> r) -->* Bcfg 2 n (2 * m + 2) (3 >> r).
Proof.
  intros n m r.
  follow (macro_descent 0%nat n m (3 >> r)).
  follow (B1_iter (2 * m + 2)%nat 0%nat (3 >> [1]^^n *> 3 >> r)).
  rewrite Nat.add_0_l.
  follow (a3_step 1%nat (2 * m + 2)%nat n (3 >> r)).
  finish_cfg.
Qed.

(** An arithmetic identity used by [chain]. *)
Lemma pow_chain : forall n m,
  2 ^ S n * (m + 2) - 2 = 2 ^ n * ((2 * m + 2) + 2) - 2.
Proof.
  intros n m.
  assert (H : 0 <= n) by lia.
  rewrite Nat.pow_succ_r by exact H.
  rewrite <- Nat.mul_assoc.
  replace ((2 * m + 2) + 2)%nat with (2 * (m + 2))%nat by lia.
  nia.
Qed.

Lemma chain : forall n m r,
  Bcfg 2 (S n) m (3 >> r) -->* Bcfg 2 0%nat (2 ^ (S n) * (m + 2) - 2) (3 >> r).
Proof.
  induction n as [|n IH]; intros m r.
  - eapply evstep_trans.
    + apply (chain_step 0%nat m r).
    + replace (2 ^ 1 * (m + 2) - 2)%nat with (2 * m + 2)%nat by (simpl; lia).
      finish.
  - eapply evstep_trans.
    + apply (chain_step (S n) m r).
    + rewrite (pow_chain (S n) m).
      apply (IH (2 * m + 2)%nat r).
Qed.
