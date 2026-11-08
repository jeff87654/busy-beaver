(** * The D/E phase of the BB(5,4) machine, in general.

    The phase starts with the machine in state A on a blank cell, with a
    block of twos to its left.  The machine eats the twos two at a time:

      D2 = 3LE   writes a three and steps left,
      E2 = 1LD   writes a one and steps left.

    Each pair of twos therefore contributes "1 3" to the right context.  If
    the number of twos is even, the machine arrives in state D on the first
    three of the block of threes (which is then turned into a block of
    twos); if it is odd, it arrives in state E there, where the halting
    transition E3 = 1RZ applies. *)

From TM54 Require Import Individual54 BB54_rules.
From Coq Require Import Lia PeanoNat List Ring.
Import ListNotations.
Set Default Goal Selector "!".


(** ** The patterns (1 3)^k and (3 1)^k in a right context. *)

Fixpoint pat13 (k : nat) (s : Stream sym) : Stream sym :=
  match k with
  | O => s
  | S k' => 1 >> 3 >> pat13 k' s
  end.

Fixpoint pat31 (k : nat) (s : Stream sym) : Stream sym :=
  match k with
  | O => s
  | S k' => 3 >> 1 >> pat31 k' s
  end.

Lemma pat13_S : forall k s, pat13 (S k) s = 1 >> 3 >> pat13 k s.
Proof. reflexivity. Qed.

Lemma pat31_S : forall k s, pat31 (S k) s = 3 >> 1 >> pat31 k s.
Proof. reflexivity. Qed.

(** Shifting the pattern one place to the left. *)
Lemma pat13_shift : forall k s,
  pat13 k (1 >> 3 >> 1 >> s) = 1 >> 3 >> pat13 k (1 >> s).
Proof.
  induction k as [|k IH]; intros s.
  - reflexivity.
  - cbn [pat13 pat31]. rewrite IH. reflexivity.
Qed.

(** The same shift, one pair further to the left. *)
Lemma pat13_2 : forall k s,
  pat13 (S k) (1 >> 3 >> 1 >> s) = pat13 (S (S k)) (1 >> s).
Proof.
  intros k s.
  rewrite pat13_shift.
  cbn [pat13 pat31]. reflexivity.
Qed.

(** Dropping the leading one turns the pattern (1 3)^k 1 into (3 1)^k. *)
Lemma pat13_1 : forall k s,
  pat13 k (1 >> s) = 1 >> pat31 k s.
Proof.
  induction k as [|k IH]; intros s.
  - reflexivity.
  - cbn [pat13 pat31]. rewrite IH. reflexivity.
Qed.

(** ** The number of twos [2n+2], in nested-successor form.

    The Coq simplifier can only peel a successor off a block of twos when
    the block length is in successor form, so the length of the block of
    twos is built up in that form. *)

Fixpoint twos (n : nat) : nat :=
  match n with
  | O => 2
  | S n' => S (S (twos n'))
  end.

Lemma twos_S : forall n, twos (S n) = S (S (twos n)).
Proof. reflexivity. Qed.

Lemma twos_spec : forall n, twos n = 2 * n + 2.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [twos]. rewrite IH. lia.
Qed.

(** ** Eating the twos.

    One pair of twos is eaten by D2 = 3LE (write a three, step left) and
    E2 = 1LD (write a one, step left).  The pair contributes "1 3" to the
    right context. *)

Lemma eat2 : forall j l r,
  ([2]^^(S (S j)) *> l) <{{D}} r -->*
  ([2]^^j *> l) <{{D}} (1 >> 3 >> r).
Proof.
  intros j l r.
  st_step.
  st_step.
  finish_norm.
Qed.

(** The whole eat phase: [twos n] twos are eaten, one pair at a time. *)
Lemma eat_reach : forall n L s,
  ([2]^^(twos n) *> [3]^^(S L) *> const 0) <{{D}} (1 >> s) -->*
  ([3]^^(S L) *> const 0) <{{D}} (pat13 (S n) (1 >> s)).
Proof.
  induction n as [|n IH]; intros L s.
  - (* two twos *)
    apply (eat2 0 ([3]^^(S L) *> const 0) (1 >> s)).
  - (* eat the first pair, then use the induction hypothesis *)
    rewrite (twos_S n).
    eapply evstep_trans.
    + apply (eat2 (twos n) ([3]^^(S L) *> const 0) (1 >> s)).
    + rewrite <- (pat13_2 n s).
      apply (IH L (3 >> 1 >> s)).
Qed.

(** The eat phase, leaving one two behind (the odd case). *)
Lemma eat_reach_odd : forall n L s,
  ([2]^^(S (twos n)) *> [3]^^(S L) *> const 0) <{{D}} (1 >> s) -->*
  ([2]^^1 *> [3]^^(S L) *> const 0) <{{D}} (pat13 (S n) (1 >> s)).
Proof.
  induction n as [|n IH]; intros L s.
  - (* three twos: eat one pair *)
    apply (eat2 1 ([3]^^(S L) *> const 0) (1 >> s)).
  - rewrite (twos_S n).
    eapply evstep_trans.
    + apply (eat2 (S (twos n)) ([3]^^(S L) *> const 0) (1 >> s)).
    + rewrite <- (pat13_2 n s).
      apply (IH L (3 >> 1 >> s)).
Qed.

(** The same shift for the pattern (3 1)^k. *)
Lemma pat31_shift : forall k s,
  pat31 k (3 >> 1 >> s) = pat31 (S k) s.
Proof.
  induction k as [|k IH]; intros s.
  - reflexivity.
  - cbn [pat13 pat31]. rewrite IH. reflexivity.
Qed.

Lemma pat31_2 : forall k s,
  pat31 (S k) (3 >> 1 >> s) = pat31 (S (S k)) s.
Proof.
  intros k s.
  rewrite pat31_shift.
  cbn [pat13 pat31]. reflexivity.
Qed.

(** ** The D/E phase with an even number of twos.

    The block of threes is turned into a block of twos and the right
    context becomes (3 1)^(n+1). *)

Lemma D_phase_even_aux : forall n L s,
  ([2]^^(twos n) *> [3]^^(S L) *> const 0) <{{D}} (1 >> s) -->*
  ([2]^^(S L) *> 3 >> const 0) {{A}}> (1 >> pat31 (S n) s).
Proof.
  intros n L s.
  (* eat the twos, two at a time *)
  follow (eat_reach n L s).
  (* D3 = 3LD: walk left over the whole block of threes *)
  follow (D_sweep_left (S L) (const 0) (pat13 (S n) (1 >> s))).
  (* D0 = 3RB: write a three on the blank beyond the block and step right *)
  st_step.
  (* B3 = 2RA and A3 = 2RA: the block of threes becomes a block of twos *)
  follow (BA_sweep L (3 >> const 0) (pat13 (S n) (1 >> s))).
  rewrite (pat13_1 (S n) s).
  finish.
Qed.

Lemma D_phase_even_raw : forall n L,
  ([2]^^(twos n) *> [3]^^(S L) *> const 0) {{A}}> (const 0) -->*
  ([2]^^(S L) *> 3 >> const 0) {{A}}> (1 >> pat31 (S n) (const 0)).
Proof.
  induction n as [|n IH]; intros L.
  - (* two twos *)
    st_step.
    apply (D_phase_even_aux 0 L (const 0)).
  - rewrite (twos_S n).
    rewrite <- (pat31_2 n (const 0)).
    st_step.
    eapply evstep_trans.
    + apply (eat2 (twos n) ([3]^^(S L) *> const 0) (1 >> const 0)).
    + apply (D_phase_even_aux n L (3 >> 1 >> const 0)).
Qed.

(** ** The D/E phase with an odd number of twos.

    The machine arrives in state E on the first three of the block, where
    the halting transition E3 = 1RZ applies. *)

Lemma D_phase_odd_aux : forall n L s,
  ([2]^^(S (twos n)) *> [3]^^(S L) *> const 0) <{{D}} (1 >> s) -->*
  (E;; (([3]^^L *> const 0) {{ 3 }} (3 >> pat13 (S n) (1 >> s)))).
Proof.
  intros n L s.
  (* eat the twos, two at a time, leaving one two *)
  follow (eat_reach_odd n L s).
  (* D2 = 3LE: write a three and step left onto the first three of the
     block; the machine is now in state E *)
  st_step.
  finish.
Qed.

Lemma D_phase_odd_raw : forall n L,
  ([2]^^(S (twos n)) *> [3]^^(S L) *> const 0) {{A}}> (const 0) -->*
  (E;; (([3]^^L *> const 0) {{ 3 }} (3 >> pat13 (S n) (1 >> const 0)))).
Proof.
  induction n as [|n IH]; intros L.
  - (* three twos *)
    st_step.
    apply (D_phase_odd_aux 0 L (const 0)).
  - rewrite (twos_S n).
    rewrite <- (pat13_2 n (const 0)).
    st_step.
    eapply evstep_trans.
    + apply (eat2 (S (twos n)) ([3]^^(S L) *> const 0) (1 >> const 0)).
    + apply (D_phase_odd_aux n L (3 >> 1 >> const 0)).
Qed.

(** ** The D/E phase in the configuration family.

    [Bcfg k n m r] is [0^inf 3^(2m+1) 2^k A> 1^n r]; the block of threes has
    length [2m+1]. *)

Lemma D_phase_even : forall q m,
  Bcfg (S (S (2 * q))) 0 m (const 0) -->*
  Bcfg (2 * m + 1) 1 0 (pat31 (S q) (const 0)).
Proof.
  intros q m.
  change (([2]^^(S (S (2 * q))) *> [3]^^(2 * m + 1) *> const 0) {{A}}> (const 0) -->*
          ([2]^^(2 * m + 1) *> 3 >> const 0) {{A}}> (1 >> pat31 (S q) (const 0))).
  replace (S (S (2 * q)))%nat with (twos q) by (rewrite twos_spec; lia).
  replace (2 * m + 1)%nat with (S (2 * m)) by lia.
  apply (D_phase_even_raw q (2 * m)).
Qed.

Lemma D_phase_odd : forall q m,
  Bcfg (S (S (S (2 * q)))) 0 m (const 0) -->*
  (E;; (([3]^^(2 * m) *> const 0) {{ 3 }} (3 >> pat13 (S q) (1 >> const 0)))).
Proof.
  intros q m.
  change (([2]^^(S (S (S (2 * q)))) *> [3]^^(2 * m + 1) *> const 0) {{A}}> (const 0) -->*
          (E;; (([3]^^(2 * m) *> const 0) {{ 3 }} (3 >> pat13 (S q) (1 >> const 0))))).
  replace (S (S (S (2 * q))))%nat with (S (twos q)) by (rewrite twos_spec; lia).
  replace (2 * m + 1)%nat with (S (2 * m)) by lia.
  apply (D_phase_odd_raw q (2 * m)).
Qed.

(** ** The chain of the BB(5,4) run.

    [B(5, 0, g_4(0)) (3 1) 0^inf]
      --A3-->   [B(6, 1, g_4(0)) 0^inf]
      --B-->    [B(6, 0, g_5(g_4(0))) 0^inf]
      --D/E-->  [B(2 g_5(g_4(0)) + 1, 1, 0) (3 1)^3 0^inf]. *)
Theorem bb54_dchain :
  Bcfg 5 0 (g 4 0) (3 >> 1 >> const 0) -->*
  Bcfg (2 * g 5 (g 4 0) + 1) 1 0 (pat31 3 (const 0)).
Proof.
  eapply evstep_trans.
  - apply (a3_step 5 (g 4 0) 1 (const 0)).
  - eapply evstep_trans.
    + apply (B_rule 5 1 (g 4 0) (const 0)).
    + apply (D_phase_even 2 (g 5 (g 4 0))).
Qed.

(** ** The rounds and the levels of the main regime.

    A round consists of the B rule followed by the A3 sweep.  It consumes one
    "3 1" pair of the right context, raises the number of twos by one, and
    replaces the number [m] -- the length of the block of threes -- by
    [g_(k-1)(m)], where [k] is the number of twos.

    After [T] rounds the machine is in state A on a blank cell again, and the
    D/E phase starts afresh.  The number [m] is then a nested application of
    the [g]'s; [gchain] records it. *)

(** The nested application of the [g]'s performed by [T] rounds. *)
Fixpoint gchain (j : nat) (T : nat) (m : nat) : nat :=
  match T with
  | O => g j m
  | S T' => gchain (S j) T' (g j m)
  end.

(** One round: the B rule and the A3 sweep. *)
Lemma round_step : forall k m T r,
  Bcfg (S (S k)) 1 m (pat31 (S T) r) -->*
  Bcfg (S (S (S k))) 1 (g (S k) m) (pat31 T r).
Proof.
  intros k m T r.
  rewrite (pat31_S T r).
  eapply evstep_trans.
  - apply (B_rule (S k) 1 m (3 >> 1 >> pat31 T r)).
  - apply (a3_step (S (S k)) (g (S k) m) 1 (pat31 T r)).
Qed.

(** A whole level: [T] rounds followed by the final B rule. *)
Lemma level : forall T k m r,
  Bcfg (S (S k)) 1 m (pat31 T r) -->*
  Bcfg (S (S k + T)) 0 (gchain (S k) T m) r.
Proof.
  induction T as [|T IH]; intros k m r.
  - (* no round: just the final B rule *)
    replace (S (S k + 0))%nat with (S (S k))%nat by lia.
    replace (gchain (S k) 0 m)%nat with (g (S k) m)%nat by reflexivity.
    apply (B_rule (S k) 1 m r).
  - (* one round, then the induction hypothesis *)
    replace (S (S k + S T))%nat with (S (S (S k) + T))%nat by lia.
    eapply evstep_trans.
    + apply (round_step k m T r).
    + apply (IH (S k) (g (S k) m) r).
Qed.

(** ** The same level, with the number of twos in the form [S k].

    For the main regime the number of twos is odd, and it is convenient to
    write it as [S k] rather than [S (S k')].  The two forms of the level
    are interchangeable; the arithmetic that relates them is done in
    BB54_halt.v. *)

Lemma count_succ_one : forall k, S k + 1 = S (S k).
Proof. intros k. lia. Qed.

Lemma count_shift : forall k t, S (S k) + t = S k + S t.
Proof. intros k t. lia. Qed.

Lemma level_gen : forall T k m r,
  Bcfg (S k) 1 m (pat31 T r) -->* Bcfg (S k + T) 0 (gchain k T m) r.
Proof.
  induction T as [|T IH]; intros k m r.
  - rewrite Nat.add_0_r.
    replace (gchain k 0 m)%nat with (g k m)%nat by reflexivity.
    apply (B_rule k 1 m r).
  - eapply evstep_trans.
    + (* one round: the B rule and the A3 sweep *)
      rewrite (pat31_S T r).
      eapply evstep_trans.
      * apply (B_rule k 1 m (3 >> 1 >> pat31 T r)).
      * apply (a3_step (S k) (g k m) 1 (pat31 T r)).
    + (* the remaining rounds *)
      rewrite <- (count_shift k T).
      apply (IH (S k) (g k m) r).
Qed.
