(** * BB(7) holdout, subtask 16582: 1RB1LD_1RC0RF_0LA0RA_0LA0LE_1LA0LG_0LA---_1RD1LG never halts *)

(** Formalization of the informal proof in
    [bb8_list/investigations/bb7_control_16582.md]. Tape notation in the comments is plain
    binary read left to right, [A>] marks the head (in state A, on the cell to its right),
    [(u)^n] is n copies of u, and [r] is an arbitrary right part of the tape that is never read.

    Configuration families (as in the informal proof, with the untouched tail
    "(10)^t 1101" folded into [r]):
      beta  x j k r = 0^inf A> 0 0 (100)^x 1010 (100)^j 1010 (110)^k 10100 r
      gamma x j m r = 0^inf A> 0 0 (100)^x 1010 (100)^j 10   (100)^m 00100 r
    Rules, proved for ALL x, j, k, m >= 0 and every r:
      R1 : beta  x j (k+1) r -->+ beta  (2x+3) (j+2) k r
      T1 : beta  x j 0     r -->+ gamma (2x+3) 0 (j+1) (10 r)
      R2 : gamma x j (m+1) r -->+ gamma (2x+3) (j+2) m r
      T2 : gamma x j 0     r -->+ beta  (2x+3) 0 j r
    so every member of the family has a successor in the family. The blank tape reaches
    gamma 61 0 3 (1101 0^inf) after 11,331 steps (accelerated below with the bounce lemma L0s). *)

From BB7 Require Import Individual72.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".

(* machine: 1RB1LD_1RC0RF_0LA0RA_0LA0LE_1LA0LG_0LA---_1RD1LG *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, L, D)
  | B, 0 => Some (1, R, C)  | B, 1 => Some (0, R, F)
  | C, 0 => Some (0, L, A)  | C, 1 => Some (0, R, A)
  | D, 0 => Some (0, L, A)  | D, 1 => Some (0, L, E)
  | E, 0 => Some (1, L, A)  | E, 1 => Some (0, L, G)
  | F, 0 => Some (0, L, A)  | F, 1 => None
  | G, 0 => Some (1, R, D)  | G, 1 => Some (1, L, G)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** ** Tape normalization *)

(** Rotating a run past a matching symbol (same lemma as busycoq's Finned.v). *)
Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : Sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof. intros. rewrite const_unfold at 1. apply align_lpow. Qed.

(** Push concrete symbols in front of runs as far as possible (a normal form). *)
Ltac align_tape := repeat ((rewrite align_lpow || rewrite align_lpow_const); simpl app).
(** Pull successors out of run counts ([n + S m = S (n + m)]) so that [simpl] peels them. *)
Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
(** Close [c -->* c'] when [c] and [c'] are the same tape up to the normal form above. *)
Ltac finish_norm := apply evstep_refl'; norm_nat; align_tape; try reflexivity; lia_refl.

(** ** Crossing a run of 3-cell blocks

    Blocks are written in stream order (nearest the head first); on the left side this is
    the reverse of the visual order. Each lemma is stated in the alignment in which the
    machine first reads the run. *)

(** C> over (100)^n leaves (011)^n behind (visual order). *)
Lemma cross_CR : forall n l r, l {{C}}> [1;0;0]^^n *> r -->* l <* [1;1;0]^^n {{C}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** A> over (001)^n leaves (110)^n behind. *)
Lemma cross_AR : forall n l r, l {{A}}> [0;0;1]^^n *> r -->* l <* [0;1;1]^^n {{A}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** <A over (011)^n (visual) gives (101)^n. *)
Lemma cross_AL : forall n l r, l <* [1;1;0]^^n <{{A}} r -->* l <{{A}} [1;0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** <D over (011)^n gives (100)^n. *)
Lemma cross_DL : forall n l r, l <* [1;1;0]^^n <{{D}} r -->* l <{{D}} [1;0;0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** <E over (110)^n gives (011)^n. *)
Lemma cross_EL : forall n l r, l <* [0;1;1]^^n <{{E}} r -->* l <{{E}} [0;1;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** <G over (011)^n gives (001)^n. *)
Lemma cross_GL : forall n l r, l <* [1;1;0]^^n <{{G}} r -->* l <{{G}} [0;0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** ** Bounces (informal L0 and L0-star), with blank tape on the left *)

(** L0: 0^inf A> 0 0 (100)^j 1010 (110)^(k+1) r  -->*  0^inf A> 0 0 (100)^(j+2) 1010 (110)^k r *)
Lemma L0 : forall j k r,
  const 0 {{A}}> 0 >> 0 >> [1;0;0]^^j *> 1 >> 0 >> 1 >> 0 >> [1;1;0]^^(S k) *> r -->*
  const 0 {{A}}> 0 >> 0 >> [1;0;0]^^(S (S j)) *> 1 >> 0 >> 1 >> 0 >> [1;1;0]^^k *> r.
Proof.
  intros. execute. follow cross_CR. execute. follow cross_DL. do 6 step. finish_norm.
Qed.

(** L0-star: 0^inf A> 0 0 (100)^j 1010 (110)^k r  -->*  0^inf A> 0 0 (100)^(j+2k) 1010 r *)
Lemma L0s : forall k j r,
  const 0 {{A}}> 0 >> 0 >> [1;0;0]^^j *> 1 >> 0 >> 1 >> 0 >> [1;1;0]^^k *> r -->*
  const 0 {{A}}> 0 >> 0 >> [1;0;0]^^(j + 2 * k) *> 1 >> 0 >> 1 >> 0 >> r.
Proof.
  induction k; intros.
  - finish.
  - follow L0. follow IHk. finish.
Qed.

(** ** The configuration families and the four rules *)

Definition beta (x j k : nat) (r : side) : Q * tape :=
  const 0 {{A}}> 0 >> 0 >> [1;0;0]^^x *> 1 >> 0 >> 1 >> 0 >> [1;0;0]^^j *> 1 >> 0 >> 1 >> 0 >>
    [1;1;0]^^k *> 1 >> 0 >> 1 >> 0 >> 0 >> r.

Definition gamma (x j m : nat) (r : side) : Q * tape :=
  const 0 {{A}}> 0 >> 0 >> [1;0;0]^^x *> 1 >> 0 >> 1 >> 0 >> [1;0;0]^^j *> 1 >> 0 >>
    [1;0;0]^^m *> 0 >> 0 >> 1 >> 0 >> 0 >> r.

Arguments beta : simpl never.
Arguments gamma : simpl never.

(** Each rule: sweep right across x and j, sweep back, sweep right across x again, return to
    the left end, then bounce (L0s) the x+1 blocks of (110) back to the left as (100)s. The
    step counts and rotations were found by a planner that mirrors [execute] on symbolic
    tapes. *)

(** R1 : beta x j (k+1) r -->+ beta (2x+3) (j+2) k r *)
Lemma rule_R1 : forall x j k r, beta x j (S k) r -->+ beta (S (S (S (x + x)))) (S (S j)) k r.
Proof.
  intros. unfold beta at 1.
  start_progress. follow cross_CR. execute. follow cross_CR. execute. follow cross_DL.
  execute. follow cross_GL. execute. follow cross_AR. execute. follow cross_EL.
  do 22 step. rewrite (align_lpow 0 [1;1] _ x). simpl app. follow (L0s (S x) 1).
  unfold beta. finish_norm.
Qed.

(** T1 : beta x j 0 r -->+ gamma (2x+3) 0 (j+1) (10 r) *)
Lemma rule_T1 : forall x j r, beta x j 0 r -->+ gamma (S (S (S (x + x)))) 0 (S j) (1 >> 0 >> r).
Proof.
  intros. unfold beta.
  start_progress. follow cross_CR. execute. follow cross_CR. execute. follow cross_GL.
  execute. follow cross_GL. execute. follow cross_AR. execute. follow cross_EL.
  do 22 step. rewrite (align_lpow 0 [1;1] _ x). simpl app. follow (L0s (S x) 1).
  unfold gamma. finish_norm.
Qed.

(** R2 : gamma x j (m+1) r -->+ gamma (2x+3) (j+2) m r *)
Lemma rule_R2 : forall x j m r, gamma x j (S m) r -->+ gamma (S (S (S (x + x)))) (S (S j)) m r.
Proof.
  intros. unfold gamma at 1.
  start_progress. follow cross_CR. execute. follow cross_CR. execute. follow cross_DL.
  execute. follow cross_GL. execute. follow cross_AR. execute. follow cross_EL.
  do 22 step. rewrite (align_lpow 0 [1;1] _ x). simpl app. follow (L0s (S x) 1).
  unfold gamma. finish_norm.
Qed.

(** T2 : gamma x j 0 r -->+ beta (2x+3) 0 j r *)
Lemma rule_T2 : forall x j r, gamma x j 0 r -->+ beta (S (S (S (x + x)))) 0 j r.
Proof.
  intros. unfold gamma.
  start_progress. follow cross_CR. execute. follow cross_CR. execute. follow cross_AL.
  execute. follow cross_DL. execute. follow cross_CR.
  execute. rewrite (align_lpow 1 [0;1] _ j). simpl app. execute. follow cross_AL.
  do 21 step. rewrite (align_lpow 1 [0;1] _ x). simpl app. rewrite (align_lpow 0 [1;1] _ x). simpl app.
  follow (L0s (S x) 1).
  unfold beta. finish_norm.
Qed.

(** ** Reaching the family from the blank tape *)

(** Literal steps, with the four bounce phases (at steps 143, 361, 1040, 3441, each of the form
    0^inf A> 0 0 (100)^1 1010 (110)^k ...) accelerated by L0s. The endpoint is the machine's
    configuration at step 11,331. *)
Lemma init_reach : c0 -->* gamma 61 0 3 (1 >> 1 >> 0 >> 1 >> const 0).
Proof.
  do 143 step. follow (L0s 2 1).
  do 140 step. follow (L0s 6 1).
  do 253 step. follow (L0s 14 1).
  do 511 step. follow (L0s 30 1).
  unfold gamma. finish_norm.
Qed.

(** ** Non-halting *)

Definition cfg (i : bool * nat * nat * nat * side) : Q * tape :=
  match i with
  | (true, x, j, k, r) => beta x j k r
  | (false, x, j, m, r) => gamma x j m r
  end.

Lemma cfg_step : forall i, exists i', cfg i -->+ cfg i'.
Proof.
  intros [[[[[] x] j] [| k]] r].
  - exists (false, S (S (S (x + x))), 0%nat, S j, 1 >> 0 >> r). apply rule_T1.
  - exists (true, S (S (S (x + x))), S (S j), k, r). apply rule_R1.
  - exists (true, S (S (S (x + x))), 0%nat, j, r). apply rule_T2.
  - exists (false, S (S (S (x + x))), S (S j), k, r). apply rule_R2.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (cfg (false, 61%nat, 0%nat, 3%nat, 1 >> 1 >> 0 >> 1 >> const 0)).
  - apply init_reach.
  - apply progress_nonhalt_simple. apply cfg_step.
Qed.
