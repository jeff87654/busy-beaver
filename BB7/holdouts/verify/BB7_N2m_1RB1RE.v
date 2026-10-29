(** * BB(7) holdout 1RB1RE_1LC0RA_1RF0RD_1LC0LE_1LD0LC_1RG0RE_0RB--- never halts (mirror of N2) *)

(** After 4 steps this machine is in state E on the blank tape, and from there it is the mirror image of
    N2 = 1RB0RC_1RC0RA_1LD0LB_1LE0LA_0LF---_1RC0LG_1LF1LA with the states renamed by [f] (E -> A).  N2 never halts
    (BB7_N2_1RB0RC.v), so neither does this machine.  Uses busycoq's Flip / Permute lemmas (flip_halts, perm_nonhalt). *)

From BB7 Require Import Individual72.
From BB7 Require BB7_N2_1RB0RC.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB1RE_1LC0RA_1RF0RD_1LC0LE_1LD0LC_1RG0RE_0RB--- *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, R, E)
  | B, 0 => Some (1, L, C)  | B, 1 => Some (0, R, A)
  | C, 0 => Some (1, R, F)  | C, 1 => Some (0, R, D)
  | D, 0 => Some (1, L, C)  | D, 1 => Some (0, L, E)
  | E, 0 => Some (1, L, D)  | E, 1 => Some (0, L, C)
  | F, 0 => Some (1, R, G)  | F, 1 => Some (0, R, E)
  | G, 0 => Some (0, R, B)  | G, 1 => None
  end.

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).

(** State renaming from (flip tm) to N2. *)
Definition f (q : Q) : Q :=
  match q with
  | A => G | B => F | C => C | D => B | E => A | F => D | G => E
  end.

Lemma perm : Perm (flip tm) BB7_N2_1RB0RC.tm f.
Proof.
  split.
  - intros q s H. destruct q, s; cbv in H |- *; congruence.
  - intros q s s' d q' H. destruct q, s; cbv in H |- *; inversion H; reflexivity.
Qed.

Lemma start : c0 -->* (E;; tape0).
Proof. unfold c0, tape0. do 4 step. finish. Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (E;; tape0).
  - exact start.
  - intro H. apply flip_halts in H. simpl in H.
    revert H. change (~ halts (flip tm) (E;; tape0)).
    apply (perm_nonhalt (flip tm) BB7_N2_1RB0RC.tm f E tape0 perm).
    exact BB7_N2_1RB0RC.nonhalt.
Qed.
