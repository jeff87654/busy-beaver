(** * Defs.v : everything the statements in Statement.v mention, apart from busycoq's own definitions (BB7/verify).

    Read this file together with busycoq's verify/TM.v (commit bd2e36f: TM, tape, step, -[ ]->*, halted, halts,
    c0 = (q0, tape0), tape0 = all blank), instantiated for 7 states by BB72.v / Individual72.v (states A..G,
    symbols S0 = 0, S1 = 1, q0 = A, s0 = S0).

    - tm231, tm232: the machines champ_231 = 1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB and
      champ_232 = 1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_1LC0RB (C1 undefined = the halt; they differ only in G0).
    - ones c N: the tape of c is a finite word padded with blanks on both sides, and it holds N ones
      (sym_val, count1, ones: textually the same as BB8/verify_m8/Defs.v).
    - iter; U, W (the score's recursion, through the pair fixpoint UW); arrow (Knuth's up-arrows: arrow k a b = a ↑^k b,
      arrow 0 a b = a * b; textually the same as BB8/verify_m8/Defs.v). *)
From BB7 Require Import Individual72.
From Coq Require Import List.
Import ListNotations.

(** The machines. *)
Definition tm231 : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (0, R, G)
  | B, 0 => Some (1, R, C)  | B, 1 => Some (1, R, B)
  | C, 0 => Some (0, R, D)  | C, 1 => None
  | D, 0 => Some (0, L, E)  | D, 1 => Some (0, L, D)
  | E, 0 => Some (0, L, F)  | E, 1 => Some (1, L, E)
  | F, 0 => Some (1, R, A)  | F, 1 => Some (1, L, F)
  | G, 0 => Some (0, L, D)  | G, 1 => Some (0, R, B)
  end.

Definition tm232 : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (0, R, G)
  | B, 0 => Some (1, R, C)  | B, 1 => Some (1, R, B)
  | C, 0 => Some (0, R, D)  | C, 1 => None
  | D, 0 => Some (0, L, E)  | D, 1 => Some (0, L, D)
  | E, 0 => Some (0, L, F)  | E, 1 => Some (1, L, E)
  | F, 0 => Some (1, R, A)  | F, 1 => Some (1, L, F)
  | G, 0 => Some (1, L, C)  | G, 1 => Some (0, R, B)
  end.

(** Counting ones. *)
Definition sym_val (s : Sym) : nat :=
  match s with
  | S0 => 0
  | S1 => 1
  end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with
  | [] => 0
  | x :: t => sym_val x + count1 t
  end.

Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

(** Numbers. *)
Local Open Scope nat_scope.

Fixpoint iter (n : nat) (g : nat -> nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n' => g (iter n' g x)
  end.

(** The score's recursion:
      U 0 x = 3x + 9,   U (j+1) x = (U j)^(x+2-j) (W j 3),   W 0 B = B,   W (j+1) B = U j (W j B).
    U j x is the counter after one unit of a digit at list position j is cleared, starting from counter x;
    W j B is the counter after j digits equal to 1 (positions 0..j-1) are cleared, starting from B. *)
Fixpoint UW (j : nat) : (nat -> nat) * (nat -> nat) :=
  match j with
  | O => (fun x => 3 * x + 9, fun B => B)
  | S i => let p := UW i in (fun x => iter (x + 2 - i) (fst p) (snd p 3), fun B => fst p (snd p B))
  end.

Definition U (j : nat) : nat -> nat := fst (UW j).
Definition W (j : nat) : nat -> nat := snd (UW j).

(** a ↑^0 b = a * b,  a ↑^(k+1) b = (a ↑^k)^b (1). *)
Fixpoint arrow (k a b : nat) : nat :=
  match k with
  | O => a * b
  | S k' => Nat.iter b (arrow k' a) 1
  end.
