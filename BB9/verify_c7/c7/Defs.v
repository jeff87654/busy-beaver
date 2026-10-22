(** * Defs.v : everything the C7 statements mention, apart from busycoq's own definitions (BB9/verify_c7).

    Read this file together with busycoq's verify/TM.v (commit bd2e36f; TM, tape, step, -[ ]->*,
    halted, halts, c0 = (q0, tape0), tape0 = all blank), instantiated for 9 states by BB92.v / Individual92.v
    (states A..I, symbols S0 = 0, S1 = 1, q0 = A, s0 = S0; the same two files as BB9/verify_c04/lib).

    - tm7: the machine C7 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA (H1 undefined = the halt).
    - ones c N: the tape of c is a finite word padded with blanks on both sides, and it holds N ones.
    - iter, arrow (Knuth's up-arrows: arrow k a b = a ↑^k b), f / f_omega (the fast-growing hierarchy f_k, f_omega).
    These bodies are textually those of BB8/verify_m8/Defs.v (M8's statement file) and ../verify_f3/f3/Defs.v. *)
From BB8 Require Import Individual92.
From Coq Require Import List.
Import ListNotations.

(** The machine. *)
Definition tm7 : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (0, R, A)
  | B, 0 => Some (1, L, C)  | B, 1 => Some (1, L, F)
  | C, 0 => Some (1, R, D)  | C, 1 => Some (0, L, B)
  | D, 0 => Some (1, R, A)  | D, 1 => Some (1, L, E)
  | E, 0 => Some (1, L, H)  | E, 1 => Some (0, L, C)
  | F, 0 => Some (1, R, G)  | F, 1 => Some (1, L, D)
  | G, 0 => Some (0, R, G)  | G, 1 => Some (0, R, F)
  | H, 0 => Some (0, L, I)  | H, 1 => None
  | I, 0 => Some (1, L, C)  | I, 1 => Some (0, R, A)
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

(** a ↑^0 b = a * b,  a ↑^(k+1) b = (a ↑^k)^b (1). *)
Fixpoint arrow (k a b : nat) : nat :=
  match k with
  | O => a * b
  | S k' => Nat.iter b (arrow k' a) 1
  end.

(** f 0 n = n + 1,  f (k+1) n = (f k)^n (n),  f_omega n = f n n,  f_w1 n = f_omega^n (n). *)
Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | O => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.

Definition f_w1 (n : nat) : nat := iter n f_omega n.
