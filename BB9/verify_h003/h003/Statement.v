(** * Statement.v : what is proved about h003, in terms of Defs.v and busycoq's TM.v only (BB9/verify_h003).

    h003 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC

    To check the claims, read this file, Defs.v (the machine tmh, the ones count, iter, arrow, f, f_omega) and
    busycoq's verify/TM.v (commit bd2e36f: TM, tape, the step relation, c0 = (q0, tape0) with tape0 the all-blank
    tape, -[ tm ]->*, halted tm c := tm (q, s) = None, halts tm c).  h003 halts on the undefined transition H1 = "---",
    where the head reads a 1, so its score is the number N of ones on the halted tape.

    Every theorem is proved in one line from Final.v (on top of Sim.v and the X3 development in x/); probe.v runs
    Print Assumptions on each. *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat String Ascii.
From H3 Require Import Defs.
From H3 Require Final.
Local Open Scope nat_scope.

(** ** 1. The table, against the machine string (standard format: 9 groups of 6 characters separated by "_"; the
    transition (state i, symbol j) is the three characters at 7 i + 3 j; "---" is undefined, i.e. None). *)
Definition h003_string : string := "1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC".

Definition p_sym (c : ascii) : option Sym :=
  if Ascii.eqb c "0"%char then Some S0 else if Ascii.eqb c "1"%char then Some S1 else None.
Definition p_dir (c : ascii) : option dir :=
  if Ascii.eqb c "L"%char then Some L else if Ascii.eqb c "R"%char then Some R else None.
Definition p_st (c : ascii) : option Q :=
  match c with
  | "A"%char => Some A | "B"%char => Some B | "C"%char => Some C | "D"%char => Some D | "E"%char => Some E
  | "F"%char => Some F | "G"%char => Some G | "H"%char => Some H | "I"%char => Some I | _ => None
  end.
Definition st_idx (q : Q) : nat :=
  match q with A => 0 | B => 1 | C => 2 | D => 3 | E => 4 | F => 5 | G => 6 | H => 7 | I => 8 end.
Definition sym_idx (s : Sym) : nat := match s with S0 => 0 | S1 => 1 end.

Definition parse_slot (str : string) (i j : nat) : option (Sym * dir * Q) :=
  let k := 7 * i + 3 * j in
  match String.get k str, String.get (k + 1) str, String.get (k + 2) str with
  | Some a, Some b, Some c =>
    match p_sym a, p_dir b, p_st c with
    | Some s, Some d, Some q => Some (s, d, q)
    | _, _, _ => None
    end
  | _, _, _ => None
  end.

Theorem h003_table : String.length h003_string = 62 /\ forall q s, tmh (q, s) = parse_slot h003_string (st_idx q) (sym_idx s).
Proof. split; [reflexivity |]. intros q s. destruct q, s; reflexivity. Qed.

(** ** 2. Halting and the score *)
Theorem h003_halts : halts tmh c0.
Proof. exact Final.h003_halts. Qed.

(** The score: at least f_omega^6 (6 * 2^^13 3 + 2), i.e. f_omega^6 (12 B + 26) with 2B + 4 = 2^^13 3 (B = C04's
    level-0 accumulator, the first clear).  The proof follows h003's run: the top Top(12B+27) is rebuilt four times
    (branches 4, 3, 1, 1 of its size mod 5; every accumulator is congruent to the same tower residue modulo
    2^5 3^4 5^14), each rebuild a clear at a depth at least the previous accumulator (one f_omega each); at the fifth
    top (size 0 mod 5) the machine runs M8's cascade and endgame, which add two more f_omega. *)
Theorem h003_lower : forall c N, c0 -[ tmh ]->* c -> halted tmh c -> ones c N ->
  f_omega (f_omega (f_omega (f_omega (f_omega (f_omega (6 * arrow 13 2 3 + 2)))))) < N.
Proof. exact Final.h003_lower. Qed.

(** Hence also f_omega^7 (12) < N (f_omega 12 <= B). *)
Theorem h003_lower7_12 : forall c N, c0 -[ tmh ]->* c -> halted tmh c -> ones c N ->
  f_omega (f_omega (f_omega (f_omega (f_omega (f_omega (f_omega 12)))))) < N.
Proof. exact Final.h003_lower7_12. Qed.

(** M8's (and C04's) score is below f_omega (f_omega (6 * arrow 13 2 3 + 3)) (BB8/verify_m8 Statement.m8_bracket). *)
Theorem h003_beats_m8_bound : forall c N, c0 -[ tmh ]->* c -> halted tmh c -> ones c N ->
  f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N.
Proof. exact Final.h003_beats_m8_bound. Qed.
