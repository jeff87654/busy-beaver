(** * Statement.v : what is proved about f3_0RC, in terms of Defs.v and busycoq's TM.v only (bb9_f3_coq).

    f3_0RC = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF

    To check the claims, read this file, Defs.v (the machine tm3, the ones count, iter, arrow, f, f_omega) and
    busycoq's verify/TM.v (commit bd2e36f: TM, tape, the step relation, c0 = (q0, tape0) with tape0 the all-blank
    tape, -[ tm ]->*, halted tm c := tm (q, s) = None, halts tm c).  f3 halts on the undefined transition H1 = "---",
    where the head reads a 1, so its score is the number N of ones on the halted tape.

    Every theorem is proved in one line from Final3.v (on top of Sim.v and the X development in lib/, dev/, k31/,
    score/); probe.v runs Print Assumptions on each.  The constant in f3_beats_m8_bound is the upper bound of
    BB8/verify_m8's Statement.m8_bracket (every halting count of M8 is below it), with the same Defs.v text for
    f_omega and arrow. *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat String Ascii.
From F3 Require Import Defs.
From F3 Require Final3.
Local Open Scope nat_scope.

(** ** 1. The table, against the machine string (standard format: 9 groups of 6 characters separated by "_"; the
    transition (state i, symbol j) is the three characters at 7 i + 3 j; "---" is undefined, i.e. None). *)
Definition f3_string : string := "1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF".

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

Theorem f3_table : String.length f3_string = 62 /\ forall q s, tm3 (q, s) = parse_slot f3_string (st_idx q) (sym_idx s).
Proof. split; [reflexivity |]. intros q s. destruct q, s; reflexivity. Qed.

(** ** 2. Halting and the score *)
Theorem f3_halts : halts tm3 c0.
Proof. exact Final3.f3_halts. Qed.

(** The score: 6 * iter (2^^13 3 - 5) (2 ↑^6 _) (iter 4 (2 ↑^5 _) 4) - 14 = 12 R'' + 10, where 2 R'' + 4 is the value
    of exhaustion #1's clear (R'' = iter (2 B - 1) (U 5) (iter 4 (U 4) 0) in the development). *)
Theorem f3_lower : forall c N, c0 -[ tm3 ]->* c -> halted tm3 c -> ones c N ->
  f_omega (f_omega (6 * iter (arrow 13 2 3 - 5) (arrow 6 2) (iter 4 (arrow 5 2) 4) - 14)) < N.
Proof. exact Final3.f3_lower. Qed.

(** M8's (and C04's) score is below f_omega (f_omega (6 * arrow 13 2 3 + 3)) (BB8/verify_m8 Statement.m8_bracket). *)
Theorem f3_beats_m8_bound : forall c N, c0 -[ tm3 ]->* c -> halted tm3 c -> ones c N ->
  f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N.
Proof. exact Final3.f3_beats_m8_bound. Qed.
