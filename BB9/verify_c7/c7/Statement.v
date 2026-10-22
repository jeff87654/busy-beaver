(** * Statement.v : what is proved about C7, in terms of Defs.v and busycoq's TM.v only (BB9/verify_c7).

    C7 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA

    To check the claims, read this file, Defs.v (the machine tm7, the ones count, iter, arrow, f, f_omega) and
    busycoq's verify/TM.v (commit bd2e36f: TM, tape, the step relation, c0 = (q0, tape0) with tape0 the all-blank
    tape, -[ tm ]->*, halted tm c := tm (q, s) = None, halts tm c).  C7 halts on the undefined transition H1 = "---",
    where the head reads a 1, so its score is the number N of ones on the halted tape.

    Every theorem is proved in one line from Final7.v (on top of Sim.v and the X' development in x/); probe.v runs
    Print Assumptions on each. *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat String Ascii.
From C7 Require Import Defs.
From C7 Require Final7.
Local Open Scope nat_scope.

(** ** 1. The table, against the machine string (standard format: 9 groups of 6 characters separated by "_"; the
    transition (state i, symbol j) is the three characters at 7 i + 3 j; "---" is undefined, i.e. None). *)
Definition c7_string : string := "1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA".

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

Theorem c7_table : String.length c7_string = 62 /\ forall q s, tm7 (q, s) = parse_slot c7_string (st_idx q) (sym_idx s).
Proof. split; [reflexivity |]. intros q s. destruct q, s; reflexivity. Qed.

(** ** 2. Halting and the score *)
Theorem c7_halts : halts tm7 c0.
Proof. exact Final7.c7_halts. Qed.

(** The score: at least f_omega^4 (6 * 2^^13 3 + 3), i.e. f_omega^4 (12 B + 27) with 2B + 4 = 2^^13 3 (B = C04's
    level-0 accumulator, the first clear).  The proof follows C7's run: eleven rebuilds and a counter, then a cascade
    of eight sub-steps whose residues mod 5 are fixed (every accumulator is congruent to the same tower residue modulo
    2^5 3^4 5^14), ending in the halting branch; the four f_omega come from the levels of the clears after J3, J4, J5, J6. *)
Theorem c7_lower : forall c N, c0 -[ tm7 ]->* c -> halted tm7 c -> ones c N ->
  f_omega (f_omega (f_omega (f_omega (6 * arrow 13 2 3 + 3)))) < N.
Proof. exact Final7.c7_lower. Qed.

(** M8's (and C04's) score is below f_omega (f_omega (6 * arrow 13 2 3 + 3)) (BB8/verify_m8 Statement.m8_bracket). *)
Theorem c7_beats_m8_bound : forall c N, c0 -[ tm7 ]->* c -> halted tm7 c -> ones c N ->
  f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N.
Proof. exact Final7.c7_beats_m8_bound. Qed.
