(** * Statement.v : what is proved about M8, in terms of Defs.v and busycoq's TM.v only.

    M8 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---

    To check the claims, read three things: this file, Defs.v (the machine tm8, the ones count, iter, arrow, f,
    f_omega, f_w1), and busycoq's verify/TM.v (commit bd2e36f: TM, tape, the step relation, c0 = (q0, tape0) with
    tape0 the all-blank tape, -[ tm ]->*, halted tm c := tm (q, s) = None, halts tm c). M8 halts on the undefined
    transition H1 = "---", where the head reads a 1, so its score is the number N of ones on the halted tape.

    Every theorem below is proved in one line from the development (Transfer.v, Beats8.v, Headline8.v, on top of the
    C04 development in BB9/verify_c04) and Bridge.v; probe.v runs Print Assumptions on each of them.

    The comparisons also name two other machines, the previous BB(8) entry champ35 (BB8/verify) and fw2 (BB9),
    through their own Coq files. Their tables are pinned here against their strings, like tm8's (section 1); their
    ones counts BB8_champ35_bound.ones and BB9_fw2_bound.ones are textual copies of Defs.ones over their own
    8- and 9-state symbol types (probe.v prints them). *)
From M8 Require Import Individual82.
From Coq Require Import Lia PeanoNat String Ascii.
From M8 Require Import Defs.
From BB8 Require Individual92 BB92 BB9_fw2_1RB0RD BB9_fw2_bound.
From BB8 Require BB82 Individual82 BB8_champ35_1RB0RA BB8_champ35_bound.
From Fgh Require Exact.
From M8 Require Bridge Transfer Beats8 Headline8.
Local Open Scope nat_scope.

(** busycoq's machine semantics for the other two machines' state sets (9 states for fw2, 8 for champ35). *)
Module T9 := BB8.Individual92.Individual92.Permute.Flip.Compute.TM.
Module C8 := BB8.Individual82.Individual82.Permute.Flip.Compute.TM.

(** ** 1. The tables, against the machine strings

    Standard format: states A, B, C, ... in order, two transitions each (reading 0, reading 1), states separated by
    "_". A transition is the symbol written (0/1), the move (L/R) and the next state, so transition (state i, symbol j)
    is the three characters at 7i + 3j. A transition whose next state is not a state letter ("---", or "1RZ" for a
    halting transition) is undefined: the table returns None there. *)
Definition p_dir (c : ascii) : option dir :=
  if Ascii.eqb c "L"%char then Some L else if Ascii.eqb c "R"%char then Some R else None.

Definition parse_slot {Q' Sym' : Type} (p_sym : ascii -> option Sym') (p_st : ascii -> option Q')
    (str : string) (i j : nat) : option (Sym' * dir * Q') :=
  let k := 7 * i + 3 * j in
  match String.get k str, String.get (k + 1) str, String.get (k + 2) str with
  | Some a, Some b, Some c =>
    match p_sym a, p_dir b, p_st c with
    | Some s, Some d, Some q => Some (s, d, q)
    | _, _, _ => None
    end
  | _, _, _ => None
  end.

(** M8 *)
Definition m8_string : string := "1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---".
Definition m8_sym (c : ascii) : option Sym :=
  if Ascii.eqb c "0"%char then Some S0 else if Ascii.eqb c "1"%char then Some S1 else None.
Definition m8_st (c : ascii) : option Q :=
  match c with
  | "A"%char => Some A | "B"%char => Some B | "C"%char => Some C | "D"%char => Some D
  | "E"%char => Some E | "F"%char => Some F | "G"%char => Some G | "H"%char => Some H | _ => None
  end.
Definition m8_idx (q : Q) : nat :=
  match q with A => 0 | B => 1 | C => 2 | D => 3 | E => 4 | F => 5 | G => 6 | H => 7 end.
Definition m8_sidx (s : Sym) : nat := match s with S0 => 0 | S1 => 1 end.

Theorem m8_table : String.length m8_string = 55 /\
  forall q s, tm8 (q, s) = parse_slot m8_sym m8_st m8_string (m8_idx q) (m8_sidx s).
Proof. split; [reflexivity |]. intros q s. destruct q, s; reflexivity. Qed.

(** champ35, the previous BB(8) entry (BB8/verify; its halting transition is E0 = 1RZ) *)
Definition champ35_string : string := "1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_1LC0RH_1RG1LF".
Definition c8_sym (c : ascii) : option BB8.BB82.sym :=
  if Ascii.eqb c "0"%char then Some BB8.BB82.S0 else if Ascii.eqb c "1"%char then Some BB8.BB82.S1 else None.
Definition c8_st (c : ascii) : option BB8.BB82.state :=
  match c with
  | "A"%char => Some BB8.BB82.A | "B"%char => Some BB8.BB82.B | "C"%char => Some BB8.BB82.C | "D"%char => Some BB8.BB82.D
  | "E"%char => Some BB8.BB82.E | "F"%char => Some BB8.BB82.F | "G"%char => Some BB8.BB82.G | "H"%char => Some BB8.BB82.H
  | _ => None
  end.
Definition c8_idx (q : BB8.BB82.state) : nat :=
  match q with
  | BB8.BB82.A => 0 | BB8.BB82.B => 1 | BB8.BB82.C => 2 | BB8.BB82.D => 3 | BB8.BB82.E => 4 | BB8.BB82.F => 5 | BB8.BB82.G => 6 | BB8.BB82.H => 7
  end.
Definition c8_sidx (s : BB8.BB82.sym) : nat := match s with BB8.BB82.S0 => 0 | BB8.BB82.S1 => 1 end.

Theorem champ35_table : String.length champ35_string = 55 /\
  forall q s, BB8_champ35_1RB0RA.tm (q, s) = parse_slot c8_sym c8_st champ35_string (c8_idx q) (c8_sidx s).
Proof. split; [reflexivity |]. intros q s. destruct q, s; reflexivity. Qed.

(** fw2 (BB9/verify_fw2; its halting transition is I0 = 1RZ) *)
Definition fw2_string : string := "1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA".
Definition f9_sym (c : ascii) : option BB92.sym :=
  if Ascii.eqb c "0"%char then Some BB92.S0 else if Ascii.eqb c "1"%char then Some BB92.S1 else None.
Definition f9_st (c : ascii) : option BB92.state :=
  match c with
  | "A"%char => Some BB92.A | "B"%char => Some BB92.B | "C"%char => Some BB92.C | "D"%char => Some BB92.D
  | "E"%char => Some BB92.E | "F"%char => Some BB92.F | "G"%char => Some BB92.G | "H"%char => Some BB92.H
  | "I"%char => Some BB92.I | _ => None
  end.
Definition f9_idx (q : BB92.state) : nat :=
  match q with
  | BB92.A => 0 | BB92.B => 1 | BB92.C => 2 | BB92.D => 3 | BB92.E => 4 | BB92.F => 5 | BB92.G => 6 | BB92.H => 7
  | BB92.I => 8
  end.
Definition f9_sidx (s : BB92.sym) : nat := match s with BB92.S0 => 0 | BB92.S1 => 1 end.

Theorem fw2_table : String.length fw2_string = 62 /\
  forall q s, BB9_fw2_1RB0RD.tm (q, s) = parse_slot f9_sym f9_st fw2_string (f9_idx q) (f9_sidx s).
Proof. split; [reflexivity |]. intros q s. destruct q, s; reflexivity. Qed.

(** ** 2. M8 halts, and its score *)

Theorem m8_halts : halts tm8 c0.
Proof. exact Transfer.m8_halts. Qed.

Theorem m8_reached : exists c N, c0 -[ tm8 ]->* c /\ halted tm8 c /\ ones c N.
Proof. destruct Transfer.m8_score_reached as [c [H1 [H2 H3]]]. exists c, Exact.sigma_c04. exact (conj H1 (conj H2 H3)). Qed.

(** The headline. *)
Theorem m8_fgh3 : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
  f_omega (f_omega (f_omega 12)) < N /\ N < f_omega (f_omega (f_omega 13)).
Proof. intros c N H1 H2 H3. exact (Bridge.fw3_bridge 12 13 N (Headline8.m8_fgh3 c N H1 H2 H3)). Qed.

(** More precisely (6 * arrow 13 2 3 + 2 = 6 * (2 ↑^13 3) + 2 = 12 B + 26). *)
Theorem m8_bracket : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
  f_omega (f_omega (6 * arrow 13 2 3 + 2)) < N /\ N < f_omega (f_omega (6 * arrow 13 2 3 + 3)).
Proof.
  intros c N H1 H2 H3. destruct Bridge.bx_eq as [E2 E3].
  exact (Bridge.fw2_bridge _ _ _ _ N E2 E3 (Transfer.m8_fgh_bracket c N H1 H2 H3)).
Qed.

(** Coarser: f_(omega+1)(3) < N < f_(omega+1)(4). *)
Theorem m8_coarse : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N -> f_w1 3 < N /\ N < f_w1 4.
Proof. intros c N H1 H2 H3. exact (Bridge.fw1_bridge 3 4 N (Transfer.m8_fgh_coarse c N H1 H2 H3)). Qed.

(** The exact score. [Exact.sigma_c04] is a pure arithmetic recursion (on numbers only; it never mentions a machine),
    so this is a real statement about the halting tape. *)
Theorem m8_score_exact : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N -> N = Exact.sigma_c04.
Proof. exact Transfer.m8_score_exact. Qed.

(** ** 3. Comparisons *)

(** Above the previous BB(8) entry's score 12 (2 ↑^37 3) + 59. *)
Theorem m8_beats_bb8 : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N -> 12 * arrow 37 2 3 + 59 < N.
Proof.
  intros c N H1 H2 H3. exact (Bridge.lin_bb8 _ _ N (Bridge.arrow_eq 37 2 3) (Transfer.m8_beats_bb8 c N H1 H2 H3)).
Qed.

(** Above champ35's exact count, from its own Coq files: champ35 halts with Nf ones and Nf + 1 < N (its halting
    transition writes a 1 on a 0, so its score is Nf + 1). *)
Theorem m8_beats_champ35 : exists c N, c0 -[ tm8 ]->* c /\ halted tm8 c /\ ones c N /\
  exists cf Nf, C8.evstep BB8_champ35_1RB0RA.tm C8.c0 cf /\ C8.halted BB8_champ35_1RB0RA.tm cf /\
    BB8_champ35_bound.ones cf Nf /\ Nf + 1 < N.
Proof. exact Beats8.m8_beats_champ35. Qed.

(** Above fw2's exact count (fw2's score is Nf + 1), and above f_omega (f_omega 465009). *)
Theorem m8_beats_fw2 : exists c N, c0 -[ tm8 ]->* c /\ halted tm8 c /\ ones c N /\
  f_omega (f_omega (465 * 1000 + 9)) < N /\
  exists cf Nf, T9.evstep BB9_fw2_1RB0RD.tm T9.c0 cf /\ T9.halted BB9_fw2_1RB0RD.tm cf /\
    BB9_fw2_bound.ones cf Nf /\ Nf + 1 < N.
Proof.
  destruct Transfer.m8_beats_fw2 as [c [N [H1 [H2 [H3 [H4 H5]]]]]].
  exists c, N. exact (conj H1 (conj H2 (conj H3 (conj (Bridge.fw2_lower_bridge _ N H4) H5)))).
Qed.
