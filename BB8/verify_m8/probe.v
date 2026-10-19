(** Independent probe for M8 (coq_m8/).  Build order: BB82.v, Individual82.v, Tm8.v, Sim.v, Transfer.v, probe.v, all with
    -Q <coq_m8> M8, on top of the compiled C04 tree BB9/verify_c04 (lib = BB8, dev = Dev, k31 = K31, score = Score,
    fgh = Fgh).  The optional Beats8.v (comparison with the BB(8) champion's exact count) also loads the repo's BB8/verify
    files (logical BB8: BB82, Individual82, BB8_champ35_1RB0RA/bound/exact).  Nothing else is loaded.
    Machine: M8 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---.
    (1) The compiled transition table Tm8.tm8 (a busycoq TM over the 8-state context BB82) equals the machine string,
        entry by entry: by eq_refl, and also against a parser of the literal string (16 slots, H1 undefined = None).
        c0 is the blank tape in state A.
    (2) The definitions the statements use are printed (Tm8.ones is a verbatim copy of BB8_champ35_bound.ones;
        Abs.arrow is the same Fixpoint as BB8_champ35_bound.arrow).
    (3) The main theorems have the stated types.  (4) They use no axioms (one Print Assumptions on their conjunction). *)
From M8 Require Import Individual82.
From Coq Require Import String Ascii.
From BB8 Require BB9_fw2_bound.
From Dev Require Abs.
From Score Require Score.
From Fgh Require FArith Exact.
From M8 Require Tm8 Sim Transfer Beats8 Headline8.
From BB8 Require BB8_champ35_1RB0RA BB8_champ35_bound BB8_champ35_exact.
Local Open Scope sym_scope.

Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Print Tm8.tm8.
Check (eq_refl : Tm8.tm8 (A, 0) = Some (1, R, B)).
Check (eq_refl : Tm8.tm8 (A, 1) = Some (0, R, A)).
Check (eq_refl : Tm8.tm8 (B, 0) = Some (1, L, C)).
Check (eq_refl : Tm8.tm8 (B, 1) = Some (1, L, F)).
Check (eq_refl : Tm8.tm8 (C, 0) = Some (1, R, D)).
Check (eq_refl : Tm8.tm8 (C, 1) = Some (0, L, B)).
Check (eq_refl : Tm8.tm8 (D, 0) = Some (1, R, A)).
Check (eq_refl : Tm8.tm8 (D, 1) = Some (1, L, E)).
Check (eq_refl : Tm8.tm8 (E, 0) = Some (1, L, H)).
Check (eq_refl : Tm8.tm8 (E, 1) = Some (0, L, C)).
Check (eq_refl : Tm8.tm8 (F, 0) = Some (1, R, G)).
Check (eq_refl : Tm8.tm8 (F, 1) = Some (1, L, D)).
Check (eq_refl : Tm8.tm8 (G, 0) = Some (0, R, G)).
Check (eq_refl : Tm8.tm8 (G, 1) = Some (0, R, F)).
Check (eq_refl : Tm8.tm8 (H, 0) = Some (1, R, G)).
Check (eq_refl : Tm8.tm8 (H, 1) = None).

(** The table against a parser of the literal machine string (standard format: 8 groups of 6 chars, '_'-separated;
    each slot = write symbol, direction, next state; "---" = undefined). *)
Definition m8_string : string := "1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---".

Definition st_idx (q : Q) : nat :=
  match q with A => 0 | B => 1 | C => 2 | D => 3 | E => 4 | F => 5 | G => 6 | H => 7 end%nat.
Definition sym_idx (s : Sym) : nat := match s with S0 => 0 | S1 => 1 end%nat.

Definition p_sym (c : ascii) : option Sym :=
  match c with "0"%char => Some S0 | "1"%char => Some S1 | _ => None end.
Definition p_dir (c : ascii) : option dir :=
  match c with "L"%char => Some L | "R"%char => Some R | _ => None end.
Definition p_st (c : ascii) : option Q :=
  match c with
  | "A"%char => Some A | "B"%char => Some B | "C"%char => Some C | "D"%char => Some D
  | "E"%char => Some E | "F"%char => Some F | "G"%char => Some G | "H"%char => Some H | _ => None
  end.

Definition parse_slot (str : string) (i j : nat) : option (Sym * dir * Q) :=
  let k := 7 * i + 3 * j in
  match get k str, get (k + 1) str, get (k + 2) str with
  | Some a, Some b, Some c =>
    match p_sym a, p_dir b, p_st c with
    | Some s, Some d, Some q => Some (s, d, q)
    | _, _, _ => None
    end
  | _, _, _ => None
  end.

Lemma m8_string_ok : length m8_string = 55 /\ forall q s, Tm8.tm8 (q, s) = parse_slot m8_string (st_idx q) (sym_idx s).
Proof. split; [reflexivity |]. intros q s. destruct q, s; reflexivity. Qed.
Check (eq_refl : parse_slot m8_string 7%nat 1%nat = None).   (* H1 = "---" *)

(** Definitions used by the statements *)
Print Tm8.ones.
Print Tm8.count1.
Print Tm8.sym_val.
Print Score.f.
Print Score.f_omega.
Print FArith.f_w1.
Print Abs.Bx.
Check Abs.Bx_def.
Check FArith.Bx_knuth.
Print Abs.arrow.
Print BB8_champ35_bound.arrow.
Check Beats8.arrow_same.
Print Exact.sigma_c04.
Print Sim.stmap.
Print Sim.Rel.

(** Main theorems *)
Check Transfer.m8_halts.
Check Transfer.m8_fgh_bracket.
Check Transfer.m8_fgh_coarse.
Check Transfer.m8_score_exact.
Check Transfer.m8_score_reached.
Check Transfer.m8_sigma_bracket.
Check Transfer.m8_beats_bb8.
Check Transfer.m8_beats_fw2.
Check Beats8.m8_beats_bb8r.
Check Beats8.m8_beats_champ35.
Check BB8_champ35_exact.score_closed.
Check Transfer.m8_score_to_c04.
Check Transfer.m8_score_from_c04.
Check Sim.sim_step.
Check Sim.m8_to_c04.
Check Sim.c04_to_m8.

Definition m8_all : Prop :=
  halts Tm8.tm8 c0 /\
  (forall c N, c0 -[ Tm8.tm8 ]->* c -> halted Tm8.tm8 c -> Tm8.ones c N ->
     Score.f_omega (Score.f_omega (12 * Abs.Bx + 26)) < N /\ N < Score.f_omega (Score.f_omega (12 * Abs.Bx + 27)))%nat /\
  (forall c N, c0 -[ Tm8.tm8 ]->* c -> halted Tm8.tm8 c -> Tm8.ones c N -> FArith.f_w1 3 < N /\ N < FArith.f_w1 4)%nat /\
  (forall c N, c0 -[ Tm8.tm8 ]->* c -> halted Tm8.tm8 c -> Tm8.ones c N -> N = Exact.sigma_c04) /\
  (exists c, c0 -[ Tm8.tm8 ]->* c /\ halted Tm8.tm8 c /\ Tm8.ones c Exact.sigma_c04) /\
  (Score.f_omega (Score.f_omega (12 * Abs.Bx + 26)) < Exact.sigma_c04 /\
     Exact.sigma_c04 < Score.f_omega (Score.f_omega (12 * Abs.Bx + 27)))%nat /\
  (forall c N, c0 -[ Tm8.tm8 ]->* c -> halted Tm8.tm8 c -> Tm8.ones c N ->
     12 * Abs.arrow 37 2 3 + 59 < N)%nat /\
  (2 * Abs.Bx + 4 = Abs.arrow 13 2 3)%nat.

Theorem m8_all_ok : m8_all.
Proof.
  split; [exact Transfer.m8_halts |]. split; [exact Transfer.m8_fgh_bracket |]. split; [exact Transfer.m8_fgh_coarse |].
  split; [exact Transfer.m8_score_exact |]. split; [exact Transfer.m8_score_reached |].
  split; [exact Transfer.m8_sigma_bracket |]. split; [exact Transfer.m8_beats_bb8 |].
  exact FArith.Bx_knuth.
Qed.

Print Assumptions m8_all_ok.
Print Assumptions Transfer.m8_beats_fw2.
Print Assumptions Transfer.m8_score_to_c04.
Print Assumptions Transfer.m8_score_from_c04.
Print Assumptions m8_string_ok.
Print Assumptions Beats8.m8_beats_bb8r.
Print Assumptions Beats8.m8_beats_champ35.

(** The bound without B (Headline8.v, from C04's fgh/Headline.v): f_omega^3 12 < N < f_omega^3 13. *)
Definition m8_headline : Prop :=
  forall c N, c0 -[ Tm8.tm8 ]->* c -> halted Tm8.tm8 c -> Tm8.ones c N ->
    (Score.f_omega (Score.f_omega (Score.f_omega 12)) < N /\ N < Score.f_omega (Score.f_omega (Score.f_omega 13)))%nat.

Theorem m8_headline_ok : m8_headline.
Proof. exact Headline8.m8_fgh3. Qed.

Print Assumptions m8_headline_ok.
