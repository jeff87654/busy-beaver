(** Independent probe: the Coq table [tm] equals the machine string, and the main
    theorems are axiom-free.  Requires all of BB83 to compile first. *)
From TM83 Require Import Individual83 BB83_rules BB83_start BB83_run BB83_score.
From Coq Require Import String Ascii List.
Import ListNotations.
Open Scope string_scope.

Definition machine : string :=
  "2LH1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LD0RH_1RC2LE1LG_0LA0LD1RZ_1LD2RA2LG_2RD1LF1LG".

Definition qi (q : state) : nat :=
  match q with A => 0 | B => 1 | C => 2 | D => 3
            | E => 4 | F => 5 | G => 6 | H => 7 end.
Definition si (s : sym) : nat := match s with S0 => 0 | S1 => 1 | S2 => 2 end.
Definition sym_of (c : ascii) : option sym :=
  match c with
  | "0"%char => Some S0
  | "1"%char => Some S1
  | "2"%char => Some S2
  | _ => None end.
Definition dir_of (c : ascii) : option dir :=
  match c with
  | "L"%char => Some L | "R"%char => Some R | _ => None end.
(** [Some (Some q)] = go to q; [Some None] = halt (Z); [None] = parse error *)
Definition st_of (c : ascii) : option (option state) :=
  match c with
  | "A"%char => Some (Some A)
  | "B"%char => Some (Some B)
  | "C"%char => Some (Some C)
  | "D"%char => Some (Some D)
  | "E"%char => Some (Some E)
  | "F"%char => Some (Some F)
  | "G"%char => Some (Some G)
  | "H"%char => Some (Some H)
  | "Z"%char => Some None
  | _ => None end.

(** Each row has 9 characters (3 symbols x 3), rows separated by "_".
    The rows therefore start at 0, 10, ... , so k = 10 * qi + 3 * si. *)
Definition parsed (q : state) (s : sym) : option (option (sym * dir * state)) :=
  let k := 10 * qi q + 3 * si s in
  match String.get k machine, String.get (k + 1) machine, String.get (k + 2) machine with
  | Some c1, Some c2, Some c3 =>
    match sym_of c1, dir_of c2, st_of c3 with
    | Some w, Some d, Some (Some q') => Some (Some (w, d, q'))
    | Some _, Some _, Some None => Some None
    | _, _, _ => None
    end
  | _, _, _ => None
  end.

Lemma underscores :
    String.get 9 machine = Some "_"%char /\
  String.get 19 machine = Some "_"%char /\
  String.get 29 machine = Some "_"%char /\
  String.get 39 machine = Some "_"%char /\
  String.get 49 machine = Some "_"%char /\
  String.get 59 machine = Some "_"%char /\
  String.get 69 machine = Some "_"%char /\
  String.length machine = 79.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma halt_entries :
  String.substring 36 3 machine = "0RH" /\
  String.substring 56 3 machine = "1RZ".
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma table_matches_string : forall q s, Some (tm (q, s)) = parsed q s.
Proof. intros [] []; vm_compute; reflexivity. Qed.

Lemma c0_is_blank_A : c0 = (A, (Streams.const S0, S0, Streams.const S0)).
Proof. reflexivity. Qed.

(** The statements of the main results, for the record. *)
Check bb83_halts.
Check reaches_final.
Check final_halted.
Check fomega1_iter3_lt_sigma.
Check bb83_main.

Print Assumptions underscores.
Print Assumptions halt_entries.
Print Assumptions table_matches_string.
Print Assumptions c0_is_blank_A.
Print Assumptions bb83_halts.
Print Assumptions reaches_final.
Print Assumptions final_halted.
Print Assumptions fomega1_iter3_lt_sigma.
Print Assumptions bb83_main.
