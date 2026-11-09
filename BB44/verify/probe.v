(** Independent probe: the Coq table [tm] equals the machine string, and the main
    theorems are axiom-free.  Requires all of TM44 to compile first. *)
From TM44 Require Import Individual44 BB44_rules BB44_start BB44_run BB44_score.
From Coq Require Import String Ascii List.
Import ListNotations.
Open Scope string_scope.

Definition machine : string := "0LB3LB1RZ2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_0RD2RC2LB0RA".

Definition qi (q : state) : nat := match q with A => 0 | B => 1 | C => 2 | D => 3 end.
Definition si (s : sym) : nat := match s with S0 => 0 | S1 => 1 | S2 => 2 | S3 => 3 end.

Definition sym_of (c : ascii) : option sym :=
  match c with
  | "0"%char => Some S0 | "1"%char => Some S1 | "2"%char => Some S2 | "3"%char => Some S3
  | _ => None end.
Definition dir_of (c : ascii) : option dir :=
  match c with
  | "L"%char => Some L | "R"%char => Some R | _ => None end.
(** [Some (Some q)] = go to q; [Some None] = halt (Z); [None] = parse error *)
Definition st_of (c : ascii) : option (option state) :=
  match c with
  | "A"%char => Some (Some A) | "B"%char => Some (Some B) | "C"%char => Some (Some C)
  | "D"%char => Some (Some D) | "Z"%char => Some None | _ => None end.

(** Each row has 12 characters (4 states x 4 symbols x 3 chars), rows separated by "_".
    The rows therefore start at 0, 13, 26 and 39, so k = 13 * qi + 3 * si. *)
Definition parsed (q : state) (s : sym) : option (option (sym * dir * state)) :=
  let k := 13 * qi q + 3 * si s in
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
  String.get 12 machine = Some "_"%char /\
  String.get 25 machine = Some "_"%char /\
  String.get 38 machine = Some "_"%char /\
  String.length machine = 51.
Proof. vm_compute. repeat split. Qed.

Lemma halt_entry : String.substring 6 3 machine = "1RZ".
Proof. vm_compute. reflexivity. Qed.

Lemma table_matches_string : forall q s, Some (tm (q, s)) = parsed q s.
Proof. intros [] []; vm_compute; reflexivity. Qed.

Lemma c0_is_blank_A : c0 = (A, (Streams.const S0, S0, Streams.const S0)).
Proof. reflexivity. Qed.

(** The halting configuration: A reading the 2 after 3^(2 g509 + 1) 2^510. *)
Lemma c_final_shape :
  c_final = (A, ([S2]^^510 *> [S3]^^(2 * g509 + 1) *> Streams.const S0,
                 S2, [S1;S3] *> Streams.const S0)).
Proof. reflexivity. Qed.

(** After the halting write (1RZ), the nonblank cells are exactly [final_cells]. *)
Lemma final_tape_cells : length final_cells = sigma /\ forall x, In x final_cells -> x <> S0.
Proof. split; [exact final_cells_count | exact final_cells_all_nonblank]. Qed.

(** The statements of the main results, for the record. *)
Check bb44_halts.
Check reaches_final.
Check final_halted.
Check sigma_eq.
Check bb44_main.
Check B_rule.
Check g_closed.
Check g_iter_closed.
Check g509_closed.
Check start.
Check sigma.
Check c_final.
Check B_phase.
Check D_phase.
Check D_phase_p.

Print Assumptions underscores.
Print Assumptions halt_entry.
Print Assumptions table_matches_string.
Print Assumptions c0_is_blank_A.
Print Assumptions c_final_shape.
Print Assumptions start.
Print Assumptions start_raw.
Print Assumptions B_rule.
Print Assumptions B_rule_gen.
Print Assumptions B_rule_509.
Print Assumptions B_phase.
Print Assumptions Bloop.
Print Assumptions Bloop_step.
Print Assumptions D_phase.
Print Assumptions D_phase_p.
Print Assumptions D1_loop.
Print Assumptions D3_loop.
Print Assumptions block_snoc.
Print Assumptions bb44_halts.
Print Assumptions reaches_final.
Print Assumptions final_halted.
Print Assumptions final_cells_count.
Print Assumptions final_cells_all_nonblank.
Print Assumptions g509_eq.
Print Assumptions g_closed.
Print Assumptions g_iter_closed.
Print Assumptions g_iter_closed_gen.
Print Assumptions g509_closed.
Print Assumptions score_generic.
Print Assumptions sigma_eq.
Print Assumptions sigma_general.
Print Assumptions bb44_main.
