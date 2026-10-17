(** Independent probe: the Coq table [tm] equals the machine string, and the main theorems are axiom-free. *)
From TM43 Require Import Individual43 BB43_rules BB43_run BB43_bound.
From Coq Require Import String Ascii List.
Import ListNotations.
Open Scope string_scope.

Definition machine : string := "1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD".

Definition qi (q : state) : nat := match q with A => 0 | B => 1 | C => 2 | D => 3 end.
Definition si (s : sym) : nat := match s with S0 => 0 | S1 => 1 | S2 => 2 end.

Definition sym_of (c : ascii) : option sym :=
  match c with "0"%char => Some S0 | "1"%char => Some S1 | "2"%char => Some S2 | _ => None end.
Definition dir_of (c : ascii) : option dir :=
  match c with "L"%char => Some L | "R"%char => Some R | _ => None end.
(** [Some (Some q)] = go to q; [Some None] = halt (Z); [None] = parse error *)
Definition st_of (c : ascii) : option (option state) :=
  match c with "A"%char => Some (Some A) | "B"%char => Some (Some B) | "C"%char => Some (Some C)
             | "D"%char => Some (Some D) | "Z"%char => Some None | _ => None end.

(** Transition for (q, s) read from the string: group q (10 chars incl. '_'), entry s (3 chars).
    Outer [None] = parse error; [Some None] = halting transition. *)
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

Lemma underscores : String.get 9 machine = Some "_"%char /\ String.get 19 machine = Some "_"%char /\
                    String.get 29 machine = Some "_"%char /\ String.length machine = 39.
Proof. vm_compute. repeat split. Qed.

(** The halting entry C0 is 1RZ: it writes a 1, so sigma counts the final write. *)
Lemma halt_entry : String.substring 20 3 machine = "1RZ".
Proof. vm_compute. reflexivity. Qed.

Lemma table_matches_string : forall q s, Some (tm (q, s)) = parsed q s.
Proof. intros [] []; vm_compute; reflexivity. Qed.

(** The start configuration is state A on the all-0 tape. *)
Lemma c0_is_blank_A : c0 = (A, (Streams.const S0, S0, Streams.const S0)).
Proof. reflexivity. Qed.

(** The halting configuration: state C on a blank with 4*e4+17 ones to its right (C0 = 1RZ writes one more). *)
Lemma c_final_shape : c_final = (C, (Streams.const S0, S0, [S1]^^(4 * e4 + 17) *> Streams.const S0)).
Proof. reflexivity. Qed.

Lemma sigma_def : sigma = 4 * e4 + 18.
Proof. reflexivity. Qed.

Print Assumptions table_matches_string.
Print Assumptions halt_entry.
Print Assumptions c0_is_blank_A.
Print Assumptions c_final_shape.
Print Assumptions bb43_halts.
Print Assumptions reaches_final.
Print Assumptions final_halted.
Print Assumptions sigma_lower.
Print Assumptions e4_eq.
Check bb43_halts.
Check reaches_final.
Check sigma_lower.
Check e4_eq.
Print E4. Print E3. Print E2. Print G. Print f1. Print g. Print e1. Print v. Print sigma.
