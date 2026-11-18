(** Independent probe: the Coq table [tm] equals the machine string, and the main
    theorems are axiom-free.  Requires all of TM35 to compile first. *)
From TM35 Require Import Individual35 BB35_rules BB35_start BB35_run BB35_score.
From Coq Require Import String Ascii List.
Import ListNotations.
Open Scope string_scope.

Definition machine : string := "1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC".

Definition qi (q : state) : nat := match q with A => 0 | B => 1 | C => 2 end.
Definition si (s : sym) : nat := match s with S0 => 0 | S1 => 1 | S2 => 2 | S3 => 3 | S4 => 4 end.

Definition sym_of (c : ascii) : option sym :=
  match c with
  | "0"%char => Some S0 | "1"%char => Some S1 | "2"%char => Some S2 | "3"%char => Some S3
  | "4"%char => Some S4
  | _ => None end.
Definition dir_of (c : ascii) : option dir :=
  match c with
  | "L"%char => Some L | "R"%char => Some R | _ => None end.
(** [Some (Some q)] = go to q; [Some None] = halt (Z); [None] = parse error *)
Definition st_of (c : ascii) : option (option state) :=
  match c with
  | "A"%char => Some (Some A) | "B"%char => Some (Some B) | "C"%char => Some (Some C)
  | "Z"%char => Some None | _ => None end.

(** Each row has 15 characters (5 symbols x 3 chars), rows separated by "_".
    The rows therefore start at 0, 16 and 32, so k = 16 * qi + 3 * si. *)
Definition parsed (q : state) (s : sym) : option (option (sym * dir * state)) :=
  let k := 16 * qi q + 3 * si s in
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
  String.get 15 machine = Some "_"%char /\
  String.get 31 machine = Some "_"%char /\
  String.length machine = 47.
Proof. vm_compute. repeat split. Qed.

Lemma halt_entry : String.substring 28 3 machine = "1RZ".
Proof. vm_compute. reflexivity. Qed.

Lemma table_matches_string : forall q s, Some (tm (q, s)) = parsed q s.
Proof. intros [] []; vm_compute; reflexivity. Qed.

Lemma c0_is_blank_A : c0 = (A, (Streams.const S0, S0, Streams.const S0)).
Proof. reflexivity. Qed.

(** The halting configuration: state B reading the 4 that follows the block
    [3^(2 mfin + 3)]. *)
Lemma c_final_shape :
  c_final = (B, ([S3]^^(2 * mfin + 3) *> Streams.const S0, S4, Streams.const S0)).
Proof. reflexivity. Qed.

(** The nonzero cells of the final tape. *)
Lemma final_tape_cells : length final_cells = sigma /\ forall x, In x final_cells -> x <> S0.
Proof. split; [exact final_cells_count | exact final_cells_all_nonblank]. Qed.

(** The statements of the main results, for the record. *)
Check bb35_halts.
Check reaches_post.
Check reaches_final.
Check final_halted.
Check sigma_closed.
Check sigma_gt_fomega.
Check fomega_lt_sigma.
Check desc_closed_gen.
Check bb35_main.
Check B_rule.
Check rule1.
Check rule2.
Check rule3.
Check g_closed.
Check g_iter_closed.
Check g15_closed.
Check start.
Check sigma.
Check c_final.
Check f_omega.

Print Assumptions underscores.
Print Assumptions halt_entry.
Print Assumptions table_matches_string.
Print Assumptions c0_is_blank_A.
Print Assumptions c_final_shape.
Print Assumptions start.
Print Assumptions start_raw.
Print Assumptions B_rule.
Print Assumptions B_rule_gen.
Print Assumptions B_rule_15.
Print Assumptions rule1.
Print Assumptions rule2.
Print Assumptions rule3.
Print Assumptions GT.
Print Assumptions StepE.
Print Assumptions StepN.
Print Assumptions cycle3.
Print Assumptions bb35_halts.
Print Assumptions reaches_post.
Print Assumptions reaches_final.
Print Assumptions final_halted.
Print Assumptions final_cells_count.
Print Assumptions final_cells_all_nonblank.
Print Assumptions g15_eq.
Print Assumptions g_closed.
Print Assumptions g_iter_closed.
Print Assumptions g_iter_closed_gen.
Print Assumptions g15_closed.
Print Assumptions desc_closed_gen.
Print Assumptions sigma_closed.
Print Assumptions sigma_lower_gen.
Print Assumptions chain_gen.
Print Assumptions sigma_gt_fomega.
Print Assumptions fomega_lt_sigma.
Print Assumptions bb35_main.
