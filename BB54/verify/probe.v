(** Independent probe: the Coq table [tm] equals the machine string, and the main
    theorems are axiom-free.  Requires all of TM54 to compile first. *)
From TM54 Require Import Individual54 BB54_rules BB54_start BB54_run BB54_score
  BB54_dphase BB54_halt BB54_bound BB54_tower.
From Coq Require Import String Ascii List.
Import ListNotations.
Open Scope string_scope.

Definition machine : string :=
  "1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ".

Definition qi (q : state) : nat :=
  match q with A => 0 | B => 1 | C => 2 | D => 3 | E => 4 end.
Definition si (s : sym) : nat :=
  match s with S0 => 0 | S1 => 1 | S2 => 2 | S3 => 3 end.

Definition sym_of (c : ascii) : option sym :=
  match c with
  | "0"%char => Some S0 | "1"%char => Some S1 | "2"%char => Some S2 | "3"%char => Some S3
  | _ => None end.
Definition dir_of (c : ascii) : option dir :=
  match c with
  | "L"%char => Some L | "R"%char => Some R | _ => None end.
(** [Some (Some q)] = go to q; [Some None] = halt (Z) or no transition ("---"). *)
Definition st_of (c : ascii) : option (option state) :=
  match c with
  | "A"%char => Some (Some A) | "B"%char => Some (Some B) | "C"%char => Some (Some C)
  | "D"%char => Some (Some D) | "E"%char => Some (Some E)
  | "Z"%char => Some None | _ => None end.

(** Each row has 12 characters (4 symbols x 3 chars), rows separated by "_".
    The rows therefore start at 0, 13, 26, 39 and 52, so k = 13 * qi + 3 * si. *)
Definition parsed (q : state) (s : sym) : option (option (sym * dir * state)) :=
  let k := 13 * qi q + 3 * si s in
  match String.get k machine, String.get (k + 1) machine, String.get (k + 2) machine with
  | Some c1, Some c2, Some c3 =>
    match sym_of c1, dir_of c2, st_of c3 with
    | Some w, Some d, Some (Some q') => Some (Some (w, d, q'))
    | _, _, _ => Some None
    end
  | _, _, _ => None
  end.

Lemma underscores :
  String.get 12 machine = Some "_"%char /\
  String.get 25 machine = Some "_"%char /\
  String.get 38 machine = Some "_"%char /\
  String.get 51 machine = Some "_"%char /\
  String.length machine = 64.
Proof. vm_compute. repeat split. Qed.

(** The halting transition E3 = 1RZ sits in the last row, last entry. *)
Lemma halt_entry : String.substring 61 3 machine = "1RZ".
Proof. vm_compute. reflexivity. Qed.

(** The entries of the state E are "------1LD1RZ": E0 and E1 are undefined,
    E2 = 1LD and E3 = 1RZ. *)
Lemma state_E : String.substring 52 12 machine = "------1LD1RZ".
Proof. vm_compute. reflexivity. Qed.

Lemma table_matches_string : forall q s, Some (tm (q, s)) = parsed q s.
Proof. intros [] []; vm_compute; reflexivity. Qed.

Lemma c0_is_blank_A : c0 = (A, (Streams.const S0, S0, Streams.const S0)).
Proof. reflexivity. Qed.

(** The configuration the run reaches: state A, two twos and one three to the
    left, one 1 under the head. *)
Lemma start_shape :
  Bcfg 2 1 0 (Streams.const S0)
  = (A, ([S2;S2;S3] *> Streams.const S0, S1, Streams.const S0)).
Proof. reflexivity. Qed.

(** The score-carrying configuration: state A, five twos and a block of
    [2 g40 + 1] threes to the left, the tail "3 1" to the right. *)
Lemma c_score_shape :
  c_score = (A, ([S2]^^5 *> [S3]^^(2 * g40 + 1) *> Streams.const S0,
                 S3, [S1] *> Streams.const S0)).
Proof. reflexivity. Qed.

(** The nonzero cells of the tape of [c_score]. *)
Lemma score_tape_cells : length score_cells = sigma /\ forall x, In x score_cells -> x <> S0.
Proof. split; [exact score_cells_count | exact score_cells_all_nonblank]. Qed.

(** The statements of the main results, for the record. *)
Check start.
Check descent_1.
Check D_phase_run.
Check descent_4.
Check reaches_score.
Check sigma_eq.
Check bb54_main.
Check B_rule.
Check g_closed.
Check g_iter_closed.
Check g40_closed.
Check D_phase_raw.
Check D_phase_2.
Check D_phase_halt.
Check D_phase_halt_1.
Check D_sweep_left.
Check macro_descent.
Check B1_iter.
Check a3_step.
Check chain_step.
Check chain.
Check pow_chain.
Check sigma.
Check c_score.
Check target.
Check f_omega.
Check f_omega2.

(** The D/E phase and the halting proof. *)
Check eat2.
Check eat_reach.
Check eat_reach_odd.
Check D_phase_even.
Check D_phase_odd.
Check bb54_dchain.
Check round_step.
Check level.
Check level_gen.
Check reaches_d1.
Check level0.
Check level1.
Check count_final_gen.
Check count_final.
Check bb54_halt.
Check sigma_final.
Check final_cells_count.
Check sigma_final_eq.
Check final_cells_nonblank.
Check bb54_halt_main.

(** The runtime bounds: Jacobzheng's original one and the refined one. *)
Check knuth_3_2_4.
Check knuth_4_2_3.
Check g5_closed_gen.
Check g4_zero_iter.
Check g4_zero_closed.
Check X_inner.
Check target_is_jacobzheng.
Check target_refined.
Check target_refined_eq.

(** The comparison of the two inner towers. *)
Check knuth_1_pow.
Check knuth_2_pow.
Check pow2_pos.
Check pow2_ge2.
Check pow2_ge4.
Check pow2_mul4.
Check pow2_add4.
Check pow_two_pow.
Check knuth2_pos.
Check tower2_ge2.
Check tower2_ge4.
Check tower10_inv.
Check tower10_lt.
Check tower10_lt_tower3.

Print Assumptions underscores.
Print Assumptions halt_entry.
Print Assumptions state_E.
Print Assumptions table_matches_string.
Print Assumptions c0_is_blank_A.
Print Assumptions start_shape.
Print Assumptions c_score_shape.
Print Assumptions start.
Print Assumptions start_raw.
Print Assumptions B_rule.
Print Assumptions B_rule_gen.
Print Assumptions g1_0.
Print Assumptions descent_1.
Print Assumptions D_phase_raw.
Print Assumptions D_phase_2.
Print Assumptions D_phase_halt.
Print Assumptions D_phase_halt_1.
Print Assumptions D_sweep_left.
Print Assumptions macro_descent.
Print Assumptions B1_iter.
Print Assumptions a3_step.
Print Assumptions chain_step.
Print Assumptions chain.
Print Assumptions pow_chain.
Print Assumptions D_phase_run.
Print Assumptions descent_4.
Print Assumptions reaches_score.
Print Assumptions g40_eq.
Print Assumptions g_closed.
Print Assumptions g_iter_closed.
Print Assumptions g_iter_closed_gen.
Print Assumptions g40_closed.
Print Assumptions cells_count.
Print Assumptions score_cells_count.
Print Assumptions score_cells_all_nonblank.
Print Assumptions sigma_eq.
Print Assumptions bb54_main.
Print Assumptions eat2.
Print Assumptions eat_reach.
Print Assumptions eat_reach_odd.
Print Assumptions D_phase_even.
Print Assumptions D_phase_odd.
Print Assumptions bb54_dchain.
Print Assumptions round_step.
Print Assumptions level.
Print Assumptions level_gen.
Print Assumptions reaches_d1.
Print Assumptions level0.
Print Assumptions level1.
Print Assumptions count_final_gen.
Print Assumptions count_final.
Print Assumptions bb54_halt.
Print Assumptions sigma_final.
Print Assumptions final_cells_count.
Print Assumptions sigma_final_eq.
Print Assumptions final_cells_nonblank.
Print Assumptions bb54_halt_main.
Print Assumptions knuth_3_2_4.
Print Assumptions knuth_4_2_3.
Print Assumptions g5_closed_gen.
Print Assumptions g4_zero_iter.
Print Assumptions g4_zero_closed.
Print Assumptions X_inner.
Print Assumptions target_is_jacobzheng.
Print Assumptions target_refined_eq.
Print Assumptions knuth_1_pow.
Print Assumptions knuth_2_pow.
Print Assumptions pow2_pos.
Print Assumptions pow2_ge2.
Print Assumptions pow2_ge4.
Print Assumptions pow2_mul4.
Print Assumptions pow2_add4.
Print Assumptions pow_two_pow.
Print Assumptions knuth2_pos.
Print Assumptions tower2_ge2.
Print Assumptions tower2_ge4.
Print Assumptions tower10_inv.
Print Assumptions tower10_lt.
Print Assumptions tower10_lt_tower3.
