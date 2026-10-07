(** Independent probe for BB9_record_1RB0RA_selfcontained.v (run after `coqc BB9_record_1RB0RA_selfcontained.v`
    in the same directory:  coqc probe_selfcontained.v).

    Coq itself confirms here, by conversion, that (1) the compiled transition table of [tm] is the declared machine,
    entry by entry, and the champion's table is Jacobzheng's published machine; (2) the main theorems have exactly
    the stated types; (3) they use no axioms.  It also prints the definitions that the statements depend on
    ([halts], [halted], [c0], [ones], [arrow], [Bx], [bp], [U], [iter], [dbl]) so that a reader can check that they
    mean what the header says. *)

Require Import BB9_record_1RB0RA_selfcontained.
From Coq Require Import PeanoNat.
(* tape symbols 0/1 on top; nat arithmetic still resolves through nat-typed arguments and nat_scope notations *)
Local Open Scope sym_scope.

(* 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH--- *)
Check (eq_refl : tm (A, 0) = Some (1, R, B)).  Check (eq_refl : tm (A, 1) = Some (0, R, A)).
Check (eq_refl : tm (B, 0) = Some (1, L, C)).  Check (eq_refl : tm (B, 1) = Some (1, L, F)).
Check (eq_refl : tm (C, 0) = Some (1, R, D)).  Check (eq_refl : tm (C, 1) = Some (0, L, B)).
Check (eq_refl : tm (D, 0) = Some (1, R, A)).  Check (eq_refl : tm (D, 1) = Some (1, L, E)).
Check (eq_refl : tm (E, 0) = Some (1, L, I)).  Check (eq_refl : tm (E, 1) = Some (0, L, C)).
Check (eq_refl : tm (F, 0) = Some (1, R, G)).  Check (eq_refl : tm (F, 1) = Some (1, L, D)).
Check (eq_refl : tm (G, 0) = Some (0, R, H)).  Check (eq_refl : tm (G, 1) = Some (0, R, F)).
Check (eq_refl : tm (H, 0) = Some (0, R, G)).  Check (eq_refl : tm (H, 1) = Some (0, R, E)).
Check (eq_refl : tm (I, 0) = Some (0, L, H)).  Check (eq_refl : tm (I, 1) = None).

(* champion 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH *)
Check (eq_refl : Champion9.tm (A, 0) = Some (1, R, B)).  Check (eq_refl : Champion9.tm (A, 1) = Some (1, R, A)).
Check (eq_refl : Champion9.tm (B, 0) = Some (0, L, C)).  Check (eq_refl : Champion9.tm (B, 1) = Some (0, L, F)).
Check (eq_refl : Champion9.tm (C, 0) = Some (0, R, D)).  Check (eq_refl : Champion9.tm (C, 1) = Some (1, L, C)).
Check (eq_refl : Champion9.tm (D, 0) = Some (1, R, A)).  Check (eq_refl : Champion9.tm (D, 1) = Some (1, R, G)).
Check (eq_refl : Champion9.tm (E, 0) = None).            Check (eq_refl : Champion9.tm (E, 1) = Some (0, R, A)).
Check (eq_refl : Champion9.tm (F, 0) = Some (1, L, B)).  Check (eq_refl : Champion9.tm (F, 1) = Some (1, L, F)).
Check (eq_refl : Champion9.tm (G, 0) = Some (1, L, H)).  Check (eq_refl : Champion9.tm (G, 1) = Some (1, R, E)).
Check (eq_refl : Champion9.tm (H, 0) = Some (0, L, I)).  Check (eq_refl : Champion9.tm (H, 1) = Some (1, L, H)).
Check (eq_refl : Champion9.tm (I, 0) = Some (1, L, B)).  Check (eq_refl : Champion9.tm (I, 1) = Some (0, L, H)).

(* the blank tape, state A *)
Check (eq_refl : c0 = (A, (const 0, 0, const 0))).

(* statements *)
Check (halt : halts tm c0).
Check (score_closed : exists c, c0 -[ tm ]->* c /\ halted tm c /\
                                ones c (3 * arrow (12 * Bx - 9) 2 8 + 108 * (Bx / 5) + 70)).
Check (Bx_arrow13 : 2 * Bx + 4 = arrow 13 2 3).
Check (sigma_lower_bound : exists c N, c0 -[ tm ]->* c /\ halted tm c /\ ones c N /\ arrow (arrow 13 2 3) 2 3 < N).
Check (sigma_lower_bound_strong : exists c N, c0 -[ tm ]->* c /\ halted tm c /\ ones c N /\
                                              arrow (6 * arrow 13 2 3 - 33) 2 8 < N).
Check (Champion9.halt : halts Champion9.tm c0).
Check (Champion9.score_exact : exists c, c0 -[ Champion9.tm ]->* c /\ halted Champion9.tm c /\
                                         Champion9.ones c (Champion9.b2 + 3)).
Check (new_champion : exists cc Nc co No,
    c0 -[ Champion9.tm ]->* cc /\ halted Champion9.tm cc /\ ones cc Nc /\
    c0 -[ tm ]->* co /\ halted tm co /\ ones co No /\ Nc + 1 < No).
Check (new_champion_margin : exists cc Nc co No,
    c0 -[ Champion9.tm ]->* cc /\ halted Champion9.tm cc /\ ones cc Nc /\
    c0 -[ tm ]->* co /\ halted tm co /\ ones co No /\ 3 * (Nc + 1) < No).

(* the definitions behind the statements *)
Print halts. Print halts_in. Print halted. Print step. Print c0. Print tape0.
Print ones. Print count1. Print sym_val.
Print arrow. Print Bx. Print Bx_def. Print bp. Print bp_def. Print U. Print iter. Print dbl.
Print Champion9.ones. Print Champion9.b2. Print Champion9.b1. Print Champion9.second.

(* no axioms *)
Print Assumptions halt.
Print Assumptions score_closed.
Print Assumptions sigma_lower_bound.
Print Assumptions sigma_lower_bound_strong.
Print Assumptions Champion9.halt.
Print Assumptions Champion9.score_exact.
Print Assumptions new_champion.
Print Assumptions new_champion_margin.
