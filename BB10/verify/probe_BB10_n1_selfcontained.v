(** Independent probe for BB10_n1_selfcontained.v (run after `coqc BB10_n1_selfcontained.v` in the same
    directory:  coqc probe_BB10_n1_selfcontained.v).

    Coq itself confirms here, by conversion, that (1) the compiled transition tables of [N1.tm], [Champion10.tm]
    and [Lead10.tm] are the declared machines, entry by entry (an undefined entry, written --- or 1RZ in the
    machine string, is busycoq's halt: None); (2) the main theorems have exactly the stated types; (3) they use no
    axioms.  It also prints the definitions that the statements depend on ([halts], [halted], [step], [c0], [ones],
    [count1], [sym_val], [arrow], [iter], [fgh], [f_omega1], [Graham]) so that a reader can check that they mean what the header says. *)

Require Import BB10_n1_selfcontained.
From Coq Require Import PeanoNat.
(* the tape symbols 0/1 for the table checks (sym_scope is not exported by the compiled file) *)
Local Open Scope sym_scope.

(* 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_---0LC *)
Check (eq_refl : N1.tm (A, 0) = Some (1, R, B)).         Check (eq_refl : N1.tm (A, 1) = Some (0, R, A)).
Check (eq_refl : N1.tm (B, 0) = Some (1, L, C)).         Check (eq_refl : N1.tm (B, 1) = Some (1, L, F)).
Check (eq_refl : N1.tm (C, 0) = Some (1, R, D)).         Check (eq_refl : N1.tm (C, 1) = Some (0, L, B)).
Check (eq_refl : N1.tm (D, 0) = Some (1, R, A)).         Check (eq_refl : N1.tm (D, 1) = Some (1, L, E)).
Check (eq_refl : N1.tm (E, 0) = Some (1, L, I)).         Check (eq_refl : N1.tm (E, 1) = Some (0, L, C)).
Check (eq_refl : N1.tm (F, 0) = Some (0, R, G)).         Check (eq_refl : N1.tm (F, 1) = Some (1, L, D)).
Check (eq_refl : N1.tm (G, 0) = Some (1, R, H)).         Check (eq_refl : N1.tm (G, 1) = Some (1, L, G)).
Check (eq_refl : N1.tm (H, 0) = Some (1, L, C)).         Check (eq_refl : N1.tm (H, 1) = Some (0, R, G)).
Check (eq_refl : N1.tm (I, 0) = Some (0, L, J)).         Check (eq_refl : N1.tm (I, 1) = Some (0, L, I)).
Check (eq_refl : N1.tm (J, 0) = None).                   Check (eq_refl : N1.tm (J, 1) = Some (0, L, C)).

(* the BB(10) champion *)
(* 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ *)
Check (eq_refl : Champion10.tm (A, 0) = Some (1, R, B)). Check (eq_refl : Champion10.tm (A, 1) = Some (1, R, A)).
Check (eq_refl : Champion10.tm (B, 0) = Some (0, L, C)). Check (eq_refl : Champion10.tm (B, 1) = Some (0, L, F)).
Check (eq_refl : Champion10.tm (C, 0) = Some (0, R, D)). Check (eq_refl : Champion10.tm (C, 1) = Some (1, L, C)).
Check (eq_refl : Champion10.tm (D, 0) = Some (1, R, A)). Check (eq_refl : Champion10.tm (D, 1) = Some (1, R, G)).
Check (eq_refl : Champion10.tm (E, 0) = None).           Check (eq_refl : Champion10.tm (E, 1) = Some (0, R, A)).
Check (eq_refl : Champion10.tm (F, 0) = Some (1, L, B)). Check (eq_refl : Champion10.tm (F, 1) = Some (1, L, F)).
Check (eq_refl : Champion10.tm (G, 0) = Some (1, L, H)). Check (eq_refl : Champion10.tm (G, 1) = Some (1, R, E)).
Check (eq_refl : Champion10.tm (H, 0) = Some (0, L, I)). Check (eq_refl : Champion10.tm (H, 1) = Some (1, L, H)).
Check (eq_refl : Champion10.tm (I, 0) = Some (0, L, F)). Check (eq_refl : Champion10.tm (I, 1) = Some (0, L, J)).
Check (eq_refl : Champion10.tm (J, 0) = Some (1, L, H)). Check (eq_refl : Champion10.tm (J, 1) = Some (0, L, J)).

(* the candidate 0LJ0LC *)
(* 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_1RG1LD_0RI0RH_1RG1LF_1RE1RI_---1LC *)
Check (eq_refl : Lead10.tm (A, 0) = Some (1, R, B)).     Check (eq_refl : Lead10.tm (A, 1) = Some (0, R, A)).
Check (eq_refl : Lead10.tm (B, 0) = Some (1, L, C)).     Check (eq_refl : Lead10.tm (B, 1) = Some (1, L, F)).
Check (eq_refl : Lead10.tm (C, 0) = Some (1, R, D)).     Check (eq_refl : Lead10.tm (C, 1) = Some (0, L, B)).
Check (eq_refl : Lead10.tm (D, 0) = Some (1, R, A)).     Check (eq_refl : Lead10.tm (D, 1) = Some (1, L, E)).
Check (eq_refl : Lead10.tm (E, 0) = Some (0, L, J)).     Check (eq_refl : Lead10.tm (E, 1) = Some (0, L, C)).
Check (eq_refl : Lead10.tm (F, 0) = Some (1, R, G)).     Check (eq_refl : Lead10.tm (F, 1) = Some (1, L, D)).
Check (eq_refl : Lead10.tm (G, 0) = Some (0, R, I)).     Check (eq_refl : Lead10.tm (G, 1) = Some (0, R, H)).
Check (eq_refl : Lead10.tm (H, 0) = Some (1, R, G)).     Check (eq_refl : Lead10.tm (H, 1) = Some (1, L, F)).
Check (eq_refl : Lead10.tm (I, 0) = Some (1, R, E)).     Check (eq_refl : Lead10.tm (I, 1) = Some (1, R, I)).
Check (eq_refl : Lead10.tm (J, 0) = None).               Check (eq_refl : Lead10.tm (J, 1) = Some (1, L, C)).

(* the blank tape, state A *)
Check (eq_refl : c0 = (A, (const 0, 0, const 0))).

Local Open Scope nat_scope.

(* statements *)
Check (n1_halts : halts N1.tm c0).
Check (n1_score_exact : exists c f k w,
  c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c (2 * w + f + 3 * k + 22) /\
  iter (2 * ((3 * arrow 37 2 3 - 13) / 7) + 1) (fun n => arrow n 2 4) 34 <= w).
Check (n1_sigma_lower_bound : exists c N,
  c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c N /\
  iter ((6 * arrow 37 2 3 - 19) / 7) (fun x => arrow (x + 1) 2 3) 33 < N).
Check (n1_beats_M3_bound : exists c N,
  c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c N /\
  arrow (4 * arrow 37 2 3 + 41) 2 (arrow (4 * arrow 37 2 3 + 39) 2 (arrow (4 * arrow 37 2 3 + 35) 2 5)) < N).
Check (n1_beats_champion : exists cc Nc co No,
  c0 -[ Champion10.tm ]->* cc /\ halted Champion10.tm cc /\ ones cc Nc /\
  c0 -[ N1.tm ]->* co /\ halted N1.tm co /\ ones co No /\ Nc + 1 < No + 1).
Check (n1_beats_lead : exists cl Nl co No,
  c0 -[ Lead10.tm ]->* cl /\ halted Lead10.tm cl /\ ones cl Nl /\
  c0 -[ N1.tm ]->* co /\ halted N1.tm co /\ ones co No /\ Nl + 1 < No + 1).
Check (n1_fgh_level : exists c N,
  c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c N /\
  f_omega1 ((3 * arrow 37 2 3 - 13) / 7 - 2) < N /\ N < f_omega1 (6 * arrow 37 2 3)).
Check (n1_fgh_lower_64 : exists c N, c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c N /\ f_omega1 64 < N).
Check (graham_lt_f_omega1_64 : Graham < f_omega1 64).
Check (n1_beats_graham : exists c N, c0 -[ N1.tm ]->* c /\ halted N1.tm c /\ ones c N /\ Graham < N).
Check (Champion10.halt : halts Champion10.tm c0).
Check (Champion10.score_exact : exists c, c0 -[ Champion10.tm ]->* c /\ halted Champion10.tm c /\
                                          Champion10.ones c (Champion10.b2 + 3)).
Check (Lead10.halt : halts Lead10.tm c0).
Check (Lead10.score_exact : exists c, c0 -[ Lead10.tm ]->* c /\ halted Lead10.tm c /\
                                      Lead10.ones c (2 * Lead10.b2 + 2 * (4 * Lead10.bf + 33) + 5)).

(* the definitions behind the statements *)
Print halts. Print halts_in. Print halted. Print step. Print c0. Print tape0.
Print ones. Print count1. Print sym_val.
Print N1.arrow. Print N1.iter.
Print N1.fgh. Print N1.f_omega. Print N1.f_omega1. Print N1.up3. Print N1.graham_g. Print N1.Graham.

(* no axioms *)
Print Assumptions n1_halts.
Print Assumptions n1_score_exact.
Print Assumptions n1_sigma_lower_bound.
Print Assumptions n1_beats_M3_bound.
Print Assumptions n1_beats_champion.
Print Assumptions n1_beats_lead.
Print Assumptions Champion10.halt.
Print Assumptions Champion10.score_exact.
Print Assumptions Lead10.halt.
Print Assumptions Lead10.score_exact.
Print Assumptions n1_fgh_level.
Print Assumptions n1_fgh_lower_64.
Print Assumptions graham_lt_f_omega1_64.
Print Assumptions n1_beats_graham.
Print Assumptions N1.fgh_level.
Print Assumptions N1.beats_graham.
Print Assumptions N1.graham_lt_f_omega1_64.
Print Assumptions N1.fgh_lower_64.
