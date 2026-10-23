(** Independent probe for h003 (BB9/verify_h003).  Machine: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC.
    (1) The compiled transition table Defs.tmh (a busycoq TM over the 9-state context BB92) equals the machine
        string, entry by entry (lines written from the string; H1 = None), and against Statement's parser.
        c0 is the blank tape in state A.
    (2) The definitions the statements use are printed.
    (3) The main theorems have the stated types (written out with qualified names), proved as one conjunction.
    (4) Print Assumptions on the conjunction and on each theorem of Statement.v (6 results). *)
From BB8 Require Import Individual92.
From Coq Require Import String Ascii.
From H3 Require Defs Sim Final Statement.
Local Open Scope sym_scope.

Print c0.
Print tape0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Print Defs.tmh.
Check (eq_refl : Defs.tmh (A, 0) = Some (1, R, B)).
Check (eq_refl : Defs.tmh (A, 1) = Some (0, R, A)).
Check (eq_refl : Defs.tmh (B, 0) = Some (1, L, C)).
Check (eq_refl : Defs.tmh (B, 1) = Some (1, L, F)).
Check (eq_refl : Defs.tmh (C, 0) = Some (1, R, D)).
Check (eq_refl : Defs.tmh (C, 1) = Some (0, L, B)).
Check (eq_refl : Defs.tmh (D, 0) = Some (1, R, A)).
Check (eq_refl : Defs.tmh (D, 1) = Some (1, L, E)).
Check (eq_refl : Defs.tmh (E, 0) = Some (0, L, H)).
Check (eq_refl : Defs.tmh (E, 1) = Some (0, L, C)).
Check (eq_refl : Defs.tmh (F, 0) = Some (1, R, G)).
Check (eq_refl : Defs.tmh (F, 1) = Some (1, L, D)).
Check (eq_refl : Defs.tmh (G, 0) = Some (0, R, G)).
Check (eq_refl : Defs.tmh (G, 1) = Some (0, R, F)).
Check (eq_refl : Defs.tmh (H, 0) = Some (0, L, I)).
Check (eq_refl : Defs.tmh (H, 1) = None).
Check (eq_refl : Defs.tmh (I, 0) = Some (1, R, I)).
Check (eq_refl : Defs.tmh (I, 1) = Some (1, R, C)).
Check Statement.h003_table.
Check (eq_refl : Statement.parse_slot Statement.h003_string 7%nat 1%nat = None).   (* H1 = "---" *)

Print Defs.ones.
Print Defs.count1.
Print Defs.sym_val.
Print Defs.iter.
Print Defs.arrow.
Print Defs.f.
Print Defs.f_omega.

Definition h003_all : Prop :=
  halts Defs.tmh c0 /\
  (forall c N, c0 -[ Defs.tmh ]->* c -> halted Defs.tmh c -> Defs.ones c N ->
     Defs.f_omega (Defs.f_omega (Defs.f_omega (Defs.f_omega (Defs.f_omega (Defs.f_omega (6 * Defs.arrow 13 2 3 + 2)))))) < N) /\
  (forall c N, c0 -[ Defs.tmh ]->* c -> halted Defs.tmh c -> Defs.ones c N ->
     Defs.f_omega (Defs.f_omega (Defs.f_omega (Defs.f_omega (Defs.f_omega (Defs.f_omega (Defs.f_omega 12)))))) < N) /\
  (forall c N, c0 -[ Defs.tmh ]->* c -> halted Defs.tmh c -> Defs.ones c N ->
     Defs.f_omega (Defs.f_omega (6 * Defs.arrow 13 2 3 + 3)) < N).

Lemma h003_all_ok : h003_all.
Proof.
  split; [exact Statement.h003_halts |].
  split; [exact Statement.h003_lower |].
  split; [exact Statement.h003_lower7_12 | exact Statement.h003_beats_m8_bound].
Qed.

Check Statement.h003_halts.
Check Statement.h003_lower.
Check Statement.h003_lower7_12.
Check Statement.h003_beats_m8_bound.

Print Assumptions h003_all_ok.
Print Assumptions Statement.h003_table.
Print Assumptions Statement.h003_halts.
Print Assumptions Statement.h003_lower.
Print Assumptions Statement.h003_lower7_12.
Print Assumptions Statement.h003_beats_m8_bound.
