(** Independent probe for C7 (BB9/verify_c7).  Machine: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA.
    (1) The compiled transition table Defs.tm7 (a busycoq TM over the 9-state context BB92) equals the machine
        string, entry by entry (lines written from the string; H1 = None), and against Statement's parser.
        c0 is the blank tape in state A.
    (2) The definitions the statements use are printed.
    (3) The main theorems have the stated types (written out with qualified names), proved as one conjunction.
    (4) Print Assumptions on the conjunction and on each theorem of Statement.v (5 results). *)
From BB8 Require Import Individual92.
From Coq Require Import String Ascii.
From C7 Require Defs Sim Final7 Statement.
Local Open Scope sym_scope.

Print c0.
Print tape0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Print Defs.tm7.
Check (eq_refl : Defs.tm7 (A, 0) = Some (1, R, B)).
Check (eq_refl : Defs.tm7 (A, 1) = Some (0, R, A)).
Check (eq_refl : Defs.tm7 (B, 0) = Some (1, L, C)).
Check (eq_refl : Defs.tm7 (B, 1) = Some (1, L, F)).
Check (eq_refl : Defs.tm7 (C, 0) = Some (1, R, D)).
Check (eq_refl : Defs.tm7 (C, 1) = Some (0, L, B)).
Check (eq_refl : Defs.tm7 (D, 0) = Some (1, R, A)).
Check (eq_refl : Defs.tm7 (D, 1) = Some (1, L, E)).
Check (eq_refl : Defs.tm7 (E, 0) = Some (1, L, H)).
Check (eq_refl : Defs.tm7 (E, 1) = Some (0, L, C)).
Check (eq_refl : Defs.tm7 (F, 0) = Some (1, R, G)).
Check (eq_refl : Defs.tm7 (F, 1) = Some (1, L, D)).
Check (eq_refl : Defs.tm7 (G, 0) = Some (0, R, G)).
Check (eq_refl : Defs.tm7 (G, 1) = Some (0, R, F)).
Check (eq_refl : Defs.tm7 (H, 0) = Some (0, L, I)).
Check (eq_refl : Defs.tm7 (H, 1) = None).
Check (eq_refl : Defs.tm7 (I, 0) = Some (1, L, C)).
Check (eq_refl : Defs.tm7 (I, 1) = Some (0, R, A)).
Check Statement.c7_table.
Check (eq_refl : Statement.parse_slot Statement.c7_string 7%nat 1%nat = None).   (* H1 = "---" *)

Print Defs.ones.
Print Defs.count1.
Print Defs.sym_val.
Print Defs.iter.
Print Defs.arrow.
Print Defs.f.
Print Defs.f_omega.

Definition c7_all : Prop :=
  halts Defs.tm7 c0 /\ (forall c N, c0 -[ Defs.tm7 ]->* c -> halted Defs.tm7 c -> Defs.ones c N ->
     Defs.f_omega (Defs.f_omega (Defs.f_omega (Defs.f_omega (6 * Defs.arrow 13 2 3 + 3)))) < N) /\
  (forall c N, c0 -[ Defs.tm7 ]->* c -> halted Defs.tm7 c -> Defs.ones c N ->
     Defs.f_omega (Defs.f_omega (6 * Defs.arrow 13 2 3 + 3)) < N).

Lemma c7_all_ok : c7_all.
Proof. split; [exact Statement.c7_halts | split; [exact Statement.c7_lower | exact Statement.c7_beats_m8_bound]]. Qed.

Check Statement.c7_halts.
Check Statement.c7_lower.
Check Statement.c7_beats_m8_bound.

Print Assumptions c7_all_ok.
Print Assumptions Statement.c7_table.
Print Assumptions Statement.c7_halts.
Print Assumptions Statement.c7_lower.
Print Assumptions Statement.c7_beats_m8_bound.
