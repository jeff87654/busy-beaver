(** Independent probe for f3_0RC (BB9/verify_f3).  Machine: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF.
    (1) The compiled transition table Defs.tm3 (a busycoq TM over the 9-state context BB92) equals the machine
        string, entry by entry (lines generated from the string; H1 = None), and against Statement's parser.
        c0 is the blank tape in state A.
    (2) The definitions the statements use are printed.
    (3) The main theorems have the stated types (written out with qualified names), proved as one conjunction.
    (4) Print Assumptions on the conjunction and on each theorem of Statement.v (five results in all). *)
From BB8 Require Import Individual92.
From Coq Require Import String Ascii.
From F3 Require Defs Sim Final3 Statement.
Local Open Scope sym_scope.

Print c0.
Print tape0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Print Defs.tm3.
Check (eq_refl : Defs.tm3 (A, 0) = Some (1, R, B)).
Check (eq_refl : Defs.tm3 (A, 1) = Some (0, R, A)).
Check (eq_refl : Defs.tm3 (B, 0) = Some (1, L, C)).
Check (eq_refl : Defs.tm3 (B, 1) = Some (1, L, F)).
Check (eq_refl : Defs.tm3 (C, 0) = Some (1, R, D)).
Check (eq_refl : Defs.tm3 (C, 1) = Some (0, L, B)).
Check (eq_refl : Defs.tm3 (D, 0) = Some (1, R, A)).
Check (eq_refl : Defs.tm3 (D, 1) = Some (1, L, E)).
Check (eq_refl : Defs.tm3 (E, 0) = Some (1, L, H)).
Check (eq_refl : Defs.tm3 (E, 1) = Some (0, L, C)).
Check (eq_refl : Defs.tm3 (F, 0) = Some (1, R, G)).
Check (eq_refl : Defs.tm3 (F, 1) = Some (1, L, D)).
Check (eq_refl : Defs.tm3 (G, 0) = Some (0, R, G)).
Check (eq_refl : Defs.tm3 (G, 1) = Some (0, R, F)).
Check (eq_refl : Defs.tm3 (H, 0) = Some (0, L, I)).
Check (eq_refl : Defs.tm3 (H, 1) = None).
Check (eq_refl : Defs.tm3 (I, 0) = Some (0, R, C)).
Check (eq_refl : Defs.tm3 (I, 1) = Some (1, R, F)).
Check Statement.f3_table.
Check (eq_refl : Statement.parse_slot Statement.f3_string 7%nat 1%nat = None).   (* H1 = "---" *)

Print Defs.ones.
Print Defs.count1.
Print Defs.sym_val.
Print Defs.iter.
Print Defs.arrow.
Print Defs.f.
Print Defs.f_omega.

Definition f3_all : Prop :=
  halts Defs.tm3 c0 /\ (forall c N, c0 -[ Defs.tm3 ]->* c -> halted Defs.tm3 c -> Defs.ones c N ->
     Defs.f_omega (Defs.f_omega (6 * Defs.iter (Defs.arrow 13 2 3 - 5) (Defs.arrow 6 2) (Defs.iter 4 (Defs.arrow 5 2) 4) - 14)) < N) /\ (forall c N, c0 -[ Defs.tm3 ]->* c -> halted Defs.tm3 c -> Defs.ones c N ->
     Defs.f_omega (Defs.f_omega (6 * Defs.arrow 13 2 3 + 3)) < N).

Lemma f3_all_ok : f3_all.
Proof. split; [exact Statement.f3_halts | split; [exact Statement.f3_lower | exact Statement.f3_beats_m8_bound]]. Qed.

Check Statement.f3_halts.
Check Statement.f3_lower.
Check Statement.f3_beats_m8_bound.

Print Assumptions f3_all_ok.
Print Assumptions Statement.f3_table.
Print Assumptions Statement.f3_halts.
Print Assumptions Statement.f3_lower.
Print Assumptions Statement.f3_beats_m8_bound.
