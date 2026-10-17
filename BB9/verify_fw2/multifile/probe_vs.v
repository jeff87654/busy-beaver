(** Independent probe for the comparisons BB9_fw2_vs_records.v (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q . BB8 probe_vs.v).

    Coq confirms here, by conversion, that the transition table of every machine in the comparisons is the declared
    machine, entry by entry (the lines were generated from the machine strings, not from the Coq files; a halting
    transition, 1RZ or ---, is None):
      BB9_redir_0LA_fh.tm      1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LI0LC_1RG1LD_1LC1RH_0LH0RF_---0LA
      BB9_redir_0LA.tm         1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LI0LC_1RG1LD_1LC0RH_1RG1LF_---0LA
      BB9_record_1RB0RA.tm     1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_1RG1LD_0RH0RF_0RG0RE_0LH1RZ
      BB9_champion_1RB1RA.tm   1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH   (Jacobzheng)
      BB10_champion_1RB1RA.tm  1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ   (Racheline)
    that the ones-counting predicates of the 9-state files are the same predicate as BB9_fw2_bound.ones, and that the
    five comparison theorems have the stated types and use no axioms. *)

From BB8 Require BB9_fw2_1RB0RD BB9_fw2_bound BB9_fw2_vs_records.
From BB8 Require BB9_champion_1RB1RA BB9_champion_bound BB9_record_1RB0RA BB9_record_bound.
From BB8 Require BB9_redir_0LA BB9_redir_0LA_bound BB9_redir_0LA_fh BB9_redir_0LA_fh_bound.
From BB8 Require BB102 Individual102 BB10_champion_1RB1RA BB10_champion_bound.
From BB8 Require Import Individual92.
From Coq Require Import PeanoNat.
Local Open Scope sym_scope.

Module TM10 := Individual102.Individual102.Permute.Flip.Compute.TM.

Check (eq_refl : BB9_redir_0LA_fh.tm (A, 0) = Some (1, R, B)).  Check (eq_refl : BB9_redir_0LA_fh.tm (A, 1) = Some (0, R, A)).
Check (eq_refl : BB9_redir_0LA_fh.tm (B, 0) = Some (1, L, C)).  Check (eq_refl : BB9_redir_0LA_fh.tm (B, 1) = Some (1, L, F)).
Check (eq_refl : BB9_redir_0LA_fh.tm (C, 0) = Some (1, R, D)).  Check (eq_refl : BB9_redir_0LA_fh.tm (C, 1) = Some (0, L, B)).
Check (eq_refl : BB9_redir_0LA_fh.tm (D, 0) = Some (1, R, A)).  Check (eq_refl : BB9_redir_0LA_fh.tm (D, 1) = Some (1, L, E)).
Check (eq_refl : BB9_redir_0LA_fh.tm (E, 0) = Some (0, L, I)).  Check (eq_refl : BB9_redir_0LA_fh.tm (E, 1) = Some (0, L, C)).
Check (eq_refl : BB9_redir_0LA_fh.tm (F, 0) = Some (1, R, G)).  Check (eq_refl : BB9_redir_0LA_fh.tm (F, 1) = Some (1, L, D)).
Check (eq_refl : BB9_redir_0LA_fh.tm (G, 0) = Some (1, L, C)).  Check (eq_refl : BB9_redir_0LA_fh.tm (G, 1) = Some (1, R, H)).
Check (eq_refl : BB9_redir_0LA_fh.tm (H, 0) = Some (0, L, H)).  Check (eq_refl : BB9_redir_0LA_fh.tm (H, 1) = Some (0, R, F)).
Check (eq_refl : BB9_redir_0LA_fh.tm (I, 0) = None).  Check (eq_refl : BB9_redir_0LA_fh.tm (I, 1) = Some (0, L, A)).

Check (eq_refl : BB9_redir_0LA.tm (A, 0) = Some (1, R, B)).  Check (eq_refl : BB9_redir_0LA.tm (A, 1) = Some (0, R, A)).
Check (eq_refl : BB9_redir_0LA.tm (B, 0) = Some (1, L, C)).  Check (eq_refl : BB9_redir_0LA.tm (B, 1) = Some (1, L, F)).
Check (eq_refl : BB9_redir_0LA.tm (C, 0) = Some (1, R, D)).  Check (eq_refl : BB9_redir_0LA.tm (C, 1) = Some (0, L, B)).
Check (eq_refl : BB9_redir_0LA.tm (D, 0) = Some (1, R, A)).  Check (eq_refl : BB9_redir_0LA.tm (D, 1) = Some (1, L, E)).
Check (eq_refl : BB9_redir_0LA.tm (E, 0) = Some (0, L, I)).  Check (eq_refl : BB9_redir_0LA.tm (E, 1) = Some (0, L, C)).
Check (eq_refl : BB9_redir_0LA.tm (F, 0) = Some (1, R, G)).  Check (eq_refl : BB9_redir_0LA.tm (F, 1) = Some (1, L, D)).
Check (eq_refl : BB9_redir_0LA.tm (G, 0) = Some (1, L, C)).  Check (eq_refl : BB9_redir_0LA.tm (G, 1) = Some (0, R, H)).
Check (eq_refl : BB9_redir_0LA.tm (H, 0) = Some (1, R, G)).  Check (eq_refl : BB9_redir_0LA.tm (H, 1) = Some (1, L, F)).
Check (eq_refl : BB9_redir_0LA.tm (I, 0) = None).  Check (eq_refl : BB9_redir_0LA.tm (I, 1) = Some (0, L, A)).

Check (eq_refl : BB9_record_1RB0RA.tm (A, 0) = Some (1, R, B)).  Check (eq_refl : BB9_record_1RB0RA.tm (A, 1) = Some (0, R, A)).
Check (eq_refl : BB9_record_1RB0RA.tm (B, 0) = Some (1, L, C)).  Check (eq_refl : BB9_record_1RB0RA.tm (B, 1) = Some (1, L, F)).
Check (eq_refl : BB9_record_1RB0RA.tm (C, 0) = Some (1, R, D)).  Check (eq_refl : BB9_record_1RB0RA.tm (C, 1) = Some (0, L, B)).
Check (eq_refl : BB9_record_1RB0RA.tm (D, 0) = Some (1, R, A)).  Check (eq_refl : BB9_record_1RB0RA.tm (D, 1) = Some (1, L, E)).
Check (eq_refl : BB9_record_1RB0RA.tm (E, 0) = Some (1, L, I)).  Check (eq_refl : BB9_record_1RB0RA.tm (E, 1) = Some (0, L, C)).
Check (eq_refl : BB9_record_1RB0RA.tm (F, 0) = Some (1, R, G)).  Check (eq_refl : BB9_record_1RB0RA.tm (F, 1) = Some (1, L, D)).
Check (eq_refl : BB9_record_1RB0RA.tm (G, 0) = Some (0, R, H)).  Check (eq_refl : BB9_record_1RB0RA.tm (G, 1) = Some (0, R, F)).
Check (eq_refl : BB9_record_1RB0RA.tm (H, 0) = Some (0, R, G)).  Check (eq_refl : BB9_record_1RB0RA.tm (H, 1) = Some (0, R, E)).
Check (eq_refl : BB9_record_1RB0RA.tm (I, 0) = Some (0, L, H)).  Check (eq_refl : BB9_record_1RB0RA.tm (I, 1) = None).

Check (eq_refl : BB9_champion_1RB1RA.tm (A, 0) = Some (1, R, B)).  Check (eq_refl : BB9_champion_1RB1RA.tm (A, 1) = Some (1, R, A)).
Check (eq_refl : BB9_champion_1RB1RA.tm (B, 0) = Some (0, L, C)).  Check (eq_refl : BB9_champion_1RB1RA.tm (B, 1) = Some (0, L, F)).
Check (eq_refl : BB9_champion_1RB1RA.tm (C, 0) = Some (0, R, D)).  Check (eq_refl : BB9_champion_1RB1RA.tm (C, 1) = Some (1, L, C)).
Check (eq_refl : BB9_champion_1RB1RA.tm (D, 0) = Some (1, R, A)).  Check (eq_refl : BB9_champion_1RB1RA.tm (D, 1) = Some (1, R, G)).
Check (eq_refl : BB9_champion_1RB1RA.tm (E, 0) = None).  Check (eq_refl : BB9_champion_1RB1RA.tm (E, 1) = Some (0, R, A)).
Check (eq_refl : BB9_champion_1RB1RA.tm (F, 0) = Some (1, L, B)).  Check (eq_refl : BB9_champion_1RB1RA.tm (F, 1) = Some (1, L, F)).
Check (eq_refl : BB9_champion_1RB1RA.tm (G, 0) = Some (1, L, H)).  Check (eq_refl : BB9_champion_1RB1RA.tm (G, 1) = Some (1, R, E)).
Check (eq_refl : BB9_champion_1RB1RA.tm (H, 0) = Some (0, L, I)).  Check (eq_refl : BB9_champion_1RB1RA.tm (H, 1) = Some (1, L, H)).
Check (eq_refl : BB9_champion_1RB1RA.tm (I, 0) = Some (1, L, B)).  Check (eq_refl : BB9_champion_1RB1RA.tm (I, 1) = Some (0, L, H)).

Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.A, BB102.S0) = Some (BB102.S1, R, BB102.B)).  Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.A, BB102.S1) = Some (BB102.S1, R, BB102.A)).
Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.B, BB102.S0) = Some (BB102.S0, L, BB102.C)).  Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.B, BB102.S1) = Some (BB102.S0, L, BB102.F)).
Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.C, BB102.S0) = Some (BB102.S0, R, BB102.D)).  Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.C, BB102.S1) = Some (BB102.S1, L, BB102.C)).
Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.D, BB102.S0) = Some (BB102.S1, R, BB102.A)).  Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.D, BB102.S1) = Some (BB102.S1, R, BB102.G)).
Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.E, BB102.S0) = None).  Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.E, BB102.S1) = Some (BB102.S0, R, BB102.A)).
Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.F, BB102.S0) = Some (BB102.S1, L, BB102.B)).  Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.F, BB102.S1) = Some (BB102.S1, L, BB102.F)).
Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.G, BB102.S0) = Some (BB102.S1, L, BB102.H)).  Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.G, BB102.S1) = Some (BB102.S1, R, BB102.E)).
Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.H, BB102.S0) = Some (BB102.S0, L, BB102.I)).  Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.H, BB102.S1) = Some (BB102.S1, L, BB102.H)).
Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.I, BB102.S0) = Some (BB102.S0, L, BB102.F)).  Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.I, BB102.S1) = Some (BB102.S0, L, BB102.J)).
Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.J, BB102.S0) = Some (BB102.S1, L, BB102.H)).  Check (eq_refl : BB10_champion_1RB1RA.tm (BB102.J, BB102.S1) = Some (BB102.S0, L, BB102.J)).
Check (eq_refl : TM10.c0 = (BB102.A, TM10.tape0)).  Check (eq_refl : TM10.tape0 = (const BB102.S0, BB102.S0, const BB102.S0)).

(* the 9-state ones-counting predicates are one and the same *)
Check (eq_refl : BB9_redir_0LA_fh_bound.ones = BB9_fw2_bound.ones).
Check (eq_refl : BB9_redir_0LA_bound.ones = BB9_fw2_bound.ones).
Check (eq_refl : BB9_record_bound.ones = BB9_fw2_bound.ones).
Check (eq_refl : BB9_champion_bound.ones = BB9_fw2_bound.ones).
Print BB9_fw2_bound.ones.
Print BB10_champion_bound.ones.

Check BB9_fw2_vs_records.fw2_beats_redir_0LA_fh.
Check BB9_fw2_vs_records.fw2_beats_redir_0LA.
Check BB9_fw2_vs_records.fw2_beats_record.
Check BB9_fw2_vs_records.fw2_beats_bb9_champion.
Check BB9_fw2_vs_records.fw2_beats_bb10_champion.

Print Assumptions BB9_fw2_vs_records.fw2_beats_redir_0LA_fh.
Print Assumptions BB9_fw2_vs_records.fw2_beats_redir_0LA.
Print Assumptions BB9_fw2_vs_records.fw2_beats_record.
Print Assumptions BB9_fw2_vs_records.fw2_beats_bb9_champion.
Print Assumptions BB9_fw2_vs_records.fw2_beats_bb10_champion.
