(** Independent probe for the C04 proof (run after compile_clean.sh, in this directory:
      coqc -Q $BUSYCOQ BusyCoq -Q lib BB8 -Q dev Dev -Q k31 K31 -Q score Score probe.v).

    Machine: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_0RG1LD_0LH1LH_1RI---_0RI0RF (9 states A..I, 2 symbols; it halts on the
    undefined transition H1).

    Coq confirms here, by conversion, that (1) the compiled transition table [Base.tm] is the declared machine entry by
    entry (these 18 lines were generated from the machine string, not from the Coq file; the undefined slot H1 is None),
    and the start configuration [c0] is the blank tape in state A; (2) the three main theorems have exactly the stated
    types, written out here with fully qualified names (so [tm] is [Base.tm], [ones] is [K31_Abs.ones], [f_omega] is
    [Score.f_omega]); (3) [K31_Abs.ones] and [Score.f_omega] are convertible with fw2's [BB9_fw2_bound.ones] and
    [BB9_fw2_bound.f_omega], so the C04 score is counted, and compared, with fw2's definitions; (4) the theorems use no
    axioms.  It also prints the definitions the statements use.
    Part (5), for fgh/: the two-sided bracket f_omega (f_omega (12 Bx + 26)) < N < f_omega (f_omega (12 Bx + 27)) for
    every reachable halted configuration, the coarse placement f_w1 3 < N < f_w1 4, the exact score sigma_c04 (a
    symbolic recursion), and 2 Bx + 4 = 2 ^(13) 3, 2 R2 + 4 = 2 ^(12 Bx + 26) 4 (Knuth arrows): their types written
    out in one conjunction, the definitions printed, and one Print Assumptions on the conjunction. *)

From BB8 Require Import Individual92.
From BB8 Require BB9_fw2_1RB0RD BB9_fw2_bound.
From Dev Require Base Final ScoreEnd.
From K31 Require K31_Abs.
From Score Require Score.
From Dev Require Abs Chain.
From Fgh Require FArith EndU Exact.
Local Open Scope sym_scope.

(** (1) the machine and the start configuration *)
Print c0.
Check (eq_refl : q0 = A).  Check (eq_refl : s0 = S0).
Check (eq_refl : Base.tm (A, 0) = Some (1, R, B)).  Check (eq_refl : Base.tm (A, 1) = Some (0, R, A)).
Check (eq_refl : Base.tm (B, 0) = Some (1, L, C)).  Check (eq_refl : Base.tm (B, 1) = Some (1, L, F)).
Check (eq_refl : Base.tm (C, 0) = Some (1, R, D)).  Check (eq_refl : Base.tm (C, 1) = Some (0, L, B)).
Check (eq_refl : Base.tm (D, 0) = Some (1, R, A)).  Check (eq_refl : Base.tm (D, 1) = Some (1, L, E)).
Check (eq_refl : Base.tm (E, 0) = Some (1, L, H)).  Check (eq_refl : Base.tm (E, 1) = Some (0, L, C)).
Check (eq_refl : Base.tm (F, 0) = Some (0, R, G)).  Check (eq_refl : Base.tm (F, 1) = Some (1, L, D)).
Check (eq_refl : Base.tm (G, 0) = Some (0, L, H)).  Check (eq_refl : Base.tm (G, 1) = Some (1, L, H)).
Check (eq_refl : Base.tm (H, 0) = Some (1, R, I)).  Check (eq_refl : Base.tm (H, 1) = None).
Check (eq_refl : Base.tm (I, 0) = Some (0, R, I)).  Check (eq_refl : Base.tm (I, 1) = Some (0, R, F)).

(** (2) the definitions the statements use *)
Print halted.
Print K31_Abs.sym_val.
Print K31_Abs.count1.
Print K31_Abs.ones.
Print Score.f.
Print Score.f_omega.

(** (3) the score is counted, and compared, with fw2's definitions *)
Goal K31_Abs.ones = BB9_fw2_bound.ones. Proof. reflexivity. Qed.
Goal Score.f_omega = BB9_fw2_bound.f_omega. Proof. reflexivity. Qed.

(** (2) the main theorems, with their types written out *)
Check (Final.c04_halts : halts Base.tm c0).
Check (ScoreEnd.c04_sigma_lower_bound :
  exists c N, c0 -[ Base.tm ]->* c /\ halted Base.tm c /\ K31_Abs.ones c N /\
    Score.f_omega (Score.f_omega (465 * 1000 + 9)) < N).
Check (ScoreEnd.c04_beats_fw2 :
  exists c N, c0 -[ Base.tm ]->* c /\ halted Base.tm c /\ K31_Abs.ones c N /\
    BB9_fw2_bound.f_omega (BB9_fw2_bound.f_omega (465 * 1000 + 9)) < N /\
    exists cf Nf, c0 -[ BB9_fw2_1RB0RD.tm ]->* cf /\ halted BB9_fw2_1RB0RD.tm cf /\ BB9_fw2_bound.ones cf Nf /\
      Nf + 1 < N).

(** (4) no axioms *)
Print Assumptions Final.c04_halts.
Print Assumptions ScoreEnd.c04_sigma_lower_bound.
Print Assumptions ScoreEnd.c04_beats_fw2.

(** (5) fgh/: the two-sided bracket, the coarse placement, the exact score, B and R2 in Knuth arrows *)
Print Abs.U.
Print Abs.iter.
Print Abs.arrow.
Print Abs.Bx.
Check Abs.Bx_def.
Print Chain.R2.
Print FArith.f_w1.
Print Exact.sigma_c04.
Print Exact.top.
Print Exact.run.
Print Exact.gnext.
Print Exact.sig_key.
Print Exact.sig31.
Print Exact.sig37.
Print Exact.sig43.
Print Exact.sig49.
Print Exact.sig55.
Print Exact.HN.

Definition c04_fgh_all : Prop :=
  (forall c N, c0 -[ Base.tm ]->* c -> halted Base.tm c -> K31_Abs.ones c N ->
     Score.f_omega (Score.f_omega (12 * Abs.Bx + 26)) < N /\ N < Score.f_omega (Score.f_omega (12 * Abs.Bx + 27)))%nat /\
  (forall c N, c0 -[ Base.tm ]->* c -> halted Base.tm c -> K31_Abs.ones c N ->
     FArith.f_w1 3 < N /\ N < FArith.f_w1 4)%nat /\
  (forall c N, c0 -[ Base.tm ]->* c -> halted Base.tm c -> K31_Abs.ones c N -> N = Exact.sigma_c04) /\
  (exists c, c0 -[ Base.tm ]->* c /\ halted Base.tm c /\ K31_Abs.ones c Exact.sigma_c04) /\
  (Score.f_omega (Score.f_omega (12 * Abs.Bx + 26)) < Exact.sigma_c04 /\
     Exact.sigma_c04 < Score.f_omega (Score.f_omega (12 * Abs.Bx + 27)))%nat /\
  (2 * Abs.Bx + 4 = Abs.arrow 13 2 3)%nat /\
  (2 * Chain.R2 Abs.Bx + 4 = Abs.arrow (12 * Abs.Bx + 26) 2 4)%nat.

Theorem c04_fgh_all_ok : c04_fgh_all.
Proof.
  split; [exact EndU.c04_fgh_bracket |]. split; [exact EndU.c04_fgh_coarse |].
  split; [exact Exact.c04_score_exact |]. split; [exact Exact.c04_score_reached |].
  split; [exact Exact.c04_sigma_bracket |]. split; [exact FArith.Bx_knuth | exact FArith.R2_knuth].
Qed.

Print Assumptions c04_fgh_all_ok.
