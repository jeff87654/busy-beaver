(** * Final7.v : C7 halts, and its score (BB9/verify_c7).
    C7 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA halts in state H reading 1 (H1 undefined),
    so its score is the number N of ones on the halting tape.  From the simulation (Sim.v: X' simulates C7 with the
    same tape) and X''s run (XDev.C7Final.x_goal: X' halts with N ones, f_omega^4 (12 Bx + 27) < N):
      c7_halts, c7_lower (f_omega^4 (6 * 2^^13 3 + 3) < N), c7_beats_m8_bound (f_omega^2 (6 * 2^^13 3 + 3) < N). *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XL Require Individual112.
From XDev Require Abs Ones C7Final.
From XScore Require Score.
From C7 Require Import Defs.
From C7 Require Sim.
Opaque Abs.U Abs.arrow Score.f_omega.
Local Open Scope nat_scope.

Theorem c7_halts : halts tm7 c0.
Proof. exact (Sim.c7_halts_of_x C7Final.x_halts). Qed.

(** ** X''s ones count is unique *)
Theorem ones_uniquex : forall c N1 N2, Ones.ones c N1 -> Ones.ones c N2 -> N1 = N2.
Proof.
  intros c N1 N2 [q1 [L1 [R1 [s1 [E1 F1]]]]] [q2 [L2 [R2 [s2 [E2 F2]]]]].
  rewrite E1 in E2. injection E2 as Eq EL Es ER. subst.
  rewrite (Sim.side_countx L1 L2 EL), (Sim.side_countx R1 R2 ER). reflexivity.
Qed.

Theorem c7_score_x : forall c N, c0 -[ tm7 ]->* c -> halted tm7 c -> ones c N ->
  Score.f_omega (Score.f_omega (12 * Abs.Bx + 27)) < N /\
  Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (12 * Abs.Bx + 27)))) < N.
Proof.
  intros c N H1 H2 H3.
  destruct (Sim.c7_to_x c N H1 H2 H3) as [cx [G1 [G2 G3]]].
  destruct C7Final.x_goal as [cx' [N' [G1' [G2' [G3' [G4' G5']]]]]].
  pose proof (Sim.halted_uniquex _ _ _ G1 G1' G2 G2') as E. subst cx'.
  pose proof (ones_uniquex _ _ _ G3 G3') as E. subst N'.
  split; assumption.
Qed.

(** ** Arithmetic *)
Lemma arrow13 : Abs.arrow 13 2 3 = Abs.arrow 11 2 (Abs.arrow 11 2 4).
Proof.
  rewrite (Abs.arrow_SS 12 2 2), (Abs.arrow_two 13), (Abs.arrow_SS 11 2 3), (Abs.arrow_SS 11 2 2), (Abs.arrow_two 12).
  reflexivity.
Qed.

Lemma Bx_knuth : 2 * Abs.Bx + 4 = Abs.arrow 13 2 3.
Proof. rewrite arrow13. exact Abs.Bx_closed. Qed.

Transparent Abs.arrow.
Lemma arrow_eq : forall k a b, arrow k a b = Abs.arrow k a b.
Proof. intros. reflexivity. Qed.
Opaque Abs.arrow arrow.
Transparent Score.f_omega.
Lemma fomega_eq : forall n, f_omega n = Score.f_omega n.
Proof. intros. reflexivity. Qed.
Opaque Score.f_omega f_omega.

Lemma m8_arg : 6 * arrow 13 2 3 + 3 = 12 * Abs.Bx + 27.
Proof. rewrite arrow_eq. pose proof Bx_knuth. lia. Qed.

Theorem c7_lower : forall c N, c0 -[ tm7 ]->* c -> halted tm7 c -> ones c N ->
  f_omega (f_omega (f_omega (f_omega (6 * arrow 13 2 3 + 3)))) < N.
Proof.
  intros c N H1 H2 H3. rewrite m8_arg, !fomega_eq. exact (proj2 (c7_score_x c N H1 H2 H3)).
Qed.

(** M8's (and C04's) score is below f_omega (f_omega (6 * arrow 13 2 3 + 3)) (BB8/verify_m8 Statement.m8_bracket). *)
Theorem c7_beats_m8_bound : forall c N, c0 -[ tm7 ]->* c -> halted tm7 c -> ones c N ->
  f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N.
Proof.
  intros c N H1 H2 H3. rewrite m8_arg, !fomega_eq. exact (proj1 (c7_score_x c N H1 H2 H3)).
Qed.
