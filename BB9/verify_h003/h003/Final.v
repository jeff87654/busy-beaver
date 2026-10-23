(** * Final.v : h003 halts, and its score (BB9/verify_h003).
    h003 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LH0LC_1RG1LD_0RG0RF_0LI---_1RI1RC halts in state H reading 1 (H1 undefined),
    so its score is the number N of ones on the halting tape.  From the simulation (Sim.v: X3 simulates h003 with the
    same tape) and X3's run (XDev.HGoal.x_goal6: X3 halts with N ones, f_omega^6 (12 Bx + 26) < N, f_omega^7 12 < N,
    f_omega^2 (12 Bx + 27) < N):
      h003_halts, h003_lower (f_omega^6 (6 * 2^^13 3 + 2) < N), h003_lower7_12 (f_omega^7 12 < N),
      h003_beats_m8_bound (f_omega^2 (6 * 2^^13 3 + 3) < N). *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XL Require Individual112.
From XDev Require Abs Ones HFinal HGoal.
From XScore Require Score.
From H3 Require Import Defs.
From H3 Require Sim.
Opaque Abs.U Abs.arrow Score.f_omega arrow f_omega.   (* the f_omega of a numeral must never be unfolded *)
Local Open Scope nat_scope.

Theorem h003_halts : halts tmh c0.
Proof. exact (Sim.h003_halts_of_x HFinal.x_halts). Qed.

(** ** X3's ones count is unique *)
Theorem ones_uniquex : forall c N1 N2, Ones.ones c N1 -> Ones.ones c N2 -> N1 = N2.
Proof.
  intros c N1 N2 [q1 [L1 [R1 [s1 [E1 F1]]]]] [q2 [L2 [R2 [s2 [E2 F2]]]]].
  rewrite E1 in E2. injection E2 as Eq EL Es ER. subst.
  rewrite (Sim.side_countx L1 L2 EL), (Sim.side_countx R1 R2 ER). reflexivity.
Qed.

Theorem h003_score_x : forall c N, c0 -[ tmh ]->* c -> halted tmh c -> ones c N ->
  Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (12 * Abs.Bx + 26)))))) < N /\
  Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega 12)))))) < N /\
  Score.f_omega (Score.f_omega (12 * Abs.Bx + 27)) < N.
Proof.
  intros c N H1 H2 H3.
  destruct (Sim.h003_to_x c N H1 H2 H3) as [cx [G1 [G2 G3]]].
  destruct HGoal.x_goal6 as [cx' [N' [G1' [G2' [G3' [G4' [G5' G6']]]]]]].
  pose proof (Sim.halted_uniquex _ _ _ G1 G1' G2 G2') as E. subst cx'.
  pose proof (ones_uniquex _ _ _ G3 G3') as E. subst N'.
  split; [assumption | split; assumption].
Qed.

(** ** Arithmetic *)
Lemma arrow13 : Abs.arrow 13 2 3 = Abs.arrow 11 2 (Abs.arrow 11 2 4).
Proof.
  rewrite (Abs.arrow_SS 12 2 2), (Abs.arrow_two 13), (Abs.arrow_SS 11 2 3), (Abs.arrow_SS 11 2 2), (Abs.arrow_two 12).
  reflexivity.
Qed.

Lemma Bx_knuth : 2 * Abs.Bx + 4 = Abs.arrow 13 2 3.
Proof. rewrite arrow13. exact Abs.Bx_closed. Qed.

Transparent Abs.arrow arrow.
Lemma arrow_eq : forall k a b, arrow k a b = Abs.arrow k a b.
Proof. intros. reflexivity. Qed.
Opaque Abs.arrow arrow.

(** Defs.f_omega to Score.f_omega under a VARIABLE argument only: with a numeral or a sum argument, unifying the
    two (convertible) constants would make Coq evaluate the fixpoint f (as in ../verify_c7/c7/Final7.v). *)
Transparent Score.f_omega f_omega.
Lemma fomega_eq : forall n, f_omega n = Score.f_omega n.
Proof. intros. reflexivity. Qed.
Opaque Score.f_omega f_omega.

Lemma tr2 : forall x N, Score.f_omega (Score.f_omega x) < N -> f_omega (f_omega x) < N.
Proof. intros x N H. rewrite !fomega_eq. exact H. Qed.

Lemma tr6 : forall x N,
  Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega x))))) < N ->
  f_omega (f_omega (f_omega (f_omega (f_omega (f_omega x))))) < N.
Proof. intros x N H. rewrite !fomega_eq. exact H. Qed.

Lemma tr7 : forall x N,
  Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega x)))))) < N ->
  f_omega (f_omega (f_omega (f_omega (f_omega (f_omega (f_omega x)))))) < N.
Proof. intros x N H. rewrite !fomega_eq. exact H. Qed.

Lemma arg26 : 6 * arrow 13 2 3 + 2 = 12 * Abs.Bx + 26.
Proof. rewrite arrow_eq. pose proof Bx_knuth. lia. Qed.

Lemma arg27 : 6 * arrow 13 2 3 + 3 = 12 * Abs.Bx + 27.
Proof. rewrite arrow_eq. pose proof Bx_knuth. lia. Qed.

(** ** The bounds *)
Theorem h003_lower : forall c N, c0 -[ tmh ]->* c -> halted tmh c -> ones c N ->
  f_omega (f_omega (f_omega (f_omega (f_omega (f_omega (6 * arrow 13 2 3 + 2)))))) < N.
Proof.
  intros c N H1 H2 H3. pose proof (proj1 (h003_score_x c N H1 H2 H3)) as G.
  rewrite <- arg26 in G. exact (tr6 _ N G).
Qed.

Theorem h003_lower7_12 : forall c N, c0 -[ tmh ]->* c -> halted tmh c -> ones c N ->
  f_omega (f_omega (f_omega (f_omega (f_omega (f_omega (f_omega 12)))))) < N.
Proof.
  intros c N H1 H2 H3. exact (tr7 12 N (proj1 (proj2 (h003_score_x c N H1 H2 H3)))).
Qed.

(** M8's (and C04's) score is below f_omega (f_omega (6 * arrow 13 2 3 + 3)) (BB8/verify_m8 Statement.m8_bracket). *)
Theorem h003_beats_m8_bound : forall c N, c0 -[ tmh ]->* c -> halted tmh c -> ones c N ->
  f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N.
Proof.
  intros c N H1 H2 H3. pose proof (proj2 (proj2 (h003_score_x c N H1 H2 H3))) as G.
  rewrite <- arg27 in G. exact (tr2 _ N G).
Qed.
