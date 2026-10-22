(** * Lower5.v : C7's score is above f_omega^5 (2 * 2^^13 3) and above f_omega^6 (12) (BB9/verify_c7).
    C7 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_1LC0RA.
    Same run as Final7.v (Sim.v + X''s run), with the stronger bounds of XDev.C7Final5.x_goal5: the f_omega levels
    start at the clear after J2 (depth 3 j1 + 12 = (27 B + 33)/5, linear in B), one level more than c7_lower.
    The statements below use only Defs.v and busycoq's TM.v, like Statement.v. *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XL Require Individual112.
From XDev Require Abs Ones C7Final5.
From XScore Require Score.
From C7 Require Import Defs.
From C7 Require Sim Final7.
Opaque Abs.U Abs.arrow Score.f_omega arrow f_omega.   (* Defs.f_omega 12 must never be unfolded *)
Local Open Scope nat_scope.

Theorem c7_score_x5 : forall c N, c0 -[ tm7 ]->* c -> halted tm7 c -> ones c N ->
  Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (4 * Abs.Bx + 8))))) < N /\
  Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega 12))))) < N.
Proof.
  intros c N H1 H2 H3.
  destruct (Sim.c7_to_x c N H1 H2 H3) as [cx [G1 [G2 G3]]].
  destruct C7Final5.x_goal5 as [cx' [N' [G1' [G2' [G3' [G4' G5']]]]]].
  pose proof (Sim.halted_uniquex _ _ _ G1 G1' G2 G2') as E. subst cx'.
  pose proof (Final7.ones_uniquex _ _ _ G3 G3') as E. subst N'.
  split; assumption.
Qed.

Lemma arg5 : 2 * arrow 13 2 3 = 4 * Abs.Bx + 8.
Proof. rewrite Final7.arrow_eq. pose proof Final7.Bx_knuth. lia. Qed.

(** Defs.f_omega to Score.f_omega under a variable argument only: with a numeral or a sum argument, unifying the two
    (convertible) constants would make Coq evaluate the fixpoint f. *)
Lemma tr5 : forall x N,
  Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega x)))) < N ->
  f_omega (f_omega (f_omega (f_omega (f_omega x)))) < N.
Proof. intros x N H. rewrite !Final7.fomega_eq. exact H. Qed.

Lemma tr6 : forall x N,
  Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega (Score.f_omega x))))) < N ->
  f_omega (f_omega (f_omega (f_omega (f_omega (f_omega x))))) < N.
Proof. intros x N H. rewrite !Final7.fomega_eq. exact H. Qed.

(** ** The bounds (2 * 2^^13 3 = 4 B + 8 with 2B + 4 = 2^^13 3, B = C04's first accumulator) *)
Theorem c7_lower5 : forall c N, c0 -[ tm7 ]->* c -> halted tm7 c -> ones c N ->
  f_omega (f_omega (f_omega (f_omega (f_omega (2 * arrow 13 2 3))))) < N.
Proof.
  intros c N H1 H2 H3. pose proof (proj1 (c7_score_x5 c N H1 H2 H3)) as G.
  rewrite <- arg5 in G. exact (tr5 _ N G).
Qed.

Theorem c7_lower6_12 : forall c N, c0 -[ tm7 ]->* c -> halted tm7 c -> ones c N ->
  f_omega (f_omega (f_omega (f_omega (f_omega (f_omega 12))))) < N.
Proof.
  intros c N H1 H2 H3. exact (tr6 12 N (proj2 (c7_score_x5 c N H1 H2 H3))).
Qed.
