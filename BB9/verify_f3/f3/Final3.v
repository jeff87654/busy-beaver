(** * Final3.v : f3_0RC halts, and its score (bb9_f3_coq).

    f3 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_0LI---_0RC1RF halts in state H reading 1 (H1 undefined),
    so its score is the number N of ones on the halting tape.  From the simulation (Sim.v: X simulates f3 with the
    same tape) and X's score (XScore.x_goal):
      f3_halts       : halts tm3 c0
      f3_score_x     : every halting count N satisfies f_omega (f_omega a) < N for every a <= 12 Rpp + 10
      Rpp_explicit   : 2 Rpp + 4 = iter (2^^13 3 - 5) (arrow 6 2) (iter 4 (arrow 5 2) 4)   (arrow k 2 = 2 ↑^k)
      m8_le          : 6 * arrow 13 2 3 + 3 <= 12 Rpp + 10   (6 * 2^^13 3 + 3 = 12 B + 27, M8's upper bound argument) *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XL Require Individual112.
From XDev Require Abs XTop XScore.
From XScore Require Score.
From XK31 Require K31_Abs.
From F3 Require Import Defs.
From F3 Require Sim.
Opaque Abs.U Abs.arrow Score.f_omega.
Local Open Scope nat_scope.

Theorem f3_halts : halts tm3 c0.
Proof. exact Sim.f3_halts_sim. Qed.

(** ** X's ones count is unique *)
Theorem ones_uniquex : forall c N1 N2, K31_Abs.ones c N1 -> K31_Abs.ones c N2 -> N1 = N2.
Proof.
  intros c N1 N2 [q1 [L1 [R1 [s1 [E1 F1]]]]] [q2 [L2 [R2 [s2 [E2 F2]]]]].
  rewrite E1 in E2. injection E2 as Eq EL Es ER. subst.
  rewrite (Sim.side_countx L1 L2 EL), (Sim.side_countx R1 R2 ER). reflexivity.
Qed.

Theorem f3_score_x : forall c N, c0 -[ tm3 ]->* c -> halted tm3 c -> ones c N ->
  forall a, a <= 12 * XTop.Rpp + 10 -> Score.f_omega (Score.f_omega a) < N.
Proof.
  intros c N H1 H2 H3 a Ha.
  destruct (Sim.f3_to_x c N H1 H2 H3) as [cx [G1 [G2 G3]]].
  destruct XScore.x_goal as [cx' [N' [G1' [G2' [G3' G4']]]]].
  pose proof (Sim.halted_uniquex _ _ _ G1 G1' G2 G2') as E. subst cx'.
  pose proof (ones_uniquex _ _ _ G3 G3') as E. subst N'.
  exact (G4' a Ha).
Qed.

(** ** Arithmetic *)
Lemma arrow13 : Abs.arrow 13 2 3 = Abs.arrow 11 2 (Abs.arrow 11 2 4).
Proof.
  rewrite (Abs.arrow_SS 12 2 2), (Abs.arrow_two 13), (Abs.arrow_SS 11 2 3), (Abs.arrow_SS 11 2 2), (Abs.arrow_two 12).
  reflexivity.
Qed.

Lemma Bx_knuth : 2 * Abs.Bx + 4 = Abs.arrow 13 2 3.
Proof. rewrite arrow13. exact Abs.Bx_closed. Qed.

Lemma iterU_closed : forall j n x, 2 * Abs.iter n (Abs.U j) x + 4 = Abs.iter n (Abs.arrow (S j) 2) (2 * x + 4).
Proof.
  intros j n x. induction n as [| n IH]; [reflexivity |].
  change (Abs.iter (S n) (Abs.U j) x) with (Abs.U j (Abs.iter n (Abs.U j) x)).
  change (Abs.iter (S n) (Abs.arrow (S j) 2) (2 * x + 4)) with (Abs.arrow (S j) 2 (Abs.iter n (Abs.arrow (S j) 2) (2 * x + 4))).
  rewrite Abs.U_closed, IH. reflexivity.
Qed.

Theorem Rpp_explicit : 2 * XTop.Rpp + 4 = Abs.iter (Abs.arrow 13 2 3 - 5) (Abs.arrow 6 2) (Abs.iter 4 (Abs.arrow 5 2) 4).
Proof.
  unfold XTop.Rpp, XTop.R1x. rewrite iterU_closed, iterU_closed.
  pose proof Bx_knuth. replace (Abs.arrow 13 2 3 - 5) with (2 * Abs.Bx - 1) by lia. reflexivity.
Qed.

Lemma Rpp_ge : Abs.Bx + 2 <= XTop.Rpp.
Proof.
  pose proof Abs.Bx_ge6.
  assert (Hg : forall a, a + 1 <= Abs.U 5 a) by (intro a; pose proof (Score.sc_U_lin 5 a); lia).
  pose proof (Score.sc_iter_count (Abs.U 5) Hg (2 * Abs.Bx - 1) XTop.R1x). unfold XTop.Rpp. lia.
Qed.

Theorem m8_le : 6 * Abs.arrow 13 2 3 + 3 <= 12 * XTop.Rpp + 10.
Proof. pose proof Bx_knuth. pose proof Rpp_ge. lia. Qed.

(** ** The score with Defs.v's definitions *)
Lemma iter_eq : forall n g x, iter n g x = Abs.iter n g x.
Proof. intros. reflexivity. Qed.

Transparent Abs.arrow.
Lemma arrow_eq : forall k a b, arrow k a b = Abs.arrow k a b.
Proof. intros. reflexivity. Qed.
Opaque Abs.arrow arrow.

Transparent Score.f_omega.
Lemma fomega_eq : forall n, f_omega n = Score.f_omega n.
Proof. intros. reflexivity. Qed.
Lemma fomega2_eq : forall x y, x = y -> f_omega (f_omega x) = Score.f_omega (Score.f_omega y).
Proof. intros x y ->. reflexivity. Qed.
Opaque Score.f_omega f_omega.

Lemma iter_arrow_eq : forall n1 n2 k x1 x2,
  n1 = n2 -> x1 = x2 -> iter n1 (arrow k 2) x1 = Abs.iter n2 (Abs.arrow k 2) x2.
Proof.
  intros n1 n2 k x1 x2 -> ->.
  induction n2 as [| n IH]; [reflexivity |].
  change (iter (S n) (arrow k 2) x2) with (arrow k 2 (iter n (arrow k 2) x2)).
  change (Abs.iter (S n) (Abs.arrow k 2) x2) with (Abs.arrow k 2 (Abs.iter n (Abs.arrow k 2) x2)).
  rewrite IH. apply arrow_eq.
Qed.

Opaque iter Abs.iter arrow Abs.arrow f_omega Score.f_omega.

Lemma rhs_eq : iter (arrow 13 2 3 - 5) (arrow 6 2) (iter 4 (arrow 5 2) 4) =
  Abs.iter (Abs.arrow 13 2 3 - 5) (Abs.arrow 6 2) (Abs.iter 4 (Abs.arrow 5 2) 4).
Proof.
  apply iter_arrow_eq.
  - exact (f_equal2 Nat.sub (arrow_eq 13 2 3) eq_refl).
  - exact (iter_arrow_eq 4 4 5 4 4 eq_refl eq_refl).
Qed.

Theorem f3_lower : forall c N, c0 -[ tm3 ]->* c -> halted tm3 c -> ones c N ->
  f_omega (f_omega (6 * iter (arrow 13 2 3 - 5) (arrow 6 2) (iter 4 (arrow 5 2) 4) - 14)) < N.
Proof.
  intros c N H1 H2 H3.
  assert (E : 6 * iter (arrow 13 2 3 - 5) (arrow 6 2) (iter 4 (arrow 5 2) 4) - 14 = 12 * XTop.Rpp + 10).
  { rewrite rhs_eq. pose proof Rpp_explicit. lia. }
  rewrite E, fomega_eq. exact (f3_score_x c N H1 H2 H3 _ (le_n _)).
Qed.

Theorem f3_beats_m8_bound : forall c N, c0 -[ tm3 ]->* c -> halted tm3 c -> ones c N ->
  f_omega (f_omega (6 * arrow 13 2 3 + 3)) < N.
Proof.
  intros c N H1 H2 H3.
  assert (E : f_omega (f_omega (6 * arrow 13 2 3 + 3)) = Score.f_omega (Score.f_omega (6 * Abs.arrow 13 2 3 + 3))).
  { apply fomega2_eq. exact (f_equal (fun z => 6 * z + 3) (arrow_eq 13 2 3)). }
  exact (eq_ind_r (fun z => z < N) (f3_score_x c N H1 H2 H3 (6 * Abs.arrow 13 2 3 + 3) m8_le) E).
Qed.

(* Print Assumptions is run in XScore.v, XFinal.v, and probe.v *)
