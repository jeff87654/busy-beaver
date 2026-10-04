(** * Exact score of the 35-digit BB(8) champion-rule machine, in closed form *)

(** Machine: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_---0LC_1RG1LD_1LC0RH_1RG1LF  (E0 undefined = the halt).

    BB8_champ35_bound.v proves  score_exact : ones at the halt = 24 * bf + 106  with
    bf = U 34 (U 34 0), and the inequality  arrow 35 2 (arrow 35 2 3) <= bf + 2.
    This file replaces the inequality by an equation.  In Ligocki's notation for the BB(7)
    champion (wiki page of 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF), the accumulator
    of  B(A; b, c, ...) = 0^inf 1 (01)^(3z+1) 1 ... 1 (01)^(3b+1) 1 (01)^0 1 (01)^(3A+1) G> 0^inf
    is A = 2 b + 1 where b is the counter of Kc, and the clearing functions satisfy

      2 * U j x + 4 = 2 ^(j+1 arrows) (2 x + 4)            (U_closed)

    i.e. g_(j+1)(A) + 3 = 2 ^(j+1 arrows) (A + 3) for the accumulator A = 2 x + 1.  Hence

      2 * bf + 4 = 2 ^(37 arrows) 3                        (bf_closed)
      ones at the halt = 12 * (2 ^(37 arrows) 3) + 58      (score_closed)

    and the standard score (counting the 1 written by the halting transition) is
    12 * (2 ^(37 arrows) 3) + 59.  Everything is imported unchanged from the two files above.

    Tactic discipline: never let the unifier compare two different closed [arrow] or [U] terms
    (it would evaluate them).  All rewrites use fully instantiated equations, and [lia] only sees
    the goal after the closed term has been generalized. *)

From BB8 Require Import Individual82.
From BB8 Require Import BB8_champ35_1RB0RA.
From BB8 Require Import BB8_champ35_bound.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

Opaque arrow.
Opaque U.
Opaque bf.

(** 2 * U j x + 4 = 2 ^(j+1) (2 x + 4), arrows *)
Lemma U_closed : forall j x, 2 * U j x + 4 = arrow (S j) 2 (2 * x + 4).
Proof.
  induction j as [| j IH]; intros x.
  - rewrite (U_0 x), (arrow_1_pow 2 (2 * x + 4)).
    pose proof (dbl_closed (2 * x + 2) 0) as H.
    replace (2 * x + 4) with (S (S (2 * x + 2))) by lia.
    rewrite !Nat.pow_succ_r'. lia.
  - assert (Hit : forall n, 2 * iter n (U j) 0 + 4 = iter n (arrow (S j) 2) 4).
    { induction n as [| n IHn].
      - reflexivity.
      - simpl iter. rewrite (IH (iter n (U j) 0)), IHn. reflexivity. }
    rewrite (U_S j x), (arrow_S_iter (S j) 2 (2 * x + 4)).
    replace (2 * x + 4) with (S (S (2 * x + 2))) by lia.
    rewrite (iter_S' (S (2 * x + 2)) (arrow (S j) 2) 1).
    rewrite (iter_S' (2 * x + 2) (arrow (S j) 2) (arrow (S j) 2 1)).
    rewrite (arrow_one (S j)), (arrow_two (S j)).
    exact (Hit (2 * x + 2)).
Qed.

(** 2 ^37 3 = 2 ^36 4 = 2 ^35 (2 ^36 3) = 2 ^35 (2 ^35 4), arrows *)
Lemma arrow_37_3 : arrow 37 2 3 = arrow 35 2 (arrow 35 2 4).
Proof.
  transitivity (arrow 36 2 (arrow 37 2 2)); [exact (arrow_SS 36 2 2) |].
  rewrite (arrow_two 37).
  transitivity (arrow 35 2 (arrow 36 2 3)); [exact (arrow_SS 35 2 3) |].
  rewrite (arrow_SS 35 2 2), (arrow_two 36).
  reflexivity.
Qed.

Theorem bf_closed : 2 * bf + 4 = arrow 37 2 3.
Proof.
  rewrite arrow_37_3, bf_def.
  rewrite (U_closed 34 (U 34 0)).
  rewrite (U_closed 34 0).
  change (2 * 0 + 4) with 4.
  reflexivity.
Qed.

(** ones on the tape when the machine halts (head in E on a 0, before the final write) *)
Theorem score_closed : exists c, c0 -->* c /\ halted tm c /\ ones c (12 * arrow 37 2 3 + 58).
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c. split; [exact H1 | split; [exact H2 |]].
  rewrite <- bf_closed.
  replace (12 * (2 * bf + 4) + 58) with (24 * bf + 106) by lia.
  exact H3.
Qed.

Theorem sigma_gt_arrow37 : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ arrow 37 2 3 < N.
Proof.
  destruct score_closed as [c [H1 [H2 H3]]].
  exists c, (12 * arrow 37 2 3 + 58).
  split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  generalize (arrow 37 2 3). intros T. lia.
Qed.

Print Assumptions U_closed.
Print Assumptions bf_closed.
Print Assumptions score_closed.
Print Assumptions sigma_gt_arrow37.
