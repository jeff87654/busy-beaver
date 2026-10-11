(** * T12a in the fast-growing hierarchy: a lower bound at level (omega+1)^2

    T12a = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LI0LC_0RG1LD_1RH1LG_1LC0RG_0LJ0LI_1RK0LC_0RL---_0RF---

    Imports the halting proof BB12_T12a.v and the score file BB12_T12a_bound.v unchanged, and reuses the standard
    fast-growing hierarchy of BB10_n1_fgh.v (fgh 0 n = n + 1, fgh (k+1) n = (fgh k)^n n, f_omega n = fgh n n,
    f_omega1 n = f_omega^n n).  Main result (no axioms):

      fgh_lower2 : the halting tape holds N ones with  f_omega1 (f_omega1 (JJ - 2)) <= 6 N + 11,
                   JJ = (3 T - 13) / 7,  T = 2 ^(37 arrows) 3.

    Proof: sigma_lower_bound gives w >= F^(2 JJ + 1)(34), F w <= 7 J + 9 and F^(2 J)(w) <= 6 N + 11.  n1's
    lower_from turns the first into w >= f_omega1 (JJ - 2); F w >= 7 w + 9 gives J >= w; n1's fo_iter_le
    (f_omega^j m <= F^(2 j) m) gives f_omega1 w = f_omega^w w <= f_omega^J w <= F^(2 J) w.  The two files define
    arrow, F, iter and JJ separately; they agree (arrow_n1, JJ_n1 of BB12_T12a_bound.v, and F_n1, iterF_n1 here). *)

From BB8 Require Import Individual122.
From BB8 Require Import BB12_T12a BB12_T12a_bound.
From BB8 Require BB10_n1 BB10_n1_fgh.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

(** Never let a tactic compute these numbers (Opaque declarations are not exported by the imported files). *)
Opaque U arrow F BB10_n1.U BB10_n1.arrow BB10_n1.F BB10_n1_fgh.fgh.

Transparent F BB10_n1.F.
Lemma F_n1 : forall n, BB10_n1.F n = F n.
Proof. intro n. unfold BB10_n1.F, F. apply arrow_n1. Qed.
Opaque F BB10_n1.F.

Lemma iterF_n1 : forall j x, BB10_n1.iter j BB10_n1.F x = iter j F x.
Proof.
  induction j as [| j IH]; intro x; [reflexivity |].
  cbn [BB10_n1.iter iter]. rewrite IH, F_n1. reflexivity.
Qed.

(** F w >= 7 w + 9 (n1's F; F w = 2 ^(w-1 arrows) F (w-1) >= 3 F (w-1)) *)
Lemma F_7 : forall w, 4 <= w -> 7 * w + 9 <= BB10_n1.F w.
Proof.
  intros w Hw.
  replace w with (S (S (S (S (w - 4))))) by lia.
  rewrite BB10_n1.F_S.
  pose proof (BB10_n1_fgh.arrow_3x (S (w - 4)) (BB10_n1.F (S (S (S (w - 4))))) ltac:(pose proof (BB10_n1.F_ge (S (S (S (w - 4))))); lia)) as A.
  rewrite BB10_n1.F_S in A |- *.
  pose proof (BB10_n1_fgh.arrow_3x (w - 4) (BB10_n1.F (S (S (w - 4)))) ltac:(pose proof (BB10_n1.F_ge (S (S (w - 4)))); lia)) as B.
  pose proof (BB10_n1.F_ge (S (S (w - 4)))).
  lia.
Qed.

Theorem fgh_lower2 : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  BB10_n1_fgh.f_omega1 (BB10_n1_fgh.f_omega1 (JJ - 2)) <= 6 * N + 11.
Proof.
  destruct sigma_lower_bound as [c [N [J [w [H1 [H2 [H3 [Hw [HFJ HN]]]]]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  rewrite <- iterF_n1 in Hw, HN. rewrite <- F_n1 in HFJ. rewrite <- JJ_n1 in Hw |- *.
  assert (A : BB10_n1_fgh.f_omega1 (BB10_n1.JJ - 2) <= w).
  { pose proof (BB10_n1_fgh.lower_from (S w) ltac:(lia)). lia. }
  assert (Hw34 : 34 <= w) by (pose proof (BB10_n1.iterF_ge (2 * BB10_n1.JJ + 1) 34); lia).
  pose proof (F_7 w ltac:(lia)) as B.
  assert (Jw : w <= J) by lia.
  pose proof (BB10_n1_fgh.fo_iter_le J w ltac:(lia)) as C.
  pose proof (BB10_n1_fgh.iterfo_mono w J w w Jw (le_n w)) as D.
  pose proof (BB10_n1_fgh.f_omega1_mono _ _ A) as E. rewrite (BB10_n1_fgh.f_omega1_iter w) in E.
  lia.
Qed.

Print Assumptions fgh_lower2.
