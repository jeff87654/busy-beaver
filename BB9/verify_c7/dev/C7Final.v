(** * C7Final.v : X' halts from the blank tape, with N ones, f_omega^4 (12 Bx + 27) < N (BB9/verify_c7).
    j1, j2 are fixed by Bx, R1, R2 (divisions by 5, exact by the residues); C7Arith.c7_arith provides the rest. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List ZArith.
Import ListNotations.
Set Default Goal Selector "!".
From XScore Require Import Score.   (* first: C7Top's R2 etc. must shadow Score's *)
From XL Require Import Individual112.   (* again: S1 is the symbol, not Score.S1 *)
From XDev Require Import Base G_rules Abs Lift KStep Res C7Arith C7Count C7Top C7Halt C7Score.
From XDev Require Ones.
Opaque U arrow f_omega.
Local Open Scope nat_scope.

Lemma div5_exact : forall a q, a = 5 * q -> a / 5 = q.
Proof. intros a q ->. rewrite Nat.mul_comm, Nat.div_mul; lia. Qed.

Theorem x_goal : exists cx N, c0 -->* cx /\ halted tm cx /\ Ones.ones cx N /\
  f_omega (f_omega (12 * Bx + 27)) < N /\ f_omega (f_omega (f_omega (f_omega (12 * Bx + 27)))) < N.
Proof.
  set (j1 := (9 * Bx - 9) / 5).
  set (j2 := (9 * R2 j1 + 12 * R1 j1 + 3 * j1 - 2) / 5).
  assert (HB1 : (Z.of_nat Bx mod Mres = rho)%Z) by exact Bx_res.
  assert (HR1 : (Z.of_nat (R1 j1) mod Mres = rho)%Z) by (unfold R1; apply iter_U_res; lia).
  assert (HR2 : (Z.of_nat (R2 j1) mod Mres = rho)%Z) by (unfold R2, D3; apply iter_U_res; lia).
  assert (HR3 : (Z.of_nat (R3 j2) mod Mres = rho)%Z) by (unfold R3; apply iter_U_res; lia).
  assert (HR4 : (Z.of_nat (R4 j2) mod Mres = rho)%Z) by (unfold R4, D5; apply iter_U_res; lia).
  destruct (c7_arith Bx (R1 j1) (R2 j1) (R3 j2) (R4 j2) HB1 HR1 HR2 HR3 HR4)
    as [j1' [j2' [j3 [m [J2 [J3 [J4 [J5 [J6 [J7 [J8 [u [jj [E1 [E2 [E3 [E4 [E5 [E6 [E7 [E8 [E9 [E10 [E11 [E12 [E13 [Hj1 Hjj]]]]]]]]]]]]]]]]]]]]]]]]]]].
  clear HB1 HR1 HR2 HR3 HR4.   (* lia would expand these mod facts with 13-digit constants *)
  assert (Ej1 : j1' = j1) by (unfold j1; symmetry; apply div5_exact; clear - E1; lia).
  subst j1'. clearbody j1.
  assert (Ej2 : j2' = j2) by (unfold j2; symmetry; apply div5_exact; clear - E2; lia).
  subst j2'. clearbody j2.
  (* the run up to the cascade *)
  pose proof (reach_count j1 j2 j3 E1 E2 E3 Hj1) as Hcount.
  assert (HRA : 3 * j3 + 20 <= R10 j3).
  { unfold R10, cend.
    pose proof (C7Top.iter_U_ge (2 * iter (2 * U (S (3 * j3 + 19)) (U (S (3 * j3 + 19)) (R9 j3)) + 1) (U (3 * j3 + 19)) 0 + 3)
                  (3 * j3 + 19 - 1) 0 ltac:(lia)). lia. }
  replace (3 * j3 + 19) with (5 * m) in Hcount by lia.
  destruct (reach_L9 m (R10 j3) J2 J3 J4 J5 J6 J7 J8 u ltac:(lia) ltac:(lia) E5 E6 E7 E8 E9 E10 E11 E12 ltac:(lia))
    as [l [Hl HL9]].
  (* the r = 2 branch *)
  set (R := R10 j3) in *.
  set (A0 := 12 * R - 38 - 4 * u).
  assert (Hu : u <= m) by lia.
  pose proof (r2a1 (12 * R - 34) 22 u (J8 + 8) l) as H1.
  replace (12 * R - 34 + 2) with (12 * R - 32) in H1 by lia. replace (J8 + 8 + 5) with (J8 + 13) in H1 by lia.
  pose proof (pre (A0 + 4 * u) 22 u (J8 + 8) l) as H2.
  replace (A0 + 4 * u + 5) with (S (12 * R - 34)) in H2 by (unfold A0; lia).
  pose proof (rounds u 0 A0 0 (3 * u + 6) 22 (J8 + 8) l) as H3.
  replace (0 + 3 * u + 1) with (3 * u + 1) in H3 by lia. replace (0 + u) with u in H3 by lia.
  replace (0 + 1) with 1 in H3 by lia.
  replace (3 * u + 6 + 3 * u) with (30 * jj + 15 + 3) in H3 by lia.
  pose proof (vh u A0 (30 * jj + 15) 22 (J8 + 8) l) as H4.
  replace (3 * (30 * jj + 15) + 14) with (5 * (18 * jj + 11) + 4) in H4 by lia.
  pose proof (vh2 u A0 (18 * jj + 11) 22 (J8 + 8) l) as H5.
  destruct Hl as [Ll ->].
  destruct (Hc_ones u A0 (18 * jj + 11) 22 (J8 + 8) Ll) as [N [HN HNA]].
  exists (Hc u A0 (18 * jj + 11) 22 (J8 + 8) (Ll *> const S0)), N.
  split; [| split; [apply Hc_halted | split; [exact HN |]]].
  - eapply evstep_trans; [exact Hcount |].
    eapply evstep_trans; [apply progress_evstep, HL9 |].
    eapply evstep_trans; [apply progress_evstep, H1 |].
    eapply evstep_trans; [apply progress_evstep, H2 |].
    eapply evstep_trans; [exact H3 |].
    eapply evstep_trans; [apply progress_evstep, H4 |].
    apply progress_evstep, H5.
  - (* the bounds *)
    destruct (chain_bound j1 j2 j3 E1 E2 E3 Hj1) as [B2 B4].
    pose proof (R5_le_R10 j3) as R510.
    assert (R35 : R3 j2 <= R5 j3).
    { pose proof (C7Top.iter_U_ge (j3 + 3) (3 * j3 + 21) 0 ltac:(lia)).
      pose proof (C7Top.iter_U_ge 2 (D5 j2) 0 ltac:(lia)). unfold R5, R4, D5 in *. lia. }
    fold R in R510. unfold A0 in HNA. split; lia.
Qed.

Theorem x_halts : halts tm c0.
Proof.
  destruct x_goal as [cx [N [H1 [H2 _]]]].
  eapply halts_evstep; [apply halted_halts, H2 | exact H1].
Qed.

Print Assumptions x_goal.
Print Assumptions x_halts.
