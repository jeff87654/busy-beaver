(** * BB44A_cmp: Argon's BB(4,4) machine 44-A beats 44-C (and the published BB(4,4) entry).

    44-A = 1LB2LC3RA0RB_2RC1RZ2LB3LB_1LB2RC3RA1LD_2RC1LC3RD2LD  (BB44A_rules.v, BB44A_run.v, new)
    44-C = 1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD  (argon_scout/M44, unchanged: BB44, Individual44,
           BB44_rules, BB44_run, BB44_bound; logical root Local)

    BB44_bound.sigma_exact_closed_form : BB44_run.sigma = knuth (2^16 - 4) 2 6 + (2^16 - 4)    (44-C, exact)
    BB44_bound.sigma_beats_official_bb44 : knuth 509 2 3 + 510 < BB44_run.sigma
    BB44A_run : 44-A halts with sigma = 2 M3 + 2 M1 + 3 nonzero cells, where (closed forms, M44's g_iter_closed)
       2 M1 + 4 = 2 ^^^^ 6,   2 M2 + 4 = 2 ^(2 M1) 5,   2 M3 + 4 = 2 ^(2 M1) (2 M2 + 5).

      Theorem sigma_A_closed : 2 * BB44A_run.M3 + 4 = knuth (2 * BB44A_run.M1) 2 (2 * BB44A_run.M2 + 5)
                               /\ 2 * BB44A_run.M1 + 4 = knuth 4 2 6.
      Theorem BB44A_beats_C : BB44_run.sigma < BB44A_run.sigma.
      Corollary BB44A_beats_official : knuth 509 2 3 + 510 < BB44A_run.sigma.

    Both sigmas count the nonzero cells after the halting transition (44-C: A2 = 1RZ over a 2; 44-A: B1 = 1RZ over
    a 1; BB44A_run.c_final_nonzero / c_final_head). *)

From Local Require Import Individual44 BB44_bound.
From Local Require BB44_rules BB44_run BB44A_rules BB44A_run.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

Lemma knuth_k_4_gt : forall j, knuth j 2 4 >= j + 6.
Proof.
  induction j as [|j IH].
  - simpl. lia.
  - destruct j as [|j'].
    + simpl. lia.
    + rewrite (knuth_S (S j') 2 3), (knuth_S (S j') 2 2), knuth_2.
      pose proof (knuth_ge_2b (S j') (knuth (S j') 2 4)) as H2. lia.
Qed.

Theorem sigma_A_closed : 2 * BB44A_run.M3 + 4 = knuth (2 * BB44A_run.M1) 2 (2 * BB44A_run.M2 + 5)
  /\ 2 * BB44A_run.M1 + 4 = knuth 4 2 6.
Proof.
  split.
  - rewrite (g_iter_closed_gen (2 * BB44A_run.M1) (2 * BB44A_run.M2 + 3) BB44A_run.M3 BB44A_run.M3_eq).
    f_equal. lia.
  - exact (g_iter_closed_gen 4 4 BB44A_run.M1 BB44A_run.M1_eq).
Qed.

Lemma knuth_2_2_4 : knuth 2 2 4 = 2 ^ 16.
Proof. rewrite (knuth_S 1 2 3), knuth_1_pow. reflexivity. Qed.

Theorem BB44A_beats_C : BB44_run.sigma < BB44A_run.sigma.
Proof.
  destruct sigma_A_closed as [H3 H1].
  pose proof (g_iter_closed_gen (2 * BB44A_run.M1) 3 BB44A_run.M2 BB44A_run.M2_eq) as H2.
  rewrite sigma_exact_closed_form. unfold BB44A_run.sigma.
  (* 2 M1 >= 2^16 - 4 *)
  assert (HM1 : 2 ^ 16 <= knuth 4 2 6).
  { rewrite <- knuth_2_2_4. eapply Nat.le_trans; [apply (knuth_mono_b 2 4 6); lia|].
    apply knuth_mono_k; lia. }
  (* M2 >= 3 *)
  pose proof (knuth_ge_2b (2 * BB44A_run.M1) (3 + 2)) as HM2.
  assert (H16 : 5 <= 2 ^ 16).
  { apply Nat.le_trans with (m := 2 ^ 3); [simpl; lia | apply Nat.pow_le_mono_r; lia]. }
  remember (2 ^ 16 - 5) as L eqn:HL.
  assert (E : 2 ^ 16 - 4 = S L) by (subst L; lia).
  rewrite E.
  assert (HL1 : S L <= 2 * BB44A_run.M1) by (subst L; lia).
  (* 2 M3 + 4 >= 2^(S L) 7 = 2^L (2^(S L) 6) >= 2 * K6 *)
  assert (HK : knuth (S L) 2 7 <= knuth (2 * BB44A_run.M1) 2 (2 * BB44A_run.M2 + 5)).
  { eapply Nat.le_trans; [apply (knuth_mono_k (S L) (2 * BB44A_run.M1) 7); lia|]. apply knuth_mono_b. lia. }
  rewrite (knuth_S L 2 6) in HK.
  pose proof (knuth_ge_2b L (knuth (S L) 2 6)) as HK2.
  pose proof (knuth_k_4_gt (S L)) as HK3.
  pose proof (knuth_mono_b (S L) 4 6 ltac:(lia)) as HK4.
  lia.
Qed.

Corollary BB44A_beats_official : knuth 509 2 3 + 510 < BB44A_run.sigma.
Proof. pose proof sigma_beats_official_bb44. pose proof BB44A_beats_C. lia. Qed.

Print Assumptions sigma_A_closed.
Print Assumptions BB44A_beats_C.
Print Assumptions BB44A_beats_official.
