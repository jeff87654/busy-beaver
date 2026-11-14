(** * BB44B_cmp: Argon's BB(4,4) machine 44-B beats 44-A (hence 44-C and the published BB(4,4) entry).

    44-B = 1RB2LC3RA1RZ_2RC3LB2LB0LC_1LB2RC3RA1LD_2RC1LC3RD2LD   (BB44B_rules.v, BB44B_run.v)
    44-A = 1LB2LC3RA0RB_2RC1RZ2LB3LB_1LB2RC3RA1LD_2RC1LC3RD2LD   (BB44A_rules.v, BB44A_run.v, BB44A_cmp.v)
    Closed forms from argon_scout/M44/BB44_bound.v (g_closed, g_iter_closed_gen, knuth lemmas), unchanged.

      Theorem sigma_B_closed : 2 dB + 4 = knuth (S (2 cB + 1)) 2 3 /\ 2 cB + 4 = knuth 1 2 (2 bB + 4)
                               /\ 2 bB + 4 = knuth 3 2 (2 a6 + 4) /\ 2 a6 + 4 = knuth 4 2 (2 a5 + 4)
      Theorem BB44B_beats_A : BB44A_run.sigma < BB44B_run.sigma
      Corollary BB44B_beats_C : BB44_run.sigma < BB44B_run.sigma
      Corollary BB44B_beats_official : knuth 509 2 3 + 510 < BB44B_run.sigma
      Theorem sigma_B_f_omega : f_omega (knuth 5 2 3) < BB44B_run.sigma
        with f_omega n = knuth (S n) 2 (n + 3) = 2 ^(n+1) (n+3), the Knuth-arrow f_omega of the published
        BB54_score.v (text-identical definition here): Argon's claim sigma > f_w(2 ^5 3) in that convention.
    Both sigmas count the nonzero cells after the halting transition (BB44B_run.c_final_nonzero / c_final_head). *)

From Local Require Import Individual44 BB44_bound.
From Local Require BB44_rules BB44_run BB44A_run BB44A_cmp BB44B_rules BB44B_run.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

Lemma g_pos : forall k m, 1 <= BB44_rules.g k m.
Proof.
  induction k as [|k IH]; intros m; [cbn [BB44_rules.g]; lia|].
  change (BB44_rules.g (S k) m) with (Nat.iter (2 * m + 2) (BB44_rules.g k) 0%nat).
  replace (2 * m + 2) with (S (2 * m + 1)) by lia. rewrite Nat.iter_succ. apply IH.
Qed.

Lemma knuth_k_4_gt_local : forall j, knuth j 2 4 >= j + 6.
Proof.
  induction j as [|j IH].
  - simpl. lia.
  - destruct j as [|j'].
    + simpl. lia.
    + rewrite (knuth_S (S j') 2 3), (knuth_S (S j') 2 2), knuth_2.
      pose proof (knuth_ge_2b (S j') (knuth (S j') 2 4)) as H2. lia.
Qed.

Lemma k3 : forall n, knuth (S n) 2 3 = knuth n 2 4.
Proof. intros n. rewrite (knuth_S n 2 2), knuth_2. reflexivity. Qed.

Lemma k4 : forall n, knuth (S n) 2 4 = knuth n 2 (knuth n 2 4).
Proof. intros n. rewrite (knuth_S n 2 3), k3. reflexivity. Qed.

Lemma lvl4 : forall L, knuth L 2 (knuth L 2 (knuth L 2 4)) <= knuth (S (S (S (S L)))) 2 3.
Proof.
  intros L. rewrite k3, k4, k4.
  assert (H1 : knuth L 2 4 <= knuth (S L) 2 4) by (apply knuth_mono_k; lia).
  assert (H2 : knuth L 2 (knuth L 2 4) <= knuth (S L) 2 (knuth (S L) 2 4)).
  { eapply Nat.le_trans; [apply knuth_mono_b; exact H1|]. apply knuth_mono_k; [lia|].
    pose proof (knuth_ge_2b L 4). lia. }
  assert (H3 : knuth L 2 (knuth L 2 (knuth L 2 4)) <= knuth (S (S L)) 2 (knuth (S L) 2 (knuth (S L) 2 4))).
  { eapply Nat.le_trans; [apply knuth_mono_b; exact H2|]. apply knuth_mono_k; [lia|].
    pose proof (knuth_ge_2b (S L) (knuth (S L) 2 4)). pose proof (knuth_ge_2b (S L) 4). lia. }
  exact H3.
Qed.

Theorem sigma_B_closed :
  2 * BB44B_run.dB + 4 = knuth (S (2 * BB44B_run.cB + 1)) 2 3 /\
  2 * BB44B_run.cB + 4 = knuth 1 2 (2 * BB44B_run.bB + 4) /\
  2 * BB44B_run.bB + 4 = knuth 3 2 (2 * BB44B_run.a6 + 4) /\
  2 * BB44B_run.a6 + 4 = knuth 4 2 (2 * BB44B_run.a5 + 4).
Proof.
  split; [exact (g_iter_closed_gen _ 1 _ BB44B_run.d_eq)|].
  split; [rewrite (g_iter_closed_gen 1 _ _ BB44B_run.c_eq); f_equal; lia|].
  split; [rewrite (g_iter_closed_gen 3 _ _ BB44B_run.b_eq); f_equal; lia|].
  rewrite BB44B_run.a6_eq. change (Nat.iter 1 (BB44_rules.g 5) BB44B_run.a5) with (BB44_rules.g (S 4) BB44B_run.a5).
  apply g_closed.
Qed.

Theorem BB44B_beats_A : BB44A_run.sigma < BB44B_run.sigma.
Proof.
  destruct sigma_B_closed as (Hd & Hc & Hb & Ha6).
  destruct BB44A_cmp.sigma_A_closed as [HA3 HA1].
  pose proof (g_iter_closed_gen (2 * BB44A_run.M1) 3 BB44A_run.M2 BB44A_run.M2_eq) as HA2.
  replace (3 + 2) with 5 in HA2 by reflexivity.
  unfold BB44A_run.sigma, BB44B_run.sigma.
  pose proof (knuth_ge_2b 4 6) as H46.
  assert (EL : exists L', 2 * BB44A_run.M1 = S L') by (exists (2 * BB44A_run.M1 - 1); lia).
  destruct EL as [L' EL]. rewrite EL in *.
  (* a6 >= M1 *)
  assert (H5 : 1 <= BB44B_run.a5).
  { rewrite BB44B_run.a5_eq. change (Nat.iter 1 (BB44_rules.g 4) BB44B_run.a4) with (BB44_rules.g 4 BB44B_run.a4).
    apply g_pos. }
  pose proof (knuth_mono_b 4 6 (2 * BB44B_run.a5 + 4) ltac:(lia)) as H6.
  pose proof (knuth_ge_2b 3 (2 * BB44B_run.a6 + 4)) as Hb2.
  pose proof (knuth_ge_2b 1 (2 * BB44B_run.bB + 4)) as Hc2.
  (* the level of 44-B's last B_rule is far above that of 44-A, plus 4 *)
  assert (HLc : S (S (S (S (S L')))) <= S (2 * BB44B_run.cB + 1)) by lia.
  pose proof (knuth_mono_k _ _ 3 HLc ltac:(lia)) as Hk.
  pose proof (lvl4 (S L')) as Hl4.
  pose proof (knuth_ge_2b (S L') 4) as Hg4.
  pose proof (knuth_mono_b (S L') 6 (knuth (S L') 2 4) ltac:(lia)) as Hm6.
  pose proof (knuth_strict_b L' 5) as Hs5.
  pose proof (knuth_mono_b (S L') (2 * BB44A_run.M2 + 5) (knuth (S L') 2 (knuth (S L') 2 4)) ltac:(lia)) as Hm.
  lia.
Qed.

Corollary BB44B_beats_C : BB44_run.sigma < BB44B_run.sigma.
Proof. pose proof BB44A_cmp.BB44A_beats_C. pose proof BB44B_beats_A. lia. Qed.

Corollary BB44B_beats_official : knuth 509 2 3 + 510 < BB44B_run.sigma.
Proof. pose proof BB44A_cmp.BB44A_beats_official. pose proof BB44B_beats_A. lia. Qed.

Definition f_omega (n : nat) : nat := knuth (S n) 2 (n + 3).

Theorem sigma_B_f_omega : f_omega (knuth 5 2 3) < BB44B_run.sigma.
Proof.
  destruct sigma_B_closed as (Hd & Hc & Hb & Ha6).
  unfold f_omega, BB44B_run.sigma.
  rewrite (k3 4).
  assert (H5 : 1 <= BB44B_run.a5).
  { rewrite BB44B_run.a5_eq. change (Nat.iter 1 (BB44_rules.g 4) BB44B_run.a4) with (BB44_rules.g 4 BB44B_run.a4).
    apply g_pos. }
  pose proof (knuth_mono_b 4 4 (2 * BB44B_run.a5 + 4) ltac:(lia)) as H6.
  pose proof (knuth_ge_2b 3 (2 * BB44B_run.a6 + 4)) as Hb2.
  pose proof (knuth_ge_2b 1 (2 * BB44B_run.bB + 4)) as Hc2.
  pose proof (knuth_ge_2b 4 4) as HN.
  set (N := knuth 4 2 4) in *.
  assert (HLc : S (S (S (S (S N)))) <= S (2 * BB44B_run.cB + 1)) by lia.
  pose proof (knuth_mono_k _ _ 3 HLc ltac:(lia)) as Hk.
  pose proof (lvl4 (S N)) as Hl4.
  pose proof (knuth_k_4_gt_local (S N)) as Hg.
  pose proof (knuth_ge_2b (S N) (knuth (S N) 2 4)) as Hg2.
  pose proof (knuth_mono_b (S N) (N + 3) (knuth (S N) 2 (knuth (S N) 2 4)) ltac:(lia)) as Hm.
  lia.
Qed.

Print Assumptions sigma_B_closed.
Print Assumptions BB44B_beats_A.
Print Assumptions BB44B_beats_C.
Print Assumptions BB44B_beats_official.
Print Assumptions sigma_B_f_omega.
