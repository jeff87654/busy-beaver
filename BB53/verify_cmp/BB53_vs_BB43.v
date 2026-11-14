(** * BB53_vs_BB43: Argon's BB(5,3) machine 1RB1LC1RA_1LA2LC1RB_1LB1LD2LC_2RE2LD1RA_1RZ2RE1RB beats the
    published BB(4,3) champion 1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD (Kropitz) + 1, exact score against a
    proved upper bound.

    Published files used unchanged (busy-beaver BB43/verify, logical root TM43): BB43, Individual43, BB43_rules,
    BB43_run, BB43_score.  TM43.BB43_score.sigma_bounds proves, for the exact score sigma = 4 e4 + 18
    (TM43.BB43_run.sigma, bb43_main):   sigma <= 4 * P (P (P (2^96 + 6))) + 18,   P = 2 ^^^ = knuth 3 2.
    Argon's verified files (argon_scout/M53, logical root Local): BB53, Individual53, BB53_rules, BB53_run,
    BB53_bound.  Local.BB53_bound.sigma_exceeds_f_omega2: f_omega (f_omega 7) < sigma, f_omega n = knuth n 2 n.
    Both developments define knuth with the same text (bridged by knuth_same).

      Theorem BB53_beats_BB43 : TM43.BB43_run.sigma + 1 < Local.BB53_run.sigma.

    Both sigmas count the nonzero cells of the final tape after the halting transition (BB(4,3): C0 = 1RZ
    writes a 1, counted in 4 e4 + 18; BB(5,3): E0 = 1RZ, counted in Argon's final_cells). *)

From TM43 Require BB43_run BB43_score.
From Local Require BB53_run BB53_bound.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

Module L := Local.BB53_bound.

Lemma iter_ext_nat : forall (f h : nat -> nat) n x, (forall y, f y = h y) -> Nat.iter n f x = Nat.iter n h x.
Proof.
  intros f h n x H. induction n as [|n IH]; [reflexivity|]. rewrite !Nat.iter_succ, IH. apply H.
Qed.

Lemma knuth_same : forall n a b, L.knuth n a b = TM43.BB43_score.knuth n a b.
Proof.
  induction n as [|n IH]; intros a b; [reflexivity|].
  change (L.knuth (S n) a b) with (Nat.iter b (L.knuth n a) 1).
  change (TM43.BB43_score.knuth (S n) a b) with (Nat.iter b (TM43.BB43_score.knuth n a) 1).
  apply iter_ext_nat. intro y. apply IH.
Qed.

Lemma nest_same : forall x, TM43.BB43_score.knuth 3 2 (TM43.BB43_score.knuth 3 2 (TM43.BB43_score.knuth 3 2 x))
  = L.knuth 3 2 (L.knuth 3 2 (L.knuth 3 2 x)).
Proof.
  intros x. rewrite <- (knuth_same 3 2 x). rewrite <- (knuth_same 3 2 (L.knuth 3 2 x)).
  rewrite <- (knuth_same 3 2 (L.knuth 3 2 (L.knuth 3 2 x))). reflexivity.
Qed.

(** P(P(P(2^96 + 6))) <= 2 ^^^^ 7  (N2_96 = 2^96 is Argon's sealed constant; lia never sees 2^96) *)
Lemma tower43_le : L.knuth 3 2 (L.knuth 3 2 (L.knuth 3 2 (L.N2_96 + 6))) <= L.knuth 4 2 7.
Proof.
  pose proof L.N2_96_le_knuth3_5 as H0.
  assert (H6 : L.N2_96 + 6 <= L.knuth 3 2 6).
  { rewrite (L.knuth_S 2 2 5). pose proof (L.knuth_ge_2b 2 (L.knuth 3 2 5)).
    pose proof (L.knuth_ge_2b 3 5). lia. }
  assert (H43 : 6 <= L.knuth 4 2 3) by (rewrite L.knuth4_3_eq; pose proof (L.knuth_4_gt_k 3); lia).
  assert (H44 : L.N2_96 + 6 <= L.knuth 4 2 4).
  { rewrite (L.knuth_S 3 2 3). pose proof (L.knuth_mono_b 3 6 (L.knuth 4 2 3) H43). lia. }
  assert (H45 : L.knuth 3 2 (L.N2_96 + 6) <= L.knuth 4 2 5) by (rewrite (L.knuth_S 3 2 4); apply L.knuth_mono_b; exact H44).
  assert (H46 : L.knuth 3 2 (L.knuth 3 2 (L.N2_96 + 6)) <= L.knuth 4 2 6)
    by (rewrite (L.knuth_S 3 2 5); apply L.knuth_mono_b; exact H45).
  rewrite (L.knuth_S 3 2 6). apply L.knuth_mono_b. exact H46.
Qed.

Theorem BB53_beats_BB43 : TM43.BB43_run.sigma + 1 < Local.BB53_run.sigma.
Proof.
  pose proof (proj2 TM43.BB43_score.sigma_bounds) as H43. rewrite (nest_same (2 ^ 96 + 6)), <- L.N2_96_def in H43.
  pose proof tower43_le as HT.
  pose proof (proj2 L.sigma_exceeds_f_omega2) as H53.
  rewrite (L.f_omega_def (L.f_omega 7)) in H53.
  pose proof (L.f_omega_ge_2n 7) as H7.
  assert (H10 : L.knuth 4 2 10 <= L.knuth (L.f_omega 7) 2 (L.f_omega 7)).
  { eapply Nat.le_trans; [apply (L.knuth_mono_k 4 (L.f_omega 7) 10); lia|]. apply L.knuth_mono_b. lia. }
  assert (E10 : L.knuth 4 2 10 = L.knuth 3 2 (L.knuth 3 2 (L.knuth 3 2 (L.knuth 4 2 7)))).
  { rewrite (L.knuth_S 3 2 9), (L.knuth_S 3 2 8), (L.knuth_S 3 2 7). reflexivity. }
  pose proof (L.knuth_ge_2b 3 (L.knuth 4 2 7)) as G1.
  pose proof (L.knuth_ge_2b 3 (L.knuth 3 2 (L.knuth 4 2 7))) as G2.
  pose proof (L.knuth_ge_2b 3 (L.knuth 3 2 (L.knuth 3 2 (L.knuth 4 2 7)))) as G3.
  pose proof (L.knuth_ge_2b 4 7) as G0.
  assert (HA : TM43.BB43_run.sigma <= 4 * L.knuth 4 2 7 + 18) by lia.
  assert (HB : 8 * L.knuth 4 2 7 <= L.knuth 4 2 10) by (rewrite E10; lia).
  lia.
Qed.

Print Assumptions BB53_beats_BB43.
