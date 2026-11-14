(** * FGH_BB44: the BB(4,4) machines 44-B (the record), 44-A and 44-C in the standard fast-growing hierarchy.

    Files (logical root Local): argon_scout/M44 BB44, Individual44, BB44_rules, BB44_run, BB44_bound (44-C, unchanged; the
    same files as published in busy-beaver BB44/verify_44c); claims_coq BB44A_rules, BB44A_run, BB44A_cmp, BB44B_rules,
    BB44B_run, BB44B_cmp.  Standard FGH: published Ord.v (root BB8); KnuthFGH.v (new library).

      bb44B_fgh : f_w(f_2(f_4(f_5(f_4(f_3(64)))))) < sigma(44-B) < f_w(f_2(f_4(f_5(f_4(f_3(256))))))
      bb44A_fgh : f_w(2M1+1) < sigma(44-A) < f_w(2M1+2) <= f_w(f_5(4)),   2 M1 + 4 = 2 ^4 6
      bb44C_fgh : f_w(2^16-4) < sigma(44-C) < f_w(2^16-3)                  (65532 and 65533)

    with f_k = FGH (ofin k), f_w = FGH omega.  44-B's chain (BB44B_run, BB44B_cmp.sigma_B_closed, BB44_bound.g_closed):
    a3 = 126, 2a4+4 = 2^^256, 2a5+4 = 2^^^(2a4+4), 2a6+4 = 2^^^^(2a5+4), 2bB+4 = 2^^^(2a6+4), 2cB+4 = 2^(2bB+4),
    2dB+4 = 2^(2cB+2) 3, sigma = 2cB + 2dB + 9.  chain44 proves the window for these equations with variables. *)

From BB8 Require Import Ord KnuthFGH.
From Local Require BB44_rules BB44_run BB44_bound BB44A_run BB44A_cmp BB44B_run BB44B_cmp.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".

Lemma iter_ext_nat : forall (f h : nat -> nat) n x, (forall y, f y = h y) -> Nat.iter n f x = Nat.iter n h x.
Proof. intros f h n x H. induction n as [|n IH]; [reflexivity|]. rewrite !Nat.iter_succ, IH. apply H. Qed.

Lemma knuth_same : forall n a b, Local.BB44_bound.knuth n a b = kn n a b.
Proof.
  induction n as [|n IH]; intros a b; [reflexivity|].
  change (Local.BB44_bound.knuth (S n) a b) with (Nat.iter b (Local.BB44_bound.knuth n a) 1).
  change (kn (S n) a b) with (Nat.iter b (kn n a) 1).
  apply iter_ext_nat. intro y. apply IH.
Qed.

(** ** 44-B, for variables *)

Lemma chain44 : forall W V U T c d,
  W = kn 2 2 256 -> V = kn 3 2 W -> U = kn 4 2 V -> T = kn 3 2 U ->
  2 * c + 4 = kn 1 2 T -> 2 * d + 4 = kn (S (2 * c + 1)) 2 3 ->
  FGH omega (fin_fgh 2 (fin_fgh 4 (fin_fgh 5 (fin_fgh 4 (fin_fgh 3 64))))) < 2 * c + 2 * d + 9 /\
  2 * c + 2 * d + 9 < FGH omega (fin_fgh 2 (fin_fgh 4 (fin_fgh 5 (fin_fgh 4 (fin_fgh 3 256))))).
Proof.
  intros W V U T c d HW HV HU HT Hc Hd.
  assert (Hs : 2 * c + 2 * d + 9 = kn (S (2 * c + 1)) 2 3 + S (2 * c + 1) + 3) by lia.
  rewrite Hs.
  (* basic sizes *)
  pose proof (ge_2b 2 256) as GW. pose proof (ge_2b 3 W) as GV. pose proof (ge_2b 4 V) as GU.
  pose proof (ge_2b 3 U) as GT.
  (* the lower chain *)
  set (y1 := fin_fgh 3 64).
  set (y2 := fin_fgh 4 y1).
  set (y3 := fin_fgh 5 y2).
  set (y4 := fin_fgh 4 y3).
  set (y5 := fin_fgh 2 y4).
  assert (g1 : 64 <= y1) by apply fin_ge.
  assert (g2 : y1 <= y2) by apply fin_ge.
  assert (g3 : y2 <= y3) by apply fin_ge.
  assert (g4 : y3 <= y4) by apply fin_ge.
  assert (g5 : y4 <= y5) by apply fin_ge.
  assert (h1 : y1 <= kn 2 2 192) by (apply (fin_upper 2 64); lia).
  pose proof (quad 2 192 ltac:(lia)) as q1. replace (192 + 2) with 194 in q1 by reflexivity.
  assert (h2 : y2 <= kn 3 2 (kn 2 2 194)).
  { eapply Nat.le_trans; [apply (fin_upper 3 y1); lia|]. apply mono_b. lia. }
  pose proof (quad 3 (kn 2 2 194) ltac:(lia)) as q2.
  assert (h3 : y3 <= kn 4 2 (kn 3 2 (kn 2 2 194 + 2))).
  { eapply Nat.le_trans; [apply (fin_upper 4 y2); lia|]. apply mono_b. lia. }
  pose proof (quad 4 (kn 3 2 (kn 2 2 194 + 2)) ltac:(lia)) as q3.
  assert (h4 : y4 <= kn 3 2 (kn 4 2 (kn 3 2 (kn 2 2 194 + 2) + 2))).
  { eapply Nat.le_trans; [apply (fin_upper 3 y3); lia|]. apply mono_b. lia. }
  assert (h5 : y5 <= kn 1 2 (3 * y4)) by (apply (fin_upper 1 y4); lia).
  (* W >= A1 + 4, V >= Z + 2, U >= X + 2, T >= 4 y4 *)
  assert (W1 : kn 2 2 194 + 4 <= W).
  { pose proof (quad 2 194 ltac:(lia)) as Q. replace (194 + 2) with 196 in Q by reflexivity.
    pose proof (mono_b 2 196 256 ltac:(lia)). pose proof (ge_2b 2 194). lia. }
  assert (V1 : kn 3 2 (kn 2 2 194 + 2) + 4 <= V).
  { pose proof (quad 3 (kn 2 2 194 + 2) ltac:(lia)). pose proof (mono_b 3 (kn 2 2 194 + 2 + 2) W ltac:(lia)).
    pose proof (kn_pos 2 (kn 2 2 194 + 2)). lia. }
  assert (U1 : kn 4 2 (kn 3 2 (kn 2 2 194 + 2) + 2) + 2 <= U).
  { pose proof (quad 4 (kn 3 2 (kn 2 2 194 + 2) + 2) ltac:(lia)).
    pose proof (mono_b 4 (kn 3 2 (kn 2 2 194 + 2) + 2 + 2) V ltac:(lia)).
    pose proof (kn_pos 3 (kn 3 2 (kn 2 2 194 + 2) + 2)). lia. }
  assert (T1 : 4 * y4 <= T).
  { pose proof (quad 3 (kn 4 2 (kn 3 2 (kn 2 2 194 + 2) + 2)) ltac:(lia)).
    pose proof (mono_b 3 (kn 4 2 (kn 3 2 (kn 2 2 194 + 2) + 2) + 2) U ltac:(lia)). lia. }
  rewrite kn_1_pow in Hc, h5.
  assert (P1 : 2 ^ (3 * y4) <= 2 ^ (T - 2)) by (apply Nat.pow_le_mono_r; lia).
  assert (P2 : 2 ^ T = 4 * 2 ^ (T - 2)).
  { destruct T as [|[|T']]; [lia | lia |]. rewrite !Nat.pow_succ_r'. replace (S (S T') - 2) with T' by lia. lia. }
  pose proof (Nat.pow_gt_lin_r 2 (T - 2) ltac:(lia)) as P3.
  (* the upper chain *)
  pose proof (fin_lower 2 256 ltac:(lia)) as u1.
  pose proof (fin_lower 3 W ltac:(lia)) as u2.
  pose proof (fin_mono 4 W (fin_fgh 3 256) ltac:(lia)) as u2'.
  pose proof (fin_lower 4 V ltac:(lia)) as u3.
  pose proof (fin_mono 5 V (fin_fgh 4 (fin_fgh 3 256)) ltac:(lia)) as u3'.
  pose proof (fin_lower 3 U ltac:(lia)) as u4.
  pose proof (fin_mono 4 U (fin_fgh 5 (fin_fgh 4 (fin_fgh 3 256))) ltac:(lia)) as u4'.
  pose proof (fin_lower 1 T ltac:(lia)) as u5. rewrite kn_1_pow in u5.
  pose proof (fin_mono 2 T (fin_fgh 4 (fin_fgh 5 (fin_fgh 4 (fin_fgh 3 256)))) ltac:(lia)) as u5'.
  apply window_kn3; lia.
Qed.

Theorem bb44B_fgh :
  FGH omega (FGH (ofin 2) (FGH (ofin 4) (FGH (ofin 5) (FGH (ofin 4) (FGH (ofin 3) 64))))) < BB44B_run.sigma /\
  BB44B_run.sigma < FGH omega (FGH (ofin 2) (FGH (ofin 4) (FGH (ofin 5) (FGH (ofin 4) (FGH (ofin 3) 256))))).
Proof.
  rewrite !FGH_fin.
  destruct BB44B_cmp.sigma_B_closed as (Hd & Hc & Hb & Ha6).
  assert (Ea3 : BB44B_run.a3 = 126) by (rewrite BB44B_run.a3_eq, BB44B_run.a2_eq; reflexivity).
  assert (Ha4 : 2 * BB44B_run.a4 + 4 = Local.BB44_bound.knuth 2 2 256).
  { rewrite BB44B_run.a4_eq. change (Nat.iter 1 (BB44_rules.g 3) BB44B_run.a3) with (BB44_rules.g (S 2) BB44B_run.a3).
    rewrite Local.BB44_bound.g_closed, Ea3. reflexivity. }
  assert (Ha5 : 2 * BB44B_run.a5 + 4 = Local.BB44_bound.knuth 3 2 (2 * BB44B_run.a4 + 4)).
  { rewrite BB44B_run.a5_eq. change (Nat.iter 1 (BB44_rules.g 4) BB44B_run.a4) with (BB44_rules.g (S 3) BB44B_run.a4).
    apply Local.BB44_bound.g_closed. }
  rewrite knuth_same in Hd, Hc, Hb, Ha6, Ha4, Ha5.
  unfold BB44B_run.sigma.
  exact (chain44 _ _ _ _ _ _ Ha4 Ha5 Ha6 Hb Hc Hd).
Qed.

(** ** 44-A *)

Theorem bb44A_fgh :
  FGH omega (2 * BB44A_run.M1 + 1) < BB44A_run.sigma /\ BB44A_run.sigma < FGH omega (2 * BB44A_run.M1 + 2) /\
  FGH omega (2 * BB44A_run.M1 + 2) <= FGH omega (FGH (ofin 5) 4) /\ 2 * BB44A_run.M1 + 4 = kn 4 2 6.
Proof.
  destruct BB44A_cmp.sigma_A_closed as [H3 H1].
  pose proof (Local.BB44_bound.g_iter_closed_gen (2 * BB44A_run.M1) 3 BB44A_run.M2 BB44A_run.M2_eq) as H2.
  replace (3 + 2) with 5 in H2 by reflexivity.
  rewrite knuth_same in H1, H2, H3.
  assert (E : 2 * BB44A_run.M2 + 5 = kn (2 * BB44A_run.M1) 2 5 + 1) by lia. rewrite E in H3.
  pose proof (ge_2b 4 6) as G.
  pose proof (window_knA (2 * BB44A_run.M1) ltac:(lia)) as [W1 W2].
  unfold BB44A_run.sigma.
  replace (S (2 * BB44A_run.M1)) with (2 * BB44A_run.M1 + 1) in W1 by lia.
  replace (S (S (2 * BB44A_run.M1))) with (2 * BB44A_run.M1 + 2) in W2 by lia.
  split; [lia|]. split; [lia|]. split; [| exact H1].
  rewrite FGH_fin. apply fw_mono.
  pose proof (fin_lower2 3 4 ltac:(lia)) as F. replace (4 + 2) with 6 in F by reflexivity. lia.
Qed.

(** ** 44-C *)

Theorem bb44C_fgh : FGH omega (2 ^ 16 - 4) < BB44_run.sigma /\ BB44_run.sigma < FGH omega (2 ^ 16 - 3).
Proof.
  rewrite Local.BB44_bound.sigma_exact_closed_form, knuth_same.
  assert (H5 : 8 <= 2 ^ 16) by (apply Nat.le_trans with (m := 2 ^ 3); [simpl; lia | apply Nat.pow_le_mono_r; lia]).
  pose proof (window_kn6 (2 ^ 16 - 4) ltac:(lia)) as [W1 W2].
  replace (S (2 ^ 16 - 4)) with (2 ^ 16 - 3) in W2 by lia.
  split; assumption.
Qed.

Print Assumptions bb44B_fgh.
Print Assumptions bb44A_fgh.
Print Assumptions bb44C_fgh.
