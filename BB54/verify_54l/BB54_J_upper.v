(** * BB54_J_upper: a Coq UPPER bound for the sigma of the published BB(5,4) champion (Jacobzheng's machine
      1LD3LB---2RA_1LD3RB1LC2RA_3RB1LB3LC2RC_3RB---3LE3LD_------1LD1RZ),
    and the comparison with Argon's new BB(5,4) machine
      1RB3LC1LD2RA_2RC1RZ2LB2LB_1LD3RC1LE2RA_3RC0LB1LD3LD_3RC1LC3LE2RE.

    Published files used unchanged (busy-beaver BB54/verify, logical root TM54): BB54, Individual54, BB54_rules,
    BB54_start, BB54_run, BB54_score, BB54_dphase, BB54_halt, BB54_bound.  Argon's verified files (argon_scout/M54,
    logical root Local): BB54, Individual54, BB54_rules, BB54_run, BB54_bound.

    The published development proves (BB54_halt.bb54_halt_main) that the machine halts with
      sigma_final = 2 M1 + 2 M0 + 2 (X/2) + 5     nonzero cells,  X = g_5(g_4(0)),
      M0 = gchain (2X) 3 0,  M1 = gchain (2 M0) (X+2) 0,
    and its README states, on paper only, sigma < f_omega^2(2 ^4 2 ^3 4).  This file proves it:

      Theorem sigma_final_upper : sigma_final <= f_omega2 (knuth 4 2 (knuth 3 2 4)).

    with f_omega n = 2 ^(n+1) (n+3) (BB54_score.f_omega, Knuth arrows BB54_score.knuth).  Argon's
    Local.BB54_bound.sigma_beats_official_bb54 proves f_omega2 (knuth 4 2 (knuth 3 2 4)) < sigma for the new machine
    (his knuth / f_omega are the same definitions, text for text; bridged here by knuth_same), hence

      Theorem new_beats_jacobzheng : TM54.BB54_halt.sigma_final < Local.BB54_run.sigma.

    Both sigmas count the nonzero cells after the halting transition (the published final_cells /
    sigma_final; Argon's final_cells / sigma), the same convention.  No large number is evaluated: every bound
    is proved for variables (Section Bound) and instantiated with the sealed terms of the published files. *)

From TM54 Require Import BB54_rules BB54_score BB54_dphase BB54_halt BB54_bound.
From Local Require BB54_run BB54_bound.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(** ** Growth of Knuth arrows (proofs as in argon_scout/M54/BB54_bound.v, for the published [knuth]) *)

Lemma knuth_ge_2b : forall k b, knuth k 2 b >= 2 * b.
Proof.
  induction k as [|k IHk]; intros b.
  - simpl. lia.
  - induction b as [|b IHb].
    + simpl. lia.
    + destruct b as [|b'].
      * rewrite knuth_1. lia.
      * rewrite knuth_S.
        pose proof (IHk (knuth (S k) 2 (S b'))) as H1.
        lia.
Qed.

Lemma knuth_pos : forall k b, knuth (S k) 2 b >= 1.
Proof.
  intros k [|b].
  - simpl. lia.
  - pose proof (knuth_ge_2b (S k) (S b)). lia.
Qed.

Lemma knuth_strict_b : forall k b, knuth (S k) 2 (S b) > knuth (S k) 2 b.
Proof.
  intros k b. rewrite knuth_S.
  pose proof (knuth_ge_2b k (knuth (S k) 2 b)). pose proof (knuth_pos k b). lia.
Qed.

Lemma knuth_mono_b : forall k b1 b2, b1 <= b2 -> knuth k 2 b1 <= knuth k 2 b2.
Proof.
  intros [|k] b1 b2 Hle.
  - simpl. lia.
  - induction b2 as [|b2 IH].
    + assert (b1 = 0) by lia. subst. lia.
    + destruct (Nat.eq_dec b1 (S b2)) as [Heq | Hne].
      * subst. lia.
      * assert (b1 <= b2) by lia. pose proof (IH H). pose proof (knuth_strict_b k b2). lia.
Qed.

Lemma knuth_step_k : forall k b, b >= 1 -> knuth k 2 b <= knuth (S k) 2 b.
Proof.
  intros k b Hb.
  destruct b as [|[|b']].
  - lia.
  - rewrite !knuth_1. lia.
  - rewrite (knuth_S k 2 (S b')). apply knuth_mono_b.
    destruct b' as [|b''].
    + rewrite knuth_1. lia.
    + pose proof (knuth_ge_2b (S k) (S (S b''))). lia.
Qed.

Lemma knuth_mono_k : forall k1 k2 b, k1 <= k2 -> b >= 1 -> knuth k1 2 b <= knuth k2 2 b.
Proof.
  intros k1 k2 b Hk Hb. induction k2 as [|k2 IH].
  - assert (k1 = 0) by lia. subst. lia.
  - destruct (Nat.eq_dec k1 (S k2)) as [Heq | Hne].
    + subst. lia.
    + assert (k1 <= k2) by lia. pose proof (IH H). pose proof (knuth_step_k k2 b Hb). lia.
Qed.

Lemma knuth_k_4_gt : forall j, j >= 1 -> knuth j 2 4 >= j + 6.
Proof.
  induction j as [|j IH]; intros Hj.
  - lia.
  - destruct j as [|j'].
    + simpl. lia.
    + rewrite (knuth_S (S j') 2 3), (knuth_S (S j') 2 2), knuth_2.
      assert (H1 : knuth (S j') 2 4 >= S j' + 6) by (apply IH; lia).
      pose proof (knuth_ge_2b (S j') (knuth (S j') 2 4)) as H2. lia.
Qed.

Lemma knuth_mono : forall k1 k2 b1 b2, k1 <= k2 -> 1 <= b1 -> b1 <= b2 -> knuth k1 2 b1 <= knuth k2 2 b2.
Proof.
  intros. eapply Nat.le_trans; [apply knuth_mono_k; eassumption | apply knuth_mono_b; assumption].
Qed.

Lemma iter_knuth_mono : forall L n x y, x <= y -> Nat.iter n (knuth L 2) x <= Nat.iter n (knuth L 2) y.
Proof.
  intros L n. induction n as [|n IH]; intros x y H; [exact H|].
  cbn [Nat.iter]. apply knuth_mono_b. apply IH. exact H.
Qed.

(** iter c (2 ^L .) 4 = 2 ^(L+1) (c + 2) *)
Lemma iter_knuth_4 : forall L c, Nat.iter c (knuth L 2) 4 = knuth (S L) 2 (c + 2).
Proof.
  intros L c. rewrite knuth_S0, iter_add, iter2_knuth. reflexivity.
Qed.

(** ** The g hierarchy along a chain *)

Lemma g_pos : forall k m, 1 <= g k m.
Proof.
  induction k as [|k IH]; intros m; [cbn [g]; lia|].
  cbn [g]. replace (2 * m + 2) with (S (2 * m + 1)) by lia. cbn [Nat.iter]. apply IH.
Qed.

Lemma gchain_pos : forall T j m, 1 <= gchain j T m.
Proof. induction T as [|T IH]; intros j m; cbn [gchain]; [apply g_pos | apply IH]. Qed.

(** Upper bound: every g_i of the chain is at a level <= L (i <= L + 1, i >= 1). *)
Lemma gchain_upper : forall T j m L, 1 <= j -> j + T <= S L ->
  2 * gchain j T m + 4 <= Nat.iter (S T) (knuth L 2) (2 * m + 4).
Proof.
  induction T as [|T IH]; intros j m L Hj HL.
  - cbn [gchain Nat.iter]. destruct j as [|j]; [lia|].
    rewrite g_closed. apply knuth_mono_k; lia.
  - cbn [gchain]. eapply Nat.le_trans; [apply (IH (S j) (g j m) L); lia|].
    assert (E : Nat.iter (S (S T)) (knuth L 2) (2 * m + 4) = Nat.iter (S T) (knuth L 2) (knuth L 2 (2 * m + 4)))
      by apply Nat.iter_succ_r.
    rewrite E. apply iter_knuth_mono.
    destruct j as [|j]; [lia|]. rewrite g_closed. apply knuth_mono_k; lia.
Qed.

(** Lower bound: the last g of the chain has level j + T - 1. *)
Lemma gchain_lower : forall T j m, 1 <= j -> knuth (j + T - 1) 2 4 <= 2 * gchain j T m + 4.
Proof.
  induction T as [|T IH]; intros j m Hj.
  - cbn [gchain]. destruct j as [|j]; [lia|]. rewrite g_closed.
    replace (S j + 0 - 1) with j by lia. apply knuth_mono_b. lia.
  - cbn [gchain]. replace (j + S T - 1) with (S j + T - 1) by lia. apply IH. lia.
Qed.

(** ** The bound, for variables (named Xv, Mv0, Mv1: X, M0, M1 are notations of BB54_halt) *)

Section Bound.
Variables Xv Mv0 Mv1 : nat.
Hypothesis HX : 2 <= Xv.
Hypothesis HM0 : Mv0 = gchain (2 * Xv) 3 0.
Hypothesis HM1 : Mv1 = gchain (2 * Mv0) (S (Xv + 1)) 0.

Lemma M0_upper : 2 * Mv0 + 4 <= knuth (2 * Xv + 3) 2 6.
Proof.
  pose proof (gchain_upper 3 (2 * Xv) 0 (2 * Xv + 2) ltac:(lia) ltac:(lia)) as H.
  change (2 * 0 + 4) with 4 in H. rewrite iter_knuth_4 in H.
  replace (S (2 * Xv + 2)) with (2 * Xv + 3) in H by lia. change (4 + 2) with 6 in H.
  rewrite HM0. exact H.
Qed.

Lemma M0_lower : 2 * Xv + 8 <= 2 * Mv0 + 4.
Proof.
  rewrite HM0. eapply Nat.le_trans; [| apply gchain_lower; lia].
  pose proof (knuth_k_4_gt (2 * Xv + 3 - 1) ltac:(lia)). lia.
Qed.

Lemma M1_upper : 2 * Mv1 + 4 <= knuth (2 * Mv0 + Xv + 2) 2 (Xv + 5).
Proof.
  pose proof M0_lower as H0.
  pose proof (gchain_upper (S (Xv + 1)) (2 * Mv0) 0 (2 * Mv0 + Xv + 1) ltac:(lia) ltac:(lia)) as H.
  change (2 * 0 + 4) with 4 in H. rewrite iter_knuth_4 in H.
  replace (S (2 * Mv0 + Xv + 1)) with (2 * Mv0 + Xv + 2) in H by lia.
  replace (S (S (Xv + 1)) + 2) with (Xv + 5) in H by lia.
  rewrite HM1. exact H.
Qed.

Theorem bound_gen : 2 * Mv1 + 2 * Mv0 + 2 * (Xv / 2) + 5 <= f_omega2 (2 * Xv + 4).
Proof.
  pose proof M0_upper as HA. pose proof M0_lower as HL. pose proof M1_upper as HB.
  pose proof (Nat.Div0.mul_div_le Xv 2) as Hdiv.
  assert (HA1 : 2 * Xv + 9 <= knuth (2 * Xv + 3) 2 6).
  { pose proof (knuth_k_4_gt (2 * Xv + 3) ltac:(lia)).
    pose proof (knuth_mono_b (2 * Xv + 3) 4 6 ltac:(lia)). lia. }
  assert (E7 : knuth (2 * Xv + 3) 2 7 = knuth (2 * Xv + 2) 2 (knuth (2 * Xv + 3) 2 6)).
  { replace (2 * Xv + 3) with (S (2 * Xv + 2)) by lia. apply knuth_S. }
  pose proof (knuth_ge_2b (2 * Xv + 2) (knuth (2 * Xv + 3) 2 6)) as H7.
  assert (HF1 : 2 * knuth (2 * Xv + 3) 2 6 <= f_omega (2 * Xv + 4)).
  { unfold f_omega.
    pose proof (knuth_mono (2 * Xv + 3) (S (2 * Xv + 4)) 7 (2 * Xv + 4 + 3) ltac:(lia) ltac:(lia) ltac:(lia)).
    lia. }
  assert (HB1 : knuth (2 * Xv + 3) 2 6 + Xv + 5 <= knuth (2 * Mv0 + Xv + 2) 2 (Xv + 5)).
  { pose proof (knuth_mono (2 * Xv + 3) (2 * Mv0 + Xv + 2) 7 (Xv + 5) ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
  unfold f_omega2. revert HF1. generalize (f_omega (2 * Xv + 4)) as F1. intros F1 HF1.
  unfold f_omega.
  assert (HK : knuth (S (2 * Mv0 + Xv + 2)) 2 (Xv + 6) <= knuth (S F1) 2 (F1 + 3))
    by (apply knuth_mono; lia).
  assert (E6 : knuth (S (2 * Mv0 + Xv + 2)) 2 (Xv + 6)
             = knuth (2 * Mv0 + Xv + 2) 2 (knuth (S (2 * Mv0 + Xv + 2)) 2 (Xv + 5)))
    by (replace (Xv + 6) with (S (Xv + 5)) by lia; apply knuth_S).
  pose proof (knuth_ge_2b (2 * Mv0 + Xv + 2) (knuth (S (2 * Mv0 + Xv + 2)) 2 (Xv + 5))).
  pose proof (knuth_step_k (2 * Mv0 + Xv + 2) (Xv + 5) ltac:(lia)).
  lia.
Qed.

End Bound.

(** ** Instantiation with the published run *)

Lemma X_ge_2 : 2 <= X.
Proof.
  pose proof X_inner as E.
  pose proof (knuth_ge_2b 4 (knuth 3 2 4)) as H1. pose proof (knuth_ge_2b 3 4) as H2. lia.
Qed.

(** The published machine's sigma (BB54_halt.sigma_final = length final_cells, bb54_halt_main) is at most the
    README's paper upper bound f_omega^2(2 ^4 2 ^3 4). *)
Theorem sigma_final_upper : sigma_final <= f_omega2 (knuth 4 2 (knuth 3 2 4)).
Proof.
  unfold sigma_final.
  pose proof (bound_gen X M0s M1s X_ge_2 M0s_eq M1s_eq) as H.
  rewrite X_inner in H. exact H.
Qed.

(** ** Comparison with Argon's machine *)

Lemma iter_ext_nat : forall (f h : nat -> nat) n x, (forall y, f y = h y) -> Nat.iter n f x = Nat.iter n h x.
Proof.
  intros f h n x H. induction n as [|n IH]; [reflexivity|]. rewrite !Nat.iter_succ, IH. apply H.
Qed.

Lemma knuth_same : forall n a b, Local.BB54_bound.knuth n a b = knuth n a b.
Proof.
  induction n as [|n IH]; intros a b; [reflexivity|].
  change (Local.BB54_bound.knuth (S n) a b) with (Nat.iter b (Local.BB54_bound.knuth n a) 1).
  change (knuth (S n) a b) with (Nat.iter b (knuth n a) 1).
  apply iter_ext_nat. intro y. apply IH.
Qed.

Lemma f_omega2_same : forall n, Local.BB54_bound.f_omega2 n = f_omega2 n.
Proof.
  intros n.
  change (Local.BB54_bound.f_omega2 n)
    with (Local.BB54_bound.knuth (S (Local.BB54_bound.knuth (S n) 2 (n + 3))) 2
                                 (Local.BB54_bound.knuth (S n) 2 (n + 3) + 3)).
  change (f_omega2 n) with (knuth (S (knuth (S n) 2 (n + 3))) 2 (knuth (S n) 2 (n + 3) + 3)).
  repeat rewrite knuth_same. reflexivity.
Qed.

Lemma nest_same : forall x, Local.BB54_bound.knuth 4 2 (Local.BB54_bound.knuth 3 2 x) = knuth 4 2 (knuth 3 2 x).
Proof. intros x. rewrite (knuth_same 3 2 x). rewrite (knuth_same 4 2 (knuth 3 2 x)). reflexivity. Qed.

(** sigma(Jacobzheng) < sigma(new): the new machine beats the published BB(5,4) champion. *)
Theorem new_beats_jacobzheng : sigma_final < Local.BB54_run.sigma.
Proof.
  pose proof sigma_final_upper as H1.
  pose proof Local.BB54_bound.sigma_beats_official_bb54 as H2.
  rewrite f_omega2_same, (nest_same 4) in H2. lia.
Qed.

Print Assumptions sigma_final_upper.
Print Assumptions new_beats_jacobzheng.
