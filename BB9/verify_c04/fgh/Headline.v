(** * Headline.v : C04's score in FGH terms only, without Bx.

      Bx_fw    : f_omega 12 < 12 Bx + 26  /\  12 Bx + 27 <= f_omega 13
      c04_fgh3 : forall c N, c0 -->* c -> halted tm c -> ones c N ->
                 f_omega (f_omega (f_omega 12)) < N < f_omega (f_omega (f_omega 13)).
    (12, 13) is the tightest such integer pair: f_omega 13 >= arrow 12 2 13 > 12 Bx + 26 (Bx_fw_tight), so a = 13 fails.
    Here 2 Bx + 4 = arrow 12 2 4 = arrow 13 2 3 (Abs.Bx_closed, FArith.Bx_knuth).
    Proofs:  f_omega 12 = f 12 12 <= U 10 12 <= U 10 (U 10 0) = Bx        (FArith.f_le_U2, U 10 0 >= 12)
             12 Bx + 27 <= 64 Bx <= U 10 (U 10 0 + 3) <= U 11 1 < f 13 6 <= f 13 13 = f_omega 13
             f_omega 13 >= arrow 12 2 13 >= arrow 12 2 5 = arrow 11 2 (2 Bx + 4) > 6 (2 Bx + 4)     (tightness) *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Set Default Goal Selector "!".
From Dev Require Import Base Abs Chain.
From K31 Require Import K31_Abs.
From Score Require Import Score.
From Fgh Require Import FArith EndU.
Local Open Scope nat_scope.
Opaque U arrow Bx f f_omega.

Lemma fomega12_le_Bx : f_omega 12 <= Bx.
Proof.
  pose proof (fomega_le_U2 10) as H1. pose proof (sc_U0_ge 10) as H2.
  pose proof (sc_U_mono 10 12 (U 10 0) ltac:(lia)) as H3. pose proof Bx_def as E. lia.
Qed.

Lemma Bx_le_fomega13 : 12 * Bx + 27 <= f_omega 13.
Proof.
  pose proof Bx_def as E. pose proof (sc_U_lin 10 (U 10 0)).
  pose proof (U64 10 (U 10 0)) as A1. pose proof (U_iter3 10) as A2.
  pose proof (U_lt_f 11 1) as A3. change (2 * 1 + 4) with 6 in A3.
  pose proof (f_mono 13 6 13 ltac:(lia)) as A4. pose proof (fomega_eq 13) as A5.
  lia.
Qed.

Theorem Bx_fw : f_omega 12 < 12 * Bx + 26 /\ 12 * Bx + 27 <= f_omega 13.
Proof. pose proof fomega12_le_Bx. pose proof Bx_le_fomega13. split; lia. Qed.

(** Tightness: f_omega 13 is far above 12 Bx + 26, so (13, 14) is not a valid pair. *)
Lemma arrow_mono_arg : forall k a b, 1 <= a -> a <= b -> arrow k 2 a <= arrow k 2 b.
Proof.
  induction k as [| k IH]; intros a b Ha Hab.
  - rewrite (arrow_0 2 a), (arrow_0 2 b). lia.
  - rewrite (arrow_S_iter k 2 a), (arrow_S_iter k 2 b).
    assert (Hg : forall z, 1 <= z -> z <= arrow k 2 z).
    { intros z Hz. destruct k as [| k'].
      - rewrite arrow_0. lia.
      - destruct (Nat.eq_dec z 1) as [-> | Hne]; [rewrite (arrow_one (S k')); lia |].
        pose proof (arrow_gt_arg (S k') z ltac:(lia) ltac:(lia)). lia. }
    assert (Hpos : forall m, 1 <= iter m (arrow k 2) 1).
    { induction m; cbn [iter]; [lia |]. pose proof (Hg _ IHm). lia. }
    induction Hab as [| b Hab IHb]; [lia |].
    change (iter (S b) (arrow k 2) 1) with (arrow k 2 (iter b (arrow k 2) 1)).
    pose proof (Hg _ (Hpos b)). lia.
Qed.

Lemma Bx_fw_tight : 12 * Bx + 26 < f_omega 13.
Proof. pose proof Bx_le_fomega13. lia. Qed.

Lemma arrow_lvl1 : forall j y, 1 <= y -> arrow 1 2 y <= arrow (S j) 2 y.
Proof.
  induction j; intros y Hy; [lia |].
  pose proof (IHj y Hy). rewrite (arrow_S_iter (S j) 2 y).
  assert (Hgen : forall z, 1 <= z -> arrow (S j) 2 z <= iter z (arrow (S j) 2) 1).
  { induction z as [| z IHz]; intros Hz; [lia |].
    destruct (Nat.eq_dec z 0) as [-> | Hz0].
    - cbn [iter]. lia.
    - change (iter (S z) (arrow (S j) 2) 1) with (arrow (S j) 2 (iter z (arrow (S j) 2) 1)).
      specialize (IHz ltac:(lia)).
      assert (Hgt : S z <= arrow (S j) 2 z).
      { destruct (Nat.eq_dec z 1) as [-> | Hne]; [rewrite (arrow_one (S j)); lia |].
        pose proof (arrow_gt_arg (S j) z ltac:(lia) ltac:(lia)). lia. }
      apply arrow_mono_arg; lia. }
  pose proof (Hgen y Hy). lia.
Qed.

(** How far a = 13 fails: 6 (2 Bx + 4) < arrow 12 2 13 <= f_omega 13. *)
Lemma Bx_fw_tight2 : 6 * (2 * Bx + 4) < arrow 12 2 13 /\ arrow 12 2 13 <= f_omega 13.
Proof.
  split.
  - pose proof (arrow_mono_arg 12 5 13 ltac:(lia) ltac:(lia)) as H1.
    pose proof (arrow_SS 11 2 4) as H2.
    assert (E2 : 2 * Bx + 4 = arrow 12 2 4).
    { rewrite Bx_closed, (arrow_SS 11 2 3), (arrow_SS 11 2 2), (arrow_two 12). reflexivity. }
    rewrite <- E2 in H2.
    pose proof Bx_ge6. set (X := 2 * Bx + 4) in *. assert (HX : 6 <= X) by (unfold X; lia). clearbody X.
    pose proof (arrow_lvl1 10 X ltac:(lia)) as H3. rewrite arrow_1_pow in H3.
    assert (H5 : 8 * X <= 2 ^ X).
    { assert (G : forall m, 8 * (m + 6) <= 2 ^ (m + 6)).
      { induction m; [simpl; lia |]. replace (S m + 6) with (S (m + 6)) by lia. rewrite Nat.pow_succ_r'. lia. }
      replace X with ((X - 6) + 6) by lia. apply G. }
    lia.
  - pose proof (arrow_le_f 12 13 ltac:(lia)) as H. rewrite fomega_eq. exact H.
Qed.

(** The headline: C04's score lies strictly between f_omega^3 12 and f_omega^3 13. *)
Print Assumptions Bx_fw.
Print Assumptions Bx_fw_tight2.

Theorem c04_fgh3 : forall c N, c0 -->* c -> halted tm c -> ones c N ->
  f_omega (f_omega (f_omega 12)) < N /\ N < f_omega (f_omega (f_omega 13)).
Proof.
  intros c N H1 H2 H3. destruct (c04_fgh_bracket c N H1 H2 H3) as [HL HU].
  destruct Bx_fw as [B1 B2].
  pose proof (fomega_ge 12) as G0.
  pose proof (fomega_mono (f_omega 12) (12 * Bx + 26) ltac:(lia) ltac:(lia)) as G1.
  pose proof (fomega_ge (f_omega 12)) as G2.
  pose proof (fomega_mono (f_omega (f_omega 12)) (f_omega (12 * Bx + 26)) ltac:(lia) G1) as G3.
  pose proof (fomega_mono (12 * Bx + 27) (f_omega 13) ltac:(lia) B2) as G4.
  pose proof (fomega_ge (12 * Bx + 27)) as G5.
  pose proof (fomega_mono (f_omega (12 * Bx + 27)) (f_omega (f_omega 13)) ltac:(lia) G4) as G6.
  split; lia.
Qed.
