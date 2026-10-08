(** * The BB(10) candidate beats the BB(10) champion: the two exact scores compared *)

(** Candidate: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_1RG1LD_0RI0RH_1RG1LF_1RE1RI_---1LC
      (BB10_lead_1RB0RA.v: halts; BB10_lead_bound.v: ones at the halt = 2 b2 + 2 (4 bf + 33) + 5, with
       bf = (F 26)^2 0, b2 = (F (4 bf + 33))^3 0, F 0 b = b + 2, F (k+1) b = (F k)^(b+2) 0).
    Champion (Racheline 2024): 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_0LF0LJ_1LH0LJ
      (BB10_champion_bound.v: ones at the halt = b2c + 3, head on a 0, halting transition 1RZ, so its standard
       score is b2c + 4; b1c = Tv 7 1 7, b2c = Tv (b1c/4) 1 7, Tv m j B = U (j+3m+2) (U (j+3m+2) (Tpre m j B))).

    Main results (no axioms):
      Theorem candidate_beats_champion :
        exists cc nc co no, c0 -[ champion tm ]->* cc /\ halted (champion tm) cc /\ champion ones cc nc /\
          c0 -->* co /\ halted tm co /\ ones co no /\ nc + 1 < no + 1.
      Theorem sigma_gt_f_omega2_25 :
        exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ f_omega (f_omega 25) < n + 1.
    Both machines halt by an undefined transition while reading a 0, so the standard scores are nc + 1 and no + 1.

    The argument:
      1. Domination: U j x <= F (j+1) (F (j+1) x) and X j <= (F (j+1))^(4j+2) 0 (Dom), by induction on j.
      2. Hence Tpre m 1 7 <= (F (3m+1))^(6m) 7 and Tv m 1 7 <= F (3m+5) (6m+6) (Tv_le).
      3. b1c = Tv 7 1 7 <= F 26 48 <= F 26 (F 26 0) = bf.
      4. b2c = Tv (b1c/4) 1 7 <= F (3m+5) (6m+6) <= F L (F L 0) <= F L (F L (F L 0)) = b2, with m = b1c/4 <= bf
         and L = 4 bf + 33 (so 3m+5 <= L and 6m+6 <= 4L <= F L 0). *)

From BB8 Require Import Individual102.
From BB8 Require BB10_champion_1RB1RA BB10_champion_bound.
From BB8 Require Import BB10_lead_1RB0RA BB10_lead_bound.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

Notation Uc := BB10_champion_1RB1RA.U.
Notation Xc := BB10_champion_1RB1RA.X.
Notation iterc := BB10_champion_1RB1RA.iter.
Notation Tprec := BB10_champion_1RB1RA.Tpre.
Notation Tvc := BB10_champion_1RB1RA.Tv.
Notation b1c := BB10_champion_1RB1RA.b1.
Notation b2c := BB10_champion_1RB1RA.b2.

Opaque BB10_champion_1RB1RA.U BB10_champion_1RB1RA.X BB10_champion_1RB1RA.Tv
  BB10_champion_1RB1RA.b1 BB10_champion_1RB1RA.b2.

(** ** Iteration *)

Lemma iterc_eq : forall n g x, iterc n g x = iter n g x.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma iter_ge2 : forall g, (forall y, y + 2 <= g y) -> forall n x, x + 2 * n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_x : forall g, (forall y z, y <= z -> g y <= g z) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

Lemma iter_ge : forall g, (forall y, y <= g y) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_n : forall g, (forall y, y <= g y) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge. exact Hg.
Qed.

Lemma iter_le_fun : forall f g, (forall y, f y <= g y) -> (forall y z, y <= z -> g y <= g z) ->
  forall n x, iter n f x <= iter n g x.
Proof.
  intros f g Hfg Hg. induction n; intros x; simpl. - lia.
  - specialize (IHn x). specialize (Hfg (iter n f x)). specialize (Hg _ _ IHn). lia.
Qed.

Lemma iter_twice : forall g n x, iter n (fun y => g (g y)) x = iter (2 * n) g x.
Proof.
  intros g. induction n; intros x. - reflexivity.
  - replace (2 * S n) with (S (S (2 * n))) by lia. simpl. rewrite IHn. reflexivity.
Qed.

(** ** The clearing functions F of the candidate *)

Lemma F_ge : forall k y, y + 2 <= F k y.
Proof.
  induction k as [| k IH]; intros y.
  - simpl. lia.
  - rewrite F_S. pose proof (iter_ge2 (F k) IH (y + 2) 0). lia.
Qed.

Lemma F_infl : forall k y, y <= F k y.
Proof. intros. pose proof (F_ge k y). lia. Qed.

Lemma F_mono : forall k y z, y <= z -> F k y <= F k z.
Proof.
  destruct k as [| k]; intros y z Hyz.
  - simpl. lia.
  - rewrite !F_S. apply iter_mono_n; [apply F_infl | lia].
Qed.

Lemma F_lvl : forall k y, F k y <= F (S k) y.
Proof.
  intros k y. rewrite F_S. replace (y + 2) with (S (y + 1)) by lia.
  change (iter (S (y + 1)) (F k) 0) with (F k (iter (y + 1) (F k) 0)).
  apply F_mono. pose proof (iter_ge2 (F k) (F_ge k) (y + 1) 0). lia.
Qed.

Lemma F_lvl_mono : forall d k y, F k y <= F (d + k) y.
Proof.
  induction d; intros k y. - reflexivity.
  - specialize (IHd k y). pose proof (F_lvl (d + k) y). change (S d + k) with (S (d + k)). lia.
Qed.

Lemma F_lvl_le : forall k K y, k <= K -> F k y <= F K y.
Proof. intros k K y H. replace K with ((K - k) + k) by lia. apply F_lvl_mono. Qed.

Lemma F1_eq : forall y, F 1 y = 2 * y + 4.
Proof.
  intros y. rewrite F_S.
  assert (E : forall n x, iter n (F 0) x = x + 2 * n).
  { induction n; intros x; simpl. - lia. - rewrite IHn. lia. }
  rewrite E. lia.
Qed.

Lemma F_dbl : forall k y, 1 <= k -> 2 * y + 4 <= F k y.
Proof. intros k y Hk. rewrite <- F1_eq. apply F_lvl_le. exact Hk. Qed.

Lemma F0_big : forall j, 4 * j + 8 <= F (S (S j)) 0.
Proof.
  induction j as [| j IH].
  - change (F 2 0) with (F 1 (F 1 0)). rewrite !F1_eq. lia.
  - change (F (S (S (S j))) 0) with (F (S (S j)) (F (S (S j)) 0)).
    pose proof (F_dbl (S (S j)) (F (S (S j)) 0) ltac:(lia)). lia.
Qed.

Opaque F.

(** ** Domination of the champion's clearing functions *)

Lemma Dom : forall j, (forall x, Uc j x <= F (S j) (F (S j) x)) /\ Xc j <= iter (4 * j + 2) (F (S j)) 0.
Proof.
  induction j as [| j [HU HX]].
  - split.
    + intros x. rewrite BB10_champion_1RB1RA.U_0, !F1_eq. lia.
    + rewrite BB10_champion_1RB1RA.X_0. change (iter (4 * 0 + 2) (F 1) 0) with (F 1 (F 1 0)).
      rewrite !F1_eq. lia.
  - assert (Hc : forall y z, y <= z -> F (S j) (F (S j) y) <= F (S j) (F (S j) z)).
    { intros y z H. apply F_mono, F_mono, H. }
    assert (HX' : Xc (S j) <= iter (4 * S j + 2) (F (S (S j))) 0).
    { rewrite BB10_champion_1RB1RA.X_S.
      transitivity (iter 4 (F (S j)) (Xc j)).
      - change (iter 4 (F (S j)) (Xc j)) with (F (S j) (F (S j) (F (S j) (F (S j) (Xc j))))).
        pose proof (HU (Xc j)) as H1. pose proof (HU (Uc j (Xc j))) as H2.
        pose proof (Hc _ _ H1) as H3. lia.
      - transitivity (iter 4 (F (S j)) (iter (4 * j + 2) (F (S j)) 0)).
        + apply iter_mono_x; [apply F_mono | exact HX].
        + rewrite <- iter_add. replace (4 + (4 * j + 2)) with (4 * S j + 2) by lia.
          apply iter_le_fun; [apply F_lvl | apply F_mono]. }
    split; [| exact HX'].
    intros x. rewrite BB10_champion_1RB1RA.U_S, iterc_eq.
    transitivity (iter (x - 2 * j) (fun y => F (S j) (F (S j) y)) (Xc j)).
    { apply iter_le_fun; [exact HU | exact Hc]. }
    rewrite iter_twice.
    transitivity (iter (2 * (x - 2 * j)) (F (S j)) (iter (4 * j + 2) (F (S j)) 0)).
    { apply iter_mono_x; [apply F_mono | exact HX]. }
    rewrite <- iter_add.
    rewrite (F_S (S j) (F (S (S j)) x)).
    apply iter_mono_n; [apply F_infl |].
    pose proof (F_dbl (S (S j)) x ltac:(lia)) as D1.
    pose proof (F0_big j) as D2. pose proof (F_mono (S (S j)) 0 x ltac:(lia)) as D3. lia.
Qed.

Lemma UD : forall j K y, j < K -> Uc j y <= F K (F K y).
Proof.
  intros j K y H. destruct (Dom j) as [HU _].
  transitivity (F (S j) (F (S j) y)); [apply HU |].
  transitivity (F K (F (S j) y)); [apply F_lvl_le; lia |].
  apply F_mono, F_lvl_le. lia.
Qed.

(** ** The champion's clearing values *)

Lemma Tpre_S : forall m j B, Tprec (S m) j B = Tprec m (j + 3) (iterc 3 (Uc (j + 2)) B).
Proof. reflexivity. Qed.

Lemma Tpre_le : forall m j B, Tprec m j B <= iter (6 * m) (F (j + 3 * m)) B.
Proof.
  induction m as [| m IH]; intros j B.
  - simpl. lia.
  - rewrite Tpre_S, iterc_eq.
    transitivity (iter (6 * m) (F (j + 3 + 3 * m)) (iter 3 (Uc (j + 2)) B)); [apply IH |].
    replace (j + 3 + 3 * m) with (j + 3 * S m) by lia.
    transitivity (iter (6 * m) (F (j + 3 * S m)) (iter 6 (F (j + 3 * S m)) B)).
    + apply iter_mono_x; [apply F_mono |].
      change 6 with (2 * 3). rewrite <- iter_twice.
      apply iter_le_fun; [| intros y z H; apply F_mono, F_mono, H].
      intros y. apply UD. lia.
    + rewrite <- iter_add. replace (6 * m + 6) with (6 * S m) by lia. apply Nat.le_refl.
Qed.

Lemma Tv_le : forall m, Tvc m 1 7 <= F (3 * m + 5) (6 * m + 6).
Proof.
  intros m. rewrite BB10_champion_bound.Tv_unfold.
  replace (1 + 3 * m + 2) with (3 * m + 3) by lia.
  set (K := 3 * m + 4).
  transitivity (iter 4 (F K) (Tprec m 1 7)).
  { change (iter 4 (F K) (Tprec m 1 7)) with (F K (F K (F K (F K (Tprec m 1 7))))).
    pose proof (UD (3 * m + 3) K (Tprec m 1 7) ltac:(unfold K; lia)) as H1.
    pose proof (UD (3 * m + 3) K (Uc (3 * m + 3) (Tprec m 1 7)) ltac:(unfold K; lia)) as H2.
    pose proof (F_mono K _ _ (F_mono K _ _ H1)) as H3. lia. }
  transitivity (iter 4 (F K) (iter (6 * m) (F K) 7)).
  { apply iter_mono_x; [apply F_mono |].
    transitivity (iter (6 * m) (F (1 + 3 * m)) 7); [apply Tpre_le |].
    apply iter_le_fun; [intros y; apply F_lvl_le; unfold K; lia | apply F_mono]. }
  rewrite <- iter_add.
  transitivity (iter (4 + 6 * m) (F K) (iter 4 (F K) 0)).
  { apply iter_mono_x; [apply F_mono |]. pose proof (iter_ge2 (F K) (F_ge K) 4 0). lia. }
  rewrite <- iter_add.
  replace (3 * m + 5) with (S K) by (unfold K; lia).
  rewrite (F_S K (6 * m + 6)). replace (6 * m + 6 + 2) with (4 + 6 * m + 4) by lia. apply Nat.le_refl.
Qed.

Lemma b1c_le : b1c <= bf.
Proof.
  (* no lia on closed F terms: only transitivity steps *)
  rewrite BB10_champion_1RB1RA.b1_def, bf_eq.
  pose proof (Tv_le 7) as H. change (3 * 7 + 5) with 26 in H. change (6 * 7 + 6) with 48 in H.
  change (iter 2 (F 26) 0) with (F 26 (F 26 0)).
  apply (Nat.le_trans _ _ _ H). apply F_mono.
  apply (Nat.le_trans _ (4 * 24 + 8)); [lia | exact (F0_big 24)].
Qed.

Lemma b2c_le : b2c <= b2.
Proof.
  rewrite BB10_champion_1RB1RA.b2_def. unfold BB10_champion_1RB1RA.second.
  pose proof b1c_le as Hb.
  assert (Hm : b1c / 4 <= bf) by (pose proof (Nat.div_le_upper_bound b1c 4 b1c ltac:(lia) ltac:(lia)); lia).
  pose proof (Tv_le (b1c / 4)) as H1.
  pose proof (F_lvl_le (3 * (b1c / 4) + 5) (4 * bf + 33) (6 * (b1c / 4) + 6) ltac:(lia)) as H2.
  pose proof (F0_big (4 * bf + 31)) as H3. replace (S (S (4 * bf + 31))) with (4 * bf + 33) in H3 by lia.
  pose proof (F_mono (4 * bf + 33) (6 * (b1c / 4) + 6) (F (4 * bf + 33) 0) ltac:(lia)) as H4.
  pose proof (F_mono (4 * bf + 33) (F (4 * bf + 33) 0) (F (4 * bf + 33) (F (4 * bf + 33) 0))
                (F_infl (4 * bf + 33) (F (4 * bf + 33) 0))) as H5.
  rewrite b2_eq. change (iter 3 (F (4 * bf + 33)) 0)
    with (F (4 * bf + 33) (F (4 * bf + 33) (F (4 * bf + 33) 0))).
  lia.
Qed.

(** ** The main theorems *)

Theorem candidate_beats_champion :
  exists cc nc co no,
    c0 -[ BB10_champion_1RB1RA.tm ]->* cc /\ halted BB10_champion_1RB1RA.tm cc /\ BB10_champion_bound.ones cc nc /\
    c0 -->* co /\ halted tm co /\ ones co no /\ nc + 1 < no + 1.
Proof.
  destruct BB10_champion_bound.score_exact as [cc [H1 [H2 H3]]].
  destruct score_exact as [co [H4 [H5 H6]]].
  exists cc, (b2c + 3), co, (2 * b2 + 2 * (4 * bf + 33) + 5).
  split; [exact H1 | split; [exact H2 | split; [exact H3 | split; [exact H4 | split; [exact H5 | split; [exact H6 |]]]]]].
  pose proof b2c_le. lia.
Qed.

(** The bound of the wiki's Champions table for the BB(10) champion, f_omega (f_omega 25), is exceeded too
    (f and f_omega are those of BB10_champion_bound.v: f 0 n = n + 1, f (k+1) n = (f k)^n n, f_omega n = f n n). *)
Theorem sigma_gt_f_omega2_25 :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
    BB10_champion_bound.f_omega (BB10_champion_bound.f_omega 25) < n + 1.
Proof.
  destruct score_exact as [co [H4 [H5 H6]]].
  exists co, (2 * b2 + 2 * (4 * bf + 33) + 5).
  split; [exact H4 | split; [exact H5 | split; [exact H6 |]]].
  pose proof (BB10_champion_bound.final_arith (b1c / 4) b2c BB10_champion_bound.b1_quarter
                BB10_champion_bound.b2_big) as Hf.
  pose proof b2c_le as Hle. revert Hf.
  generalize (BB10_champion_bound.f_omega (BB10_champion_bound.f_omega 25)). intros w Hf. lia.
Qed.

Print Assumptions candidate_beats_champion.
Print Assumptions sigma_gt_f_omega2_25.
