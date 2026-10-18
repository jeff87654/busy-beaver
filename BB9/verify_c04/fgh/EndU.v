(** * EndU.v : the endgame with the halting tape made explicit, and the two-sided FGH bracket.

    Every key ends in the H0 tape K31_End.Hc, whose ones count is Uniq.Hc_N (exact).  For each key and route the
    halting configuration is written down explicitly (keys 37/43/49/55: one generic step, entry prefix, CBtail tail;
    key 31: K31_End.k31_esc + route0..route4), and its count N satisfies
      R_E < N   (R_E = iter 2 (U K) 0 at a clear depth K >= R2 Bx)       -> f_omega (f_omega (12 Bx + 26)) < N
      N <= T Ptop 13   (Tower: every accumulator, the far side, t, n are small iterates at levels <= Ptop)
                                                                          -> N < f_omega (f_omega (12 Bx + 27)).
    The halting configuration reachable from c0 is unique (Uniq.halted_unique) and so is its count, which gives the
    bracket for EVERY halting configuration and every N with ones c N. *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List Bool.
Import ListNotations.
Set Default Goal Selector "!".
From Dev Require Import Base Abs Lift Orbit Chain Cascade Step Fin CBtail Endgame.
From K31 Require Import K31_Abs K31_Mach K31_End.
From Dev Require ScoreEnd.
From Score Require Import Score.
From Fgh Require Import FArith Tower Uniq CascU.
Opaque U arrow Bx f f_omega.

Definition Bracket (N : nat) : Prop :=
  f_omega (f_omega (12 * Bx + 26)) < N /\ N < f_omega (f_omega (12 * Bx + 27)).

Definition GoalU : Prop := exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ Bracket N.

Notation TT := (T Ptop).

(** ** Class-b tails with the halting configuration explicit *)
Lemma D0f14_exact : forall t P s a l, 18 <= P ->
  D0f t 14 P s (S a) l -->+ Hc a s [] l (ScoreEnd.Rb3 (P - 11)) (S (P - 11)) (t + 4).
Proof.
  intros t P s a l HP. destruct (split6 (P - 18)) as [p [E [HE Hp]]].
  destruct E as [|[|[|[|[|[|E]]]]]]; [| | | | | | lia].
  - replace P with (6 * p + 18) by lia. replace (6 * p + 18 - 11) with (6 * p + 7) by lia.
    eapply progress_trans; [apply pk14_0 | apply ScoreEnd.classb_tailS].
  - replace P with (6 * p + 19) by lia. replace (6 * p + 19 - 11) with (6 * p + 8) by lia.
    eapply progress_trans; [apply pk14_1 | apply ScoreEnd.classb_tailS].
  - replace P with (6 * p + 20) by lia. replace (6 * p + 20 - 11) with (6 * p + 9) by lia.
    eapply progress_trans; [apply pk14_2 | apply ScoreEnd.classb_tailS].
  - replace P with (6 * p + 21) by lia. replace (6 * p + 21 - 11) with (6 * p + 10) by lia.
    eapply progress_trans; [apply pk14_3 | apply ScoreEnd.classb_tailS].
  - replace P with (6 * p + 22) by lia. replace (6 * p + 22 - 11) with (6 * p + 11) by lia.
    eapply progress_trans; [apply pk14_4 | apply ScoreEnd.classb_tailS].
  - replace P with (6 * p + 23) by lia. replace (6 * p + 23 - 11) with (6 * p + 12) by lia.
    eapply progress_trans; [apply pk14_5 | apply ScoreEnd.classb_tailS].
Qed.

Lemma D0f20_exact : forall t P s y l, 18 <= P ->
  D0f t 20 P s y l -->+ Hc 3 y [s] l (ScoreEnd.Rb3 (P - 12)) (S (P - 12)) (t + 5).
Proof.
  intros t P s y l HP. destruct (split6 (P - 18)) as [p [E [HE Hp]]].
  destruct E as [|[|[|[|[|[|E]]]]]]; [| | | | | | lia].
  - replace P with (6 * p + 18) by lia. replace (6 * p + 18 - 12) with (6 * p + 6) by lia.
    eapply progress_trans; [apply pk20_0 | apply ScoreEnd.classb_tailS].
  - replace P with (6 * p + 19) by lia. replace (6 * p + 19 - 12) with (6 * p + 7) by lia.
    eapply progress_trans; [apply pk20_1 | apply ScoreEnd.classb_tailS].
  - replace P with (6 * p + 20) by lia. replace (6 * p + 20 - 12) with (6 * p + 8) by lia.
    eapply progress_trans; [apply pk20_2 | apply ScoreEnd.classb_tailS].
  - replace P with (6 * p + 21) by lia. replace (6 * p + 21 - 12) with (6 * p + 9) by lia.
    eapply progress_trans; [apply pk20_3 | apply ScoreEnd.classb_tailS].
  - replace P with (6 * p + 22) by lia. replace (6 * p + 22 - 12) with (6 * p + 10) by lia.
    eapply progress_trans; [apply pk20_4 | apply ScoreEnd.classb_tailS].
  - replace P with (6 * p + 23) by lia. replace (6 * p + 23 - 12) with (6 * p + 11) by lia.
    eapply progress_trans; [apply pk20_5 | apply ScoreEnd.classb_tailS].
Qed.

(** ** Glue arithmetic *)
Lemma depth_ge_R2 : forall L P K c, Pm + L <= P -> P <= K + c -> c <= 1000 -> R2 Bx <= K.
Proof.
  intros L P K c HP HK Hc. pose proof Pm_eq as E. pose proof (R2_ge Bx). pose proof Bx_ge6.
  destruct L1_val as [b [EB E1]]. unfold Ptop in E. generalize dependent (R2 Bx). intros. lia.
Qed.

Lemma T_2c : forall a c m, a <= TT m -> c <= Ptop + 3 -> 1 <= m -> 2 * a + c <= TT (S (S m)).
Proof.
  intros a c m Ha Hc Hm. pose proof (T_sum _ a a m Ha Ha) as H1.
  assert (H2 : c <= TT (S m)) by (apply T_small; lia).
  pose proof (T_sum _ _ _ (S m) H1 H2). lia.
Qed.

Lemma mass_T : forall L t s y Ll, L <= L1 -> mass t s y Ll <= L1 + (L1 - L) * Cst -> mass t s y Ll + Cst <= TT 7.
Proof.
  intros L t s y Ll HL HM. pose proof L1_le_Ptop as H0.
  assert (A1 : L1 <= TT 1) by (apply T_small; lia).
  assert (A2 : Rc <= TT 2) by (unfold Rc; apply T_iter; lia).
  assert (A3 : 6 * Rc <= TT 3) by (apply T_mul; [apply T_small; lia | exact A2]).
  assert (A4 : 19 + L1 <= TT 3) by (apply T_small; lia).
  assert (A5 : Cst <= TT 4) by (unfold Cst; apply T_sum; assumption).
  assert (A6 : L1 * Cst <= TT 5) by (apply T_mul; [apply (T_up _ L1 1 4); [exact A1 | lia] | exact A5]).
  assert (A7 : (L1 - L) * Cst <= L1 * Cst) by (apply Nat.mul_le_mono_r; lia).
  assert (A8 : L1 + (L1 - L) * Cst <= TT 6) by (apply T_sum; [apply (T_up _ L1 1 5); [exact A1 | lia] | lia]).
  apply T_sum; [lia | apply (T_up _ Cst 4 6); [exact A5 | lia]].
Qed.

Lemma T_comb : forall m a b c d e, 1 <= m -> a <= TT m -> b <= TT m -> c <= TT m -> d <= TT m -> e <= TT m ->
  1000 + 10 * a + 10 * b + 10 * c + 10 * d + 10 * e <= TT (S (S (S (S m)))).
Proof.
  intros m a b c d e Hm Ha Hb Hc Hd He. pose proof L1_le_Ptop.
  assert (K10 : 10 <= TT m) by (apply T_small; lia).
  assert (K1000 : 1000 <= TT (S m)) by (apply T_small; lia).
  pose proof (T_mul _ 10 a m K10 Ha) as H1. pose proof (T_mul _ 10 b m K10 Hb) as H2.
  pose proof (T_mul _ 10 c m K10 Hc) as H3. pose proof (T_mul _ 10 d m K10 Hd) as H4.
  pose proof (T_mul _ 10 e m K10 He) as H5.
  pose proof (T_sum _ _ _ (S m) K1000 H1) as S1. pose proof (T_sum _ _ _ (S m) H2 H3) as S2.
  pose proof (T_sum _ _ _ (S m) H4 H5) as S3. pose proof (T_sum _ _ _ (S (S m)) S1 S2) as S4.
  pose proof (T_up _ _ _ (S (S (S m))) S3 ltac:(lia)) as S5. pose proof (T_sum _ _ _ (S (S (S m))) S4 S5) as S6.
  lia.
Qed.

Lemma bracket_of : forall N K Rl, R2 Bx <= K -> iter 2 (U K) 0 <= Rl -> Rl < N -> N <= TT 13 -> Bracket N.
Proof.
  intros N K Rl HK HR HN HU. split.
  - exact (LB_chain K Rl N HK HR HN).
  - apply (UB_chain Ptop 13 N).
    + pose proof (T_le_U2 Ptop 13). lia.
    + pose proof R2_pos. unfold Ptop. lia.
Qed.

Lemma goalU_of : forall d s G Ll R n t K Rl, c0 -->* Hc d s G (Ll *> const 0) R n t ->
  R2 Bx <= K -> iter 2 (U K) 0 <= Rl -> Rl < Hc_N d s G Ll R n t -> Hc_N d s G Ll R n t <= TT 13 -> GoalU.
Proof.
  intros d s G Ll R n t K Rl H1 H2 H3 H4 H5. exists (Hc d s G (Ll *> const 0) R n t), (Hc_N d s G Ll R n t).
  split; [exact H1 | split; [apply Hc_halted | split; [apply Hc_ones_exact | exact (bracket_of _ K Rl H2 H3 H4 H5)]]].
Qed.

Lemma Rb3_T : forall K, K <= Ptop -> ScoreEnd.Rb3 K <= TT 8.
Proof.
  intros K HK. pose proof L1_le_Ptop.
  assert (A1 : ScoreEnd.Rb1 K <= TT 2) by (unfold ScoreEnd.Rb1; apply T_iter; [lia | apply T_small; lia]).
  assert (A2 : ScoreEnd.Rb2 K <= TT 5) by (unfold ScoreEnd.Rb2; apply T_iter; [lia | pose proof (T_2c _ 2 2 A1 ltac:(lia) ltac:(lia)); lia]).
  unfold ScoreEnd.Rb3. apply T_iter; [lia | pose proof (T_2c _ 2 5 A2 ltac:(lia) ltac:(lia)); lia].
Qed.

Ltac N_simp := unfold Hc_N, mass in *; rewrite ?count1_encl_cons, ?count1_app, ?count1_pow; cbn [encl count1 sym_val] in *.

(** ** Key 31 (five routes, K31_End) *)
Lemma key31U : reachU 31 -> GoalU.
Proof.
  intros [t [P [s [y [Ll [HR [Hy [HP [HPt [HL1 HM]]]]]]]]]].
  pose proof Pm_ge. pose proof L1_le_Ptop.
  pose proof (mass_T 31 t s y Ll HL1 HM) as HMT. set (M := mass t s y Ll + Cst) in HMT.
  assert (HMT9 : M <= TT 9) by (apply (T_up _ M 7 9); [exact HMT | lia]).
  assert (HPT : P <= TT 9) by (apply T_small; lia).
  pose proof (k31_esc P s t y (Ll *> const 0) ltac:(lia)) as HE.
  set (R := RE P) in *.
  assert (HRT : R <= TT 2) by (unfold R, RE; apply T_iter; [lia | apply T_small; lia]).
  assert (HRT9 : R <= TT 9) by (apply (T_up _ R 2 9); [exact HRT | lia]).
  assert (HK : R2 Bx <= P - 21) by (apply (depth_ge_R2 31 P (P - 21) 21); lia).
  assert (HR0 : iter 2 (U (P - 21)) 0 <= R) by (unfold R, RE; lia).
  destruct (split_mod (P - 35) 5 ltac:(lia)) as [w [rho [Hrho Hw]]].
  destruct rho as [|[|[|[|[|rho]]]]]; [| | | | | lia].
  - (* rho = 0 *)
    replace (P - 20) with (5 * w + 15) in HE by lia.
    pose proof (route0 w R (9 + t) [5;4;y;s]%nat (Ll *> const 0)) as HT.
    set (Rl := iter (2 * R + w + 7) (U (S (3 * w + 2))) O) in HT.
    assert (HRl : Rl <= TT 5) by (unfold Rl; apply T_iter; [lia | pose proof (T_2c R (w + 7) 2 HRT ltac:(lia) ltac:(lia)); lia]).
    pose proof (iter_ge_count (2 * R + w + 7) (S (3 * w + 2)) O) as G1. fold Rl in G1.
    apply (goalU_of 0 2 [5;4;y;s]%nat Ll Rl (S (3 * w + 2)) (3 + (9 + t)) (P - 21) R).
    + eapply evstep_trans; [exact HR | eapply evstep_trans; [exact HE | exact HT]].
    + exact HK.
    + exact HR0.
    + N_simp. lia.
    + pose proof (T_comb 9 M Rl R P 0 ltac:(lia) HMT9 ltac:(apply (T_up _ Rl 5 9); [exact HRl | lia]) HRT9 HPT
        ltac:(lia)) as HC.
      unfold M in HC. N_simp. lia.
  - (* rho = 1 *)
    replace (P - 20) with (5 * w + 16) in HE by lia.
    pose proof (route1 w R (9 + t) [4;y;s]%nat (Ll *> const 0)) as HT.
    assert (A1 : Ra1 w <= TT 2) by (unfold Ra1; apply T_iter; [lia | apply T_small; lia]).
    set (I1 := iter (2 * Ra1 w + 3) (U (3 * w + 1)) O).
    assert (A2 : I1 <= TT 5) by (unfold I1; apply T_iter; [lia | pose proof (T_2c _ 3 2 A1 ltac:(lia) ltac:(lia)); lia]).
    assert (A3 : K31_End.Rb1 w R <= TT 7).
    { unfold K31_End.Rb1. fold I1. apply T_iter; [lia |]. apply T_sum; [| exact A2].
      pose proof (T_2c R 2 2 HRT ltac:(lia) ltac:(lia)). apply (T_up _ _ 4 5); [lia | lia]. }
    set (Rl := iter 1 (U (S (S (3 * w + 1)))) (K31_End.Rb1 w R)) in HT.
    assert (HRl : Rl <= TT 9).
    { unfold Rl. apply T_iter; [lia |]. apply T_sum; [apply T_small; lia | exact A3]. }
    pose proof (iter_ge_start 1 (S (S (3 * w + 1))) (K31_End.Rb1 w R)) as G1. fold Rl in G1.
    pose proof (iter_ge_count (2 * R + 2) (S (3 * w + 1)) I1) as G2. unfold K31_End.Rb1 in G1. fold I1 in G1.
    apply (goalU_of 1 5 [4;y;s]%nat Ll Rl (S (S (3 * w + 1))) (3 + (9 + t)) (P - 21) R).
    + eapply evstep_trans; [exact HR | eapply evstep_trans; [exact HE | exact HT]].
    + exact HK.
    + exact HR0.
    + N_simp. lia.
    + pose proof (T_comb 9 M Rl R P 0 ltac:(lia) HMT9 HRl HRT9 HPT ltac:(lia)) as HC.
      unfold M in HC. N_simp. lia.
  - (* rho = 2: the token 6 R_E + 1 survives *)
    replace (P - 20) with (5 * w + 17) in HE by lia.
    pose proof (route2 w R (9 + t) [5;4;y;s]%nat (Ll *> const 0)) as HT.
    set (Rl := iter (w + 5) (U (S (3 * w + 5))) O) in HT.
    assert (HRl : Rl <= TT 2) by (unfold Rl; apply T_iter; [lia | apply T_small; lia]).
    apply (goalU_of (6 * R) 4 [2;5;4;y;s]%nat Ll Rl (S (3 * w + 5)) (3 + (9 + t)) (P - 21) R).
    + eapply evstep_trans; [exact HR | eapply evstep_trans; [exact HE | exact HT]].
    + exact HK.
    + exact HR0.
    + N_simp. lia.
    + pose proof (T_comb 9 M Rl R P 0 ltac:(lia) HMT9 ltac:(apply (T_up _ Rl 2 9); [exact HRl | lia]) HRT9 HPT
        ltac:(lia)) as HC.
      unfold M in HC. N_simp. lia.
  - (* rho = 3 *)
    replace (P - 20) with (5 * w + 18) in HE by lia.
    pose proof (route3 w R (9 + t) [4;y;s]%nat (Ll *> const 0)) as HT.
    assert (A1 : Rx3 w <= TT 2) by (unfold Rx3; apply T_iter; [lia | apply T_small; lia]).
    set (I3 := iter (2 * Rx3 w + 3) (U (3 * w + 3)) O).
    assert (A2 : I3 <= TT 5) by (unfold I3; apply T_iter; [lia | pose proof (T_2c _ 3 2 A1 ltac:(lia) ltac:(lia)); lia]).
    assert (A3 : Ry3 w R <= TT 7).
    { unfold Ry3. fold I3. apply T_iter; [lia |]. apply T_sum; [| exact A2].
      pose proof (T_2c R 1 2 HRT ltac:(lia) ltac:(lia)). apply (T_up _ _ 4 5); [lia | lia]. }
    set (Rl := iter 1 (U (S (S (3 * w + 3)))) (Ry3 w R)) in HT.
    assert (HRl : Rl <= TT 9).
    { unfold Rl. apply T_iter; [lia |]. apply T_sum; [apply T_small; lia | exact A3]. }
    pose proof (iter_ge_start 1 (S (S (3 * w + 3))) (Ry3 w R)) as G1. fold Rl in G1.
    pose proof (iter_ge_count (2 * R + 1) (S (3 * w + 3)) I3) as G2. unfold Ry3 in G1. fold I3 in G1.
    apply (goalU_of 1 5 [4;y;s]%nat Ll Rl (S (S (3 * w + 3))) (3 + (9 + t)) (P - 21) R).
    + eapply evstep_trans; [exact HR | eapply evstep_trans; [exact HE | exact HT]].
    + exact HK.
    + exact HR0.
    + N_simp. lia.
    + pose proof (T_comb 9 M Rl R P 0 ltac:(lia) HMT9 HRl HRT9 HPT ltac:(lia)) as HC.
      unfold M in HC. N_simp. lia.
  - (* rho = 4: the nested counter *)
    replace (P - 20) with (5 * w + 19) in HE by lia.
    pose proof (route4 w R (9 + t) [5;4;y;s]%nat (Ll *> const 0)) as HT.
    assert (A1 : Rx3 w <= TT 2) by (unfold Rx3; apply T_iter; [lia | apply T_small; lia]).
    set (Rl := iter (2 * Rx3 w + 2 * R + 6) (U (S (3 * w + 2))) O) in HT.
    assert (HRl : Rl <= TT 6).
    { unfold Rl. apply T_iter; [lia |]. pose proof (T_2c _ 0 2 A1 ltac:(lia) ltac:(lia)) as B1. pose proof (T_2c R 6 2 HRT ltac:(lia) ltac:(lia)) as B2.
      pose proof (T_sum _ _ _ 4 B1 B2). lia. }
    pose proof (iter_ge_count (2 * Rx3 w + 2 * R + 6) (S (3 * w + 2)) O) as G1. fold Rl in G1.
    apply (goalU_of 0 2 [5;4;y;s]%nat Ll Rl (S (3 * w + 2)) (3 + (9 + t)) (P - 21) R).
    + eapply evstep_trans; [exact HR | eapply evstep_trans; [exact HE | exact HT]].
    + exact HK.
    + exact HR0.
    + N_simp. lia.
    + pose proof (T_comb 9 M Rl R P 0 ltac:(lia) HMT9 ltac:(apply (T_up _ Rl 6 9); [exact HRl | lia]) HRT9 HPT
        ltac:(lia)) as HC.
      unfold M in HC. N_simp. lia.
Qed.

(** ** Class-b keys: one generic step to D0f(14) / D0f(20), the entry prefix and the CBtail tail *)
Lemma classb_goal : forall L P t s y Ll c K a w G Ll' t' d,
  c0 -->* D0f t (S L) P s y (Ll *> const 0) -> D0f t (S L) P s y (Ll *> const 0) -->+ c ->
  c -->+ Hc a w G (Ll' *> const 0) (ScoreEnd.Rb3 K) (S K) t' ->
  Pm + L <= P -> P <= Ptop -> K + d = P -> d <= 1000 -> L <= L1 ->
  mass t s y Ll <= L1 + (L1 - L) * Cst ->
  a + w + count1 (encl G) + count1 Ll' + 4 * t' + 40 <= 10 * (mass t s y Ll + Cst) -> GoalU.
Proof.
  intros L P t s y Ll c K a w G Ll' t' d HR H1 H2 HP HPt HK Hd HL1 HM HN.
  pose proof L1_le_Ptop. pose proof (mass_T L t s y Ll HL1 HM) as HMT.
  assert (HMT9 : mass t s y Ll + Cst <= TT 9) by (apply (T_up _ _ 7 9); [exact HMT | lia]).
  assert (HPT : P <= TT 9) by (apply T_small; lia).
  pose proof (Rb3_T K ltac:(lia)) as HB.
  assert (HB9 : ScoreEnd.Rb3 K <= TT 9) by (apply (T_up _ _ 8 9); [exact HB | lia]).
  pose proof (ScoreEnd.Rb3_ge K) as HB0.
  apply (goalU_of a w G Ll' (ScoreEnd.Rb3 K) (S K) t' K (ScoreEnd.Rb3 K)).
  - eapply evstep_trans; [exact HR |]. apply progress_evstep. eapply progress_trans; [exact H1 | exact H2].
  - apply (depth_ge_R2 L P K d); lia.
  - exact HB0.
  - unfold Hc_N. lia.
  - pose proof (T_comb 9 (mass t s y Ll + Cst) (ScoreEnd.Rb3 K) 0 P 0 ltac:(lia) HMT9 HB9 ltac:(lia) HPT ltac:(lia))
      as HC.
    unfold Hc_N. lia.
Qed.

Lemma key37U : reachU 37 -> GoalU.
Proof.
  intros [t [P [s [y [Ll [HR [Hy [HP [HPt [HL1 HM]]]]]]]]]]. pose proof Pm_ge.
  set (Ll' := [0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
  assert (HS : D0f t 38 P s y (Ll *> const 0) -->+ D0f (3 + t) 14 (P - 4) 2 (S 7) (Ll' *> const 0)).
  { unfold Ll'. rewrite !Str_app_assoc. exact (AbsSUB3 4 P s t y (Ll *> const 0) ltac:(lia)). }
  pose proof (D0f14_exact (3 + t) (P - 4) 2 7 (Ll' *> const 0) ltac:(lia)) as HT.
  apply (classb_goal 37 P t s y Ll _ (P - 4 - 11) 7 2 [] Ll' (3 + t + 4) 15 HR HS HT);
    [lia | lia | lia | lia | lia | exact HM |].
  unfold Ll', Cst, mass. rewrite ?count1_app, ?count1_pow. cbn [encl count1 sym_val]. lia.
Qed.

Lemma key43U : reachU 43 -> GoalU.
Proof.
  intros [t [P [s [y [Ll [HR [Hy [HP [HPt [HL1 HM]]]]]]]]]]. pose proof Pm_ge.
  set (Ll' := [0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
  assert (HS : D0f t 44 P s y (Ll *> const 0) -->+ D0f (3 + t) 14 (P - 6) 6 (S 9) (Ll' *> const 0)).
  { unfold Ll'. rewrite !Str_app_assoc. exact (AbsSUB4 4 P s t y (Ll *> const 0) ltac:(lia)). }
  pose proof (D0f14_exact (3 + t) (P - 6) 6 9 (Ll' *> const 0) ltac:(lia)) as HT.
  apply (classb_goal 43 P t s y Ll _ (P - 6 - 11) 9 6 [] Ll' (3 + t + 4) 17 HR HS HT);
    [lia | lia | lia | lia | lia | exact HM |].
  unfold Ll', Cst, mass. rewrite ?count1_app, ?count1_pow. cbn [encl count1 sym_val]. lia.
Qed.

Lemma key49U : reachU 49 -> GoalU.
Proof.
  intros [t [P [s [y [Ll [HR [Hy [HP [HPt [HL1 HM]]]]]]]]]]. pose proof Pm_ge.
  set (Ll' := [0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll).
  assert (HS : D0f t 50 P s y (Ll *> const 0) -->+ D0f (3 + t) 20 (P - 6) 4 12 (Ll' *> const 0)).
  { unfold Ll'. rewrite !Str_app_assoc. exact (AbsSUB5 6 P s t y (Ll *> const 0) ltac:(lia)). }
  pose proof (D0f20_exact (3 + t) (P - 6) 4 12 (Ll' *> const 0) ltac:(lia)) as HT.
  apply (classb_goal 49 P t s y Ll _ (P - 6 - 12) 3 12 [4] Ll' (3 + t + 5) 18 HR HS HT);
    [lia | lia | lia | lia | lia | exact HM |].
  unfold Ll', Cst, mass. rewrite ?count1_encl_cons, ?count1_app, ?count1_pow. cbn [encl count1 sym_val]. lia.
Qed.

Lemma key55U : reachU 55 -> GoalU.
Proof.
  intros [t [P [s [y [Ll [HR [Hy [HP [HPt [HL1 HM]]]]]]]]]]. pose proof Pm_ge. pose proof L1_le_Ptop.
  set (Rs := iter (3 + 1) (U (3 * 1 + 2)) O).
  assert (HRs : Rs <= Rc) by (unfold Rs, Rc; apply iter_U_mono3; lia).
  set (Ll' := [0;1]^^s ++ [1] ++ Ll).
  assert (HS : D0f t 56 P s y (Ll *> const 0) -->+ D0f (3 + t) 14 (P - 3) y (S (8 + 6 * Rs)) (Ll' *> const 0)).
  { unfold Ll'. rewrite !Str_app_assoc. replace (S (8 + 6 * Rs)) with (9 + 6 * Rs) by lia.
    exact (step_stopX 1 P s t y (Ll *> const 0) ltac:(lia) Hy). }
  pose proof (D0f14_exact (3 + t) (P - 3) y (8 + 6 * Rs) (Ll' *> const 0) ltac:(lia)) as HT.
  apply (classb_goal 55 P t s y Ll _ (P - 3 - 11) (8 + 6 * Rs) y [] Ll' (3 + t + 4) 14 HR HS HT);
    [lia | lia | lia | lia | lia | exact HM |].
  unfold Ll', Cst, mass. rewrite ?count1_app, ?count1_pow. cbn [encl count1 sym_val]. lia.
Qed.

Theorem casc_keyU : forall L, in_keys L = true -> reachU L -> GoalU.
Proof.
  intros L HK. unfold in_keys in HK.
  repeat (apply orb_true_iff in HK; destruct HK as [HK | HK]); apply Nat.eqb_eq in HK; subst L.
  - apply key31U.
  - apply key37U.
  - apply key43U.
  - apply key49U.
  - apply key55U.
Qed.

Theorem c04_goalU : GoalU.
Proof.
  destruct L1_props as [H60 [H2 H3]].
  exact (cascade_from_start GoalU reachU casc_stepU casc_keyU L1 H60 H2 H3 reach_topU).
Qed.

(** ** Main results *)

(** Existence of the halting configuration, with the two-sided bracket. *)
Theorem c04_fgh_exists : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  f_omega (f_omega (12 * Bx + 26)) < N /\ N < f_omega (f_omega (12 * Bx + 27)).
Proof. destruct c04_goalU as [c [N [H1 [H2 [H3 [H4 H5]]]]]]. exists c, N. auto. Qed.

(** The score of C04 (the ones count of THE halting configuration; every halting configuration reachable from c0 and
    every count N with [ones c N] satisfy it):  f_omega (f_omega (12 Bx + 26)) < sigma < f_omega (f_omega (12 Bx + 27)),
    where 2 Bx + 4 = 2 ^(13 arrows) 3 (FArith.Bx_knuth). *)
Theorem c04_fgh_bracket : forall c N, c0 -->* c -> halted tm c -> ones c N ->
  f_omega (f_omega (12 * Bx + 26)) < N /\ N < f_omega (f_omega (12 * Bx + 27)).
Proof.
  intros c N H1 H2 H3. destruct c04_goalU as [c' [N' [H1' [H2' [H3' HB]]]]].
  pose proof (halted_unique c0 c c' H1 H1' H2 H2') as E. subst c'.
  pose proof (ones_unique c N N' H3 H3') as E. subst N'. exact HB.
Qed.

(** Coarse placement: f_(omega+1)(3) < sigma < f_(omega+1)(4), f_(omega+1) n = iter n f_omega n. *)
Theorem c04_fgh_coarse : forall c N, c0 -->* c -> halted tm c -> ones c N -> f_w1 3 < N /\ N < f_w1 4.
Proof.
  intros c N H1 H2 H3. destruct (c04_fgh_bracket c N H1 H2 H3) as [HL HU].
  split; [exact (coarse_lower N HL) | exact (coarse_upper N HU)].
Qed.

(* Print Assumptions: see probe.v (each run over the full dev graph costs ~260 s). *)
