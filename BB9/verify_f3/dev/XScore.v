(** * XScore.v : the score of X (bb9_f3_coq; adapted from C04's dev/ScoreEnd.v).
    X halts in state J reading 1 (J1 undefined; J is entered only by E0 = 1LJ), on C04's halting tape K31_End.Hc.
    Every key ends with at least 6 R_last + 2 ones, R_last >= iter 2 (U K) 0, and the clear depth K is at least
    the parked count minus 1000 >= Pmx + L - 1000 >= R2x = iter 2 (U (12 Rpp + 10)) 0 >= f_omega (12 Rpp + 10) + 2.
    Hence  sigma(X) > f_omega (f_omega a)  for every a <= 12 Rpp + 10  (Score.S1_core).  The key analysis below is ScoreEnd's,
    with C04's Pm replaced by X's Pmx (XTop.v) and the goal replaced by that bound. *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List Bool.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules G_sub2 G_sub3 G_sub4 G_sub5 G_stop G_entry G_end Abs Lift Orbit
  Cascade Step CBtail G_p14_0 G_p14_1 G_p14_2 G_p14_3 G_p14_4 G_p14_5 G_p20_0 G_p20_1 G_p20_2 G_p20_3 G_p20_4 G_p20_5
  Endgame Fin XTop.
From XK31 Require Import K31_Abs K31_Mach K31_End.
From XScore Require Import Score.
Opaque U arrow.

(** The last three accumulators of the class-b tail (ESC, then the two counter clears) at near depth K. *)
Definition Rb1 (K : nat) : nat := iter 2 (U K) O.
Definition Rb2 (K : nat) : nat := iter (2 * Rb1 K + 2) (U K) O.
Definition Rb3 (K : nat) : nat := iter (2 * Rb2 K + 2) (U K) O.

Lemma iter_ge_n : forall g, (forall x, x <= g x) -> forall d n x, iter n g x <= iter (d + n) g x.
Proof.
  intros g Hg. induction d; intros n x; [change (0 + n) with n; lia |].
  change (iter (S d + n) g x) with (g (iter (d + n) g x)).
  specialize (IHd n x). specialize (Hg (iter (d + n) g x)). lia.
Qed.

Lemma Rb3_ge : forall K, iter 2 (U K) O <= Rb3 K.
Proof.
  intro K. unfold Rb3.
  replace (2 * Rb2 K + 2) with ((2 * Rb2 K) + 2) by lia.
  apply iter_ge_n. intro x. pose proof (U_lin K x). lia.
Qed.

(** CBtail.halt_kx lands exactly on K31_End.Hc (the shared H0 halting tape). *)
Lemma halt_kx_Hc : forall z R t a w rest l,
  Kx (repeat 1%nat (S z) ++ 0%nat :: S a :: w :: rest) 1 (S (3 * R + 1)) t (1 >> l) -->+ Hc a w rest l R (S z) t.
Proof.
  intros. refine (prog_eq _ _ _ _ _ _ (halt_kx z (3 * R + 1) t a w rest (1 >> l))).
  - reflexivity.
  - unfold Hc, HR. replace (3 * R + 1) with (1 + 3 * R) by lia.
    rewrite (pow_add [1;0;1;0] 1 (3 * R)), (pow_mul [1;0;1;0] 3 R). reflexivity.
Qed.

(** CBtail.classb_tail with the halting configuration made explicit. *)
Lemma classb_tailS : forall K a w rest t l,
  Kgx (repeat O K ++ [2]) (6 :: S a :: w :: rest) O O t (1 >> l) -->+ Hc a w rest l (Rb3 K) (S K) t.
Proof.
  intros K a w rest t l. set (e := 1 >> l). assert (He : good e) by (left; exists l; reflexivity).
  eapply evstep_progress_trans; [ apply (CDPx K 2 [] (6 :: S a :: w :: rest) O t e He) |].
  fold (Rb1 K). rewrite app_nil_r, kx_zeros_counter.
  eapply progress_trans; [ apply (dec6_kx K (3 * Rb1 K + 2) t (S a) (w :: rest) e ltac:(lia)) |].
  replace (2 * (3 * Rb1 K + 2) + 3) with (6 * Rb1 K + 7) by lia.
  rewrite kx_deposit_digit.
  eapply evstep_progress_trans; [ apply (CDPx K (2 * Rb1 K + 2) [] (3 :: S a :: w :: rest) O t e He) |].
  fold (Rb2 K). rewrite app_nil_r, kx_zeros_counter.
  eapply progress_trans; [ apply (dec3_kx K (3 * Rb2 K + 2) t (S a) (w :: rest) e ltac:(lia)) |].
  replace (2 * (3 * Rb2 K + 2) + 3) with (6 * Rb2 K + 7) by lia.
  rewrite kx_deposit_digit.
  eapply evstep_progress_trans; [ apply (CDPx K (2 * Rb2 K + 2) [] (0%nat :: S a :: w :: rest) O t e He) |].
  fold (Rb3 K). rewrite app_nil_r, kx_zeros_counter.
  replace (3 * Rb3 K + 2) with (S (3 * Rb3 K + 1)) by lia.
  apply halt_kx_Hc.
Qed.

Lemma D0f14_score : forall t P s y Ll, 18 <= P -> 1 <= y ->
  exists c, D0f t 14 P s y (Ll *> const 0) -->+ c /\ halted tm c /\
    exists N, ones c N /\ 6 * Rb3 (P - 11) + 2 <= N.
Proof.
  intros t P s y Ll HP Hy. destruct (split6 (P - 18)) as [p [E [HE Hp]]].
  destruct E as [|[|[|[|[|[|E]]]]]]; [| | | | | | lia].
  - replace P with (6 * p + 18) by lia.
    replace (6 * p + 18 - 11) with (6 * p + 7) by lia.
    destruct y as [|a]; [lia |].
    pose proof (classb_tailS (6 * p + 7) a s [] (t + 4) (Ll *> const 0)) as HT.
    destruct (Hc_ones a s [] Ll (Rb3 (6 * p + 7)) (S (6 * p + 7)) (t + 4)) as [N [HN HNb]].
    exists (Hc a s [] (Ll *> const 0) (Rb3 (6 * p + 7)) (S (6 * p + 7)) (t + 4)).
    split; [eapply progress_trans; [apply pk14_0 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
  - replace P with (6 * p + 19) by lia.
    replace (6 * p + 19 - 11) with (6 * p + 8) by lia.
    destruct y as [|a]; [lia |].
    pose proof (classb_tailS (6 * p + 8) a s [] (t + 4) (Ll *> const 0)) as HT.
    destruct (Hc_ones a s [] Ll (Rb3 (6 * p + 8)) (S (6 * p + 8)) (t + 4)) as [N [HN HNb]].
    exists (Hc a s [] (Ll *> const 0) (Rb3 (6 * p + 8)) (S (6 * p + 8)) (t + 4)).
    split; [eapply progress_trans; [apply pk14_1 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
  - replace P with (6 * p + 20) by lia.
    replace (6 * p + 20 - 11) with (6 * p + 9) by lia.
    destruct y as [|a]; [lia |].
    pose proof (classb_tailS (6 * p + 9) a s [] (t + 4) (Ll *> const 0)) as HT.
    destruct (Hc_ones a s [] Ll (Rb3 (6 * p + 9)) (S (6 * p + 9)) (t + 4)) as [N [HN HNb]].
    exists (Hc a s [] (Ll *> const 0) (Rb3 (6 * p + 9)) (S (6 * p + 9)) (t + 4)).
    split; [eapply progress_trans; [apply pk14_2 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
  - replace P with (6 * p + 21) by lia.
    replace (6 * p + 21 - 11) with (6 * p + 10) by lia.
    destruct y as [|a]; [lia |].
    pose proof (classb_tailS (6 * p + 10) a s [] (t + 4) (Ll *> const 0)) as HT.
    destruct (Hc_ones a s [] Ll (Rb3 (6 * p + 10)) (S (6 * p + 10)) (t + 4)) as [N [HN HNb]].
    exists (Hc a s [] (Ll *> const 0) (Rb3 (6 * p + 10)) (S (6 * p + 10)) (t + 4)).
    split; [eapply progress_trans; [apply pk14_3 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
  - replace P with (6 * p + 22) by lia.
    replace (6 * p + 22 - 11) with (6 * p + 11) by lia.
    destruct y as [|a]; [lia |].
    pose proof (classb_tailS (6 * p + 11) a s [] (t + 4) (Ll *> const 0)) as HT.
    destruct (Hc_ones a s [] Ll (Rb3 (6 * p + 11)) (S (6 * p + 11)) (t + 4)) as [N [HN HNb]].
    exists (Hc a s [] (Ll *> const 0) (Rb3 (6 * p + 11)) (S (6 * p + 11)) (t + 4)).
    split; [eapply progress_trans; [apply pk14_4 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
  - replace P with (6 * p + 23) by lia.
    replace (6 * p + 23 - 11) with (6 * p + 12) by lia.
    destruct y as [|a]; [lia |].
    pose proof (classb_tailS (6 * p + 12) a s [] (t + 4) (Ll *> const 0)) as HT.
    destruct (Hc_ones a s [] Ll (Rb3 (6 * p + 12)) (S (6 * p + 12)) (t + 4)) as [N [HN HNb]].
    exists (Hc a s [] (Ll *> const 0) (Rb3 (6 * p + 12)) (S (6 * p + 12)) (t + 4)).
    split; [eapply progress_trans; [apply pk14_5 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
Qed.

Lemma D0f20_score : forall t P s y Ll, 18 <= P -> 1 <= y ->
  exists c, D0f t 20 P s y (Ll *> const 0) -->+ c /\ halted tm c /\
    exists N, ones c N /\ 6 * Rb3 (P - 12) + 2 <= N.
Proof.
  intros t P s y Ll HP Hy. destruct (split6 (P - 18)) as [p [E [HE Hp]]].
  destruct E as [|[|[|[|[|[|E]]]]]]; [| | | | | | lia].
  - replace P with (6 * p + 18) by lia.
    replace (6 * p + 18 - 12) with (6 * p + 6) by lia.
    pose proof (classb_tailS (6 * p + 6) 3 y [s] (t + 5) (Ll *> const 0)) as HT.
    destruct (Hc_ones 3 y [s] Ll (Rb3 (6 * p + 6)) (S (6 * p + 6)) (t + 5)) as [N [HN HNb]].
    exists (Hc 3 y [s] (Ll *> const 0) (Rb3 (6 * p + 6)) (S (6 * p + 6)) (t + 5)).
    split; [eapply progress_trans; [apply pk20_0 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
  - replace P with (6 * p + 19) by lia.
    replace (6 * p + 19 - 12) with (6 * p + 7) by lia.
    pose proof (classb_tailS (6 * p + 7) 3 y [s] (t + 5) (Ll *> const 0)) as HT.
    destruct (Hc_ones 3 y [s] Ll (Rb3 (6 * p + 7)) (S (6 * p + 7)) (t + 5)) as [N [HN HNb]].
    exists (Hc 3 y [s] (Ll *> const 0) (Rb3 (6 * p + 7)) (S (6 * p + 7)) (t + 5)).
    split; [eapply progress_trans; [apply pk20_1 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
  - replace P with (6 * p + 20) by lia.
    replace (6 * p + 20 - 12) with (6 * p + 8) by lia.
    pose proof (classb_tailS (6 * p + 8) 3 y [s] (t + 5) (Ll *> const 0)) as HT.
    destruct (Hc_ones 3 y [s] Ll (Rb3 (6 * p + 8)) (S (6 * p + 8)) (t + 5)) as [N [HN HNb]].
    exists (Hc 3 y [s] (Ll *> const 0) (Rb3 (6 * p + 8)) (S (6 * p + 8)) (t + 5)).
    split; [eapply progress_trans; [apply pk20_2 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
  - replace P with (6 * p + 21) by lia.
    replace (6 * p + 21 - 12) with (6 * p + 9) by lia.
    pose proof (classb_tailS (6 * p + 9) 3 y [s] (t + 5) (Ll *> const 0)) as HT.
    destruct (Hc_ones 3 y [s] Ll (Rb3 (6 * p + 9)) (S (6 * p + 9)) (t + 5)) as [N [HN HNb]].
    exists (Hc 3 y [s] (Ll *> const 0) (Rb3 (6 * p + 9)) (S (6 * p + 9)) (t + 5)).
    split; [eapply progress_trans; [apply pk20_3 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
  - replace P with (6 * p + 22) by lia.
    replace (6 * p + 22 - 12) with (6 * p + 10) by lia.
    pose proof (classb_tailS (6 * p + 10) 3 y [s] (t + 5) (Ll *> const 0)) as HT.
    destruct (Hc_ones 3 y [s] Ll (Rb3 (6 * p + 10)) (S (6 * p + 10)) (t + 5)) as [N [HN HNb]].
    exists (Hc 3 y [s] (Ll *> const 0) (Rb3 (6 * p + 10)) (S (6 * p + 10)) (t + 5)).
    split; [eapply progress_trans; [apply pk20_4 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
  - replace P with (6 * p + 23) by lia.
    replace (6 * p + 23 - 12) with (6 * p + 11) by lia.
    pose proof (classb_tailS (6 * p + 11) 3 y [s] (t + 5) (Ll *> const 0)) as HT.
    destruct (Hc_ones 3 y [s] Ll (Rb3 (6 * p + 11)) (S (6 * p + 11)) (t + 5)) as [N [HN HNb]].
    exists (Hc 3 y [s] (Ll *> const 0) (Rb3 (6 * p + 11)) (S (6 * p + 11)) (t + 5)).
    split; [eapply progress_trans; [apply pk20_5 | exact HT] |].
    split; [apply Hc_halted |]. exists N. split; [exact HN | lia].
Qed.


(** ** The bound *)
Lemma fw_lt_iter2 : forall J a, a <= J -> f_omega a + 2 <= iter 2 (U J) 0.
Proof.
  intros J a Ha.
  change (iter 2 (U J) 0) with (U J (U J 0)).
  pose proof (fomega_le_U a).
  pose proof (sc_U_succ a a). pose proof (sc_U_succ a (S a)).
  pose proof (sc_U0_ge J).
  pose proof (sc_U_mono2 a J (S (S a)) (U J 0) ltac:(lia) ltac:(lia)).
  lia.
Qed.

Definition Bound (N : nat) : Prop := forall a, a <= 12 * Rpp + 10 -> f_omega (f_omega a) < N.

Definition GoalX : Prop := exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ Bound N.

Lemma K_ge : forall L P K k a, Pmx + L <= P -> P <= K + k -> k <= 1000 -> a <= 12 * Rpp + 10 -> f_omega a + 2 <= K.
Proof.
  intros L P K k a HP HK Hk Ha.
  pose proof (fw_lt_iter2 (12 * Rpp + 10) a Ha) as H1. fold R2x in H1.
  destruct x_vals as [q [ER [_ [_ EL]]]]. pose proof R2x_ge. unfold Pmx in HP. lia.
Qed.

Lemma bound_of : forall L P K k Rl N, Pmx + L <= P -> P <= K + k -> k <= 1000 -> iter 2 (U K) 0 <= Rl ->
  6 * Rl + 2 <= N -> Bound N.
Proof.
  intros L P K k Rl N HP HK Hk HR HN a Ha.
  pose proof (S1_core a K (K_ge L P K k a HP HK Hk Ha)) as H.
  pose proof (iter_U_ge 2 K 0 ltac:(lia)). lia.
Qed.

Lemma goal_of : forall L P K k c0' c Rl N, c0 -->* c0' -> c0' -->* c -> halted tm c -> ones c N ->
  Pmx + L <= P -> P <= K + k -> k <= 1000 -> iter 2 (U K) 0 <= Rl -> 6 * Rl + 2 <= N -> GoalX.
Proof.
  intros L P K k c0' c Rl N H1 H2 Hh Ho HP HK Hk HR HN.
  exists c, N. split; [eapply evstep_trans; [exact H1 | exact H2] |].
  split; [exact Hh |]. split; [exact Ho |].
  exact (bound_of L P K k Rl N HP HK Hk HR HN).
Qed.

Lemma key14S : forall L P k c0' t P' s y Ll, c0 -->* c0' -> c0' -->+ D0f t 14 P' s y (Ll *> const 0) ->
  Pmx + L <= P -> P' + k = P -> 18 <= P' -> 1 <= y -> k + 11 <= 1000 -> GoalX.
Proof.
  intros L P k c0' t P' s y Ll H1 H2 HP HP' H18 Hy Hk.
  destruct (D0f14_score t P' s y Ll H18 Hy) as [c [H3 [Hh [N [Ho HN]]]]].
  apply (goal_of L P (P' - 11) (k + 11) c0' c (Rb3 (P' - 11)) N H1); [| exact Hh | exact Ho | exact HP | lia | lia
    | apply Rb3_ge | exact HN].
  apply progress_evstep. eapply progress_trans; [exact H2 | exact H3].
Qed.

Lemma key20S : forall L P k c0' t P' s y Ll, c0 -->* c0' -> c0' -->+ D0f t 20 P' s y (Ll *> const 0) ->
  Pmx + L <= P -> P' + k = P -> 18 <= P' -> 1 <= y -> k + 12 <= 1000 -> GoalX.
Proof.
  intros L P k c0' t P' s y Ll H1 H2 HP HP' H18 Hy Hk.
  destruct (D0f20_score t P' s y Ll H18 Hy) as [c [H3 [Hh [N [Ho HN]]]]].
  apply (goal_of L P (P' - 12) (k + 12) c0' c (Rb3 (P' - 12)) N H1); [| exact Hh | exact Ho | exact HP | lia | lia
    | apply Rb3_ge | exact HN].
  apply progress_evstep. eapply progress_trans; [exact H2 | exact H3].
Qed.

Theorem casc_keyS : forall L, in_keys L = true -> reachF Pmx L -> GoalX.
Proof.
  intros L HK [t [P [s [y [l [HR [Hy [HP [Ll Hl]]]]]]]]]. subst l. pose proof Pmx_ge.
  unfold in_keys in HK.
  repeat (apply orb_true_iff in HK; destruct HK as [HK | HK]); apply Nat.eqb_eq in HK; subst L.
  - (* key 31: c04-k31 *)
    destruct (k31_end t P s y (Ll *> const 0) ltac:(lia)) as [c [Rl [H1 [Hh [HRl Hon]]]]].
    destruct (Hon Ll eq_refl) as [N [Ho HN]].
    exact (goal_of 31 P (P - 21) 21 _ c Rl N HR H1 Hh Ho HP ltac:(lia) ltac:(lia) HRl HN).
  - (* key 37: AbsSUB3 (J = 4) -> D0f(14) *)
    change (S 37) with (5 * 4 + 18) in HR.
    assert (HS : D0f t (5 * 4 + 18) P s y (Ll *> const 0) -->+ D0f (3 + t) 14 (P - 4) 2 (4 + 4) (([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll) *> const 0)).
    { pose proof (AbsSUB3 4 P s t y (Ll *> const 0) ltac:(lia)) as HS0. rewrite !Str_app_assoc. exact HS0. }
    exact (key14S 37 P 4 _ (3 + t) (P - 4) 2 (4 + 4) ([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll) HR HS HP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* key 43: AbsSUB4 (J = 4) -> D0f(14) *)
    change (S 43) with (5 * 4 + 24) in HR.
    assert (HS : D0f t (5 * 4 + 24) P s y (Ll *> const 0) -->+ D0f (3 + t) 14 (P - 6) 6 (6 + 4) (([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll) *> const 0)).
    { pose proof (AbsSUB4 4 P s t y (Ll *> const 0) ltac:(lia)) as HS0. rewrite !Str_app_assoc. exact HS0. }
    exact (key14S 43 P 6 _ (3 + t) (P - 6) 6 (6 + 4) ([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll) HR HS HP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* key 49: AbsSUB5 (J = 6) -> D0f(20) *)
    change (S 49) with (5 * 6 + 20) in HR.
    assert (HS : D0f t (5 * 6 + 20) P s y (Ll *> const 0) -->+ D0f (3 + t) 20 (P - 6) 4 (6 + 6) (([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll) *> const 0)).
    { pose proof (AbsSUB5 6 P s t y (Ll *> const 0) ltac:(lia)) as HS0. rewrite !Str_app_assoc. exact HS0. }
    exact (key20S 49 P 6 _ (3 + t) (P - 6) 4 (6 + 6) ([0;1]^^y ++ [1] ++ [0;1]^^s ++ [1] ++ Ll) HR HS HP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* key 55: STOP + clearing + ENTRY (i = 1) -> D0f(14) *)
    change (S 55) with (5 * (3 * 1 + 2) + 31) in HR.
    destruct (step_stop 1 P s t y (Ll *> const 0) ltac:(lia) Hy) as [R HS0].
    assert (HS : D0f t (5 * (3 * 1 + 2) + 31) P s y (Ll *> const 0) -->+ D0f (3 + t) 14 (P - 3) y (9 + 6 * R)
              (([0;1]^^s ++ [1] ++ Ll) *> const 0)).
    { rewrite !Str_app_assoc. exact HS0. }
    exact (key14S 55 P 3 _ (3 + t) (P - 3) y (9 + 6 * R) ([0;1]^^s ++ [1] ++ Ll) HR HS HP ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Theorem x_goal : GoalX.
Proof.
  destruct L1x_props as [H60 [H2 H3]].
  exact (cascade_from_start GoalX (reachF Pmx) (casc_stepF Pmx) casc_keyS L1x H60 H2 H3 reach_topX).
Qed.

Theorem x_sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ forall a, a <= 12 * Rpp + 10 -> f_omega (f_omega a) < N.
Proof. exact x_goal. Qed.

Print Assumptions x_sigma_lower_bound.
