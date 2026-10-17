(** * Score of the BB(4,3) champion 1RB1RD1LC_2LB1RB1LC_1RZ1LA1LD_0RB2RA2RD *)

(** Main results (P = 2^^^ = [knuth 3 2], pentation):
      bb43_main    : halts tm c0, the exact halting configuration (C on a blank, 4*e4+17 ones to its
                     right), and sigma = 4 * E4 e1 v + 18, a symbolic recursion (see BB43_run.v).
      e4_bounds    : P (P (P (2^96 - 1))) < e4 <= P (P (P (2^96 + 6)))
      wiki_bracket : P (P (P (792 * 10^26))) < e4 < P (P (P (793 * 10^26)))   (the bbchallenge wiki claim)
      sigma_bounds : the same bracket for sigma = 4 * e4 + 18.
    No large number is ever evaluated: every closed huge value is kept away from lia and conversion. *)

From TM43 Require Import Individual43 BB43_rules BB43_run.
From Coq Require Import Lia PeanoNat.
From Coq.micromega Require Import ZifyNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(** Knuth's up-arrows: [knuth 1 a b = a^b], [knuth 2 a b = a^^b] (tetration), [knuth 3 a b] = pentation. *)
Fixpoint knuth (n a b : nat) : nat :=
  match n with
  | 0 => a * b
  | S n' => Nat.iter b (knuth n' a) 1
  end.

Lemma knuth_S : forall n a b, knuth (S n) a (S b) = knuth n a (knuth (S n) a b).
Proof. reflexivity. Qed.

Lemma knuth1 : forall b, knuth 1 2 b = 2 ^ b.
Proof. induction b. - reflexivity. - rewrite knuth_S, IHb. simpl knuth. rewrite Nat.pow_succ_r'. lia. Qed.

(** For n >= 1, [knuth n 2] is strictly increasing and above the identity. *)
Lemma knuth_props : forall n, 1 <= n ->
  (forall b, b < knuth n 2 b) /\ (forall b b', b <= b' -> knuth n 2 b <= knuth n 2 b').
Proof.
  induction n as [|n IH]; intros Hn; [lia|].
  destruct n as [|n].
  - split.
    + intros b. rewrite knuth1. apply Nat.pow_gt_lin_r. lia.
    + intros b b' H. rewrite !knuth1. apply Nat.pow_le_mono_r; lia.
  - destruct (IH ltac:(lia)) as [Hgt Hmono].
    assert (Hstep : forall b, knuth (S (S n)) 2 b < knuth (S (S n)) 2 (S b)).
    { intros b. rewrite knuth_S. apply Hgt. }
    assert (Hm : forall b k, knuth (S (S n)) 2 b <= knuth (S (S n)) 2 (b + k)).
    { intros b k. induction k as [|k IHk].
      - rewrite Nat.add_0_r. lia.
      - rewrite Nat.add_succ_r. specialize (Hstep (b + k)). lia. }
    split.
    + intros b. induction b as [|b IHb].
      * simpl. lia.
      * specialize (Hstep b). lia.
    + intros b b' H. replace b' with (b + (b' - b)) by lia. apply Hm.
Qed.

Lemma knuth_gt : forall n b, 1 <= n -> b < knuth n 2 b.
Proof. intros. apply knuth_props. assumption. Qed.

Lemma knuth_mono : forall n b b', 1 <= n -> b <= b' -> knuth n 2 b <= knuth n 2 b'.
Proof. intros. apply knuth_props; assumption. Qed.

Lemma double_le_pow : forall x, 2 * x <= 2 ^ x.
Proof.
  induction x as [|x IH]. - simpl. lia.
  - rewrite Nat.pow_succ_r'. destruct x as [|x]. + simpl. lia.
    + assert (2 <= 2 ^ S x) by (change 2 with (2 ^ 1) at 1; apply Nat.pow_le_mono_r; lia). lia.
Qed.

(** 2 ^^ y >= 2 y for y >= 1. *)
Lemma tet_double : forall y, 1 <= y -> 2 * y <= knuth 2 2 y.
Proof.
  induction y as [|y IH]; intros H; [lia|].
  destruct y as [|y].
  - reflexivity.
  - rewrite knuth_S, knuth1.
    specialize (IH ltac:(lia)).
    pose proof (double_le_pow (2 * S y)).
    assert (2 ^ (2 * S y) <= 2 ^ knuth 2 2 (S y)) by (apply Nat.pow_le_mono_r; lia).
    lia.
Qed.

(** ** The machine's functions *)

Lemma iter_S : forall (f : nat -> nat) n x, Nat.iter (S n) f x = f (Nat.iter n f x).
Proof. reflexivity. Qed.
Lemma iter_0 : forall (f : nat -> nat) x, Nat.iter 0 f x = x.
Proof. reflexivity. Qed.

Lemma iter_g_closed : forall n, Nat.iter n g 1 + 5 = 6 * 2 ^ n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl Nat.iter. unfold g at 1. rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma f1_closed : forall x, f1 x + 5 = 6 * 2 ^ (S (S (S x))).
Proof. intros. apply iter_g_closed. Qed.

Lemma pow_le_f1 : forall x, 2 ^ x <= f1 x.
Proof.
  intros. pose proof (f1_closed x).
  assert (2 ^ x <= 2 ^ (S (S (S x)))) by (apply Nat.pow_le_mono_r; lia).
  assert (1 <= 2 ^ x) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  lia.
Qed.

Lemma tower_le_iter_f1 : forall n, knuth 2 2 n <= Nat.iter n f1 1.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite knuth_S, knuth1. simpl Nat.iter.
    eapply Nat.le_trans; [apply Nat.pow_le_mono_r; [lia | exact IH] | apply pow_le_f1].
Qed.

Lemma G_ge : forall c, knuth 2 2 (S c) <= G c.
Proof.
  intros. unfold G.
  apply (Nat.le_trans _ (knuth 2 2 (2 * c + 11))); [apply knuth_mono; lia | apply tower_le_iter_f1].
Qed.

Lemma iter_G_ge : forall k x, 2 <= x -> knuth 3 2 (S k) <= Nat.iter k G x.
Proof.
  induction k as [|k IH]; intros x Hx.
  - exact Hx.
  - rewrite knuth_S. simpl Nat.iter.
    eapply Nat.le_trans; [| apply G_ge].
    apply knuth_mono; [lia |]. specialize (IH x Hx). lia.
Qed.

(** One cascade: from e >= 2 * (2^^^K) and the next G-iteration count (2e+7)/3 or (2e+4)/3. *)
Lemma cascade : forall k x, 2 <= x -> 2 * knuth 3 2 k <= Nat.iter k G x.
Proof.
  intros k x Hx.
  eapply Nat.le_trans; [| apply iter_G_ge; exact Hx].
  rewrite knuth_S. apply tet_double.
  pose proof (knuth_gt 3 k ltac:(lia)). lia.
Qed.

Theorem E4_lower : forall x y, 2 <= y ->
  knuth 3 2 (knuth 3 2 (knuth 3 2 ((2 * x + 7) / 3))) < E4 x y.
Proof.
  intros x y Hy.
  set (k1 := (2 * x + 7) / 3).
  set (X := knuth 3 2 k1).
  assert (H2 : 2 * X <= E2 x y) by (apply cascade; exact Hy).
  set (k2 := (2 * E2 x y + 7) / 3).
  assert (Hk2 : X <= k2) by (unfold k2; lia).
  set (Y := knuth 3 2 k2).
  assert (H3 : 2 * Y <= E3 x y) by (apply cascade; exact Hy).
  set (k3 := (2 * E3 x y + 4) / 3).
  assert (Hk3 : Y <= k3) by (unfold k3; lia).
  assert (H4 : 2 * knuth 3 2 k3 <= E4 x y) by (apply cascade; exact Hy).
  assert (HY : knuth 3 2 X <= Y) by (apply knuth_mono; lia).
  assert (HZ : knuth 3 2 (knuth 3 2 X) <= knuth 3 2 k3) by (apply knuth_mono; lia).
  pose proof (knuth_gt 3 k3 ltac:(lia)).
  fold X. lia.
Qed.

(** ** The concrete values *)

Lemma e1_closed : e1 + 5 = 6 * 2 ^ 94.
Proof.
  unfold e1. rewrite iter_S, iter_S, iter_0.
  assert (E : f1 1 = 91) by reflexivity. rewrite E.
  apply f1_closed.
Qed.

Lemma k1_value : (2 * e1 + 7) / 3 = 2 ^ 96 - 1.
Proof.
  pose proof e1_closed as H.
  assert (P : 2 ^ 96 = 4 * 2 ^ 94).
  { change 96 with (2 + 94). rewrite Nat.pow_add_r. reflexivity. }
  rewrite P. revert H. generalize e1. generalize (2 ^ 94). intros p x Hx. lia.
Qed.

Lemma v_ge_2 : 2 <= v.
Proof.
  unfold v. rewrite iter_S.
  pose proof (f1_closed (Nat.iter 2 f1 1)) as H. revert H. generalize (Nat.iter 2 f1 1). intros z H.
  assert (2 ^ 3 <= 2 ^ S (S (S z))) by (apply Nat.pow_le_mono_r; lia). simpl (2 ^ 3) in *.
  lia.
Qed.

(** The score: sigma = 4 * e4 + 18 > 2 ^^^ 2 ^^^ 2 ^^^ (2^96 - 1). *)
Theorem sigma_lower : knuth 3 2 (knuth 3 2 (knuth 3 2 (2 ^ 96 - 1))) < sigma.
Proof.
  pose proof (E4_lower e1 v v_ge_2) as H.
  rewrite k1_value, <- e4_eq in H.
  unfold sigma. revert H. generalize (knuth 3 2 (knuth 3 2 (knuth 3 2 (2 ^ 96 - 1)))).
  intros T H. lia.
Qed.

(** ** Upper bound *)

Local Notation T := (knuth 2 2).
Local Notation P := (knuth 3 2).

Definition Bt (j w : nat) : nat := Nat.iter j T w.

Lemma T_S : forall z, T (S z) = 2 ^ T z.
Proof. intros. rewrite knuth_S, knuth1. reflexivity. Qed.

Lemma P_S : forall n, P (S n) = T (P n).
Proof. intros. apply knuth_S. Qed.

Lemma quad_le_pow : forall y, 4 <= y -> 4 * y <= 2 ^ y.
Proof.
  induction y as [|y IH]; intros H; [lia|].
  destruct (Nat.eq_dec y 3) as [->|Hy]. - simpl. lia.
  - rewrite Nat.pow_succ_r'. specialize (IH ltac:(lia)). lia.
Qed.

Lemma f1_up : forall x, f1 x + 6 <= 2 ^ (S (S (S (S (S (S x)))))).
Proof.
  intros. pose proof (f1_closed x) as H. rewrite !Nat.pow_succ_r' in *.
  assert (1 <= 2 ^ x) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia). lia.
Qed.

Lemma Bt_1 : forall w, Bt 1 w = T w.
Proof. reflexivity. Qed.

Lemma iter_f1_up : forall n, Nat.iter n f1 1 + 6 <= Bt 1 (S (S (S n))).
Proof.
  induction n as [|n IH].
  - rewrite Bt_1. assert (E : T 3 = 16) by reflexivity. rewrite E. simpl. lia.
  - rewrite iter_S. rewrite Bt_1 in *. rewrite T_S.
    eapply Nat.le_trans; [apply f1_up | apply Nat.pow_le_mono_r; lia].
Qed.

Lemma Bt_S : forall j w, Bt (S j) w = T (Bt j w).
Proof. reflexivity. Qed.

Lemma Bt_ge : forall j w, w <= Bt j w.
Proof.
  induction j as [|j IH]; intros. - reflexivity.
  - rewrite Bt_S. pose proof (knuth_gt 2 (Bt j w) ltac:(lia)). specialize (IH w). lia.
Qed.

Lemma Bt_mono : forall j w w', w <= w' -> Bt j w <= Bt j w'.
Proof.
  induction j as [|j IH]; intros w w' H. - exact H.
  - rewrite !Bt_S. apply knuth_mono; [lia | apply IH; exact H].
Qed.

Lemma Bt_16 : forall j w, 1 <= j -> 3 <= w -> 16 <= Bt j w.
Proof.
  intros [|j] w Hj Hw; [lia|]. rewrite Bt_S.
  assert (E : T 3 = 16) by reflexivity. rewrite <- E.
  apply knuth_mono; [lia |]. pose proof (Bt_ge j w). lia.
Qed.

Lemma Bt_shift : forall j w, 1 <= j -> 2 ^ Bt j w <= Bt j (S w).
Proof.
  induction j as [|j IH]; intros w Hj; [lia|].
  destruct j as [|j].
  - change (2 ^ T w <= T (S w)). rewrite T_S. lia.
  - specialize (IH w ltac:(lia)).
    pose proof (Nat.pow_gt_lin_r 2 (Bt (S j) w) ltac:(lia)).
    rewrite (Bt_S (S j) w), (Bt_S (S j) (S w)), <- T_S. apply knuth_mono; lia.
Qed.

Lemma G_up : forall c, G c + 6 <= T (2 * c + 14).
Proof.
  intros. unfold G. replace (2 * c + 14) with (S (S (S (2 * c + 11)))) by lia.
  apply (iter_f1_up (2 * c + 11)).
Qed.

Lemma G_step : forall j w x, 1 <= j -> 3 <= w -> x + 6 <= Bt j w -> G x + 6 <= Bt (S j) (S w).
Proof.
  intros j w x Hj Hw Hx. rewrite Bt_S.
  eapply Nat.le_trans; [apply G_up | apply knuth_mono; [lia |]].
  pose proof (Bt_shift j w Hj). pose proof (Bt_16 j w Hj Hw).
  pose proof (quad_le_pow (Bt j w) ltac:(lia)). lia.
Qed.

Lemma G_iter_up : forall k j w x, 1 <= j -> 3 <= w -> x + 6 <= Bt j w ->
  Nat.iter k G x + 6 <= Bt (j + k) (w + k).
Proof.
  induction k as [|k IH]; intros j w x Hj Hw Hx.
  - rewrite !Nat.add_0_r. exact Hx.
  - rewrite iter_S, (Nat.add_succ_r j k), (Nat.add_succ_r w k). apply G_step; [lia | lia | apply IH; assumption].
Qed.

Lemma iter_add : forall (f : nat -> nat) j m x, Nat.iter (j + m) f x = Nat.iter j f (Nat.iter m f x).
Proof. induction j; intros. - reflexivity. - simpl. rewrite IHj. reflexivity. Qed.

Lemma Bt_P : forall j w m, w <= P m -> Bt j w <= P (j + m).
Proof.
  intros j w m H. eapply Nat.le_trans; [apply Bt_mono; exact H |].
  unfold Bt. change (P (j + m)) with (Nat.iter (j + m) T 1). rewrite iter_add. reflexivity.
Qed.

Lemma cascade_up : forall k m y, y + 6 <= Bt 1 6 -> 6 + k <= P m ->
  Nat.iter k G y + 6 <= P (1 + k + m).
Proof.
  intros k m y Hy Hk.
  eapply Nat.le_trans; [apply (G_iter_up k 1 6 y); [lia | lia | exact Hy] |].
  apply (Bt_P (1 + k) (6 + k) m). lia.
Qed.

Lemma P_double : forall n, 2 * P n <= P (S n).
Proof. intros. rewrite P_S. apply tet_double. pose proof (knuth_gt 3 n ltac:(lia)). lia. Qed.

Lemma P_mono : forall a b, a <= b -> P a <= P b.
Proof. intros. apply knuth_mono; lia. Qed.

Lemma P_gt : forall n, n < P n.
Proof. intros. apply knuth_gt. lia. Qed.

Theorem E4_upper : forall x y, y + 6 <= Bt 1 6 -> 6 + (2 * x + 7) / 3 <= P 4 ->
  E4 x y <= P (P (P ((2 * x + 7) / 3 + 7))).
Proof.
  intros x y Hy H0.
  (* lia must never see the closed values Bt 1 6 and P 4 (zify would unfold them) *)
  pose proof (fun k m => cascade_up k m y Hy) as CU. clear Hy.
  assert (H2 : E2 x y + 6 <= P (1 + (2 * x + 7) / 3 + 4)) by (apply CU; exact H0).
  clear H0.
  set (k1 := (2 * x + 7) / 3) in *.
  replace (1 + k1 + 4) with (k1 + 5) in H2 by lia.
  set (k2 := (2 * E2 x y + 7) / 3).
  assert (Hk2 : k2 <= E2 x y + 3) by (unfold k2; lia).
  pose proof (P_double (k1 + 5)) as D5. pose proof (P_gt (k1 + 5)) as G5.
  replace (S (k1 + 5)) with (k1 + 6) in D5 by lia.
  (* second cascade *)
  assert (H3 : E3 x y + 6 <= P (1 + k2 + (k1 + 6))).
  { apply CU. lia. }
  set (M := P (k1 + 6)).
  assert (H3' : E3 x y + 6 <= P M).
  { eapply Nat.le_trans; [exact H3 | apply P_mono]. unfold M. lia. }
  set (k3 := (2 * E3 x y + 4) / 3).
  assert (Hk3 : k3 <= E3 x y + 2) by (unfold k3; lia).
  pose proof (P_double M) as DM. pose proof (P_gt M) as GM.
  (* third cascade *)
  assert (H4 : E4 x y + 6 <= P (1 + k3 + S M)).
  { apply CU. lia. }
  assert (HM : S M <= P (k1 + 7)).
  { unfold M. pose proof (P_double (k1 + 6)). pose proof (P_gt (k1 + 6)).
    replace (S (k1 + 6)) with (k1 + 7) in * by lia. lia. }
  assert (H5 : 1 + k3 + S M <= P (S M)) by (pose proof (P_double M); rewrite P_S in *; lia).
  eapply Nat.le_trans; [| apply P_mono, P_mono, HM].
  eapply Nat.le_trans; [| apply P_mono, H5]. lia.
Qed.

(** ** The concrete bracket *)

Lemma P4_big : 2 ^ 96 + 5 <= P 4.
Proof.
  assert (A : 2 ^ 96 + 5 <= 2 ^ 97).
  { rewrite (Nat.pow_succ_r' 2 96). pose proof (Nat.pow_le_mono_r 2 3 96 ltac:(lia) ltac:(lia)) as H.
    revert H. generalize (2 ^ 96). simpl. intros p H. lia. }
  assert (H3 : 97 <= P 3) by (apply Nat.leb_le; vm_compute; reflexivity).
  rewrite P_S. eapply Nat.le_trans; [exact A |].
  eapply Nat.le_trans; [| apply knuth_mono; [lia | exact H3]].
  clear A H3. rewrite T_S. apply Nat.pow_le_mono_r; [lia |]. apply (knuth_gt 2 96). lia.
Qed.

Lemma P_strict : forall a b, a < b -> P a < P b.
Proof.
  intros a b H. eapply Nat.lt_le_trans; [| apply P_mono; exact H].
  rewrite P_S. apply knuth_gt. lia.
Qed.

(** e4 is bracketed between two three-fold pentation towers whose seeds differ by 7. *)
Theorem e4_bounds : P (P (P (2 ^ 96 - 1))) < e4 /\ e4 <= P (P (P (2 ^ 96 + 6))).
Proof.
  split.
  - pose proof (E4_lower e1 v v_ge_2) as H. rewrite k1_value, <- e4_eq in H. exact H.
  - rewrite e4_eq. eapply Nat.le_trans; [apply E4_upper |].
    + exact (iter_f1_up 3).
    + rewrite k1_value. replace (6 + (2 ^ 96 - 1)) with (2 ^ 96 + 5) by lia. exact P4_big.
    + rewrite k1_value. replace (2 ^ 96 - 1 + 7) with (2 ^ 96 + 6) by lia. apply Nat.le_refl.
Qed.

(** The bbchallenge wiki's claim 2^^^2^^^2^^^(7.92e28) < e4 < 2^^^2^^^2^^^(7.93e28) (Polygon, Oct 2025). *)
Theorem wiki_bracket : P (P (P (792 * 10 ^ 26))) < e4 /\ e4 < P (P (P (793 * 10 ^ 26))).
Proof.
  assert (L : 792 * 10 ^ 26 <= 2 ^ 96 - 1) by lia.
  assert (U : 2 ^ 96 + 6 < 793 * 10 ^ 26) by lia.
  destruct e4_bounds as [Hl Hu]. split.
  - eapply Nat.le_lt_trans; [| exact Hl]. apply P_mono, P_mono, P_mono. exact L.
  - eapply Nat.le_lt_trans; [exact Hu |]. apply P_strict, P_strict, P_strict. exact U.
Qed.

(** ** Main theorem: halting, the exact final tape, and the exact score as a symbolic recursion *)

Theorem bb43_main :
  halts tm c0 /\
  c0 -[ tm ]->* (C;; Streams.const S0 {{S0}} [S1]^^(4 * E4 e1 v + 17) *> Streams.const S0) /\
  halted tm (C;; Streams.const S0 {{S0}} [S1]^^(4 * E4 e1 v + 17) *> Streams.const S0) /\
  sigma = 4 * E4 e1 v + 18.
Proof.
  rewrite <- e4_eq. split; [exact bb43_halts |]. split; [exact reaches_final |].
  split; [exact final_halted | reflexivity].
Qed.

Theorem sigma_bounds : 4 * P (P (P (2 ^ 96 - 1))) + 18 < sigma /\ sigma <= 4 * P (P (P (2 ^ 96 + 6))) + 18.
Proof.
  destruct e4_bounds as [Hl Hu]. unfold sigma. revert Hl Hu.
  generalize (P (P (P (2 ^ 96 - 1)))) (P (P (P (2 ^ 96 + 6)))). intros a b Hl Hu. lia.
Qed.
