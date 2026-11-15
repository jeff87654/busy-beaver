(** * BB12_P12_cmp: P12 (12 states) halts with more ones than C4 (11 states, previous BB(11)/BB(12) record) *)

(** C4 (BB11_C4.v, unchanged) proves
      BB11_C4.score_exact : exists c, c0 -[ BB11_C4.tm ]->* c /\ halted BB11_C4.tm c /\
                                       ones c (snd nFIN + 3 + fst nFIN).
    This file proves an UPPER bound for that number from C4's own definitions (W, Zs, Rnd and the run's numbers),
      snd nFIN + 3 + fst nFIN <= iter 7 f_omega2 8 + 3,
    with the fast-growing functions of the P12 bound file, and compares it with P12's lower bound
    4 * iter 8 f_omega2 (f 3 6) + 8 <= fst nP. *)

From BB8 Require Individual112.
From BB8 Require Import BB11_C4.
From BB8 Require Import Individual122.
From BB8 Require Import BB12_P12 BB12_P12_bound.
From Coq Require Import Lia PeanoNat.

Local Open Scope nat_scope.

Ltac add_div_facts :=
  repeat match goal with
  | |- context [?x / ?k] =>
      lazymatch goal with
      | _ : k * (x / k) <= x |- _ => fail
      | _ => pose proof (Nat.Div0.mul_div_le x k)
      end
  | H : context [?x / ?k] |- _ =>
      lazymatch goal with
      | _ : k * (x / k) <= x |- _ => fail
      | _ => pose proof (Nat.Div0.mul_div_le x k)
      end
  end.
Ltac dlia := add_div_facts; lia.

(** ** C4's definitions, unfolded once (variables only) *)

Lemma cW_0 : forall b, BB11_C4.W 0 b = b + 3.
Proof. reflexivity. Qed.

Lemma cW_S : forall j b, BB11_C4.W (S j) b = BB11_C4.iter (S b) (BB11_C4.W j) 2.
Proof. reflexivity. Qed.

Lemma cZs_unf : forall j b, BB11_C4.Zs (j, b) = (j + b / 2 + 1, BB11_C4.W (j + b / 2) (BB11_C4.W (j - 1) 1)).
Proof. reflexivity. Qed.

Lemma cRnd_unf : forall p u, BB11_C4.Rnd (p, u) =
  (fst (BB11_C4.iter (p / 2 + 1) BB11_C4.Zs (1, 3)) + u / 2, snd (BB11_C4.iter (p / 2 + 1) BB11_C4.Zs (1, 3)) + 2).
Proof. reflexivity. Qed.

Lemma c_iter : forall (X : Type) n (g : X -> X) x, BB11_C4.iter n g x = iter n g x.
Proof.
  intros X n g x. induction n as [| n IH]; cbn [BB11_C4.iter iter]; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma c_iter_S : forall (X : Type) n (g : X -> X) x, BB11_C4.iter (S n) g x = g (BB11_C4.iter n g x).
Proof. reflexivity. Qed.

Opaque BB11_C4.W BB11_C4.Zs BB11_C4.Rnd.

(** ** Generic FGH facts *)

Lemma cmp_iter_diag : forall g, (forall a b, a <= b -> g a <= g b) -> (forall a, a <= g a) ->
  forall n x m, n <= m -> x <= m -> iter n g x <= iter m g m.
Proof.
  intros g Hm Hid n x m Hn Hx.
  transitivity (iter n g m); [apply iter_mono_x; assumption |].
  apply iter_mono_n; assumption.
Qed.

Lemma cmp_iter_1 : forall (g : nat -> nat) x, g x = iter 1 g x.
Proof. reflexivity. Qed.

Lemma cmp_iter_iter : forall (g : nat -> nat) a b x, iter a g (iter b g x) = iter (a + b) g x.
Proof. intros. rewrite iter_add. reflexivity. Qed.

Lemma F1_succ : forall x, 1 <= x -> 2 * f_omega1 x <= f_omega1 (S x).
Proof.
  intros x Hx. rewrite (f_omega1_eq (S x)). cbn [iter].
  pose proof (iter_mono_x f_omega f_omega_mono x x (S x) ltac:(lia)) as H1.
  rewrite <- f_omega1_eq in H1.
  pose proof (f_omega_mono _ _ H1) as H2.
  pose proof (f_omega_dbl (f_omega1 x) ltac:(pose proof (f_omega1_id x); lia)) as H3.
  lia.
Qed.

Lemma F2_ge_F1 : forall x, 1 <= x -> f_omega1 x <= f_omega2 x.
Proof.
  intros x Hx. rewrite f_omega2_eq.
  pose proof (iter_mono_n f_omega1 f_omega1_id 1 x x Hx) as H. cbn [iter] in H. exact H.
Qed.

Lemma F2_ge_F1F1 : forall x, 2 <= x -> f_omega1 (f_omega1 x) <= f_omega2 x.
Proof.
  intros x Hx. rewrite f_omega2_eq.
  pose proof (iter_mono_n f_omega1 f_omega1_id 2 x x Hx) as H. cbn [iter] in H. exact H.
Qed.

Lemma F2_ge_F1F1F1 : forall x, 3 <= x -> f_omega1 (f_omega1 (f_omega1 x)) <= f_omega2 x.
Proof.
  intros x Hx. rewrite f_omega2_eq.
  pose proof (iter_mono_n f_omega1 f_omega1_id 3 x x Hx) as H. cbn [iter] in H. exact H.
Qed.

Lemma F2_3x : forall x, 3 <= x -> 3 * x <= f_omega2 x.
Proof. intros x Hx. pose proof (F1_8x x Hx). pose proof (F2_ge_F1 x ltac:(lia)). lia. Qed.

(** ** Upper bound for C4's W *)

Lemma cmp_W_aux : forall j b, BB11_C4.W j b + 3 <= f (S j) (b + 3).
Proof.
  induction j as [| j IH]; intros b.
  - rewrite cW_0, f1. dlia.
  - rewrite cW_S, c_iter.
    assert (Hi : forall i, iter i (BB11_C4.W j) 2 + 3 <= iter i (f (S j)) 5).
    { induction i as [| i IHi]; cbn [iter]; [dlia |].
      specialize (IH (iter i (BB11_C4.W j) 2)).
      pose proof (f_mono (S j) _ _ IHi). dlia. }
    transitivity (iter (S b) (f (S j)) 5); [exact (Hi (S b)) |].
    rewrite (f_S (S j) (b + 3)).
    assert (E : iter (b + 3) (f (S j)) (b + 3) = iter (S b) (f (S j)) (iter 2 (f (S j)) (b + 3))).
    { rewrite <- iter_add. f_equal. dlia. }
    rewrite E. apply iter_mono_x; [intros u v Huv; apply f_mono; exact Huv |].
    cbn [iter].
    pose proof (f_gt (S j) (b + 3) ltac:(dlia)).
    pose proof (f_gt (S j) (f (S j) (b + 3)) ltac:(dlia)). dlia.
Qed.

Lemma cmp_W : forall j b, BB11_C4.W j b <= f_omega (j + b + 4).
Proof.
  intros j b. pose proof (cmp_W_aux j b) as H0.
  pose proof (f_level_mono (b + 3) (S j) (b + 3) ltac:(dlia)) as H1.
  replace (b + 3 + S j) with (j + b + 4) in H1 by dlia.
  pose proof (f_mono (j + b + 4) (b + 3) (j + b + 4) ltac:(dlia)) as H2.
  Transparent f_omega. unfold f_omega. Opaque f_omega. dlia.
Qed.

(** ** Zs and Rnd in the size measure j + b *)

Definition sz (x : nat * nat) : nat := fst x + snd x.

Lemma cmp_sz : forall x, sz x = fst x + snd x.
Proof. reflexivity. Qed.

Lemma cZs : forall j b t, j + b <= t -> 8 <= t -> sz (BB11_C4.Zs (j, b)) <= iter 5 f_omega t.
Proof.
  intros j b t Hs Ht. rewrite cZs_unf. unfold sz; cbn [fst snd].
  pose proof (f_omega_dbl t ltac:(lia)) as H3.
  pose proof (cmp_W (j - 1) 1) as H1.
  pose proof (f_omega_mono (j - 1 + 1 + 4) (f_omega t) ltac:(dlia)) as H2.
  pose proof (f_omega_dbl (f_omega t) ltac:(lia)) as H4.
  set (A := f_omega (f_omega t)) in *.
  pose proof (f_omega_dbl A ltac:(lia)) as H7.
  pose proof (cmp_W (j + b / 2) (BB11_C4.W (j - 1) 1)) as H5.
  pose proof (f_omega_mono (j + b / 2 + BB11_C4.W (j - 1) 1 + 4) (f_omega A) ltac:(dlia)) as H6.
  pose proof (f_omega_dbl (f_omega A) ltac:(lia)) as H8.
  pose proof (f_omega_dbl (f_omega (f_omega A)) ltac:(lia)) as H9.
  change (iter 5 f_omega t) with (f_omega (f_omega (f_omega A))).
  dlia.
Qed.

Lemma cZs_it : forall n jb t, sz jb <= t -> 8 <= t ->
  sz (BB11_C4.iter n BB11_C4.Zs jb) <= iter (5 * n) f_omega t.
Proof.
  induction n as [| n IH]; intros jb t Hs Ht.
  - cbn [BB11_C4.iter]. rewrite Nat.mul_0_r. cbn [iter]. exact Hs.
  - rewrite c_iter_S.
    specialize (IH jb t Hs Ht).
    destruct (BB11_C4.iter n BB11_C4.Zs jb) as [j b]. unfold sz in IH; cbn [fst snd] in IH.
    pose proof (iter_ge f_omega f_omega_id (5 * n) t).
    replace (5 * S n) with (5 + 5 * n) by dlia. rewrite iter_add.
    apply cZs; dlia.
Qed.

Lemma cZs13 : forall k, sz (BB11_C4.iter k BB11_C4.Zs (1, 3)) <= f_omega1 (5 * k + 8).
Proof.
  intros k.
  pose proof (cZs_it k (1, 3) 8 ltac:(unfold sz; cbn; lia) ltac:(lia)) as H.
  eapply Nat.le_trans; [exact H |].
  rewrite f_omega1_eq. apply cmp_iter_diag; [exact f_omega_mono | exact f_omega_id | lia | lia].
Qed.

Lemma cRnd : forall p u t, p + u <= t -> 8 <= t -> sz (BB11_C4.Rnd (p, u)) <= iter 2 f_omega1 t.
Proof.
  intros p u t Hs Ht. rewrite cRnd_unf. unfold sz; cbn [fst snd].
  pose proof (cZs13 (p / 2 + 1)) as H1. unfold sz in H1.
  set (Z := BB11_C4.iter (p / 2 + 1) BB11_C4.Zs (1, 3)) in *.
  pose proof (f_omega1_mono (5 * (p / 2 + 1) + 8) (3 * t + 13) ltac:(dlia)) as H2.
  pose proof (F1_succ (3 * t + 13) ltac:(lia)) as H3.
  pose proof (f_omega1_id (3 * t + 13)) as H4.
  pose proof (F1_8x t ltac:(lia)) as H5.
  pose proof (f_omega1_mono (S (3 * t + 13)) (f_omega1 t) ltac:(lia)) as H6.
  change (iter 2 f_omega1 t) with (f_omega1 (f_omega1 t)).
  dlia.
Qed.

Lemma cRnd_it : forall n pu t, sz pu <= t -> 8 <= t ->
  sz (BB11_C4.iter n BB11_C4.Rnd pu) <= f_omega2 (2 * n + t).
Proof.
  intros n pu t Hs Ht.
  assert (G : sz (BB11_C4.iter n BB11_C4.Rnd pu) <= iter (2 * n) f_omega1 t).
  { induction n as [| n IH].
    - cbn [BB11_C4.iter]. rewrite Nat.mul_0_r. cbn [iter]. exact Hs.
    - rewrite c_iter_S.
      destruct (BB11_C4.iter n BB11_C4.Rnd pu) as [p u]. unfold sz in IH; cbn [fst snd] in IH.
      pose proof (iter_ge f_omega1 f_omega1_id (2 * n) t).
      replace (2 * S n) with (2 + 2 * n) by dlia. rewrite iter_add.
      apply cRnd; dlia. }
  eapply Nat.le_trans; [exact G |].
  rewrite f_omega2_eq. apply cmp_iter_diag; [exact f_omega1_mono | exact f_omega1_id | lia | lia].
Qed.

(** ** C4's run, bounded by iter k f_omega2 B, B = f_omega2 8 *)

Lemma F1_8_ge : 2048 <= f_omega1 8.
Proof.
  rewrite f_omega1_eq.
  assert (G : forall n, 8 * 2 ^ n <= iter n f_omega 8).
  { induction n as [| n IHn]; cbn [iter]; [simpl; lia |].
    rewrite Nat.pow_succ_r'.
    assert (2 ^ n <> 0) by (apply Nat.pow_nonzero; lia).
    pose proof (f_omega_dbl (iter n f_omega 8) ltac:(lia)). lia. }
  pose proof (G 8) as H. change (2 ^ 8) with 256 in H. lia.
Qed.

Lemma F2_8_ge : f_omega1 (f_omega1 8) <= f_omega2 8.
Proof. apply F2_ge_F1F1. lia. Qed.

(** the variables-only skeleton of C4's run *)
Lemma c4_skeleton : forall (a1 : nat) (Q1 M1 T4 FIN : nat * nat) (s2 c2 : nat) (B : nat),
  8 <= B -> 2 * a1 <= B ->
  sz Q1 <= f_omega2 (2 * a1 + B) ->
  sz M1 <= f_omega1 (5 * (fst Q1 / 2 + 1) + 8) ->
  s2 = (fst M1 + snd Q1 / 2 + 1) / 2 ->
  c2 = snd M1 / 4 ->
  sz T4 <= f_omega1 (5 * s2 + 8) ->
  (forall t, sz T4 + 2 <= t -> 8 <= t -> sz FIN <= f_omega2 (2 * c2 + t)) ->
  sz FIN + 3 <= iter 6 f_omega2 B + 3.
Proof.
  intros a1 Q1 M1 T4 FIN s2 c2 B HB H2 HQ HM Hs Hc HT HF.
  pose proof (F2_3x B ltac:(lia)) as A1.
  pose proof (f_omega2_mono (2 * a1 + B) (f_omega2 B) ltac:(lia)) as A2.
  pose proof (f_omega2_id B) as A0.
  set (Q := f_omega2 (f_omega2 B)) in *.
  assert (HQ' : sz Q1 <= Q) by lia.
  assert (HQ3 : 3 <= Q) by (pose proof (f_omega2_id (f_omega2 B)); unfold Q; lia).
  pose proof (F1_8x Q HQ3) as A3.
  assert (A4' : 5 * (fst Q1 / 2 + 1) + 8 <= f_omega1 Q) by (unfold sz in HQ'; dlia).
  pose proof (f_omega1_mono _ _ A4') as A4.
  pose proof (F2_ge_F1F1 Q ltac:(lia)) as A5.
  pose proof (f_omega2_id Q) as A5'.
  set (M := f_omega2 Q) in *.
  assert (HM' : sz M1 <= M) by lia.
  pose proof (f_omega1_id (f_omega1 Q)) as A5''.
  assert (HM3 : 8 <= M) by lia.
  pose proof (F1_8x M ltac:(lia)) as A6.
  pose proof (F1_8x (f_omega1 M) ltac:(lia)) as A7.
  assert (Hs2 : 5 * s2 + 8 <= 8 * (8 * M)) by (rewrite Hs; unfold sz in HM', HQ'; dlia).
  pose proof (f_omega1_mono (5 * s2 + 8) (f_omega1 (f_omega1 M)) ltac:(lia)) as A8.
  pose proof (F2_ge_F1F1F1 M ltac:(lia)) as A9.
  pose proof (f_omega2_id M) as A9'.
  set (T := f_omega2 M) in *.
  assert (HT' : sz T4 <= T) by lia.
  pose proof (HF (T + 2) ltac:(lia) ltac:(lia)) as HF'.
  assert (Hc2 : 2 * c2 + (T + 2) <= 3 * T) by (rewrite Hc; unfold sz in HM'; dlia).
  pose proof (F2_3x T ltac:(lia)) as A10.
  pose proof (f_omega2_mono (2 * c2 + (T + 2)) (f_omega2 T) ltac:(lia)) as A11.
  assert (E : iter 6 f_omega2 B = f_omega2 (f_omega2 T)) by reflexivity.
  rewrite E. lia.
Qed.

Lemma sz_pair2 : forall X : nat * nat, sz (fst X, snd X + 2) = sz X + 2.
Proof. intros [a b]. unfold sz. cbn [fst snd]. lia. Qed.

Lemma sz_score : forall (X : nat * nat) b, sz X + 3 <= b -> snd X + 3 + fst X <= b.
Proof. intros [a c] b H. unfold sz in H. cbn [fst snd] in *. lia. Qed.

Lemma W24c : BB11_C4.W 2 4 = 1091.
Proof. Transparent BB11_C4.W. reflexivity. Qed.
Opaque BB11_C4.W.

Lemma c4_a1 : 2 * (BB11_C4.W 5 (BB11_C4.W 2 4) / 4) <= f_omega2 8.
Proof.
  rewrite W24c.
  pose proof (cmp_W 5 1091) as H1. change (5 + 1091 + 4) with 1100 in H1.
  pose proof F1_8_ge as H2.
  pose proof (f_omega_mono 1100 (f_omega1 8) ltac:(lia)) as H3.
  pose proof (f_omega1_id (f_omega1 8)) as H4.
  pose proof (F1_8x (f_omega1 8) ltac:(lia)) as H5.
  assert (H6 : f_omega (f_omega1 8) <= f_omega1 (f_omega1 8)).
  { rewrite (f_omega1_eq (f_omega1 8)).
    pose proof (iter_mono_n f_omega f_omega_id 1 (f_omega1 8) (f_omega1 8) ltac:(lia)) as H. cbn [iter] in H. exact H. }
  pose proof F2_8_ge as H7.
  set (w := BB11_C4.W 5 1091) in *. clearbody w. dlia.
Qed.

Lemma c4_T3 : sz (BB11_C4.iter 3 BB11_C4.Zs (1, 3)) + 2 <= f_omega2 8.
Proof.
  pose proof (cZs13 3) as H1. change (5 * 3 + 8) with 23 in H1.
  pose proof (F1_succ 23 ltac:(lia)) as H2.
  pose proof (f_omega1_id 23) as H3.
  pose proof F1_8_ge as H4.
  pose proof (f_omega1_mono 24 (f_omega1 8) ltac:(lia)) as H5.
  pose proof F2_8_ge as H6.
  lia.
Qed.

Lemma c4_score_ub : snd nFIN + 3 + fst nFIN <= iter 6 f_omega2 (f_omega2 8) + 3.
Proof.
  apply sz_score.
  pose proof (f_omega2_id 8) as HB.
  pose proof c4_T3 as HT3. rewrite <- (sz_pair2 (BB11_C4.iter 3 BB11_C4.Zs (1, 3))) in HT3.
  exact (c4_skeleton na1 nQ1 nM1 nT4 nFIN ns2 nc2 (f_omega2 8) HB c4_a1
    (cRnd_it na1 (fst nT3, snd nT3 + 2) (f_omega2 8) HT3 HB)
    (cZs13 (fst nQ1 / 2 + 1)) eq_refl eq_refl (cZs13 ns2)
    (fun t H1 H2 => cRnd_it nc2 (fst nT4, snd nT4 + 2) t (eq_ind_r (fun v => v <= t) H1 (sz_pair2 nT4)) H2)).
Qed.

(** ** The comparison *)

Lemma cmp_tower : forall a b, a <= b -> iter 6 f_omega2 (f_omega2 a) <= iter 8 f_omega2 b.
Proof.
  intros a b Hab. rewrite <- iter_S'.
  pose proof (iter_mono_x f_omega2 f_omega2_mono 7 a b Hab) as H1.
  pose proof (f_omega2_id (iter 7 f_omega2 b)) as H2.
  change (iter 8 f_omega2 b) with (f_omega2 (iter 7 f_omega2 b)). lia.
Qed.

Lemma f36_8 : 8 <= f 3 6.
Proof. pose proof (f_dbl 3 6 ltac:(lia)). lia. Qed.

Lemma cmp_final : forall NC x y n, NC <= x + 3 -> x <= y -> 4 * y + 8 <= n -> NC + 1 < n.
Proof. intros. lia. Qed.

Theorem beats_C4_exact :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ snd nFIN + 3 + fst nFIN + 1 < n.
Proof.
  destruct BB12_P12.score_exact as [c [H1 [H2 H3]]].
  exists c, (snd nP + fst nP + 1).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof N_dom as HN.
  assert (HN' : 4 * iter 8 f_omega2 (f 3 6) + 8 <= snd nP + fst nP + 1) by lia.
  exact (cmp_final _ _ _ _ c4_score_ub (cmp_tower 8 (f 3 6) f36_8) HN').
Qed.

(** C4's exact-score theorem together with the comparison: the number NC of ones on C4's halting tape, plus one,
    is smaller than the number of ones on P12's halting tape. *)
Theorem beats_C4_score :
  exists NC,
    (exists c, Individual112.Individual112.Permute.Flip.Compute.TM.evstep BB11_C4.tm
                 Individual112.Individual112.Permute.Flip.Compute.TM.c0 c /\
               Individual112.Individual112.Permute.Flip.Compute.TM.halted BB11_C4.tm c /\
               BB11_C4.ones c NC) /\
    (exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ NC + 1 < n).
Proof.
  exists (snd nFIN + 3 + fst nFIN).
  split; [exact BB11_C4.score_exact | exact beats_C4_exact].
Qed.
