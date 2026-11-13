(** * Fast-growing hierarchy lower bound for the 11-state machine M11b *)

(** Machine M11b:
      1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_---0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE
    The machine table [tm], the configuration families, the rules and the halting run are imported unchanged
    from BB11_M11b.v (which proves [halt : halts tm c0]).

    Main results (no axioms):
      Theorem score_exact :
        exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa_end + snd pa_end + 4).
      Theorem sigma_lower_bound_m11 :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /        f_omega1 (f_omega (f_omega 5)) < N.
      Theorem sigma_lower_bound_64 :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /        f_omega1 (f_omega 64) < N.
    The comparison with n1 (BB(10)) is in BB11_M11b_vs_n1.v.

    Definitions:
      f 0 n = n + 1, f (k+1) n = (f k)^n (n),
      f_omega n  = f n n,
      f_omega1 n = (f_omega)^n (n)   [= f_(omega+1)(n)]. *)

From BB8 Require Import Individual112.
From BB8 Require Import BB11_M11b.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

(** ** Unfold lemmas before marking functions Opaque *)

Lemma Kc_unfold : forall p a,
  Kc (p, a) = (p + a / 2, W (p - 1) 1).
Proof. Transparent Kc. reflexivity. Qed.

Lemma pa1_val : pa1 = (7 + W 4 1 / 2, W 6 1).
Proof.
  Transparent Kc W.
  unfold pa1. cbn [iter Kc].
  change (8 / 2) with 4.
  change (1 + 4) with 5.
  change (1 - 1) with 0.
  rewrite W_0.
  change ((1 + 3) / 2) with 2.
  change (5 + 2) with 7.
  change (5 - 1) with 4.
  change (7 - 1) with 6.
  reflexivity.
Qed.

(* Re-seal W and Kc at once: with W transparent, conversion below evaluates W 4 1 and W 6 1 in unary. *)
Opaque W Kc.

Definition p'1 : nat := 6 + W 4 1 / 2.
Definition k1 : nat := W 6 1 / 2.
Definition j7_1 : nat := p'1 + k1.
Definition j9_1 : nat := j7_1 + 7.
Definition w9_1 : nat := W j7_1 (W j7_1 (W p'1 1)).
Definition w10_1 : nat := W j9_1 w9_1.
Definition p10_1 : nat := j7_1 + 6.

Lemma pa2_0_val : pa2_0 = (p10_1, W p10_1 1).
Proof.
  unfold pa2_0, br1, Bridge. rewrite pa1_val. cbn [fst snd].
  replace (7 + W 4 1 / 2 - 1) with p'1 by (unfold p'1; lia).
  unfold p10_1, j7_1, k1. reflexivity.
Qed.

Lemma c2_0_val : c2_0 = w10_1 / 2 + 1.
Proof.
  unfold c2_0, br1, Bridge. rewrite pa1_val. cbn [fst snd].
  replace (7 + W 4 1 / 2 - 1) with p'1 by (unfold p'1; lia).
  unfold w10_1, j9_1, w9_1, j7_1, k1. reflexivity.
Qed.

Lemma pa_end_def : pa_end = iter c2_0 Kc pa2_0.
Proof. reflexivity. Qed.

Opaque W Kc pa1 br1 pa2_0 c2_0 pa_end.

(** ** Fast-growing hierarchy up to omega + 1 and tape ones *)

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | O => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.
Definition f_omega1 (n : nat) : nat := iter n f_omega n.

Definition sym_val (s : Sym) : nat :=
  match s with
  | S0 => 0
  | S1 => 1
  end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with
  | [] => 0
  | x :: t => sym_val x + count1 t
  end.

Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl. - reflexivity. - rewrite IHxs. lia. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl. - reflexivity. - rewrite count1_app, IHn. lia. Qed.

Lemma ones_c_end : forall p a, ones (c_end p a) (p + a + 4).
Proof.
  intros p a.
  exists F, ([S1]^^(a + 4) ++ [S0; S1]^^p), (@nil Sym), S0.
  split.
  - unfold c_end. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

Theorem score_exact :
  exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa_end + snd pa_end + 4).
Proof.
  exists (c_end (fst pa_end) (snd pa_end)).
  split; [exact run_end |].
  split; [apply c_end_halted |].
  apply ones_c_end.
Qed.

(** ** Iteration and hierarchy monotonicity *)

Lemma iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

Lemma iter_ge : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_n : forall g, (forall a, a <= g a) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge. exact Hg.
Qed.

Lemma iter_lin1 : forall g, (forall a, 1 <= a -> a + 1 <= g a) -> forall n x, 1 <= x -> x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x Hx; simpl. - lia.
  - specialize (IHn x Hx). specialize (Hg (iter n g x) ltac:(lia)). lia.
Qed.

Lemma iter_dom : forall K g h, (forall n z, K * n <= z -> K * g n <= h z) ->
  forall m n z, K * n <= z -> K * iter m g n <= iter m h z.
Proof. intros K g h Hd. induction m; intros n z Hz; simpl; auto. Qed.

Lemma f_S : forall k n, f (S k) n = iter n (f k) n.
Proof. reflexivity. Qed.

Lemma f_props : forall k, (forall n, n <= f k n) /\ (forall a b, a <= b -> f k a <= f k b).
Proof.
  induction k as [| k [Hid Hmono]].
  - split; intros; simpl; lia.
  - split.
    + intros n. rewrite f_S. apply iter_ge. exact Hid.
    + intros a b Hab. rewrite !f_S. transitivity (iter a (f k) b).
      * apply iter_mono_x; assumption.
      * apply iter_mono_n; assumption.
Qed.

Lemma f_id : forall k n, n <= f k n.
Proof. intros. apply f_props. Qed.

Lemma f_mono : forall k a b, a <= b -> f k a <= f k b.
Proof. intros. apply f_props. assumption. Qed.

Lemma f_gt : forall k n, 1 <= n -> n < f k n.
Proof.
  induction k; intros n Hn.
  - simpl. lia.
  - rewrite f_S. destruct n as [| n']; [lia |].
    simpl. pose proof (iter_ge (f k) (f_id k) n' (S n')).
    specialize (IHk (iter n' (f k) (S n')) ltac:(lia)). lia.
Qed.

Lemma f_level : forall k n, 1 <= n -> f k n <= f (S k) n.
Proof.
  intros k n Hn. rewrite f_S. destruct n as [| n']; [lia |].
  rewrite iter_S'. apply iter_ge. apply f_id.
Qed.

Lemma f_level_mono : forall d k n, 1 <= n -> f k n <= f (d + k) n.
Proof.
  induction d; intros k n Hn. - reflexivity.
  - specialize (IHd k n Hn). pose proof (f_level (d + k) n Hn). change (S d + k) with (S (d + k)). lia.
Qed.

Lemma iter_succ_add : forall n x, iter n S x = n + x.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Lemma f1 : forall n, f 1 n = 2 * n.
Proof. intros. rewrite f_S. rewrite iter_succ_add. lia. Qed.

Lemma f_dbl : forall k n, 1 <= k -> 2 * n <= f k n.
Proof.
  intros k n Hk. destruct n as [| n']. - lia.
  - rewrite <- f1. replace k with ((k - 1) + 1) by lia. apply f_level_mono. lia.
Qed.

Lemma f_omega_id : forall n, n <= f_omega n.
Proof. intros n. unfold f_omega. apply f_id. Qed.

Lemma f_omega_dbl : forall n, 1 <= n -> 2 * n <= f_omega n.
Proof. intros n Hn. unfold f_omega. apply f_dbl. exact Hn. Qed.

Lemma f_omega_mono : forall a b, a <= b -> f_omega a <= f_omega b.
Proof.
  intros [| a'] b Hab.
  - destruct b as [| b'].
    + reflexivity.
    + change (f_omega 0) with 1. pose proof (f_omega_id (S b')). lia.
  - unfold f_omega.
    pose proof (f_level_mono (b - S a') (S a') (S a') ltac:(lia)) as L1.
    replace (b - S a' + S a') with b in L1 by lia.
    pose proof (f_mono b (S a') b Hab). lia.
Qed.

Lemma f_omega1_id : forall n, n <= f_omega1 n.
Proof. intros n. unfold f_omega1. apply iter_ge, f_omega_id. Qed.

Lemma f_omega1_mono : forall a b, a <= b -> f_omega1 a <= f_omega1 b.
Proof.
  intros a b Hab. unfold f_omega1.
  transitivity (iter a f_omega b).
  - apply iter_mono_x; [apply f_omega_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega_id | exact Hab].
Qed.

Lemma f_omega_5_ge_160 : 160 <= f_omega 5.
Proof.
  unfold f_omega.
  assert (H2 : f 2 5 = 160) by (rewrite f_S; cbn [iter]; rewrite !f1; lia).
  pose proof (f_level_mono 3 2 5 ltac:(lia)) as Hlvl.
  change (3 + 2) with 5 in Hlvl. lia.
Qed.

Opaque f f_omega f_omega1.

(** ** Lower bound for W *)

Lemma iter_W0 : forall n x, iter n (W 0) x = x + 3 * n.
Proof. induction n; intros x; simpl. - lia. - rewrite W_0, IHn. lia. Qed.

Lemma W1_val : forall b, W 1 b = 3 * b + 5.
Proof. intros b. rewrite W_S, iter_W0. lia. Qed.

Lemma W_S_0 : forall j, W (S j) 0 = W j 2.
Proof. intros j. rewrite W_S. reflexivity. Qed.

Lemma W_S_1 : forall j, W (S j) 1 = W j (W j 2).
Proof. intros j. rewrite W_S. reflexivity. Qed.

Lemma W_S' : forall j b, W (S j) b = iter b (W j) (W j 2).
Proof. intros j b. rewrite W_S, iter_S'. reflexivity. Qed.

Lemma W_S_2 : forall j, W (S j) 2 = W j (W j (W j 2)).
Proof. intros j. rewrite W_S. reflexivity. Qed.

Lemma W_mono : forall j a b, a <= b -> W j a <= W j b.
Proof.
  induction j as [| j IHj]; intros a b Hab.
  - rewrite !W_0. lia.
  - rewrite !W_S. apply iter_mono_n; [| lia].
    intros x. pose proof (W_grow j x). lia.
Qed.

Lemma pow2_ge : forall j, j + 2 <= 2 ^ (j + 1).
Proof. induction j. - simpl. lia. - change (S j + 1) with (S (j + 1)). rewrite Nat.pow_succ_r'. lia. Qed.

Lemma W_bound_all : forall j,
  (forall n z, 2 ^ (j + 1) * n <= z -> 2 ^ (j + 1) * f (S j) n <= W (S j) z) /\
  2 ^ (j + 2) * (j + 1) <= W (S j) 2.
Proof.
  induction j as [| j [Hw Hx]].
  - split.
    + intros n z Hz. rewrite W1_val, f1. simpl (2 ^ (0 + 1)) in *. lia.
    + rewrite W1_val. simpl. lia.
  - pose proof (pow2_ge j) as HKj.
    set (K := 2 ^ (j + 1)) in *.
    assert (HK1 : 2 ^ (S j + 1) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK2 : 2 ^ (j + 2) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK3 : 2 ^ (S j + 2) = 4 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    rewrite HK2 in Hx.
    assert (HX1 : K * 1 <= W (S j) 2) by nia.
    split.
    + intros n y Hy. rewrite HK1 in *. rewrite W_S', f_S.
      destruct n as [| n']. { cbn [iter]. lia. }
      set (n := S n') in *.
      assert (Hm : 2 * n + 1 <= y) by nia.
      pose proof (iter_dom K (f (S j)) (W (S j)) Hw y 1 (W (S j) 2) HX1) as Hd.
      assert (Hc : 2 * iter n (f (S j)) n <= iter y (f (S j)) 1).
      { transitivity (iter (2 * n + 1) (f (S j)) 1).
        2:{ apply iter_mono_n; [apply f_id | exact Hm]. }
        replace (2 * n + 1) with (1 + (n + n)) by lia. rewrite !iter_add.
        change (iter 1 (f (S j)) ?z) with (f (S j) z).
        pose proof (iter_lin1 (f (S j)) ltac:(intros a Ha; pose proof (f_gt (S j) a Ha); lia) n 1 ltac:(lia)).
        pose proof (iter_mono_x (f (S j)) (f_mono (S j)) n n (iter n (f (S j)) 1) ltac:(lia)).
        pose proof (f_dbl (S j) (iter n (f (S j)) (iter n (f (S j)) 1)) ltac:(lia)).
        lia. }
      nia.
    + rewrite HK3, W_S_2.
      pose proof (Hw (2 * (j + 1)) (W (S j) 2) ltac:(nia)) as H1.
      pose proof (f_dbl (S j) (2 * (j + 1)) ltac:(lia)) as H2.
      pose proof (Hw (4 * (j + 1)) (W (S j) (W (S j) 2)) ltac:(nia)) as H3.
      pose proof (f_dbl (S j) (4 * (j + 1)) ltac:(lia)) as H4.
      nia.
Qed.

Lemma W_omega_bound0 : forall m,
  2 * f_omega (S m) + 3 <= W (S (S m)) 2.
Proof.
  intros m.
  rewrite W_S_2.
  destruct (W_bound_all m) as [Hwb Hx].
  assert (H1 : 2 ^ (m + 1) * (2 * (m + 1)) <= W (S m) 2).
  { replace (m + 2) with (m + 1 + 1) in Hx by lia.
    rewrite Nat.pow_add_r in Hx. simpl (2 ^ 1) in Hx. nia. }
  pose proof (Hwb (2 * (m + 1)) (W (S m) 2) H1) as H2.
  pose proof (W_grow (S m) (W (S m) (W (S m) 2))) as H3.
  assert (H4 : f (S m) (S m) <= f (S m) (2 * (m + 1))) by (apply f_mono; lia).
  assert (H5 : 2 <= 2 ^ (m + 1)) by (pose proof (pow2_ge m); lia).
  Transparent f_omega. unfold f_omega. Opaque f_omega.
  set (P := 2 ^ (m + 1)) in *.
  set (F1 := f (S m) (S m)) in *.
  set (F2 := f (S m) (2 * (m + 1))) in *.
  set (Z := W (S m) (W (S m) (W (S m) 2))) in *.
  nia.
Qed.

Lemma W_omega_bound : forall m,
  4 * f_omega (S m) + 4 <= W (S (S (S m))) 1.
Proof.
  intros m.
  rewrite W_S. cbn [iter].
  pose proof (W_omega_bound0 m) as H0.
  set (Z := W (S (S m)) 2) in *. clearbody Z.
  rewrite W_S.
  pose proof (iter_lin3 (W (S m)) (W_grow (S m)) (S Z) 2).
  lia.
Qed.

(** ** Domination across Kc *)

Lemma Kc_dom1 : forall pa,
  4 <= fst pa -> 4 <= snd pa ->
  fst pa + 2 <= fst (Kc pa) /\
  fst pa + snd pa / 2 <= fst (Kc pa) /\
  4 * f_omega (fst pa - 3) + 4 <= snd (Kc pa).
Proof.
  intros [p a] Hp Ha. rewrite Kc_unfold. cbn [fst snd] in *.
  destruct p as [| [| [| [| m]]]]; try lia.
  replace (S (S (S (S m))) - 1) with (S (S (S m))) by lia.
  replace (S (S (S (S m))) - 3) with (S m) by lia.
  pose proof (W_omega_bound m) as Hw.
  set (z := f_omega (S m)) in *.
  set (w := W (S (S (S m))) 1) in *.
  assert (Hdiv : 2 <= a / 2) by (mods; lia).
  split; [lia | split; lia].
Qed.

Lemma Kc_dom2 : forall pa,
  4 <= fst pa -> 4 <= snd pa ->
  4 <= fst (iter 2 Kc pa) /\
  4 <= snd (iter 2 Kc pa) /\
  f_omega (fst pa - 3) + 4 <= fst (iter 2 Kc pa).
Proof.
  intros pa Hp Ha. cbn [iter].
  destruct (Kc_dom1 pa Hp Ha) as [Hp1 [_ Ha1]].
  assert (Ha1' : 4 <= snd (Kc pa)) by lia.
  destruct (Kc_dom1 (Kc pa) ltac:(lia) Ha1') as [Hp2 [Hdiv2 Ha2]].
  assert (Hq : 2 * f_omega (fst pa - 3) + 2 <= snd (Kc pa) / 2)
    by (set (z := f_omega (fst pa - 3)) in *; set (s := snd (Kc pa)) in *; mods; lia).
  split; [lia | split; [lia | lia]].
Qed.

Lemma Kc_dom_even : forall k pa,
  4 <= fst pa -> 4 <= snd pa ->
  4 <= fst (iter (2 * k) Kc pa) /\
  4 <= snd (iter (2 * k) Kc pa) /\
  iter k f_omega (fst pa - 3) <= fst (iter (2 * k) Kc pa) - 3.
Proof.
  induction k as [| k IHk]; intros pa Hp Ha.
  - change (2 * 0) with 0. cbn [iter]. split; [lia | split; [lia | lia]].
  - replace (2 * S k) with (2 + 2 * k) by lia.
    rewrite iter_add.
    change (iter (S k) f_omega (fst pa - 3)) with (f_omega (iter k f_omega (fst pa - 3))).
    destruct (IHk pa Hp Ha) as [Hp1 [Ha1 Hdom1]].
    destruct (Kc_dom2 (iter (2 * k) Kc pa) Hp1 Ha1) as [Hp2 [Ha2 Hdom2]].
    pose proof (f_omega_mono _ _ Hdom1).
    split; [exact Hp2 | split; [exact Ha2 | lia]].
Qed.

Lemma Kc_dom_any : forall c' pa,
  4 <= fst pa -> 4 <= snd pa ->
  4 <= fst (iter c' Kc pa) /\
  4 <= snd (iter c' Kc pa) /\
  iter (c' / 2) f_omega (fst pa - 3) <= fst (iter c' Kc pa) - 3.
Proof.
  intros c' pa Hp Ha.
  assert (Hc : c' = 2 * (c' / 2) \/ c' = 1 + 2 * (c' / 2)) by (mods; lia).
  set (k := c' / 2) in *.
  destruct Hc as [Hev | Hodd].
  - rewrite Hev. apply Kc_dom_even; assumption.
  - rewrite Hodd. rewrite iter_add. cbn [iter].
    destruct (Kc_dom_even k pa Hp Ha) as [Hp1 [Ha1 Hdom1]].
    destruct (Kc_dom1 (iter (2 * k) Kc pa) Hp1 Ha1) as [Hp2 [_ Ha2]].
    split; [lia | split; [lia | lia]].
Qed.

(** ** Phase 1, Bridge, and Phase 2 lower bounds for M11 *)

Lemma W6_1_bound : 32 * f_omega 5 <= W 6 1.
Proof.
  rewrite (W_S_1 5).
  destruct (W_bound_all 4) as [Hwb Hx].
  simpl (2 ^ (4 + 1)) in Hwb.
  simpl (2 ^ (4 + 2) * (4 + 1)) in Hx.
  pose proof (Hwb 10 (W 5 2) ltac:(lia)) as H1.
  assert (H2 : f 5 5 <= f 5 10) by (apply f_mono; lia).
  Transparent f_omega. unfold f_omega. Opaque f_omega.
  lia.
Qed.

Lemma k1_bound : 16 * f_omega 5 <= k1.
Proof.
  unfold k1.
  pose proof W6_1_bound as Hw.
  set (z := f_omega 5) in *.
  set (w := W 6 1) in *.
  mods; lia.
Qed.

Lemma p10_1_bound : f_omega 5 + 12 <= p10_1.
Proof.
  unfold p10_1, j7_1, p'1.
  pose proof k1_bound.
  pose proof f_omega_5_ge_160.
  lia.
Qed.

Lemma j9_1_bound : f_omega 5 + 13 <= j9_1.
Proof.
  unfold j9_1, j7_1, p'1.
  pose proof k1_bound.
  pose proof f_omega_5_ge_160.
  lia.
Qed.

Lemma w10_1_bound : 4 * f_omega (f_omega 5) + 4 <= w10_1.
Proof.
  unfold w10_1.
  assert (Hw9 : 1 <= w9_1) by (unfold w9_1; pose proof (W_grow j7_1 (W j7_1 (W p'1 1))); lia).
  pose proof (W_mono j9_1 1 w9_1 Hw9) as Hmono.
  pose proof j9_1_bound as Hj9.
  pose proof f_omega_5_ge_160 as Hf5.
  destruct j9_1 as [| [| [| [| m]]]]; try lia.
  pose proof (W_omega_bound (S m)) as Hwb.
  assert (Hm : f_omega 5 <= S (S m)) by lia.
  pose proof (f_omega_mono (f_omega 5) (S (S m)) Hm) as Hfm.
  lia.
Qed.

Lemma c2_0_bound : 2 * f_omega (f_omega 5) + 3 <= c2_0.
Proof.
  rewrite c2_0_val.
  pose proof w10_1_bound as Hw.
  set (z := f_omega (f_omega 5)) in *.
  set (w := w10_1) in *.
  mods; lia.
Qed.

Lemma pa_end_bound : f_omega1 (f_omega (f_omega 5)) + 3 <= fst pa_end.
Proof.
  rewrite pa_end_def, pa2_0_val.
  set (M := f_omega (f_omega 5)).
  pose proof f_omega_5_ge_160 as Hf5.
  pose proof (f_omega_id (f_omega 5)) as HM_ge. fold M in HM_ge.
  pose proof p10_1_bound as Hp10.
  pose proof (W_grow p10_1 1) as Ha10.
  pose proof c2_0_bound as Hc2. fold M in Hc2.
  replace c2_0 with ((c2_0 - 2) + 2) by lia.
  rewrite iter_add.
  destruct (Kc_dom2 (p10_1, W p10_1 1) ltac:(cbn [fst snd]; lia) ltac:(cbn [fst snd]; lia))
    as [Hp_mid [Ha_mid Hdom_mid]].
  cbn [fst snd] in Hdom_mid.
  assert (HM_mid : M <= f_omega (p10_1 - 3))
    by (unfold M; apply f_omega_mono; lia).
  set (pa_mid := iter 2 Kc (p10_1, W p10_1 1)) in *.
  destruct (Kc_dom_any (c2_0 - 2) pa_mid Hp_mid Ha_mid)
    as [Hp_end [Ha_end Hdom_end]].
  assert (Hdiv : M <= (c2_0 - 2) / 2)
    by (set (c' := c2_0 - 2) in *; mods; lia).
  assert (Hiter : f_omega1 M <= iter ((c2_0 - 2) / 2) f_omega (fst pa_mid - 3)).
  { Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
    transitivity (iter M f_omega (fst pa_mid - 3)).
    - apply iter_mono_x; [apply f_omega_mono | lia].
    - apply iter_mono_n; [apply f_omega_id | exact Hdiv]. }
  lia.
Qed.

Theorem sigma_lower_bound_m11 :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  f_omega1 (f_omega (f_omega 5)) < N.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (fst pa_end + snd pa_end + 4).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof pa_end_bound. lia.
Qed.

Theorem sigma_lower_bound_64 :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  f_omega1 (f_omega 64) < N.
Proof.
  destruct sigma_lower_bound_m11 as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N.
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof f_omega_5_ge_160 as Hf5.
  assert (H64 : f_omega 64 <= f_omega (f_omega 5)) by (apply f_omega_mono; lia).
  pose proof (f_omega1_mono _ _ H64).
  lia.
Qed.

Print Assumptions score_exact.
Print Assumptions sigma_lower_bound_m11.
Print Assumptions sigma_lower_bound_64.
