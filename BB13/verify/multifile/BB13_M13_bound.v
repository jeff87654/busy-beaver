(** * A machine-checked score lower bound for the 13-state machine M13 *)

(** Machine M13 (in canonical Tree Normal Form):
      1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_0LG1RI_1RE0RH_1LF0RC_1RM0LE_1LA1LE_0LL1LB_0RM1LL_1RZ1RH
    The machine table [tm], the configuration families, the rules and the halting run are imported unchanged
    from BB13_M13.v (which proves [halt : halts tm c0] and passes check.py).

    Main results (no axioms):
      Theorem score_exact :
        exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa2 + snd pa2 + 5).
      Theorem sigma_lower_bound :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        f_omega2 20 < N + 1.
      Theorem sigma_lower_bound_strong :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        f_omega2 (f_omega 20) < N + 1.

    Definitions:
      f 0 n = n + 1, f (k+1) n = (f k)^n (n),
      f_omega n  = f n n,
      f_omega1 n = (f_omega)^n (n)   [= f_(omega+1)(n)],
      f_omega2 n = (f_omega1)^n (n)  [= f_(omega+2)(n)]. *)

From BB8 Require Import Individual132.
From BB8 Require Import BB13_M13.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_0LG1RI_1RE0RH_1LF0RC_1RM0LE_1LA1LE_0LL1LB_0RM1LL_1RZ1RH *)
Lemma tm_table :
  tm (A, 0) = Some (1, TM.L, B) /\ tm (A, 1) = Some (1, TM.L, A) /\
  tm (B, 0) = Some (1, TM.R, C) /\ tm (B, 1) = Some (0, TM.L, A) /\
  tm (C, 0) = Some (1, TM.R, D) /\ tm (C, 1) = Some (1, TM.R, C) /\
  tm (D, 0) = Some (1, TM.R, E) /\ tm (D, 1) = Some (1, TM.R, K) /\
  tm (E, 0) = Some (1, TM.R, F) /\ tm (E, 1) = Some (0, TM.L, J) /\
  tm (F, 0) = Some (0, TM.L, G) /\ tm (F, 1) = Some (1, TM.R, I) /\
  tm (G, 0) = Some (1, TM.R, E) /\ tm (G, 1) = Some (0, TM.R, H) /\
  tm (H, 0) = Some (1, TM.L, F) /\ tm (H, 1) = Some (0, TM.R, C) /\
  tm (I, 0) = Some (1, TM.R, M) /\ tm (I, 1) = Some (0, TM.L, E) /\
  tm (J, 0) = Some (1, TM.L, A) /\ tm (J, 1) = Some (1, TM.L, E) /\
  tm (K, 0) = Some (0, TM.L, L) /\ tm (K, 1) = Some (1, TM.L, B) /\
  tm (L, 0) = Some (0, TM.R, M) /\ tm (L, 1) = Some (1, TM.L, L) /\
  tm (M, 0) = None              /\ tm (M, 1) = Some (1, TM.R, H).
Proof. repeat split. Qed.

Local Open Scope nat_scope.

(** Unfold lemmas before marking functions Opaque *)
Lemma Kc_unfold : forall p a,
  Kc (p, a) = (p + a / 2, W (p - 1) 1).
Proof. Transparent Kc. reflexivity. Qed.

Lemma Kd_step_unfold : forall p a,
  Kd_step (p, a) = iter (a / 2 + 1) Kc (p - 1, 2).
Proof. Transparent Kd_step. reflexivity. Qed.

Lemma Kd_iter_unfold : forall m pa,
  Kd_iter m pa = iter m Kd_step pa.
Proof. Transparent Kd_iter. reflexivity. Qed.

Lemma D_reload_unfold : forall p a,
  D_reload (p, a) = Kc (p - 2, 2).
Proof. Transparent D_reload. reflexivity. Qed.

Opaque W Kc Kd_step Kd_iter D_reload pa1 pa2_0 pa2.

(** ** Fast-growing hierarchy up to omega + 2 and tape ones *)

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | O => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.
Definition f_omega1 (n : nat) : nat := iter n f_omega n.
Definition f_omega2 (n : nat) : nat := iter n f_omega1 n.

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

Lemma ones_c_end : forall p a, ones (c_end p a) (p + a + 5).
Proof.
  intros p a.
  exists M, ([S1]^^(a + 5) ++ [S0; S1]^^p), (@nil Sym), S0.
  split.
  - unfold c_end. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

Theorem score_exact :
  exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa2 + snd pa2 + 5).
Proof.
  exists (c_end (fst pa2) (snd pa2)).
  split; [exact run_pa2 |].
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

Lemma f_omega2_id : forall n, n <= f_omega2 n.
Proof. intros n. unfold f_omega2. apply iter_ge, f_omega1_id. Qed.

Lemma f_omega2_mono : forall a b, a <= b -> f_omega2 a <= f_omega2 b.
Proof.
  intros a b Hab. unfold f_omega2.
  transitivity (iter a f_omega1 b).
  - apply iter_mono_x; [apply f_omega1_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega1_id | exact Hab].
Qed.

Opaque f f_omega f_omega1 f_omega2.

(** ** Lower bound for W *)

Lemma iter_W0 : forall n x, iter n (W 0) x = x + 3 * n.
Proof. induction n; intros x; simpl. - lia. - rewrite W_0, IHn. lia. Qed.

Lemma W1_val : forall b, W 1 b = 3 * b + 5.
Proof. intros b. rewrite W_S, iter_W0. lia. Qed.

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

(** ** Domination across Kc, Kd_step, Kd_iter, and D_reload *)

Lemma Kc_dom1 : forall pa,
  4 <= fst pa -> 2 <= snd pa ->
  fst pa + 1 <= fst (Kc pa) /\
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
  assert (Hdiv : 1 <= a / 2) by (mods; lia).
  split; [lia | split; lia].
Qed.

Lemma Kc_dom2 : forall pa,
  4 <= fst pa -> 2 <= snd pa ->
  4 <= fst (iter 2 Kc pa) /\
  2 <= snd (iter 2 Kc pa) /\
  f_omega (fst pa - 3) + 4 <= fst (iter 2 Kc pa).
Proof.
  intros pa Hp Ha. cbn [iter].
  destruct (Kc_dom1 pa Hp Ha) as [Hp1 [_ Ha1]].
  assert (Ha1' : 2 <= snd (Kc pa)) by lia.
  destruct (Kc_dom1 (Kc pa) ltac:(lia) Ha1') as [Hp2 [Hdiv2 Ha2]].
  assert (Hq : 2 * f_omega (fst pa - 3) + 2 <= snd (Kc pa) / 2)
    by (set (z := f_omega (fst pa - 3)) in *; set (s := snd (Kc pa)) in *; mods; lia).
  split; [lia | split; [lia | lia]].
Qed.

Lemma Kc_dom_even : forall k pa,
  4 <= fst pa -> 2 <= snd pa ->
  4 <= fst (iter (2 * k) Kc pa) /\
  2 <= snd (iter (2 * k) Kc pa) /\
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
  4 <= fst pa -> 2 <= snd pa ->
  4 <= fst (iter c' Kc pa) /\
  2 <= snd (iter c' Kc pa) /\
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

Definition ok_pa (n : nat) (pa : nat * nat) : Prop :=
  n <= fst pa - 4 /\ n <= snd pa / 4.

Lemma Kd_step_dom : forall n pa,
  1 <= n -> ok_pa n pa -> ok_pa (f_omega1 n) (Kd_step pa).
Proof.
  intros n [p a] Hn [Hp Ha]. unfold ok_pa in *. cbn [fst snd] in *.
  rewrite Kd_step_unfold.
  replace (a / 2 + 1) with (S (a / 2)) by lia. cbn [iter].
  destruct (Kc_dom_any (a / 2) (p - 1, 2) ltac:(cbn; lia) ltac:(cbn; lia)) as [Hp1 [Ha1 Hdom1]].
  cbn [fst snd] in Hdom1. replace (p - 1 - 3) with (p - 4) in Hdom1 by lia.
  destruct (Kc_dom1 (iter (a / 2) Kc (p - 1, 2)) Hp1 Ha1) as [Hp2 [_ Ha2]].
  assert (Hdiv : n <= (a / 2) / 2) by (mods; lia).
  assert (H1 : f_omega1 n <= iter ((a / 2) / 2) f_omega (p - 4)).
  { Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
    transitivity (iter n f_omega (p - 4)).
    - apply iter_mono_x; [apply f_omega_mono | exact Hp].
    - apply iter_mono_n; [apply f_omega_id | exact Hdiv]. }
  set (pa' := iter (a / 2) Kc (p - 1, 2)) in *.
  assert (H2 : f_omega (fst pa' - 3) <= snd (Kc pa') / 4)
    by (set (z := f_omega (fst pa' - 3)) in *; set (s := snd (Kc pa')) in *; mods; lia).
  pose proof (f_omega_id (fst pa' - 3)).
  split; lia.
Qed.

Lemma Kd_iter_dom : forall m n pa,
  1 <= n -> ok_pa n pa -> ok_pa (iter m f_omega1 n) (Kd_iter m pa).
Proof.
  intros m n pa. rewrite Kd_iter_unfold.
  induction m as [| m IHm]; intros Hn Hok.
  - cbn [iter]. exact Hok.
  - cbn [iter]. apply Kd_step_dom.
    + pose proof (iter_ge f_omega1 f_omega1_id m n). lia.
    + apply IHm; assumption.
Qed.

(** ** Round 1 and Round 2 lower bounds *)

Lemma Kc_3_2 : Kc (3, 2) = (4, 38).
Proof. Transparent Kc W. reflexivity. Qed.
Opaque W Kc.

Lemma Kc_init2 :
  fst (iter 2 Kc (3, 2)) = 23 /\ 2 <= snd (iter 2 Kc (3, 2)).
Proof.
  cbn [iter]. rewrite Kc_3_2.
  rewrite (Kc_unfold 4 38). cbn [fst snd].
  change (4 + 38 / 2) with 23. change (4 - 1) with 3.
  pose proof (W_grow 3 1) as Hwg.
  set (w := W 3 1) in *. clearbody w. lia.
Qed.

Lemma Kc_dom_step3 : forall m pa0,
  fst pa0 = S m + 3 -> 2 <= snd pa0 ->
  f_omega (S m) + 5 <= fst (Kc (iter 2 Kc pa0)) /\
  f_omega (S m) <= snd (Kc (iter 2 Kc pa0)) / 2.
Proof.
  intros m pa0 Hp0 Ha0.
  destruct (Kc_dom2 pa0 ltac:(lia) Ha0) as [Hp1 [Ha1 Hdom1]].
  replace (fst pa0 - 3) with (S m) in Hdom1 by lia.
  destruct (Kc_dom1 (iter 2 Kc pa0) Hp1 Ha1) as [Hp2 [_ Ha2]].
  set (pa' := iter 2 Kc pa0) in *.
  pose proof (f_omega_id (fst pa' - 3)).
  pose proof (f_omega_id (S m)).
  assert (Hq : 2 * f_omega (fst pa' - 3) <= snd (Kc pa') / 2)
    by (set (z := f_omega (fst pa' - 3)) in *; set (s := snd (Kc pa')) in *; mods; lia).
  split; lia.
Qed.

Lemma pa1_bounds :
  f_omega 20 + 5 <= fst pa1 /\ f_omega 20 <= snd pa1 / 2.
Proof.
  rewrite pa1_def, Kd_step_unfold.
  change (4 - 1) with 3. change (8 / 2 + 1) with (S (2 + 2)).
  cbn [iter]. rewrite iter_add.
  destruct Kc_init2 as [Hp0 Ha0].
  exact (Kc_dom_step3 19 (iter 2 Kc (3, 2)) Hp0 Ha0).
Qed.

Lemma f_omega_pos : forall m, 1 <= m -> 1 <= f_omega m.
Proof. intros m Hm. pose proof (f_omega_id m). lia. Qed.

Lemma f_omega_20_pos : 1 <= f_omega 20.
Proof. apply f_omega_pos. lia. Qed.

Lemma ok_pa_mono : forall m n pa,
  m <= n -> ok_pa n pa -> ok_pa m pa.
Proof. intros m n pa Hmn [H1 H2]. split; lia. Qed.

Lemma ok_pa_score_lt : forall B pa,
  ok_pa B pa -> B < fst pa + snd pa + 5 + 1.
Proof. intros B [p a] [Hp Ha]. cbn [fst snd] in *. mods; lia. Qed.

Lemma D_reload_dom : forall n pa,
  1 <= n -> n + 5 <= fst pa -> ok_pa n (D_reload pa).
Proof.
  intros n [p a] Hn Hp. cbn [fst snd] in *.
  rewrite D_reload_unfold, Kc_unfold. cbn [fst snd].
  change (2 / 2) with 1.
  destruct p as [| [| [| [| [| [| m]]]]]]; try lia.
  replace (S (S (S (S (S (S m))))) - 2 - 1) with (S (S (S m))) by lia.
  pose proof (W_omega_bound m) as Hw.
  pose proof (f_omega_id (S m)) as Hid.
  unfold ok_pa. cbn [fst snd].
  set (z := f_omega (S m)) in *.
  set (w := W (S (S (S m))) 1) in *.
  mods; lia.
Qed.

Lemma round2_dom : forall n pa,
  1 <= n -> n + 5 <= fst pa -> n <= snd pa / 2 ->
  ok_pa (f_omega2 n) (Kd_iter (snd pa / 2) (D_reload pa)).
Proof.
  intros n pa Hn Hp Ha.
  pose proof (D_reload_dom n pa Hn Hp) as Hrel.
  pose proof (Kd_iter_dom (snd pa / 2) n (D_reload pa) Hn Hrel) as Hloop.
  eapply ok_pa_mono; [| exact Hloop].
  Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
  apply iter_mono_n; [apply f_omega1_id | exact Ha].
Qed.

Lemma pa2_dom_strong :
  ok_pa (f_omega2 (f_omega 20)) pa2.
Proof.
  rewrite pa2_def, pa2_0_def.
  destruct pa1_bounds as [Hp Ha].
  exact (round2_dom (f_omega 20) pa1 f_omega_20_pos Hp Ha).
Qed.

Lemma pa2_dom :
  ok_pa (f_omega2 20) pa2.
Proof.
  eapply ok_pa_mono; [| exact pa2_dom_strong].
  apply f_omega2_mono. apply f_omega_id.
Qed.

Theorem sigma_lower_bound_strong :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  f_omega2 (f_omega 20) < N + 1.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (fst pa2 + snd pa2 + 5).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  apply ok_pa_score_lt. exact pa2_dom_strong.
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  f_omega2 20 < N + 1.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (fst pa2 + snd pa2 + 5).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  apply ok_pa_score_lt. exact pa2_dom.
Qed.
