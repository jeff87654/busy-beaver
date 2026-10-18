(** * A machine-checked score lower bound for the 9-state f_omega^2 champion *)

(** Machine:
      1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA
    The machine table [tm], the digit family [Kd], the rules and the 3-cascade run are imported unchanged from
    BB9_fw2_1RB0RD.v (which proves [halt : halts tm c0] and passes check.py).

    Main results (no axioms):
      Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (b3 + 3).
      Theorem sigma_lower_bound :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega (f_omega 465009) < N + 1.
      Theorem sigma_lower_bound_strong : exists c N b, c0 -->* c /\ halted tm c /\ ones c N /\
        2 ^ 465010 * f_omega 465009 <= b /\ b mod 8 = 7 /\ f_omega (3 * (b / 4) + 3) < N + 1.     (b = b2)

    Definitions as in BB9_champion_bound.v and BB10_champion_bound.v:
      f 0 n = n + 1, f (k+1) n = (f k)^n (n), f_omega n = f n n;
      [ones c N]: the tape of c holds exactly N ones.  busycoq stops before the halting transition I0 = 1RZ, which
      writes one more 1 (the head reads 0 in [c_end]), so the standard score is N + 1 = b3 + 4. *)

From BB8 Require Import Individual92.
From BB8 Require Import BB9_fw2_1RB0RD.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(** The imported [tm] is the declared machine (BB9_fw2_1RB0RD.v passes check.py, which checks this). *)
(* machine: 1RB0RD_1LC1LC_0RA0LB_1RE1RD_0LG0LF_1LE1LF_0RH1LG_1RD1RI_1RZ1RA *)
Lemma tm_table :
  tm (A, 0) = Some (1, R, B) /\ tm (A, 1) = Some (0, R, D) /\
  tm (B, 0) = Some (1, L, C) /\ tm (B, 1) = Some (1, L, C) /\
  tm (C, 0) = Some (0, R, A) /\ tm (C, 1) = Some (0, L, B) /\
  tm (D, 0) = Some (1, R, E) /\ tm (D, 1) = Some (1, R, D) /\
  tm (E, 0) = Some (0, L, G) /\ tm (E, 1) = Some (0, L, F) /\
  tm (F, 0) = Some (1, L, E) /\ tm (F, 1) = Some (1, L, F) /\
  tm (G, 0) = Some (0, R, H) /\ tm (G, 1) = Some (1, L, G) /\
  tm (H, 0) = Some (1, R, D) /\ tm (H, 1) = Some (1, R, I) /\
  tm (I, 0) = None           /\ tm (I, 1) = Some (1, R, A).
Proof. repeat split. Qed.

Local Open Scope nat_scope.

(** Never let a tactic compute these numbers (Opaque declarations are not exported by the imported file). *)
Opaque U X Tv b1 b2 b3.

(** ** Definitions used in the statement *)

(** The fast-growing hierarchy: f 0 n = n + 1, f (k+1) n = (f k)^n (n), f_omega n = f n n. *)
Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | O => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.

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

(** [ones c N]: the tape of c is L (reversed, left of the head), s (head cell), R (right of the head),
    with 0s beyond both lists, and N = number of 1s in L, s, R. *)
Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_blocks : forall m, count1 ([S0; S1; S1]^^m) = 2 * m.
Proof. induction m. - reflexivity. - simpl. rewrite IHm. lia. Qed.

Lemma ones_c_end : forall m, ones (c_end m) (2 * m + 3).
Proof.
  intros m. exists I, ([S1; S0; S1; S1] ++ [S0; S1; S1]^^m), (@nil Sym), S0. split.
  - reflexivity.
  - simpl. rewrite count1_blocks. lia.
Qed.

(** Domination of iterates through the scaling z >= K n. *)
Lemma iter_dom : forall K g h, (forall n z, K * n <= z -> K * g n <= h z) ->
  forall m n z, K * n <= z -> K * iter m g n <= iter m h z.
Proof. intros K g h Hd. induction m; intros n z Hz; simpl; auto. Qed.

(** ** The fast-growing hierarchy: basic facts *)

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

Lemma f_8x : forall d, 3 <= d -> 8 * d <= f (S d) d.
Proof.
  intros d Hd. rewrite f_S.
  pose proof (iter_mono_n (f d) (f_id d) 3 d d Hd) as H1.
  cbn [iter] in H1.
  pose proof (f_dbl d d ltac:(lia)) as D1.
  pose proof (f_dbl d (f d d) ltac:(lia)) as D2.
  pose proof (f_dbl d (f d (f d d)) ltac:(lia)) as D3.
  lia.
Qed.

Opaque f.

(** ** The lower bound for U: level j+1 of the fast-growing hierarchy, with scaling 2^(j+1) *)

Lemma pow2_ge : forall j, j + 2 <= 2 ^ (j + 1).
Proof. induction j. - simpl. lia. - change (S j + 1) with (S (j + 1)). rewrite Nat.pow_succ_r'. lia. Qed.

Lemma bound : forall j,
  (forall n z, 2 ^ (j + 1) * n <= z -> 2 ^ (j + 1) * f (S j) n <= U j z) /\
  2 ^ (j + 2) * (j + 1) <= X j.
Proof.
  induction j as [| j [Hu Hx]].
  - split.
    + intros n z Hz. rewrite U_0, f1. simpl (2 ^ (0 + 1)) in *. lia.
    + rewrite X_0. simpl. lia.
  - pose proof (pow2_ge j) as HKj.
    set (K := 2 ^ (j + 1)) in *.
    assert (HK1 : 2 ^ (S j + 1) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK2 : 2 ^ (j + 2) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK3 : 2 ^ (S j + 2) = 4 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    rewrite HK2 in Hx.
    assert (HX1 : K * 1 <= X j) by nia.
    split.
    + intros n y Hy. rewrite HK1 in *. rewrite U_S, f_S.
      destruct n as [| n']. { simpl. lia. }
      set (n := S n') in *.
      assert (Hm : 2 * n + 1 <= y - 2 * j) by nia.
      pose proof (iter_dom K (f (S j)) (U j) Hu (y - 2 * j) 1 (X j) HX1) as Hd.
      assert (Hc : 2 * iter n (f (S j)) n <= iter (y - 2 * j) (f (S j)) 1).
      { transitivity (iter (2 * n + 1) (f (S j)) 1).
        2:{ apply iter_mono_n; [apply f_id | exact Hm]. }
        replace (2 * n + 1) with (1 + (n + n)) by lia. rewrite !iter_add.
        change (iter 1 (f (S j)) ?z) with (f (S j) z).
        pose proof (iter_lin1 (f (S j)) ltac:(intros a Ha; pose proof (f_gt (S j) a Ha); lia) n 1 ltac:(lia)).
        pose proof (iter_mono_x (f (S j)) (f_mono (S j)) n n (iter n (f (S j)) 1) ltac:(lia)).
        pose proof (f_dbl (S j) (iter n (f (S j)) (iter n (f (S j)) 1)) ltac:(lia)).
        lia. }
      nia.
    + rewrite HK3, X_S.
      pose proof (Hu (2 * (j + 1)) (X j) ltac:(nia)) as H1.
      pose proof (f_dbl (S j) (2 * (j + 1)) ltac:(lia)) as H2.
      pose proof (Hu (4 * (j + 1)) (U j (X j)) ltac:(nia)) as H3.
      pose proof (f_dbl (S j) (4 * (j + 1)) ltac:(lia)) as H4.
      nia.
Qed.

Lemma Ubound : forall j n z, 2 ^ (j + 1) * n <= z -> 2 ^ (j + 1) * f (S j) n <= U j z.
Proof. intro j. apply (proj1 (bound j)). Qed.

Lemma Xbound : forall j, 2 ^ (j + 2) * (j + 1) <= X j.
Proof. intro j. apply (proj2 (bound j)). Qed.

(** ** The clearings of trip m, from below *)

Lemma Tpre_last : forall m j B,
  Tpre (S m) j B = U (j + 3 * m + 2) (U (j + 3 * m + 2) (U (j + 3 * m + 1) (Tpre m j B))).
Proof.
  induction m; intros j B.
  - cbn [Tpre]. replace (j + 3 * 0 + 2) with (j + 2) by lia.
    replace (j + 3 * 0 + 1) with (j + 1) by lia. reflexivity.
  - change (Tpre (S (S m)) j B) with (Tpre (S m) (j + 3) (U (j + 2) (U (j + 2) (U (j + 1) B)))).
    rewrite IHm. cbn [Tpre].
    replace (j + 3 + 3 * m + 2) with (j + 3 * S m + 2) by lia.
    replace (j + 3 + 3 * m + 1) with (j + 3 * S m + 1) by lia.
    reflexivity.
Qed.

Lemma Tv_unfold : forall m j B, Tv m j B = U (j + 3 * m + 2) (U (j + 3 * m + 1) (Tpre m j B)).
Proof. Transparent Tv. reflexivity. Qed.
Opaque Tv.

(** General lower bound for clearing trip m from depth 1: Tv m 1 37 >= 2^(3m+4) * f_omega(3m+3) for m >= 1 *)
Lemma Tv_big : forall m, 1 <= m -> 2 ^ (3 * m + 4) * f_omega (3 * m + 3) <= Tv m 1 37.
Proof.
  intros [| m'] Hm; [lia |].
  rewrite Tv_unfold, (Tpre_last m' 1 37).
  set (m := S m').
  replace (1 + 3 * m' + 2) with (3 * m) by (unfold m; lia).
  replace (1 + 3 * m + 1) with (3 * m + 2) by lia.
  replace (1 + 3 * m + 2) with (3 * m + 3) by lia.
  unfold f_omega.
  replace (3 * m + 4) with (3 * m + 3 + 1) by lia.
  set (D2 := 3 * m + 3).
  set (D1 := 3 * m + 2).
  set (D0 := 3 * m).
  set (u := U (1 + 3 * m' + 1) (Tpre m' 1 37)).
  assert (HD0 : D0 = S (3 * m' + 2)) by (unfold D0, m; lia).
  pose proof (U_ge_X (3 * m' + 2) u) as Hx. rewrite <- HD0 in Hx.
  pose proof (Xbound (3 * m' + 2)) as HX.
  replace (3 * m' + 2 + 2) with (D0 + 1) in HX by (unfold D0, m; lia).
  replace (3 * m' + 2 + 1) with D0 in HX by (unfold D0, m; lia).
  assert (Hu : 2 ^ (D0 + 1) * D0 <= U D0 u) by lia.
  pose proof (Ubound D0 D0 (U D0 u) Hu) as Hw.
  pose proof (f_8x D0 ltac:(unfold D0, m; lia)) as H8.
  assert (Hp1 : 2 ^ (D1 + 1) = 4 * 2 ^ (D0 + 1)).
  { replace (D1 + 1) with ((D0 + 1) + 2) by (unfold D0, D1; lia).
    rewrite Nat.pow_add_r. change (2 ^ 2) with 4. lia. }
  assert (Hw' : 2 ^ (D1 + 1) * D2 <= U D0 (U D0 u)).
  { rewrite Hp1. assert (4 * D2 <= 8 * D0) by (unfold D0, D2, m; lia).
    set (P0 := 2 ^ (D0 + 1)) in *. set (F0 := f (S D0) D0) in *. set (W := U D0 (U D0 u)) in *. nia. }
  pose proof (Ubound D1 D2 (U D0 (U D0 u)) Hw') as HU1.
  pose proof (f_dbl (S D1) D2 ltac:(unfold D1; lia)) as Hd1.
  assert (Hp2 : 2 ^ (D2 + 1) = 2 * 2 ^ (D1 + 1)).
  { replace (D2 + 1) with ((D1 + 1) + 1) by (unfold D1, D2; lia).
    rewrite Nat.pow_add_r. change (2 ^ 1) with 2. lia. }
  assert (HU1' : 2 ^ (D2 + 1) * D2 <= U D1 (U D0 (U D0 u))).
  { rewrite Hp2. set (P1 := 2 ^ (D1 + 1)) in *. set (F1 := f (S D1) D2) in *.
    set (W1 := U D1 (U D0 (U D0 u))) in *. nia. }
  pose proof (Ubound D2 D2 (U D1 (U D0 (U D0 u))) HU1') as HU2.
  pose proof (f_level D2 D2 ltac:(unfold D2; lia)) as Hl2.
  set (P2 := 2 ^ (D2 + 1)) in *. set (F2 := f (S D2) D2) in *. set (F2' := f D2 D2) in *.
  set (W2 := U D2 (U D1 (U D0 (U D0 u)))) in *. nia.
Qed.

Lemma iter3_U0 : forall x, iter 3 (U 0) x = 27 * x + 91.
Proof. intros. cbn [iter]. rewrite !U_0. lia. Qed.

Lemma iter4_U0 : forall x, iter 4 (U 0) x = 81 * x + 280.
Proof. intros. cbn [iter]. rewrite !U_0. lia. Qed.

Lemma b1_div4 : b1 / 4 = 155 * 1000 + 2.
Proof.
  assert (Hb1 : b1 = 4 * (155 * 1000 + 2) + 3).
  { rewrite b1_def, U1_x.
    replace 10 with (3 + (3 + 4)) by lia.
    rewrite !iter_add, iter4_U0, !iter3_U0. lia. }
  pose proof (Nat.div_mod_eq b1 4).
  pose proof (Nat.mod_upper_bound b1 4 ltac:(lia)).
  lia.
Qed.

Lemma b2_big : 2 ^ (3 * (b1 / 4) + 4) * f_omega (465 * 1000 + 9) <= b2.
Proof.
  rewrite b2_def. unfold second.
  pose proof (Tv_big (b1 / 4) ltac:(pose proof b1_div4; lia)) as H.
  replace (3 * (b1 / 4) + 3) with (465 * 1000 + 9) in H by (pose proof b1_div4; lia).
  exact H.
Qed.

Lemma quarter_aux : forall b y P, P * y <= b -> 4 <= P -> y <= b / 4.
Proof. intros b y P H1 H2. apply Nat.div_le_lower_bound; [lia | nia]. Qed.

Lemma b2_quarter : f_omega (465 * 1000 + 9) <= b2 / 4.
Proof.
  assert (Hp : 2 ^ 2 <= 2 ^ (3 * (b1 / 4) + 4)) by (apply Nat.pow_le_mono_r; lia).
  change (2 ^ 2) with 4 in Hp.
  exact (quarter_aux b2 _ _ b2_big Hp).
Qed.

Lemma b3_big : f_omega (3 * (b2 / 4) + 3) <= b3.
Proof.
  rewrite b3_def. unfold second.
  pose proof b2_quarter as Hq.
  assert (Hm : 1 <= b2 / 4).
  { unfold f_omega in Hq. pose proof (f_id (465 * 1000 + 9) (465 * 1000 + 9)). lia. }
  pose proof (Tv_big (b2 / 4) Hm) as H.
  assert (Hp : 1 <= 2 ^ (3 * (b2 / 4) + 4)) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  set (P := 2 ^ (3 * (b2 / 4) + 4)) in *. set (Y := f_omega (3 * (b2 / 4) + 3)) in *.
  set (Z := Tv (b2 / 4) 1 37) in *. nia.
Qed.

Lemma f_omega_mono : forall a b, 1 <= a -> a <= b -> f_omega a <= f_omega b.
Proof.
  intros a b Ha Hab. unfold f_omega.
  pose proof (f_level_mono (b - a) a a Ha) as L1. replace (b - a + a) with b in L1 by lia.
  pose proof (f_mono b a b Hab). lia.
Qed.

(** ** Main theorems *)

Lemma ones_even : forall b, b mod 2 = 0 -> ones (c_end (b / 2)) (b + 3).
Proof.
  intros b Hb. pose proof (even_half b Hb) as Hb'.
  replace (b + 3) with (2 * (b / 2) + 3) by lia. apply ones_c_end.
Qed.

Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (b3 + 3).
Proof.
  exists (c_end (b3 / 2)). split; [exact run3 |]. split; [apply c_end_halted |].
  apply ones_even, b3_even.
Qed.

Theorem sigma_lower_bound_strong : exists c N b, c0 -->* c /\ halted tm c /\ ones c N /\
  2 ^ (3 * (b1 / 4) + 4) * f_omega (465 * 1000 + 9) <= b /\ b mod 8 = 7 /\ f_omega (3 * (b / 4) + 3) < N + 1.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (b3 + 3), b2.
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  split; [exact b2_big |]. split; [exact b2_mod8 |].
  pose proof b3_big as Hb. set (t := f_omega (3 * (b2 / 4) + 3)) in *. lia.
Qed.

Lemma final_arith : forall q v, f_omega (465 * 1000 + 9) <= q -> f_omega (3 * q + 3) <= v ->
  f_omega (f_omega (465 * 1000 + 9)) < v + 3 + 1.
Proof.
  intros q v Hq Hv.
  assert (Hpos : 1 <= f_omega (465 * 1000 + 9))
    by (unfold f_omega; pose proof (f_id (465 * 1000 + 9) (465 * 1000 + 9)); lia).
  assert (Hle : f_omega (465 * 1000 + 9) <= 3 * q + 3) by lia.
  pose proof (f_omega_mono _ _ Hpos Hle). lia.
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega (f_omega (465 * 1000 + 9)) < N + 1.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (b3 + 3).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  exact (final_arith (b2 / 4) b3 b2_quarter b3_big).
Qed.

Print Assumptions score_exact.
Print Assumptions sigma_lower_bound.
Print Assumptions sigma_lower_bound_strong.
