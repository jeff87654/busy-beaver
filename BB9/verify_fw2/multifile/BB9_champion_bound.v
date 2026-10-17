(** * A machine-checked lower bound on the score of the BB(9) champion *)

(** Machine (Jacobzheng 2024, wiki "Champions" table, claimed sigma > f_omega(f_9(2))):
      1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH
    The machine table [tm], the digit family [Kd] and the rules KR1-KR4E are imported unchanged from
    BB9_champion_1RB1RA.v (which proves [halt : halts tm c0]).  Written for
    bb8_list/investigations/bb9_champion_bound.md.

    Main results (no axioms):
      Theorem sigma_lower_bound :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega (f 9 2) < N + 1.
      Theorem sigma_lower_bound_strong :
        exists c N b1, c0 -->* c /\ halted tm c /\ ones c N /\
          256 * f 9 2 <= b1 /\ 2 ^ (b1 + 2) * f (b1 + 2) b1 < N + 1.
      Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (b2 + 3).

    Definitions (standard forms, see below):
      f 0 n = n + 1,  f (k+1) n = (f k)^n (n)  (n-fold iteration),  f_omega n = f n n.
      ones c N : the configuration c has exactly N cells equal to 1 (both tape sides are finite lists
                 followed by const 0; N counts the left list, the head cell and the right list).

    Score convention.  busycoq stops BEFORE the halting transition: E0 = 1RZ is [None] in [tm], so the
    configuration [c] with [halted tm c] is the one in state E reading a 0.  The standard Busy Beaver score counts
    the 1 written by that final transition.  At the halt of this machine the head reads 0 (see [c_end]), so
    the score is exactly N + 1, which is why the theorems bound N + 1.

    Exact values (Theorem [score_exact]): with the clearing functions U j defined below,
      b1 = U 7 (U 7 (U 5 (U 3 (U 1 3)))),   b2 = U (b1+1) (U (b1+1) (Pv (b1/2) 0 3)),
      ones at the halt = b2 + 3,  score = b2 + 4. *)

From BB8 Require Import Individual92.
From BB8 Require Import BB9_champion_1RB1RA.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(** The imported [tm] is the declared machine (BB9_champion_1RB1RA.v also passes check.py, which checks this). *)
(* machine: 1RB1RA_0LC0LF_0RD1LC_1RA1RG_1RZ0RA_1LB1LF_1LH1RE_0LI1LH_1LB0LH *)
Lemma tm_table :
  tm (A, 0) = Some (1, R, B) /\ tm (A, 1) = Some (1, R, A) /\
  tm (B, 0) = Some (0, L, C) /\ tm (B, 1) = Some (0, L, F) /\
  tm (C, 0) = Some (0, R, D) /\ tm (C, 1) = Some (1, L, C) /\
  tm (D, 0) = Some (1, R, A) /\ tm (D, 1) = Some (1, R, G) /\
  tm (E, 0) = None           /\ tm (E, 1) = Some (0, R, A) /\
  tm (F, 0) = Some (1, L, B) /\ tm (F, 1) = Some (1, L, F) /\
  tm (G, 0) = Some (1, L, H) /\ tm (G, 1) = Some (1, R, E) /\
  tm (H, 0) = Some (0, L, I) /\ tm (H, 1) = Some (1, L, H) /\
  tm (I, 0) = Some (1, L, B) /\ tm (I, 1) = Some (0, L, H).
Proof. repeat split. Qed.

(** ** The halting configuration (tape level) *)

(** Kd (0^k) 0 (2m+1): the fill loop, then 7 steps to the halting configuration (state E reading 0). *)
Definition c_end (m : nat) : state * tape :=
  (1 >> 1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> const 0) {{E}}> const 0.

Lemma HALT7x : forall m,
  (1 >> 0 >> 1 >> 1 >> [0;1;1]^^m *> const 0) {{A}}> const 0 -->* c_end m.
Proof. intros. unfold c_end. do 7 step. apply evstep_refl. Qed.

Lemma c_end_halted : forall m, halted tm (c_end m).
Proof. intros. unfold c_end. simpl. reflexivity. Qed.

Lemma KR4Ox : forall k m, Kd (repeat 0%nat k) 0 (2 * m + 1) -->* c_end m.
Proof.
  intros k m. unfold Kd. rewrite lft_blank.
  change ([1]^^0 *> const 0) with (const 0).
  apply progress_evstep.
  eapply progress_evstep_trans; [apply ENTRY |].
  rewrite lpow_ones_two, const0.
  replace (2 * m + 1 + 2) with (2 * S m + 1) by lia.
  follow (LOOPS_blank (S m) 1).
  simpl lpow.
  apply HALT7x.
Qed.

Local Open Scope nat_scope.

(** ** Definitions used in the statement *)

Fixpoint iter (n : nat) (g : nat -> nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n' => g (iter n' g x)
  end.

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

(** [ones c N]: the tape of c is  L (reversed, left of the head), s (head cell), R (right of the head),
    with 0s beyond both lists, and N = number of 1s in L, s, R. *)
Definition ones (c : state * tape) (N : nat) : Prop :=
  exists (q : state) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_blocks : forall m, count1 ([S0; S1; S1]^^m) = 2 * m.
Proof. induction m. - reflexivity. - simpl. rewrite IHm. lia. Qed.

Lemma ones_c_end : forall m, ones (c_end m) (2 * m + 4).
Proof.
  intros m. exists E, ([S1; S1; S0; S1; S1] ++ [S0; S1; S1]^^m), (@nil Sym), S0. split.
  - reflexivity.
  - simpl. rewrite count1_blocks. lia.
Qed.

(** ** Iteration *)

Lemma iter_S' : forall n g x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

Lemma iter_add : forall a b g x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

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

Lemma iter_lin : forall g, (forall a, a + 1 <= g a) -> forall n x, x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_lin1 : forall g, (forall a, 1 <= a -> a + 1 <= g a) -> forall n x, 1 <= x -> x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x Hx; simpl. - lia.
  - specialize (IHn x Hx). specialize (Hg (iter n g x) ltac:(lia)). lia.
Qed.

Lemma iter_par : forall g T, (forall y, T <= y -> T <= g y /\ g y mod 2 = (y + 1) mod 2) ->
  forall n x, T <= x -> T <= iter n g x /\ iter n g x mod 2 = (x + n) mod 2.
Proof.
  intros g T Hg. induction n; intros x Hx; cbn [iter].
  - split; [lia | f_equal; lia].
  - destruct (IHn x Hx) as [H1 H2]. destruct (Hg _ H1) as [H3 H4]. split; [exact H3 |].
    rewrite H4. mods; lia.
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

(** ** The exact clearing functions *)

(** U j x : the value of b after clearing ONE unit of a digit at depth j (j zero digits above it) from b = x.
    X j   : the value of b after clearing j twos at depths 0 .. j-1, starting from b = 7.
      U 0 x = 3x + 7,  U (j+1) x = (U j)^(x - 2j) (X j),  X 0 = 7,  X (j+1) = U j (U j (X j)).
    (R2 + R1^(b+2) gives 3b+7; R3 at depth j+1 writes j twos above the refilled digit x - 2j, then b = 7.) *)
Fixpoint UX (j : nat) : (nat -> nat) * nat :=
  match j with
  | O => (fun x => 3 * x + 7, 7)
  | S i => (fun x => iter (x - 2 * i) (fst (UX i)) (snd (UX i)),
            fst (UX i) (fst (UX i) (snd (UX i))))
  end.

Definition U (j : nat) : nat -> nat := fst (UX j).
Definition X (j : nat) : nat := snd (UX j).

Lemma U_0 : forall x, U 0 x = 3 * x + 7.
Proof. reflexivity. Qed.

Lemma U_S : forall j x, U (S j) x = iter (x - 2 * j) (U j) (X j).
Proof. reflexivity. Qed.

Lemma X_0 : X 0 = 7.
Proof. reflexivity. Qed.

Lemma X_S : forall j, X (S j) = U j (U j (X j)).
Proof. reflexivity. Qed.

Lemma U1_3 : U 1 3 = 280.
Proof. reflexivity. Qed.

(** Never let a tactic compute these numbers. *)
Opaque U X.

Lemma growth : forall j, (forall x, x + 2 * j + 5 <= U j x) /\ 4 * j + 7 <= X j.
Proof.
  induction j as [| j [Hu Hx]].
  - split; [intros; rewrite U_0; lia | rewrite X_0; lia].
  - split.
    + intros x. rewrite U_S.
      pose proof (iter_lin (U j) ltac:(intros a; specialize (Hu a); lia) (x - 2 * j) (X j)). lia.
    + rewrite X_S. pose proof (Hu (X j)). pose proof (Hu (U j (X j))). lia.
Qed.

Lemma Ugrow : forall j x, x + 2 * j + 5 <= U j x.
Proof. intros. apply growth. Qed.

Lemma Xgrow : forall j, 4 * j + 7 <= X j.
Proof. intros. apply growth. Qed.

Lemma U_ge_X : forall i z, X i <= U (S i) z.
Proof.
  intros. rewrite U_S. apply iter_ge. intros a. pose proof (Ugrow i a). lia.
Qed.

(** Parity: one unit at depth j flips the parity of b (for 2j <= b). *)
Lemma parity : forall j, (forall x, 2 * j <= x -> U j x mod 2 = (x + 1) mod 2) /\ X j mod 2 = 1.
Proof.
  induction j as [| j [Hu Hx]].
  - split; [intros; rewrite U_0; mods; lia | rewrite X_0; reflexivity].
  - assert (Hg : forall y, 2 * j <= y -> 2 * j <= U j y /\ U j y mod 2 = (y + 1) mod 2).
    { intros y Hy. split; [pose proof (Ugrow j y); lia | auto]. }
    split.
    + intros x Hx'. rewrite U_S. pose proof (Xgrow j).
      destruct (iter_par (U j) (2 * j) Hg (x - 2 * j) (X j) ltac:(lia)) as [_ Hp].
      rewrite Hp. mods; lia.
    + rewrite X_S. pose proof (Xgrow j).
      destruct (Hg (X j)) as [H1 H2]; [lia |]. destruct (Hg (U j (X j)) H1) as [_ H3].
      rewrite H3. mods; lia.
Qed.

Lemma Upar : forall j x, 2 * j <= x -> U j x mod 2 = (x + 1) mod 2.
Proof. intros. apply parity. assumption. Qed.

Lemma Ustep : forall j y, 2 * j <= y -> 2 * j <= U j y /\ U j y mod 2 = (y + 1) mod 2.
Proof. intros. split; [pose proof (Ugrow j y); lia | apply Upar; assumption]. Qed.

(** b mod 4 after one unit at depth j >= 1 depends only on the parity of b. *)
Lemma U1_mod4 : forall n, (iter n (U 0) 7 mod 4 = 3 /\ n mod 2 = 0) \/ (iter n (U 0) 7 mod 4 = 0 /\ n mod 2 = 1).
Proof.
  induction n.
  - left. split; reflexivity.
  - simpl iter. rewrite U_0.
    destruct IHn as [[H1 H2] | [H1 H2]]; [right | left]; split; mods; lia.
Qed.

Lemma mod4 : forall i x, 2 * S i <= x ->
  (x mod 2 = 1 -> U (S i) x mod 4 = 0) /\ (x mod 2 = 0 -> U (S i) x mod 4 = 3).
Proof.
  induction i; intros x Hx.
  - rewrite U_S, X_0. replace (x - 2 * 0) with x by lia.
    destruct (U1_mod4 x) as [[H1 H2] | [H1 H2]]; split; intros; mods; lia.
  - rewrite U_S. remember (x - 2 * S i) as m eqn:Hm. destruct m as [| n]; [lia |].
    simpl iter.
    destruct (iter_par (U (S i)) (2 * S i) (Ustep (S i)) n (X (S i))) as [H1 H2].
    { pose proof (Xgrow (S i)). lia. }
    pose proof (proj2 (parity (S i))) as HX.
    destruct (IHi _ H1) as [H3 H4].
    split; intros Hxp.
    + apply H3. rewrite H2. mods; lia.
    + apply H4. rewrite H2. mods; lia.
Qed.

(** ** Clearing at the machine level, with exact values *)

Lemma CHx : forall v Us B, Kd (v :: Us) 0 B -->* Kd (0 :: Us) 0 (iter v (U 0) B).
Proof.
  induction v; intros Us B.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, KR2 |].
    follow (R1iter (B + 2) (v :: Us) 1).
    rewrite iter_S', U_0. replace (3 * B + 7) with (1 + 3 * (B + 2)) by lia.
    apply IHv.
Qed.

Definition CDPx (j : nat) : Prop := forall v Us B, 2 * j <= B ->
  Kd (repeat 0 j ++ v :: Us) 0 B -->* Kd (repeat 0 (S j) ++ Us) 0 (iter v (U j) B).

(** n twos cleared at depths t .. t+n-1 *)
Fixpoint Yb (t n x : nat) : nat :=
  match n with
  | O => x
  | S n' => U (t + n') (U (t + n') (Yb t n' x))
  end.

Lemma Yb_X : forall j, Yb 0 j 7 = X j.
Proof. induction j. - reflexivity. - simpl Yb. rewrite IHj, X_S. reflexivity. Qed.

Lemma Yb_ge : forall t n x, 2 * t <= x -> 2 * (t + n) <= Yb t n x.
Proof.
  intros t n x Hx. destruct n as [| n']. - simpl. lia.
  - simpl Yb. pose proof (Ugrow (t + n') (U (t + n') (Yb t n' x))). lia.
Qed.

Lemma BLKx : forall D, (forall j', j' < D -> CDPx j') ->
  forall n t V x, t + n <= D -> 2 * t <= x ->
  Kd (repeat 0 t ++ repeat 2 n ++ V) 0 x -->* Kd (repeat 0 (t + n) ++ V) 0 (Yb t n x).
Proof.
  intros D HD. induction n as [| n IHn]; intros t V x Hd Hx.
  - replace (t + 0) with t by lia. apply evstep_refl.
  - rewrite <- repeat_snoc.
    follow (IHn t (2 :: V) x ltac:(lia) Hx).
    follow (HD (t + n) ltac:(lia) 2 V (Yb t n x) (Yb_ge t n x Hx)).
    replace (t + S n) with (S (t + n)) by lia. apply evstep_refl.
Qed.

Lemma CDPx_all : forall j, CDPx j.
Proof.
  intro j. induction j as [j IH] using lt_wf_ind.
  destruct j as [| n].
  - intros v Us B _. simpl. apply CHx.
  - intro v. induction v as [| w IHw]; intros Us B HB.
    + rewrite repeat_snoc. apply evstep_refl.
    + remember (B - 2 * S n) as s eqn:Hs.
      assert (HB' : B = 2 * S n + s) by lia.
      assert (Hr : Kd (repeat 0 (S n) ++ S w :: Us) 0 B -->*
                   Kd (repeat 2 n ++ S (S s) :: w :: Us) 0 7).
      { rewrite HB'. eapply evstep_trans; [apply progress_evstep, KR3 |].
        follow (R1iter 2 (repeat 2 n ++ S (S s) :: w :: Us) 1). finish. }
      follow Hr.
      follow (BLKx (S n) IH n 0 (S (S s) :: w :: Us) 7 ltac:(lia) ltac:(lia)).
      rewrite Yb_X.
      follow (IH n ltac:(lia) (S (S s)) (w :: Us) (X n) ltac:(pose proof (Xgrow n); lia)).
      replace (iter (S (S s)) (U n) (X n)) with (U (S n) B)
        by (rewrite U_S; f_equal; lia).
      follow (IHw Us (U (S n) B) ltac:(pose proof (Ugrow (S n) B); lia)).
      rewrite iter_S'. apply evstep_refl.
Qed.

(** Clearing m pairs (0,1) from depth j: the digit 1 sits at depth j+1. *)
Fixpoint Pv (m j B : nat) : nat :=
  match m with
  | O => B
  | S m' => Pv m' (j + 2) (U (S j) B)
  end.

Lemma Pv_par : forall m j B, 2 * (j + 1) <= B ->
  2 * (j + 2 * m + 1) <= Pv m j B /\ Pv m j B mod 2 = (B + m) mod 2.
Proof.
  induction m; intros j B HB.
  - cbn [Pv]. split; [lia | f_equal; lia].
  - cbn [Pv]. pose proof (Ugrow (S j) B). pose proof (Upar (S j) B ltac:(lia)).
    destruct (IHm (j + 2) (U (S j) B) ltac:(lia)) as [H1 H2].
    split; [lia |]. rewrite H2. mods; lia.
Qed.

Lemma PAIRSx : forall m j V B, 2 * (j + 1) <= B ->
  Kd (repeat 0 j ++ pairs m V) 0 B -->* Kd (repeat 0 (j + 2 * m) ++ V) 0 (Pv m j B).
Proof.
  induction m; intros j V B HB.
  - replace (j + 2 * 0) with j by lia. apply evstep_refl.
  - simpl pairs. rewrite repeat_snoc.
    follow (CDPx_all (S j) 1 (pairs m V) B ltac:(lia)).
    replace (S (S j)) with (j + 2) by lia.
    follow (IHm (j + 2) V (U (S j) B) ltac:(pose proof (Ugrow (S j) B); lia)).
    replace (j + 2 + 2 * m) with (j + 2 * S m) by lia. apply evstep_refl.
Qed.

Lemma LASTx : forall j B, 2 * (j + 1) <= B ->
  Kd (repeat 0 j ++ [0; 2]) 0 B -->* Kd (repeat 0 (j + 2)) 0 (U (S j) (U (S j) B)).
Proof.
  intros j B HB. rewrite repeat_snoc.
  follow (CDPx_all (S j) 2 [] B ltac:(lia)).
  rewrite app_nil_r. replace (j + 2) with (S (S j)) by lia. apply evstep_refl.
Qed.

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

(** ** The two clearings of the run *)

Definition b1 : nat := U 7 (U 7 (U 5 (U 3 (U 1 3)))).
(** the second clearing, as a function of b1 *)
Definition second (b : nat) : nat := U (S b) (U (S b) (Pv (b / 2) 0 3)).
Definition b2 : nat := second b1.

Lemma b1_def : b1 = U 7 (U 7 (U 5 (U 3 (U 1 3)))).
Proof. reflexivity. Qed.

Lemma b2_def : b2 = second b1.
Proof. reflexivity. Qed.

(** [lia] stalls on closed terms such as [b1 / 2]: keep b1, b2 opaque and state the arithmetic for a
    variable b, instantiated with b1 at the end. *)
Opaque b1 b2.

Lemma b1_big : 256 * f 9 2 <= b1.
Proof.
  rewrite b1_def. rewrite U1_3.
  pose proof (Ugrow 3 280) as Hz.
  pose proof (Ubound 5 4 (U 3 280) ltac:(change (2 ^ (5 + 1)) with 64; lia)) as Hy.
  change (2 ^ (5 + 1)) with 64 in Hy.
  pose proof (f_dbl 6 4 ltac:(lia)).
  assert (Hy' : 2 ^ (7 + 1) * 2 <= U 5 (U 3 280)) by (change (2 ^ (7 + 1)) with 256; lia).
  pose proof (Ubound 7 2 _ Hy') as Hw.
  pose proof (Ubound 7 (f 8 2) _ Hw) as Hb.
  rewrite f_S. change (iter 2 (f 8) 2) with (f 8 (f 8 2)).
  change (2 ^ (7 + 1)) with 256 in Hb. exact Hb.
Qed.

(** Residue facts on plain variables ([mods] is never run on the large terms themselves). *)
Lemma m43 : forall x, x mod 4 = 3 -> x mod 2 = 1.
Proof. intros; mods; lia. Qed.

Lemma m40 : forall x, x mod 4 = 0 -> x mod 2 = 0.
Proof. intros; mods; lia. Qed.

Lemma div4 : forall x, x mod 4 = 0 -> x = 2 * (2 * (x / 4)) /\ x / 2 = 2 * (x / 4).
Proof. intros x Hx. pose proof (Nat.div_mod_eq x 2). mods; lia. Qed.

Lemma odd_half : forall x, x mod 2 = 1 -> x = 2 * (x / 2) + 1.
Proof. intros; mods; lia. Qed.

Lemma par3 : forall z w v h m, h = 2 * m -> z mod 2 = (3 + h) mod 2 -> w mod 2 = (z + 1) mod 2 ->
  v mod 2 = (w + 1) mod 2 -> v mod 2 = 1.
Proof. intros; mods; lia. Qed.

Lemma b1_mod4 : b1 mod 4 = 0.
Proof.
  rewrite b1_def. rewrite U1_3.
  pose proof (Ugrow 3 280). pose proof (Ugrow 5 (U 3 280)). pose proof (Ugrow 7 (U 5 (U 3 280))).
  destruct (mod4 2 280 ltac:(lia)) as [_ A3]. specialize (A3 eq_refl).
  destruct (mod4 4 (U 3 280) ltac:(lia)) as [A5 _]. specialize (A5 (m43 _ A3)).
  destruct (mod4 6 (U 5 (U 3 280)) ltac:(lia)) as [_ A7]. specialize (A7 (m40 _ A5)).
  destruct (mod4 6 (U 7 (U 5 (U 3 280))) ltac:(lia)) as [A7' _]. exact (A7' (m43 _ A7)).
Qed.

Lemma second_odd : forall b, b mod 4 = 0 -> second b mod 2 = 1.
Proof.
  intros b Hb4. unfold second. destruct (Pv_par (b / 2) 0 3 ltac:(lia)) as [H1 H2].
  destruct (div4 b Hb4) as [Hq Hq2].
  pose proof (Upar (S b) (Pv (b / 2) 0 3) ltac:(lia)) as H3.
  pose proof (Ugrow (S b) (Pv (b / 2) 0 3)).
  pose proof (Upar (S b) (U (S b) (Pv (b / 2) 0 3)) ltac:(lia)) as H4.
  exact (par3 _ _ _ _ _ Hq2 H2 H3 H4).
Qed.

Lemma b2_odd : b2 mod 2 = 1.
Proof. rewrite b2_def. apply second_odd, b1_mod4. Qed.

(** ** The run, with exact values *)

Lemma run1 : c0 -->* Kd (repeat 0 8) 0 b1.
Proof.
  follow init_reach.
  follow (R1iter 2 [] 0).
  change (Kd [] 0 (0 + 3 * 2)) with (Kd (repeat 0 0) 0 (2 * 3)).
  eapply evstep_trans; [apply progress_evstep, (KR4E 0 3) |].
  eapply evstep_trans; [apply progress_evstep, (KR1 (Q 3) 0 0) |].
  rewrite Q_pairs. change (Kd (pairs 3 [0; 2]) 0 (0 + 3)) with (Kd (repeat 0 0 ++ pairs 3 [0; 2]) 0 3).
  follow (PAIRSx 3 0 [0; 2] 3 ltac:(lia)).
  destruct (Pv_par 3 0 3 ltac:(lia)) as [Hp _].
  follow (LASTx (0 + 2 * 3) (Pv 3 0 3) ltac:(lia)).
  rewrite b1_def. apply evstep_refl.
Qed.

(** from the blank digit list with b = 0 mod 4: rebuild, second clearing, halt *)
Lemma run2_gen : forall k b, b mod 4 = 0 -> Kd (repeat 0 k) 0 b -->* c_end (second b / 2).
Proof.
  intros k b Hb4.
  destruct (div4 b Hb4) as [Hq Hq2].
  remember (b / 4) as q eqn:Hqdef.
  rewrite Hq at 1.
  eapply evstep_trans; [apply progress_evstep, (KR4E k (2 * q)) |].
  eapply evstep_trans; [apply progress_evstep, (KR1 (Q (2 * q)) 0 0) |].
  rewrite Q_pairs.
  change (Kd (pairs (2 * q) [0; 2]) 0 (0 + 3)) with (Kd (repeat 0 0 ++ pairs (2 * q) [0; 2]) 0 3).
  follow (PAIRSx (2 * q) 0 [0; 2] 3 ltac:(lia)).
  destruct (Pv_par (2 * q) 0 3 ltac:(lia)) as [Hp _].
  follow (LASTx (0 + 2 * (2 * q)) (Pv (2 * q) 0 3) ltac:(lia)).
  assert (Hb2 : U (S (0 + 2 * (2 * q))) (U (S (0 + 2 * (2 * q))) (Pv (2 * q) 0 3)) = 2 * (second b / 2) + 1).
  { pose proof (odd_half (second b) (second_odd b Hb4)) as Hb.
    rewrite <- Hb. unfold second. rewrite Hq2.
    replace (S (0 + 2 * (2 * q))) with (S b) by lia. reflexivity. }
  rewrite Hb2. apply KR4Ox.
Qed.

Lemma run2 : c0 -->* c_end (b2 / 2).
Proof. follow run1. rewrite b2_def. apply run2_gen, b1_mod4. Qed.

Lemma ones_odd : forall b, b mod 2 = 1 -> ones (c_end (b / 2)) (b + 3).
Proof.
  intros b Hb. pose proof (odd_half b Hb) as Hb'.
  replace (b + 3) with (2 * (b / 2) + 4) by lia. apply ones_c_end.
Qed.

(** ** Main theorems *)

Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (b2 + 3).
Proof.
  exists (c_end (b2 / 2)). split; [exact run2 |]. split; [apply c_end_halted |].
  apply ones_odd, b2_odd.
Qed.

(** second b >= 2^(b+2) * f (b+2) b: the second clearing reaches depth b+1. *)
Lemma second_big : forall b, 2 ^ (b + 2) * f (b + 2) b <= second b.
Proof.
  intros b. unfold second.
  pose proof (U_ge_X b (Pv (b / 2) 0 3)) as Hw.
  pose proof (Xbound b) as HX.
  assert (Hn : 2 ^ (S b + 1) * b <= U (S b) (Pv (b / 2) 0 3)).
  { replace (S b + 1) with (b + 2) by lia. nia. }
  pose proof (Ubound (S b) b _ Hn) as Hb.
  replace (S b + 1) with (b + 2) in Hb by lia. replace (S (S b)) with (b + 2) in Hb by lia.
  exact Hb.
Qed.

Lemma b2_big : 2 ^ (b1 + 2) * f (b1 + 2) b1 <= b2.
Proof. rewrite b2_def. apply second_big. Qed.

(** f_omega N = f N N <= f (b+2) N <= f (b+2) b <= 2^(b+2) * f (b+2) b, for 1 <= N <= b *)
Lemma omega_le : forall N b, 1 <= N -> N <= b -> f_omega N <= 2 ^ (b + 2) * f (b + 2) b.
Proof.
  intros N b HN HNb. unfold f_omega.
  pose proof (f_level_mono (b + 2 - N) N N HN) as L1.
  replace (b + 2 - N + N) with (b + 2) in L1 by lia.
  pose proof (f_mono (b + 2) N b ltac:(lia)) as L2.
  assert (L3 : 1 <= 2 ^ (b + 2)) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  nia.
Qed.

Lemma f_pos : forall k n, 1 <= n -> 1 <= f k n.
Proof. intros k n Hn. pose proof (f_id k n). lia. Qed.

Theorem sigma_lower_bound_strong : exists c N b, c0 -->* c /\ halted tm c /\ ones c N /\
  (256 * f 9 2 <= b)%nat /\ (2 ^ (b + 2) * f (b + 2) b < N + 1)%nat.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (b2 + 3), b1. repeat split; try assumption.
  - exact b1_big.
  - pose proof b2_big. lia.
Qed.

Theorem sigma_lower_bound : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega (f 9 2) < N + 1.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (b2 + 3). repeat split; try assumption.
  pose proof (omega_le (f 9 2) b1 (f_pos 9 2 ltac:(lia)) ltac:(pose proof b1_big; lia)) as Ho.
  pose proof b2_big. lia.
Qed.

Print Assumptions sigma_lower_bound.
Print Assumptions sigma_lower_bound_strong.
Print Assumptions score_exact.
