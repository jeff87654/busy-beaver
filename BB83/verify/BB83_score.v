(** * The score of 2LH1LE2RA_0LE2LE2RB_1RF1RC2RB_0RC0LD0RH_1RC2LE1LG_0LA0LD1RZ_1LD2RA2LG_2RD1LF1LG *)

(** Main results:
      sigma = 2 * mfin + 7, where mfin is the parameter after the tail run;
      f_(omega+1)^3 (f_omega^3(14)) < sigma.
    Here [f_omega n = 2 ↑^(n+1) (n+3)] is the Knuth-arrow normal form of the
    omega-th element of the fast-growing hierarchy, and [f_omega1 n = f_omega^n n]
    is the usual notation for f_(omega+1)(n).  No large number is ever evaluated:
    [mfin] is sealed behind a [sig] in BB83_run.v, and every Knuth expression is
    manipulated symbolically. *)

From TM83 Require Import Individual83 BB83_rules BB83_run.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(** ** Knuth up-arrows: [knuth n a b = a ↑^n b], with [a ↑^0 b = a*b]. *)
Fixpoint knuth (n a b : nat) : nat :=
  match n with
  | 0 => a * b
  | S n' => Nat.iter b (knuth n' a) 1
  end.

Lemma iter_add : forall (f : nat -> nat) a b x,
  Nat.iter (a + b) f x = Nat.iter a f (Nat.iter b f x).
Proof.
  induction a as [|a IH]; intros b x.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma iter_succ_l : forall (f : nat -> nat) n x,
  Nat.iter (S n) f x = f (Nat.iter n f x).
Proof.
  induction n as [|n IH]; intros x.
  - reflexivity.
  - rewrite iter_succ_r.
    rewrite (IH (f x)).
    rewrite iter_succ_r.
    reflexivity.
Qed.

Lemma knuth_S : forall n a b, knuth (S n) a (S b) = knuth n a (knuth (S n) a b).
Proof. reflexivity. Qed.

Lemma knuth_S0 : forall k b, knuth (S k) 2 b = Nat.iter b (knuth k 2) 1.
Proof. reflexivity. Qed.

Lemma knuth_1 : forall k, knuth k 2 1 = 2.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - simpl. exact IH.
Qed.

Lemma knuth_2 : forall k, knuth k 2 2 = 4.
Proof.
  induction k as [|k IH].
  - reflexivity.
  - simpl. rewrite knuth_1. exact IH.
Qed.

Lemma iter2_knuth : forall k, Nat.iter 2 (knuth k 2) 1 = 4.
Proof. intros k. simpl. rewrite knuth_1. apply knuth_2. Qed.

(** ** Basic growth facts. *)

Lemma iter_ge1 : forall (f : nat -> nat),
  (forall y, 1 <= y -> y + 1 <= f y) ->
  forall x, x + 1 <= Nat.iter x f 1.
Proof.
  intros f Hf x. induction x as [|x IH].
  - simpl. lia.
  - simpl. apply Nat.le_trans with (Nat.iter x f 1 + 1); [lia |].
    apply Hf. lia.
Qed.

Lemma knuth_ge1 : forall n x, 1 <= x -> x + 1 <= knuth n 2 x.
Proof.
  intros n. induction n as [|n IHn]; intros x Hx.
  - simpl. lia.
  - simpl. apply iter_ge1. intros y Hy. apply IHn. lia.
Qed.

Lemma knuth_ge2' : forall n x, 2 * x <= knuth n 2 x.
Proof.
  intros n. induction n as [|n IH]; intros x.
  - simpl. lia.
  - destruct x as [|x].
    + simpl. lia.
    + simpl.
      assert (H1 : x + 1 <= Nat.iter x (knuth n 2) 1).
      { apply iter_ge1. intros y Hy. apply knuth_ge1. exact Hy. }
      assert (H2 : 2 * Nat.iter x (knuth n 2) 1
                   <= knuth n 2 (Nat.iter x (knuth n 2) 1)) by (apply IH).
      lia.
Qed.

Lemma knuth_ge_id : forall n x, x <= knuth n 2 x.
Proof.
  intros n. induction n as [|n IH]; intros x.
  - simpl. lia.
  - simpl.
    assert (H : x + 1 <= Nat.iter x (knuth n 2) 1).
    { apply iter_ge1. intros y Hy. apply knuth_ge1. exact Hy. }
    lia.
Qed.

Lemma knuth_pos : forall n x, 1 <= x -> 1 <= knuth n 2 x.
Proof. intros n x Hx. assert (H := knuth_ge_id n x). lia. Qed.

Lemma iter_pos : forall (f : nat -> nat) n x,
  (forall y, 1 <= y -> 1 <= f y) -> 1 <= x -> 1 <= Nat.iter n f x.
Proof.
  intros f n. induction n as [|n IH]; intros x Hf Hx.
  - simpl. exact Hx.
  - simpl. apply Hf. apply IH; [exact Hf | exact Hx].
Qed.

Lemma iter_strict : forall (f : nat -> nat) m x,
  (forall y, 1 <= y -> y + 1 <= f y) ->
  (forall y, 1 <= y -> 1 <= f y) ->
  1 <= x ->
  forall n, n < m -> Nat.iter n f x < Nat.iter m f x.
Proof.
  intros f m. induction m as [|m IH]; intros x Hf Hpos Hx n Hnm.
  - lia.
  - destruct (Nat.eq_dec n m) as [Heq | Hne].
    + subst n. simpl. apply Nat.lt_le_trans with (Nat.iter m f x + 1); [lia |].
      apply Hf. apply iter_pos; [exact Hpos | exact Hx].
    + assert (Hn : n < m) by lia.
      assert (Hlt : Nat.iter n f x < Nat.iter m f x)
        by (apply IH; [exact Hf | exact Hpos | exact Hx | exact Hn]).
      simpl. apply Nat.lt_le_trans with (Nat.iter m f x + 1); [lia |].
      apply Hf. apply iter_pos; [exact Hpos | exact Hx].
Qed.

Lemma iter_mono_count : forall (f : nat -> nat) n m x,
  (forall y, f y <= f (S y)) -> (forall y, y <= f y) ->
  n <= m -> Nat.iter n f x <= Nat.iter m f x.
Proof.
  intros f n m x Hinc Hge Hnm.
  induction Hnm as [|m Hm IH].
  - lia.
  - simpl. apply Nat.le_trans with (Nat.iter m f x); [exact IH |].
    apply Hge.
Qed.

Lemma iter_mono_fun : forall (f g : nat -> nat) n x,
  (forall y, f y <= g y) -> (forall a b, a <= b -> f a <= f b) ->
  Nat.iter n f x <= Nat.iter n g x.
Proof.
  intros f g n. induction n as [|n IH]; intros x Hfg Hmono.
  - reflexivity.
  - simpl. apply Nat.le_trans with (f (Nat.iter n g x)); [|apply Hfg].
    apply Hmono. apply IH; [exact Hfg | exact Hmono].
Qed.

Lemma knuth_incr : forall n x y, x <= y -> knuth n 2 x <= knuth n 2 y.
Proof.
  intros n. induction n as [|n IH]; intros x y Hxy.
  - simpl. lia.
  - simpl. apply iter_mono_count.
    + intros z. apply IH. lia.
    + intros z. apply knuth_ge_id.
    + lia.
Qed.

(** Strict increase in the argument; used for f_omega. *)
Lemma knuth_strict_b : forall n x, 1 <= x -> knuth n 2 x < knuth n 2 (S x).
Proof.
  intros n. destruct n as [|n]; intros x Hx.
  - simpl. lia.
  - simpl.
    assert (Heq : Nat.iter (S x) (knuth n 2) 1
                  = knuth n 2 (Nat.iter x (knuth n 2) 1))
      by (apply iter_succ_l).
    rewrite <- Heq.
    apply iter_strict.
    + intros y Hy. apply knuth_ge1. exact Hy.
    + intros y Hy. apply knuth_pos. exact Hy.
    + lia.
    + lia.
Qed.

Lemma knuth_mono_arrow : forall n m x, n <= m -> knuth n 2 x <= knuth m 2 x.
Proof.
  intros n. induction n as [|n IH]; intros m x Hnm.
  - change (2 * x <= knuth m 2 x). apply knuth_ge2'.
  - destruct m as [|m].
    + lia.
    + rewrite (knuth_S0 n x), (knuth_S0 m x).
      apply iter_mono_fun.
      * intros z. apply IH. lia.
      * intros a b Hab. apply knuth_incr. exact Hab.
Qed.

Lemma iter4 : forall (f : nat -> nat) x, Nat.iter 4 f x = f (f (f (f x))).
Proof. intros f x. simpl. reflexivity. Qed.

Lemma knuth_S4 : forall n, knuth (S n) 2 4 = knuth n 2 (knuth n 2 4).
Proof.
  intros n. rewrite (knuth_S0 n 4). rewrite iter4.
  rewrite knuth_1, knuth_2. reflexivity.
Qed.

Lemma knuth_SS4 : forall n, knuth (S (S n)) 2 4 = knuth (S n) 2 (knuth (S n) 2 4).
Proof.
  intros n. rewrite (knuth_S0 (S n) 4). rewrite iter4.
  rewrite knuth_1, knuth_2. reflexivity.
Qed.

Lemma knuth_4_ge : forall n, n + 5 <= knuth n 2 4.
Proof.
  intros n. induction n as [|n IH].
  - simpl. lia.
  - rewrite knuth_S4.
    assert (H1 : n + 5 <= knuth n 2 4) by exact IH.
    assert (H2 : knuth n 2 (n + 5) <= knuth n 2 (knuth n 2 4)) by (apply knuth_incr; lia).
    assert (H3 : n + 5 + 1 <= knuth n 2 (n + 5)) by (apply knuth_ge1; lia).
    lia.
Qed.

(** Two more arrows beat a linear increase of the argument. *)
Lemma knuth_2_4_S : forall k, knuth (S (S (S k))) 2 4 > knuth (S k) 2 (S k + 4).
Proof.
  intros k.
  assert (E1 : knuth (S (S (S k))) 2 4
                = Nat.iter (knuth (S k) 2 (knuth (S k) 2 4)) (knuth (S k) 2) 1).
  { rewrite knuth_SS4. rewrite (knuth_S0 (S k) (knuth (S (S k)) 2 4)). rewrite knuth_SS4.
    reflexivity. }
  assert (E2 : knuth (S k) 2 (S k + 4) = Nat.iter (S k + 4) (knuth k 2) 1)
    by (rewrite knuth_S0; reflexivity).
  rewrite E1, E2.
  assert (H1 : S k + 5 <= knuth (S k) 2 4) by (apply knuth_4_ge).
  assert (H2 : knuth (S k) 2 (S k + 5) <= knuth (S k) 2 (knuth (S k) 2 4))
    by (apply knuth_incr; lia).
  assert (H3 : S k + 5 + 1 <= knuth (S k) 2 (S k + 5)) by (apply knuth_ge1; lia).
  assert (H4 : S k + 4 < knuth (S k) 2 (knuth (S k) 2 4)) by lia.
  assert (HB : Nat.iter (S k + 4) (knuth k 2) 1
              <= Nat.iter (S k + 4) (knuth (S k) 2) 1).
  { apply iter_mono_fun.
    - intros z. apply knuth_mono_arrow. lia.
    - intros a b Hab. apply knuth_incr. exact Hab. }
  assert (HA : Nat.iter (S k + 4) (knuth (S k) 2) 1
              < Nat.iter (knuth (S k) 2 (knuth (S k) 2 4)) (knuth (S k) 2) 1).
  { apply iter_strict.
    - intros y Hy. apply knuth_ge1. exact Hy.
    - intros y Hy. apply knuth_pos. exact Hy.
    - lia.
    - exact H4. }
  lia.
Qed.

(** One step in the argument at arrow level >= 1 at least doubles the value. *)
Lemma knuth_arg_double : forall k b,
  2 * knuth (S k) 2 b <= knuth (S k) 2 (S b).
Proof.
  intros k b. rewrite knuth_S. apply knuth_ge2'.
Qed.

Lemma knuth_arg_add2_quad : forall k b,
  4 * knuth (S k) 2 b <= knuth (S k) 2 (b + 2).
Proof.
  intros k b.
  assert (H1 := knuth_arg_double k b).
  assert (H2 := knuth_arg_double k (S b)).
  replace (S (S b)) with (b + 2) in H2 by lia.
  lia.
Qed.

(** ** Closed form of the g hierarchy. *)

Section ClosedForm.
Variable h kh : nat -> nat.
Hypothesis hyp : forall y, 2 * h y + 4 = kh (2 * y + 4).

Lemma iter_closed_helper : forall j x,
  2 * Nat.iter j h x + 4 = Nat.iter j kh (2 * x + 4).
Proof.
  induction j as [|j IH]; intros x.
  - simpl. lia.
  - simpl in *. rewrite hyp. rewrite (IH x). reflexivity.
Qed.
End ClosedForm.

Theorem g_closed : forall k m,
  2 * g (S k) m + 4 = knuth k 2 (2 * m + 4).
Proof.
  induction k as [|k IH]; intros m.
  - assert (E : g 1 m = 2 * m + 2).
    { assert (E2 : g 1 m = Nat.iter (2 * m + 2) (g 0) 0%nat) by reflexivity.
      rewrite E2. rewrite (iter_g0 (2 * m + 2) 0%nat). lia. }
    rewrite E. simpl. lia.
  - assert (E : g (S (S k)) m = Nat.iter (2 * m + 2) (g (S k)) 0) by reflexivity.
    rewrite E.
    rewrite (iter_closed_helper (g (S k)) (knuth k 2) IH (2 * m + 2) 0).
    change (2 * 0 + 4) with 4.
    rewrite (knuth_S0 k (2 * m + 4)).
    replace (2 * m + 4) with (2 * m + 2 + 2) by lia.
    rewrite (iter_add (knuth k 2) (2 * m + 2) 2 1).
    rewrite iter2_knuth.
    reflexivity.
Qed.

(** ** The nested Knuth expression [aw] and the closed form of [desc]. *)

Fixpoint aw (j n : nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n' => knuth j 2 (aw (S j) n' x)
  end.

Lemma aw_0 : forall j x, aw j 0 x = x.
Proof. intros j x. reflexivity. Qed.

Lemma aw_S : forall j n x, aw j (S n) x = knuth j 2 (aw (S j) n x).
Proof. intros j n x. reflexivity. Qed.

Lemma aw_shift : forall j m x,
  aw j m (knuth (m + j) 2 x) = aw j (S m) x.
Proof.
  intros j m x. revert j.
  induction m as [|m IHm]; intros j.
  - rewrite aw_0, aw_S, aw_0.
    replace (0 + j) with j by lia. reflexivity.
  - rewrite aw_S.
    replace (S m + j) with (m + S j) by lia.
    rewrite aw_S.
    rewrite <- (IHm (S j)). reflexivity.
Qed.

Lemma aw_chain : forall j n x, knuth (j + n) 2 x <= aw j (S n) x.
Proof.
  intros j n x. revert j.
  induction n as [|n IHn]; intros j.
  - rewrite aw_S, aw_0. replace (j + 0) with j by lia. reflexivity.
  - assert (H1 : aw (S j) (S n) x <= knuth j 2 (aw (S j) (S n) x))
      by (apply knuth_ge_id).
    assert (H2 : knuth ((S j) + n) 2 x <= aw (S j) (S n) x) by (apply IHn).
    assert (H3 : (S j) + n = j + S n) by lia.
    rewrite H3 in H2.
    rewrite aw_S. lia.
Qed.

(** desc n m applies g_n, g_(n-1), ..., g_1 to m. *)
Lemma desc_S : forall n m, desc (S n) m = desc n (g (S n) m).
Proof. intros n m. reflexivity. Qed.

Lemma desc_closed_gen : forall n m, 1 <= n ->
  2 * desc n m + 4 = aw 0 n (2 * m + 4).
Proof.
  intros n m Hn. revert m.
  induction n as [|n IHn]; intros m.
  - lia.
  - destruct n as [|n].
    +       assert (E : desc 1 m = 2 * m + 2).
      { cbn [desc].
        assert (E2 : g 1 m = Nat.iter (2 * m + 2) (g 0) 0%nat) by reflexivity.
        rewrite E2. rewrite (iter_g0 (2 * m + 2) 0%nat). lia. }
      rewrite E. simpl. lia.
    + assert (Hn' : 1 <= S n) by lia.
      rewrite (desc_S (S n) m).
      rewrite (IHn Hn' (g (S (S n)) m)).
      rewrite (g_closed (S n) m).
      rewrite <- (aw_shift 0 (S n) (2 * m + 4)).
      replace (S n + 0) with (S n) by lia.
      reflexivity.
Qed.

(** ** The closed form of one round.

    round m = desc (2m+2) (g_(2m+2) 0).  desc_closed_gen and g_closed give
    [2 round m + 4 = aw 0 (2m+2) (2 ↑^(2m+1) 4)], and unfolding the outer
    multiplication-level gives [round m + 2 = aw 1 (2m+1) (2 ↑^(2m+1) 4)]. *)

Lemma round_closed : forall x,
  2 * round x + 4 = aw 0 (2 * x + 2) (knuth (2 * x + 1) 2 4).
Proof.
  intros x. unfold round.
  rewrite (desc_closed_gen (2 * x + 2) (g (2 * x + 2) 0) ltac:(lia)).
  assert (Hg := g_closed (2 * x + 1) 0%nat).
  replace (S (2 * x + 1)) with (2 * x + 2) in Hg by lia.
  replace (2 * 0 + 4) with 4 in Hg by lia.
  rewrite Hg. reflexivity.
Qed.

Lemma round_eq_aw1 : forall x,
  round x + 2 = aw 1 (2 * x + 1) (knuth (2 * x + 1) 2 4).
Proof.
  intros x.
  assert (H := round_closed x).
  replace (2 * round x + 4) with (2 * (round x + 2)) in H by lia.
  assert (Heq : aw 0 (2 * x + 2) (knuth (2 * x + 1) 2 4)
                = 2 * aw 1 (2 * x + 1) (knuth (2 * x + 1) 2 4))
    by ltac:(replace (2 * x + 2) with (S (2 * x + 1)) by lia;
             rewrite aw_S; simpl; reflexivity).
  rewrite Heq in H. lia.
Qed.

(** The innermost level of that expression is [2 ↑^(2x+2) 4]. *)
Lemma aw1_lower : forall x,
  knuth (2 * x + 2) 2 4 <= aw 1 (2 * x + 1) (knuth (2 * x + 1) 2 4).
Proof.
  intros x.
  assert (H := aw_chain 1 (2 * x) (knuth (2 * x + 1) 2 4)).
  replace (1 + 2 * x) with (S (2 * x)) in H by lia.
  replace (2 * x + 1) with (S (2 * x)) in H by lia.
  rewrite <- (knuth_SS4 (2 * x)) in H.
  replace (2 * x + 2) with (S (S (2 * x))) by lia.
  replace (2 * x + 1) with (S (2 * x)) by lia.
  exact H.
Qed.

(** ** The fast-growing functions f_omega and f_(omega+1). *)

Definition f_omega (n : nat) : nat := knuth (S n) 2 (n + 3).
Definition f_omega1 (n : nat) : nat := Nat.iter n f_omega n.

Lemma f_omega_ge2n6 : forall n, 2 * n + 6 <= f_omega n.
Proof.
  intros n. unfold f_omega.
  assert (H := knuth_ge2' (S n) (n + 3)). lia.
Qed.

Lemma f_omega_strict_step : forall n, f_omega n < f_omega (S n).
Proof.
  intros n. unfold f_omega.
  assert (H1 : knuth (S n) 2 (n + 3) < knuth (S n) 2 (S (n + 3)))
    by (apply knuth_strict_b; lia).
  assert (H2 : knuth (S n) 2 (S (n + 3)) <= knuth (S (S n)) 2 (S (n + 3)))
    by (apply knuth_mono_arrow; lia).
  replace (S n + 3) with (S (n + 3)) by lia.
  lia.
Qed.

Lemma f_omega_strict : forall a b, a < b -> f_omega a < f_omega b.
Proof.
  intros a b. revert a.
  induction b as [|b IH]; intros a H.
  - lia.
  - destruct (Nat.eq_dec a b) as [Heq | Hne].
    + subst. apply f_omega_strict_step.
    + assert (Ha : a < b) by lia.
      eapply Nat.lt_trans; [apply IH; exact Ha | apply f_omega_strict_step].
Qed.

Lemma iter_fomega_pos : forall n i, 1 <= n -> 1 <= Nat.iter i f_omega n.
Proof.
  intros n i Hn. induction i as [|i IH].
  - simpl. exact Hn.
  - simpl. assert (H := f_omega_ge2n6 (Nat.iter i f_omega n)). lia.
Qed.

(** f_omega x is bounded by knuth (2x+2) 2 4 for x >= 1. *)
Lemma f_omega_le_knuth : forall x, 1 <= x ->
  f_omega x <= knuth (2 * x + 2) 2 4.
Proof.
  intros x Hx. unfold f_omega.
  assert (Harg : knuth (S x) 2 (x + 3) <= knuth (S x) 2 (S x + 4))
    by (apply knuth_incr; lia).
  assert (Hdom : knuth (S (S (S x))) 2 4 > knuth (S x) 2 (S x + 4))
    by (apply knuth_2_4_S).
  assert (Hmono : knuth (S (S (S x))) 2 4 <= knuth (2 * x + 2) 2 4)
    by (apply knuth_mono_arrow; lia).
  lia.
Qed.

(** ** One round beats f_omega at the same parameter. *)
Lemma round_gt_fomega : forall x, 1 <= x -> f_omega x < round x.
Proof.
  intros x Hx.
  assert (Hquad : 4 * f_omega x <= knuth (S x) 2 (S x + 4)).
  { unfold f_omega.
    assert (H := knuth_arg_add2_quad x (x + 3)).
    replace ((x + 3) + 2) with (S x + 4) in H by lia.
    exact H. }
  assert (Hdom : knuth (S x) 2 (S x + 4) < knuth (2 * x + 2) 2 4).
  { assert (H1 : knuth (S x) 2 (S x + 4) < knuth (S (S (S x))) 2 4)
      by (apply knuth_2_4_S).
    assert (H2 : knuth (S (S (S x))) 2 4 <= knuth (2 * x + 2) 2 4)
      by (apply knuth_mono_arrow; lia).
    lia. }
  assert (Haw := aw1_lower x).
  assert (Hr := round_eq_aw1 x).
  assert (HT : 3 <= f_omega x).
  { assert (H := f_omega_ge2n6 x). lia. }
  lia.
Qed.

(** Round is increasing enough to beat [x+1], so iterating it never stalls. *)
Lemma round_gt_succ : forall x, 1 <= x -> S x <= round x.
Proof.
  intros x Hx.
  assert (H := round_gt_fomega x Hx).
  assert (HF := f_omega_ge2n6 x).
  lia.
Qed.

Lemma iter_round_pos : forall i x, 1 <= x -> 1 <= Nat.iter i round x.
Proof.
  intros i x. induction i as [|i IH]; intros Hx.
  - simpl. exact Hx.
  - simpl. assert (HP : 1 <= Nat.iter i round x) by (exact (IH Hx)).
    assert (HS : S (Nat.iter i round x) <= round (Nat.iter i round x))
      by (apply round_gt_succ; exact HP).
    lia.
Qed.

(** The same number of iterations, starting at a positive point, is strictly
    larger for [round] than for [f_omega]. *)
Lemma iter_round_gt_fomega : forall i x, 1 <= i -> 1 <= x ->
  Nat.iter i f_omega x < Nat.iter i round x.
Proof.
  intros i. induction i as [|i IH]; intros x Hi Hx.
  - lia.
  - destruct i as [|i].
    + simpl. apply round_gt_fomega. exact Hx.
    + rewrite (iter_succ_l f_omega (S i) x), (iter_succ_l round (S i) x).
      assert (Hlt : Nat.iter (S i) f_omega x < Nat.iter (S i) round x)
        by (apply IH; lia).
      assert (Hpos : 1 <= Nat.iter (S i) round x)
        by (apply iter_round_pos; exact Hx).
      assert (HFlt : f_omega (Nat.iter (S i) f_omega x)
                     < f_omega (Nat.iter (S i) round x))
        by (apply f_omega_strict; exact Hlt).
      assert (HRlt : f_omega (Nat.iter (S i) round x)
                     < round (Nat.iter (S i) round x))
        by (apply round_gt_fomega; exact Hpos).
      lia.
Qed.

(** Iterating a strictly increasing function is strictly increasing. *)
Lemma iter_fomega_strict_count : forall i a b, a < b ->
  Nat.iter i f_omega a < Nat.iter i f_omega b.
Proof.
  intros i. induction i as [|i IH]; intros a b Hab.
  - exact Hab.
  - rewrite (iter_succ_l f_omega i a), (iter_succ_l f_omega i b).
    apply f_omega_strict. apply IH. exact Hab.
Qed.

(** ** Iterating [round] beats iterating [f_omega] with an offset. *)

Transparent next.

Lemma next_eq : forall m, next m = Nat.iter (2 * m + 2) round 6%nat.
Proof. intros m. reflexivity. Qed.

Lemma R_ge_add : forall k, 6 + k <= Nat.iter k round 6%nat.
Proof.
  intros k. induction k as [|k IH].
  - simpl. lia.
  - simpl. assert (HP : 1 <= Nat.iter k round 6%nat) by
      (assert (H : 6 + k <= Nat.iter k round 6%nat) by exact IH; lia).
    assert (HS : S (Nat.iter k round 6%nat) <= round (Nat.iter k round 6%nat))
      by (apply round_gt_succ; exact HP).
    lia.
Qed.

Lemma R_strict : forall n m, n < m ->
  Nat.iter n round 6%nat < Nat.iter m round 6%nat.
Proof.
  intros n m Hnm.
  apply (iter_strict round m 6%nat
           ltac:(intros y Hy; assert (H := round_gt_succ y Hy); lia)
           ltac:(intros y Hy; assert (H := round_gt_succ y Hy); lia)
           ltac:(lia) n Hnm).
Qed.

Lemma iter_fo_lt_R_offset : forall i x y d,
  1 <= x -> 1 <= y -> x < Nat.iter d round y ->
  Nat.iter i f_omega x < Nat.iter (i + d) round y.
Proof.
  intros i. induction i as [|i IH]; intros x y d Hx Hy Hxd.
  - simpl. exact Hxd.
  - replace (S i + d) with (S (i + d)) by lia.
    rewrite (iter_succ_l f_omega i x), (iter_succ_l round (i + d) y).
    assert (Hlt : Nat.iter i f_omega x < Nat.iter (i + d) round y)
      by (apply IH; [exact Hx | exact Hy | exact Hxd]).
    assert (Hf : f_omega (Nat.iter i f_omega x)
                 < f_omega (Nat.iter (i + d) round y))
      by (apply f_omega_strict; exact Hlt).
    assert (Hp : 1 <= Nat.iter (i + d) round y)
      by (apply iter_round_pos; exact Hy).
    assert (Hr : f_omega (Nat.iter (i + d) round y)
                 < round (Nat.iter (i + d) round y))
      by (apply round_gt_fomega; exact Hp).
    lia.
Qed.

(** The initial three rounds already beat [f_omega^3(14)]. *)

Lemma base_fo3_lt_m2 : Nat.iter 3 f_omega 14%nat < m2.
Proof.
  assert (H14 : 14%nat < round 6%nat).
  { assert (H := round_gt_fomega 6%nat ltac:(lia)).
    assert (HF := f_omega_ge2n6 6%nat). lia. }
  assert (H0 : Nat.iter 3 f_omega 14%nat < Nat.iter (3 + 1) round 6%nat).
  { apply iter_fo_lt_R_offset; [lia | lia | simpl; exact H14]. }
  replace (3 + 1) with 4 in H0 by lia.
  assert (Hm1 : 9%nat <= m1) by
    (rewrite m1_eq; apply R_ge_add).
  assert (Hcnt : 4 < 2 * m1 + 2) by lia.
  assert (H1 : Nat.iter 4 round 6%nat < Nat.iter (2 * m1 + 2) round 6%nat)
    by (apply R_strict; exact Hcnt).
  rewrite m2_eq, next_eq.
  eapply Nat.lt_trans; [exact H0 | exact H1].
Qed.

(** One reset absorbs one application of [f_omega1] at any point already
    reached by a block of rounds. *)
Lemma fomega1_lt_next_of_ltR : forall x K,
  1 <= x -> x < Nat.iter K round 6%nat ->
  f_omega1 x < Nat.iter (2 * Nat.iter K round 6%nat + 2) round 6%nat.
Proof.
  intros x K Hx HxR.
  assert (HRp : 1 <= Nat.iter K round 6%nat) by (apply iter_round_pos; lia).
  assert (HKR : K < Nat.iter K round 6%nat) by
    (assert (H := R_ge_add K); lia).
  assert (H0 : f_omega1 x < Nat.iter (x + K) round 6%nat).
  { unfold f_omega1.
    apply iter_fo_lt_R_offset; [exact Hx | lia | exact HxR]. }
  assert (Hcnt : x + K < 2 * Nat.iter K round 6%nat + 2) by lia.
  assert (H1 : Nat.iter (x + K) round 6%nat
               < Nat.iter (2 * Nat.iter K round 6%nat + 2) round 6%nat)
    by (apply R_strict; exact Hcnt).
  eapply Nat.lt_trans; [exact H0 | exact H1].
Qed.

Lemma m2_as_R : m2 = Nat.iter (2 * m1 + 2) round 6%nat.
Proof. rewrite m2_eq, next_eq. reflexivity. Qed.

Lemma m3_as_R : m3 = Nat.iter (2 * m2 + 2) round 6%nat.
Proof. rewrite m3_eq, next_eq. reflexivity. Qed.

Lemma m4_as_R : m4 = Nat.iter (2 * m3 + 2) round 6%nat.
Proof. rewrite m4_eq, next_eq. reflexivity. Qed.

Lemma fomega1_lt_next_of_ltR' : forall x K m,
  1 <= x -> m = Nat.iter K round 6%nat -> x < m -> f_omega1 x < next m.
Proof.
  intros x K m Hx Hm Hxm.
  rewrite Hm. rewrite Hm in Hxm.
  apply (fomega1_lt_next_of_ltR x K Hx Hxm).
Qed.

Lemma fomega1_pos : forall n, 1 <= n -> 1 <= f_omega1 n.
Proof.
  intros n Hn. unfold f_omega1. apply iter_fomega_pos. exact Hn.
Qed.

Lemma fomega1_iter3_lt_m5 :
  Nat.iter 3 f_omega1 (Nat.iter 3 f_omega 14%nat) < m5.
Proof.
  assert (HApos : 1 <= Nat.iter 3 f_omega 14%nat) by
    (apply iter_fomega_pos; lia).
  assert (H0 := base_fo3_lt_m2).
  assert (H1 : f_omega1 (Nat.iter 3 f_omega 14%nat) < m3).
  { rewrite m3_eq.
    apply (fomega1_lt_next_of_ltR' (Nat.iter 3 f_omega 14%nat) (2 * m1 + 2) m2
             HApos m2_as_R H0). }
  assert (H1pos : 1 <= f_omega1 (Nat.iter 3 f_omega 14%nat))
    by (apply fomega1_pos; exact HApos).
  assert (H2 : f_omega1 (f_omega1 (Nat.iter 3 f_omega 14%nat)) < m4).
  { rewrite m4_eq.
    apply (fomega1_lt_next_of_ltR' (f_omega1 (Nat.iter 3 f_omega 14%nat))
             (2 * m2 + 2) m3 H1pos m3_as_R H1). }
  assert (H2pos : 1 <= f_omega1 (f_omega1 (Nat.iter 3 f_omega 14%nat)))
    by (apply fomega1_pos; exact H1pos).
  assert (H3 : f_omega1 (f_omega1 (f_omega1 (Nat.iter 3 f_omega 14%nat))) < m5).
  { rewrite m5_eq.
    apply (fomega1_lt_next_of_ltR'
             (f_omega1 (f_omega1 (Nat.iter 3 f_omega 14%nat)))
             (2 * m3 + 2) m4 H2pos m4_as_R H2). }
  change (f_omega1 (f_omega1 (f_omega1 (Nat.iter 3 f_omega 14%nat))) < m5).
  exact H3.
Qed.

Lemma fomega1_iter3_lt_sigma :
  Nat.iter 3 f_omega1 (Nat.iter 3 f_omega 14%nat) < sigma.
Proof.
  assert (H := fomega1_iter3_lt_m5).
  unfold sigma. rewrite mfin_eq. lia.
Qed.

(** ** Main theorem of this file. *)
Theorem bb83_main :
  halts tm c0 /\
  c0 -[ tm ]->* c_final /\
  halted tm c_final /\
  sigma = 2 * mfin + 7 /\
  Nat.iter 3 f_omega1 (Nat.iter 3 f_omega 14%nat) < sigma.
Proof.
  split; [exact bb83_halts |].
  split; [exact reaches_final |].
  split; [exact final_halted |].
  split; [reflexivity |].
  exact fomega1_iter3_lt_sigma.
Qed.

