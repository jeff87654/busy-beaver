(** * Score machinery for the BB(3,5) champion
      1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC *)

(** Main results ([knuth 15 2 5] is 2 with 15 Knuth up-arrows applied to 5):
      bb35_main      : the machine halts from the blank tape, with the exact
                      final tape, and
                      sigma = 2 * mfin + 4  >  f_omega (2 ↑^15 5),
                      where [f_omega n = 2 ↑^(n+1) (n+3)] is the omega-th
                      element of the fast-growing hierarchy in arrow normal form;
      g_closed       : 2 * g_(k+1)(m) + 4 = knuth k 2 (2m+4)   (closed form of
                      the g hierarchy)
      g_iter_closed  : 2 * g_k^n(0) + 4 = knuth k 2 (n+2)
      desc_closed    : 2 * desc n m + 4 = the nested Knuth expression
                      2 ↑^0 (2 ↑^1 (... (2 ↑^(n-1) (2m+4)) ...))
    No large number is ever evaluated: [knuth 15 2 5], the sealed [g15] and the
    sealed [mfin] stay symbolic throughout.

    The BB(3,5)-specific phase that follows the descent (the analysis of which
    is in ../1RB3LB4LC2RA4LB_2LC3RB1LC2RA1RZ_3RB1LB3LC2RC4LC.md) contributes
    the final score; see the write-up for the exact value and for the parts
    that are still informal. *)

From TM35 Require Import Individual35 BB35_rules BB35_run.
From Coq Require Import Lia PeanoNat List.
From Coq.micromega Require Import ZifyNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(** ** Knuth up-arrows: [knuth n a b = a ↑^n b], with [a ↑^0 b = a * b] *)
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

Lemma knuth_S : forall n a b, knuth (S n) a (S b) = knuth n a (knuth (S n) a b).
Proof. reflexivity. Qed.

Lemma knuth_S0 : forall k b, knuth (S k) 2 b = Nat.iter b (knuth k 2) 1.
Proof. reflexivity. Qed.

(** The coincidence 2 ↑^k 2 = 4 for all k, on which the closed form rests. *)
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

Lemma knuth_step4 : forall k j, Nat.iter (j + 2) (knuth k 2) 1 = Nat.iter j (knuth k 2) 4.
Proof.
  intros k j. rewrite (iter_add (knuth k 2) j 2 1). rewrite iter2_knuth. reflexivity.
Qed.

(** Four iterations, spelled out; this is what turns 2 ↑^k 4 into a nested
    expression over the previous level. *)
Lemma iter4 : forall (f : nat -> nat) x, Nat.iter 4 f x = f (f (f (f x))).
Proof. intros f x. simpl. reflexivity. Qed.

(** ** The closed form of the g hierarchy: 2 g_(k+1)(m) + 4 = 2 ↑^k (2m+4) *)

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
  - (* k = 0:  g 1 m = 2m+2 *)
    assert (E : g 1 m = 2 * m + 2).
    { assert (E2 : g 1 m = Nat.iter (2 * m + 2) (g 0) 0%nat) by reflexivity.
      rewrite E2. rewrite (iter_g0 (2 * m + 2) 0%nat). lia. }
    rewrite E. simpl. lia.
  - (* k -> S k *)
    assert (E : g (S (S k)) m = Nat.iter (2 * m + 2) (g (S k)) 0) by reflexivity.
    rewrite E.
    rewrite (iter_closed_helper (g (S k)) (knuth k 2) IH (2 * m + 2) 0).
    change (2 * 0 + 4) with 4.
    rewrite (knuth_S0 k (2 * m + 4)).
    replace (2 * m + 4) with (2 * m + 2 + 2) by lia.
    rewrite (iter_add (knuth k 2) (2 * m + 2) 2 1).
    rewrite iter2_knuth.
    reflexivity.
Qed.

(** Corollary (Ligocki): 2 g_k^n(0) + 4 = 2 ↑^k (n + 2) *)
Theorem g_iter_closed : forall k n,
  2 * Nat.iter n (g k) 0%nat + 4 = knuth k 2 (n + 2).
Proof.
  intros k n. destruct k as [|k].
  - rewrite iter_g0. simpl. lia.
  - rewrite (iter_closed_helper (g (S k)) (knuth k 2) (g_closed k) n 0).
    change (2 * 0 + 4) with 4.
    rewrite (knuth_S0 k (n + 2)).
    rewrite (iter_add (knuth k 2) n 2 1).
    rewrite iter2_knuth.
    reflexivity.
Qed.

(** The same statement with the number abstracted.  This is the bridge used to
    instantiate the closed form with the sealed [g15] of BB35_run.v without
    ever evaluating it. *)
Theorem g_iter_closed_gen : forall k n (x : nat),
  x = Nat.iter n (g k) 0%nat -> 2 * x + 4 = knuth k 2 (n + 2).
Proof. intros k n x Hx. subst x. apply g_iter_closed. Qed.

(** [g15 = g_15^3(0)] satisfies the closed form with k = 15, n = 3:
    2 * g15 + 4 = 2 ↑^15 5. *)
Lemma g15_closed : 2 * g15 + 4 = knuth 15 2 5.
Proof. exact (g_iter_closed_gen 15 3 g15 g15_eq). Qed.

(** ** Elementary facts about the Knuth arrows.

    [knuth n 2] grows at least like [x+1] (so its iterates are increasing), it
    is at least the identity, at least [2x], increasing in its argument, and
    the whole family is increasing in the number of arrows. *)

(** Iterating a function that is at least [y+1] gives a sequence that grows by
    at least one at each step. *)
Lemma iter_ge1 : forall (f : nat -> nat),
  (forall y, 1 <= y -> y + 1 <= f y) ->
  forall x, x + 1 <= Nat.iter x f 1.
Proof.
  intros f Hf x. induction x as [|x IH].
  - simpl. lia.
  - simpl. apply Nat.le_trans with (Nat.iter x f 1 + 1); [lia|].
    apply Hf. lia.
Qed.

Lemma knuth_ge1 : forall n x, 1 <= x -> x + 1 <= knuth n 2 x.
Proof.
  intros n. induction n as [|n IHn]; intros x Hx.
  - simpl. lia.
  - simpl. apply iter_ge1. intros y Hy. apply IHn. lia.
Qed.

(** [knuth n 2 x >= 2x] for all [x] (also [x = 0]): the iterates at least
    double. *)
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

(** [knuth n 2 x >= x]. *)
Lemma knuth_ge_id : forall n x, x <= knuth n 2 x.
Proof.
  intros n. induction n as [|n IH]; intros x.
  - simpl. lia.
  - simpl.
    assert (H : x + 1 <= Nat.iter x (knuth n 2) 1).
    { apply iter_ge1. intros y Hy. apply knuth_ge1. exact Hy. }
    lia.
Qed.

(** [knuth n 2 x] is positive whenever [x] is. *)
Lemma knuth_pos : forall n x, 1 <= x -> 1 <= knuth n 2 x.
Proof.
  intros n x Hx. assert (H := knuth_ge_id n x). lia.
Qed.

(** Iterates stay at least 1. *)
Lemma iter_pos : forall (f : nat -> nat) n x,
  (forall y, 1 <= y -> 1 <= f y) -> 1 <= x -> 1 <= Nat.iter n f x.
Proof.
  intros f n. induction n as [|n IH]; intros x Hf Hx.
  - simpl. exact Hx.
  - simpl. apply Hf. apply IH; [exact Hf | exact Hx].
Qed.

(** A non-decreasing function that is at least the identity has non-decreasing
    iterates. *)
Lemma iter_mono_count : forall (f : nat -> nat) n m x,
  (forall y, f y <= f (S y)) -> (forall y, y <= f y) ->
  n <= m -> Nat.iter n f x <= Nat.iter m f x.
Proof.
  intros f n m x Hinc Hge Hnm.
  induction Hnm as [|m Hm IH].
  - lia.
  - simpl. apply Nat.le_trans with (Nat.iter m f x); [exact IH|].
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

(** Strict increase of the iterates of a function that grows by at least 1. *)
Lemma iter_strict : forall (f : nat -> nat) m x,
  (forall y, 1 <= y -> y + 1 <= f y) ->
  (forall y, 1 <= y -> 1 <= f y) ->
  1 <= x ->
  forall n, n < m -> Nat.iter n f x < Nat.iter m f x.
Proof.
  intros f m. induction m as [|m IH]; intros x Hf Hpos Hx n Hnm.
  - lia.
  - destruct (Nat.eq_dec n m) as [Heq|Hne].
    + subst n. simpl. apply Nat.lt_le_trans with (Nat.iter m f x + 1); [lia|].
      apply Hf. apply iter_pos; [exact Hpos|exact Hx].
    + assert (Hn : n < m) by lia.
      assert (Hlt : Nat.iter n f x < Nat.iter m f x)
        by (apply IH; [exact Hf|exact Hpos|exact Hx|exact Hn]).
      simpl. apply Nat.lt_le_trans with (Nat.iter m f x + 1); [lia|].
      apply Hf. apply iter_pos; [exact Hpos|exact Hx].
Qed.

(** [knuth n 2] is increasing in its argument. *)
Lemma knuth_incr : forall n, forall x y, x <= y -> knuth n 2 x <= knuth n 2 y.
Proof.
  intros n. induction n as [|n IH]; intros x y Hxy.
  - simpl. lia.
  - simpl. apply iter_mono_count.
    + intros z. apply IH. lia.
    + intros z. apply knuth_ge_id.
    + lia.
Qed.

(** The whole family is increasing in the number of arrows. *)
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

(** ** Two comparisons of the arrow family that will be needed.

    The nested form of one level: [knuth (S n) 2 4 = knuth n 2 (knuth n 2 4)]. *)
Lemma knuth_S4 : forall n, knuth (S n) 2 4 = knuth n 2 (knuth n 2 4).
Proof.
  intros n. rewrite (knuth_S0 n 4). rewrite iter4.
  rewrite knuth_1, knuth_2. reflexivity.
Qed.

(** The nested form of two levels:
    [knuth (S (S n)) 2 4 = knuth (S n) 2 (knuth (S n) 2 4)]. *)
Lemma knuth_SS4 : forall n, knuth (S (S n)) 2 4 = knuth (S n) 2 (knuth (S n) 2 4).
Proof.
  intros n. rewrite (knuth_S0 (S n) 4). rewrite iter4.
  rewrite knuth_1, knuth_2. reflexivity.
Qed.

(** [knuth n 2 4] is at least [n+5]: one more arrow multiplies the value by at
    least 2, and [knuth 1 2 4 = 16]. *)
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

(** The key comparison: two more arrows beat a bigger argument.
    [2 ↑^(k+3) 4 > 2 ↑^(k+1) (k+5)] (the form needed below: the number of
    arrows on the left is a successor of the number on the right). *)
Lemma knuth_2_4_S : forall k, knuth (S (S (S k))) 2 4 > knuth (S k) 2 (S k + 4).
Proof.
  intros k.
  assert (E1 : knuth (S (S (S k))) 2 4
                = Nat.iter (knuth (S k) 2 (knuth (S k) 2 4)) (knuth (S k) 2) 1).
  { rewrite knuth_SS4. rewrite (knuth_S0 (S k) (knuth (S(S k)) 2 4)). rewrite knuth_SS4.
    reflexivity. }
  assert (E2 : knuth (S k) 2 (S k + 4) = Nat.iter (S k + 4) (knuth k 2) 1)
    by (rewrite knuth_S0; reflexivity).
  rewrite E1, E2.
  assert (H1 : S k + 5 <= knuth (S k) 2 4) by (apply knuth_4_ge).
  assert (H2 : knuth (S k) 2 (S k + 5) <= knuth (S k) 2 (knuth (S k) 2 4))
    by (apply knuth_incr; lia).
  assert (H3 : S k + 5 + 1 <= knuth (S k) 2 (S k + 5)) by (apply knuth_ge1; lia).
  (* the left count is strictly bigger than the right one *)
  assert (H4 : S k + 4 < knuth (S k) 2 (knuth (S k) 2 4)) by lia.
  (* the right count is taken with the lower arrow count: *)
  assert (HB : Nat.iter (S k + 4) (knuth k 2) 1
              <= Nat.iter (S k + 4) (knuth (S k) 2) 1).
  { apply iter_mono_fun.
    - intros z. apply knuth_mono_arrow. lia.
    - intros a b Hab. apply knuth_incr. exact Hab. }
  (* the two iterates with the higher arrow count are strictly ordered: *)
  assert (HA : Nat.iter (S k + 4) (knuth (S k) 2) 1
              < Nat.iter (knuth (S k) 2 (knuth (S k) 2 4)) (knuth (S k) 2) 1).
  { apply iter_strict.
    - intros y Hy. apply knuth_ge1. exact Hy.
    - intros y Hy. apply knuth_pos. exact Hy.
    - lia.
    - exact H4. }
  lia.
Qed.

(** ** The nested Knuth expression.

    [aw j n x] is  2 ↑^j (2 ↑^(j+1) ( ... (2 ↑^(n-1) x) ... )): the arrow
    counts run from [j] (outermost) to [n-1] (innermost). *)
Fixpoint aw (j n : nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n' => knuth j 2 (aw (S j) n' x)
  end.

(** The two defining equations of [aw], in a usable form. *)
Lemma aw_0 : forall j x, aw j 0 x = x.
Proof. intros j x. reflexivity. Qed.

Lemma aw_S : forall j n x, aw j (S n) x = knuth j 2 (aw (S j) n x).
Proof. intros j n x. reflexivity. Qed.

(** Dropping the outermost Knuth application. *)
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

(** The chain: dropping the outer Knuth applications one at a time, [aw j n x]
    is at least [knuth (j+n-1) 2 x]. *)
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
    rewrite aw_S.
    lia.
Qed.

(** A strictly better lower bound for the outermost level: the score is at
    least twice its innermost term, hence strictly bigger. *)
Lemma aw_0_strict : forall n x, 1 <= x ->
  knuth (S n) 2 x < aw 0 (S (S n)) x.
Proof.
  intros n x Hx.
  assert (H1 : knuth (1 + n) 2 x <= aw 1 (S n) x) by (apply aw_chain).
  replace (1 + n) with (S n) in H1 by lia.
  assert (H3 : 0 < knuth (S n) 2 x).
  { apply Nat.lt_le_trans with (2 * x); [lia|apply knuth_ge2']. }
  change (knuth (S n) 2 x < 2 * aw 1 (S n) x).
  lia.
Qed.

(** ** The closed form of the rule-2 phase.

    [desc n m] is the value of the "m" parameter after the rule-2 phase: the
    descent applies [g_n], [g_(n-1)], ..., [g_1], and each of those is captured
    by the closed form of the g hierarchy.  The result is the nested Knuth
    expression [2 ↑^0 (2 ↑^1 (... (2 ↑^(n-1) (2m+4)) ...))]. *)
Lemma desc_closed_gen : forall n m, 1 <= n ->
  2 * desc n m + 4 = aw 0 n (2 * m + 4).
Proof.
  intros n m Hn. revert m.
  induction n as [|n IHn]; intros m.
  - lia.
  - destruct n as [|n].
    + (* n = 1:  desc 1 m = g 1 m = 2m+2 *)
      assert (E : desc 1 m = 2 * m + 2).
      { cbn [desc].
        assert (E2 : g 1 m = Nat.iter (2 * m + 2) (g 0) 0%nat) by reflexivity.
        rewrite E2. rewrite (iter_g0 (2 * m + 2) 0%nat). lia. }
      rewrite E. simpl. lia.
    + (* n = S (S n) *)
      assert (Hn' : 1 <= S n) by lia.
      rewrite (desc_S (S n) m).
      rewrite (IHn Hn' (g (S (S n)) m)).
      rewrite (g_closed (S n) m).
      rewrite <- (aw_shift 0 (S n) (2 * m + 4)).
      replace (S n + 0) with (S n) by lia.
      reflexivity.
Qed.

(** ** The fast-growing function at [omega].

    The Busy Beaver wiki states the runtime of the BB(3,5) champion as
    [> f_omega (2 ↑^15 5)], where [f_omega] is the omega-th element of the
    fast-growing hierarchy (Wainer's convention [F_0(n) = n+3],
    [F_{k+1}(n) = F_k^{n+3}(n)], [F_omega(n) = F_n(n)]).

    We use the Knuth-arrow normal form of that function,
    [f_omega n = 2 ↑^(n+1) (n+3)], which is an upper bound for [F_n(n)]
    (the classical arrow/FGH correspondence), so every inequality proved with
    it is also valid for the hierarchy's own value. *)
Definition f_omega (n : nat) : nat := knuth (S n) 2 (n + 3).

(** ** The score.

    The final tape is [0^inf 3^(2 mfin + 3) B> 4 0^inf]: the block of 3s has
    [2 mfin + 3] cells and the head reads a 4, so the number of nonzero cells
    is [2 mfin + 4]. *)
Definition sigma : nat := 2 * mfin + 4.

(** The nonzero cells of the final tape, from left to right. *)
Definition final_cells : list sym := [S3]^^(2 * mfin + 3) ++ [S4].

Lemma lpow_length : forall j (ys : list sym), length (ys ^^ j) = j * length ys.
Proof.
  induction j as [|j IH]; intros ys.
  - reflexivity.
  - simpl. rewrite length_app, IH. lia.
Qed.

Lemma in_lpow : forall j (ys : list sym) x, In x (ys ^^ j) -> In x ys.
Proof.
  induction j as [|j IH]; intros ys x H.
  - destruct H.
  - simpl in H. apply in_app_or in H as [H | H].
    + exact H.
    + exact (IH ys x H).
Qed.

Lemma cells_count : forall (x : nat),
  length ([S3]^^(2 * x + 3) ++ [S4]) = 2 * x + 4.
Proof.
  intros x.
  rewrite !length_app, (lpow_length (2 * x + 3) [S3]).
  simpl. lia.
Qed.

Lemma final_cells_count : length final_cells = sigma.
Proof. unfold final_cells, sigma. apply cells_count. Qed.

Lemma cells_nonblank : forall (x : nat) (y : sym),
  In y ([S3]^^(2 * x + 3) ++ [S4]) -> y <> S0.
Proof.
  intros x y H.
  apply in_app_or in H as [H | H].
  - apply in_lpow in H. simpl in H. intuition congruence.
  - simpl in H. intuition congruence.
Qed.

Lemma final_cells_all_nonblank : forall x, In x final_cells -> x <> S0.
Proof. intros y H. unfold final_cells in H. exact (cells_nonblank mfin y H). Qed.

(** ** The main comparison.

    The rule-2 phase runs [N = K+12] times, where [K = 2 g15 + 4 = 2 ↑^15 5];
    the "m" parameter at the end is [mfin = desc N 0], and the closed form
    [desc_closed_gen] turns the score into the nested Knuth expression

        sigma = 2 ↑^0 (2 ↑^1 (... (2 ↑^(N-1) 4) ...)),

    whose innermost term is [2 ↑^(N-1) 4].  That term alone already exceeds
    [f_omega K = 2 ↑^(K+1) (K+3)]: ten more arrows than [K+1] certainly beat
    the bigger argument [K+3] (Lemma [knuth_2_4] needs only two). *)

(** The score is the nested Knuth expression. *)
Lemma sigma_closed : sigma = aw 0 (2 * g15 + 16) 4.
Proof.
  unfold sigma, mfin.
  rewrite (desc_closed_gen (2 * g15 + 16) 0).
  - reflexivity.
  - lia.
Qed.

(** The innermost term of the nested expression bounds the score from below. *)
Lemma sigma_lower_gen : forall (x : nat),
  knuth (2 * x + 15) 2 4 < aw 0 (2 * x + 16) 4.
Proof.
  intros x.
  replace (2 * x + 15) with (S (2 * x + 14)) by lia.
  replace (2 * x + 16) with (S (S (2 * x + 14))) by lia.
  apply aw_0_strict. lia.
Qed.

(** The comparison of the two arrow expressions. *)
Lemma chain_gen : forall x,
  knuth (2 * x + 15) 2 4 > knuth (2 * x + 5) 2 (2 * x + 7).
Proof.
  intros x.
  assert (H2 : knuth (2 * x + 7) 2 4 > knuth (2 * x + 5) 2 (2 * x + 9)).
  { replace (2 * x + 7) with (S (S (S (2 * x + 4)))) by lia.
    replace (2 * x + 5) with (S (2 * x + 4)) by lia.
    replace (2 * x + 9) with (S (2 * x + 4) + 4) by lia.
    assert (H := knuth_2_4_S (2 * x + 4)). lia. }
  assert (H3 : knuth (2 * x + 5) 2 (2 * x + 7) <= knuth (2 * x + 5) 2 (2 * x + 9))
    by (apply knuth_incr; lia).
  assert (H1 : knuth (2 * x + 7) 2 4 <= knuth (2 * x + 15) 2 4)
    by (apply knuth_mono_arrow; lia).
  lia.
Qed.

(** The score exceeds the omega-th fast-growing function at [2 ↑^15 5]. *)
Theorem sigma_gt_fomega : knuth (S (2 * g15 + 4)) 2 (2 * g15 + 4 + 3) < sigma.
Proof.
  replace (S (2 * g15 + 4)) with (2 * g15 + 5) by lia.
  replace (2 * g15 + 4 + 3) with (2 * g15 + 7) by lia.
  rewrite sigma_closed.
  apply Nat.lt_le_trans with (knuth (2 * g15 + 15) 2 4).
  - assert (H := chain_gen g15). lia.
  - assert (H := sigma_lower_gen g15). lia.
Qed.

(** In the notation of the wiki: [f_omega (2 ↑^15 5) < sigma]. *)
Corollary fomega_lt_sigma : f_omega (knuth 15 2 5) < sigma.
Proof.
  unfold f_omega. rewrite <- g15_closed. apply sigma_gt_fomega.
Qed.

(** ** Main theorem of this file: the machine halts, with the exact score, and
    the score is above the omega-th fast-growing function at [2 ↑^15 5]. *)
Theorem bb35_main :
  halts tm c0 /\
  c0 -[ tm ]->* c_final /\
  halted tm c_final /\
  sigma = 2 * mfin + 4 /\
  f_omega (knuth 15 2 5) < sigma.
Proof.
  split; [exact bb35_halts |].
  split; [exact reaches_final |].
  split; [exact final_halted |].
  split; [reflexivity |].
  exact fomega_lt_sigma.
Qed.
