(** * Up-arrow lower bounds for the clearing functions U, W of Clr.v (machine independent) *)
From BB7 Require Import Defs Clr.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".

(** arrow (Knuth's up-arrows) is defined in Defs.v. *)
Lemma arrow_0 : forall a b, arrow 0 a b = a * b.
Proof. reflexivity. Qed.
Lemma arrow_S0 : forall k a, arrow (S k) a 0 = 1.
Proof. reflexivity. Qed.
Lemma arrow_SS : forall k a b, arrow (S k) a (S b) = arrow k a (arrow (S k) a b).
Proof. reflexivity. Qed.
Lemma arrow_1_pow : forall a b, arrow 1 a b = a ^ b.
Proof. intros a b. induction b; [reflexivity |]. rewrite arrow_SS, IHb, arrow_0. simpl. lia. Qed.
Lemma arrow_S_iter : forall k a b, arrow (S k) a b = iter b (arrow k a) 1.
Proof. induction b. - reflexivity. - rewrite arrow_SS, IHb. reflexivity. Qed.

Opaque arrow.

Lemma iter_mono_n : forall g, (forall x, x <= g x) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. induction Hnm; [lia |]. simpl. specialize (Hg (iter m g x)). lia.
Qed.

Lemma iter_mono_g : forall f g, (forall x y, x <= y -> g x <= g y) -> (forall x, f x <= g x) ->
  forall n x, iter n f x <= iter n g x.
Proof.
  intros f g Hm Hfg. induction n; intros; simpl; [lia |].
  specialize (IHn x). specialize (Hfg (iter n f x)). specialize (Hm _ _ IHn). lia.
Qed.

Lemma iter_mono_x : forall g, (forall x y, x <= y -> g x <= g y) -> forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

(** monotonicity and growth, base a >= 2 *)
Lemma arrow_props : forall a, 2 <= a -> forall k,
  (forall x y, x <= y -> arrow k a x <= arrow k a y) /\ (forall x, 1 <= x -> x + 1 <= arrow k a x) /\
  (forall x, x <= arrow k a x).
Proof.
  intros a Ha. induction k as [| k [Hm [Hs Hi]]].
  - split; [| split].
    + intros x y Hxy. rewrite (arrow_0 a x), (arrow_0 a y). apply Nat.mul_le_mono_l. exact Hxy.
    + intros x Hx. rewrite (arrow_0 a x). pose proof (Nat.mul_le_mono_r 2 a x Ha). lia.
    + intros x. rewrite (arrow_0 a x). pose proof (Nat.mul_le_mono_r 2 a x Ha). lia.
  - assert (Hm' : forall x y, x <= y -> arrow (S k) a x <= arrow (S k) a y).
    { intros x y Hxy. rewrite !arrow_S_iter. apply iter_mono_n; assumption. }
    assert (Hs' : forall x, 1 <= x -> x + 1 <= arrow (S k) a x).
    { intros x Hx. rewrite arrow_S_iter. destruct x as [| x']; [lia |].
      clear Hx. induction x' as [| x' IH]; simpl iter.
      - pose proof (Hs 1 ltac:(lia)). simpl in *. lia.
      - simpl iter in IH. pose proof (Hs (arrow k a (iter x' (arrow k a) 1))).
        assert (1 <= arrow k a (iter x' (arrow k a) 1)) by lia. lia. }
    split; [exact Hm' | split; [exact Hs' |]].
    intros x. destruct x as [| x']; [lia |]. pose proof (Hs' (S x') ltac:(lia)). lia.
Qed.

Lemma arrow_mono : forall a k x y, 2 <= a -> x <= y -> arrow k a x <= arrow k a y.
Proof. intros. apply (arrow_props a H k). assumption. Qed.
Lemma arrow_gt : forall a k x, 2 <= a -> 1 <= x -> x + 1 <= arrow k a x.
Proof. intros. apply (arrow_props a H k). assumption. Qed.
Lemma arrow_id : forall a k x, 2 <= a -> x <= arrow k a x.
Proof. intros. apply (arrow_props a H k). Qed.

Lemma arrow_one : forall k a, arrow k a 1 = a.
Proof.
  induction k; intros. - rewrite (arrow_0 a 1). lia.
  - change 1 with (S 0) at 1. rewrite arrow_SS, arrow_S0. apply IHk.
Qed.

Lemma arrow_level : forall a k x, 2 <= a -> arrow k a x <= arrow (S k) a x.
Proof.
  intros a k x Ha. destruct x as [| x'].
  - rewrite arrow_S0. destruct k; [rewrite (arrow_0 a 0); lia | rewrite arrow_S0; lia].
  - rewrite arrow_SS. apply arrow_mono; [exact Ha |].
    destruct x' as [| x'']; [rewrite arrow_S0; lia |].
    pose proof (arrow_gt a (S k) (S x'') Ha ltac:(lia)). lia.
Qed.

Lemma arrow_level_mono : forall a d k x, 2 <= a -> arrow k a x <= arrow (d + k) a x.
Proof.
  intros a d k x Ha. induction d; [change (0 + k) with k; lia |].
  pose proof (arrow_level a (d + k) x Ha). change (S d + k) with (S (d + k)). lia.
Qed.

(** base 2 <= base 3 *)
Lemma arrow_base : forall k x, arrow k 2 x <= arrow k 3 x.
Proof.
  induction k; intros x. - rewrite (arrow_0 2 x), (arrow_0 3 x). lia.
  - rewrite !arrow_S_iter. apply iter_mono_g; [| exact IHk].
    intros. apply arrow_mono; [lia | assumption].
Qed.

(** growth facts for base 3 *)
Lemma arrow_3x : forall k z, 3 * z <= arrow k 3 z.
Proof.
  induction k; intros z. - rewrite (arrow_0 3 z). lia.
  - destruct z as [| z']; [rewrite arrow_S0; lia |].
    rewrite arrow_SS. pose proof (IHk (arrow (S k) 3 z')).
    destruct z' as [| z'']; [rewrite arrow_S0 in *; lia |].
    pose proof (arrow_gt 3 (S k) (S z'') ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma arrow_succ3 : forall k z, 1 <= k -> 3 * arrow k 3 z <= arrow k 3 (S z).
Proof.
  intros k z Hk. destruct k as [| k']; [lia |]. rewrite arrow_SS. apply arrow_3x.
Qed.

Lemma arrow_33 : forall k, k + 9 <= arrow k 3 3.
Proof.
  induction k. - rewrite (arrow_0 3 3). lia.
  - change 3 with (S (S (S 0))) at 2. rewrite !arrow_SS, arrow_S0, arrow_one.
    pose proof (arrow_gt 3 k (arrow k 3 3) ltac:(lia) ltac:(lia)).
    pose proof (arrow_mono 3 k 3 (arrow k 3 3) ltac:(lia) ltac:(lia)). lia.
Qed.

(** the key step: arrow i 3 (A + 3) >= arrow i 3 A + i once A >= 3 *)
Lemma arrow_step : forall i A, 3 <= A -> arrow i 3 A + i + 1 <= arrow i 3 (A + 3).
Proof.
  intros i A HA. destruct i as [| i'].
  - rewrite (arrow_0 3 A), (arrow_0 3 (A + 3)). lia.
  - pose proof (arrow_succ3 (S i') A ltac:(lia)).
    pose proof (arrow_mono 3 (S i') (S A) (A + 3) ltac:(lia) ltac:(lia)).
    pose proof (arrow_mono 3 (S i') 3 A ltac:(lia) HA).
    pose proof (arrow_33 (S i')). lia.
Qed.

(** ** U j x >= 3 ^(j arrows) (x + 3 - j) *)
Lemma U_lower : forall i y, arrow i 3 (y + 3 - i) <= U i y.
Proof.
  induction i as [| i IH]; intros y.
  - rewrite U_0, (arrow_0 3 (y + 3 - 0)). lia.
  - assert (Hit : forall t, arrow (S i) 3 (S t) + i <= iter t (U i) (W i 3)).
    { induction t as [| t IHt].
      - simpl iter. rewrite (arrow_one (S i) 3). pose proof (W_ge i 3). lia.
      - simpl iter. rewrite arrow_SS.
        set (A := arrow (S i) 3 (S t)) in *. set (Y := iter t (U i) (W i 3)) in *.
        assert (HA : 3 <= A).
        { subst A. pose proof (arrow_mono 3 (S i) 1 (S t) ltac:(lia) ltac:(lia)).
          rewrite arrow_one in H. lia. }
        pose proof (IH Y).
        pose proof (arrow_mono 3 i (A + 3) (Y + 3 - i) ltac:(lia) ltac:(lia)).
        pose proof (arrow_step i A HA). lia. }
    rewrite U_S. pose proof (Hit (y + 2 - i)) as H1.
    pose proof (arrow_mono 3 (S i) (y + 3 - S i) (S (y + 2 - i)) ltac:(lia) ltac:(lia)). lia.
Qed.

(** ** The nested chain: Lc 20 = 3 ^19 3 ^18 ... 3 ^2 3 ^1 15 (arrows; 3 ^1 15 = 3^15) *)
Fixpoint Lc (j : nat) : nat :=
  match j with
  | O => 5
  | S i => arrow i 3 (Lc i)
  end.

Lemma Lc_S : forall j, Lc (S j) = arrow j 3 (Lc j).
Proof. reflexivity. Qed.

Lemma Lc_ge : forall j, 5 <= Lc j.
Proof.
  induction j; [simpl; lia |]. rewrite Lc_S. pose proof (arrow_id 3 j (Lc j) ltac:(lia)). lia.
Qed.

Opaque Lc.

Lemma W_chain : forall j, Lc j + j <= W j 5.
Proof.
  induction j as [| j IH].
  - rewrite W_0. Transparent Lc. simpl. Opaque Lc. lia.
  - rewrite W_S, Lc_S. pose proof (U_lower j (W j 5)) as H1.
    pose proof (Lc_ge j) as H5.
    pose proof (arrow_mono 3 j (Lc j + 3) (W j 5 + 3 - j) ltac:(lia) ltac:(lia)) as H2.
    pose proof (arrow_step j (Lc j) ltac:(lia)) as H3. lia.
Qed.

(** ** Comparisons, stated on variables (no closed arrow term is ever unfolded) *)
Lemma pow3_lin : forall z, 4 <= z -> 3 * z + 23 <= 3 ^ z.
Proof.
  intros z Hz. induction Hz; [simpl; lia |]. rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma arrow_big : forall k z, 4 <= z -> 3 * z + 23 <= arrow (S k) 3 z.
Proof.
  intros k z Hz. pose proof (arrow_level_mono 3 k 1 z ltac:(lia)) as H.
  replace (k + 1) with (S k) in H by lia. rewrite arrow_1_pow in H.
  pose proof (pow3_lin z Hz). lia.
Qed.

Lemma arrow_S3 : forall k, arrow (S k) 3 3 = arrow k 3 (arrow k 3 3).
Proof.
  intros k. change 3 with (S (S (S 0))) at 2. rewrite !arrow_SS, arrow_S0, arrow_one. reflexivity.
Qed.

Lemma arrow_S2 : forall k, arrow (S k) 3 2 = arrow k 3 3.
Proof. intros k. change 2 with (S (S 0)) at 2. rewrite !arrow_SS, arrow_S0, arrow_one. reflexivity. Qed.

Lemma arrow_level_le : forall a k k' x, 2 <= a -> k <= k' -> arrow k a x <= arrow k' a x.
Proof.
  intros a k k' x Ha Hk. replace k' with ((k' - k) + k) by lia. apply arrow_level_mono. exact Ha.
Qed.

(** Below, closed arrow terms are only combined by [exact] with lemma instances whose types match
    syntactically, and by pure arithmetic lemmas on variables: no rewriting, no unification of two
    different closed arrow terms (which would make Coq evaluate them). *)

Lemma ar_lc20 : forall L20 L19 L18 (X : nat), L20 = arrow 19 3 L19 -> L19 = arrow 18 3 L18 -> 5 <= L18 ->
  arrow 19 3 (arrow 18 3 3) <= L20.
Proof.
  intros L20 L19 L18 X E1 E2 H. subst L20 L19.
  apply arrow_mono; [lia |]. apply arrow_mono; [lia | lia].
Qed.

Lemma Lc20_ge : arrow 19 3 (arrow 18 3 3) <= Lc 20.
Proof. exact (ar_lc20 (Lc 20) (Lc 19) (Lc 18) 0 (Lc_S 19) (Lc_S 18) (Lc_ge 18)). Qed.

Lemma ar_a20 : forall A B C, A = B -> B <= C -> A <= C.
Proof. intros. lia. Qed.

(** 3 ^20 2 = 3 ^19 3 <= 3 ^19 (3 ^18 3) (arrows) *)
Lemma a20_le : arrow 20 3 2 <= arrow 19 3 (arrow 18 3 3).
Proof.
  assert (H3 : 3 <= arrow 18 3 3) by (pose proof (arrow_33 18) as H; lia).
  exact (ar_a20 _ _ _ (arrow_S2 19) (arrow_mono 3 19 3 (arrow 18 3 3) ltac:(lia) H3)).
Qed.

Lemma ar_champ : forall c c' x y, c <= c' -> c' <= x -> 18 + 9 <= x -> 3 * x + 23 <= y -> 3 * c + 22 < y.
Proof. intros. lia. Qed.

(** the BB(7) champion's sigma 3 * (2 ^13 3) + 22 (our analysis; see BB7/README.md) *)
Lemma champ_le : 3 * arrow 13 2 3 + 22 < arrow 19 3 (arrow 18 3 3).
Proof.
  assert (H4 : 4 <= arrow 18 3 3) by (pose proof (arrow_33 18) as H; lia).
  exact (ar_champ _ _ _ _ (arrow_base 13 3) (arrow_level_le 3 13 18 3 ltac:(lia) ltac:(lia))
           (arrow_33 18) (arrow_big 18 (arrow 18 3 3) H4)).
Qed.

Lemma ar_wiki : forall a a1 X b b1 b2 E y, a <= a1 -> a1 <= X -> b <= b1 -> b1 <= b2 -> b2 <= E -> E = y -> y <= X ->
  forall z, y <= z -> b <= z.
Proof. intros. lia. Qed.

(** the wiki's lower bound for the BB(7) champion, 2 ^11 (2 ^11 3) *)
Lemma wiki_le : arrow 11 2 (arrow 11 2 3) <= arrow 19 3 (arrow 18 3 3).
Proof.
  set (X := arrow 18 3 3).
  assert (H3 : 3 <= X) by (subst X; pose proof (arrow_33 18) as H; lia).
  assert (Ha : arrow 11 2 3 <= X).
  { exact (Nat.le_trans _ _ _ (arrow_base 11 3) (arrow_level_le 3 11 18 3 ltac:(lia) ltac:(lia))). }
  assert (Hb : arrow 11 2 (arrow 11 2 3) <= arrow 18 3 X).
  { exact (Nat.le_trans _ _ _ (arrow_mono 2 11 _ _ ltac:(lia) Ha)
           (Nat.le_trans _ _ _ (arrow_base 11 X) (arrow_level_le 3 11 18 X ltac:(lia) ltac:(lia)))). }
  assert (Hc : arrow 18 3 X = arrow 19 3 3) by (subst X; symmetry; exact (arrow_S3 18)).
  assert (Hd : arrow 19 3 3 <= arrow 19 3 X) by exact (arrow_mono 3 19 3 X ltac:(lia) H3).
  exact (Nat.le_trans _ _ _ Hb (Nat.le_trans _ _ _ (Nat.eq_le_incl _ _ Hc) Hd)).
Qed.

Lemma ar_final : forall N w L A B C D, N = 2 * w + 7 -> L + 20 <= w -> A <= L -> B <= A ->
  3 * C + 22 < A -> D <= A ->
  L < N /\ A < N /\ B < N /\ 3 * C + 22 < N /\ D < N.
Proof. intros. lia. Qed.

(** ** The score bound: N = 2 * W 20 5 + 7 *)
Theorem N_lower : forall N, N = 2 * W 20 5 + 7 ->
  Lc 20 < N /\ arrow 19 3 (arrow 18 3 3) < N /\ arrow 20 3 2 < N /\
  3 * arrow 13 2 3 + 22 < N /\ arrow 11 2 (arrow 11 2 3) < N.
Proof.
  intros N HN. exact (ar_final _ _ _ _ _ _ _ HN (W_chain 20) Lc20_ge a20_le champ_le wiki_le).
Qed.
