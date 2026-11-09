(** B21 / W2PR quantitative layer, part 1: level maps over a merge map, the block potential, transitions.
    Pure arithmetic on digit lists; independent of the refill rule. *)
From Coq Require Import Lia PeanoNat List Bool.
From BB8 Require Import BB21_B21_absdef BB_FGH_wa.
Import ListNotations.
Set Default Goal Selector "!".

(** Lev g i: the level-i map over g (FGH successor steps with iteration count = argument) *)
Fixpoint Lev (g : nat -> nat) (i : nat) : nat -> nat :=
  match i with
  | 0 => g
  | S i' => fun x => iter x (Lev g i') x
  end.

Lemma good_Lev : forall g, good g -> forall i, good (Lev g i).
Proof. intros g G. induction i; [exact G | apply good_diag; exact IHi]. Qed.

Lemma Lev_index : forall g, good g -> forall i i' x, i <= i' -> 1 <= x -> Lev g i x <= Lev g i' x.
Proof.
  intros g G i i' x H Hx. induction H; [lia |]. simpl.
  pose proof (iter_diag_ge _ (good_Lev g G m) x Hx). lia.
Qed.

Lemma iter_dom : forall (F H : nat -> nat), (forall x, F x <= H x) -> (forall x y, x <= y -> H x <= H y) ->
  forall n x, iter n F x <= iter n H x.
Proof. intros F H D M. induction n; intros; simpl; [lia |]. specialize (IHn x). specialize (D (iter n F x)). specialize (M _ _ IHn). lia. Qed.

Lemma Lev_fgh : forall a g, good g -> (forall x, f_wa a 0 x <= g x) -> forall b x, f_wa a b x <= Lev g b x.
Proof.
  intros a g G D. induction b; intros x; [exact (D x) |].
  rewrite f_wa_S. simpl. apply iter_dom; [exact IHb | apply (proj2 (good_Lev g G b))].
Qed.

(** depth family: Mq 0 = the merge map at depth 0, Mq (j+1) x = Lev (Mq j) x x (the omega-limit over Mq j) *)
Fixpoint Mq (G : nat -> nat) (j : nat) : nat -> nat :=
  match j with
  | 0 => G
  | S j' => fun x => Lev (Mq G j') x x
  end.

Lemma good_lim : forall g, good g -> good (fun x => Lev g x x).
Proof.
  intros g G. split.
  - intros x. apply (proj1 (good_Lev g G x)).
  - intros x y H. destruct y as [| y]; [assert (x = 0) by lia; subst; lia |].
    transitivity (Lev g x (S y)); [apply (proj2 (good_Lev g G x)); exact H | apply Lev_index; [exact G | lia | lia]].
Qed.

Lemma good_Mq : forall G, good G -> forall j, good (Mq G j).
Proof. intros G HG. induction j; [exact HG | apply good_lim; exact IHj]. Qed.

Lemma Mq_fgh : forall G, good G -> (forall x, S x <= G x) -> forall j x, f_wa j 0 x <= Mq G j x.
Proof.
  intros G HG D. induction j; intros x; [exact (D x) |].
  rewrite f_wa_lim. simpl. apply (Lev_fgh j (Mq G j) (good_Mq G HG j) IHj).
Qed.

(** ** the block potential *)
Fixpoint evalP (g : nat -> nat) (i : nat) (T : list nat) (x : nat) : nat :=
  match T with
  | [] => x
  | d :: t => evalP g (S i) t (iter (d - 1) (Lev g i) x)
  end.

Definition predlead_digit (d : nat) : bool := d =? 1.
Fixpoint predlead (t : list nat) : list nat :=
  match t with
  | [] => []
  | d :: t' => if d =? 1 then 1 :: predlead t' else (d - 1) :: t'
  end.

Definition pre (T : list nat) : list nat :=
  match T with
  | [] => []
  | d :: t => if 2 <=? d then (d - 1) :: t else d :: predlead t
  end.

Lemma evalP_ge : forall g, good g -> forall T i x, x <= evalP g i T x.
Proof.
  intros g G. induction T as [| d T IH]; intros i x; simpl; [lia |].
  pose proof (iter_ge_id _ (proj1 (good_Lev g G i)) (d - 1) x). specialize (IH (S i) (iter (d - 1) (Lev g i) x)). lia.
Qed.

Lemma evalP_mono : forall g, good g -> forall T i x y, x <= y -> evalP g i T x <= evalP g i T y.
Proof.
  intros g G. induction T as [| d T IH]; intros i x y H; simpl; [lia |].
  apply IH. apply iter_mono_arg; [apply (proj2 (good_Lev g G i)) | exact H].
Qed.

Lemma evalP_le : forall g, good g -> forall T T' i x, Forall2 le T T' -> evalP g i T x <= evalP g i T' x.
Proof.
  intros g G T T' i x H. revert i x. induction H as [| d d' T T' Hd HT IH]; intros i x; simpl; [lia |].
  transitivity (evalP g (S i) T' (iter (d - 1) (Lev g i) x)); [apply IH |].
  apply evalP_mono; [exact G |]. apply iter_mono_cnt; [apply (proj1 (good_Lev g G i)) | lia].
Qed.

Lemma evalP_ones : forall g n T i x, evalP g i (repeat 1 n ++ T) x = evalP g (i + n) T x.
Proof. intros g n. induction n; intros; simpl; [rewrite Nat.add_0_r; reflexivity |]. rewrite IHn. f_equal. lia. Qed.

Lemma Forall2_refl : forall l, Forall2 le l l.
Proof. induction l; constructor; [lia | exact IHl]. Qed.

Lemma predlead_ones : forall n d t, 2 <= d -> predlead (repeat 1 n ++ d :: t) = repeat 1 n ++ (d - 1) :: t.
Proof.
  induction n; intros d t Hd; simpl.
  - destruct (d =? 1) eqn:E; [apply Nat.eqb_eq in E; lia | reflexivity].
  - rewrite IHn by exact Hd. reflexivity.
Qed.

Lemma pre_shape : forall p y t, 2 <= y -> pre (repeat 1 p ++ y :: t) = repeat 1 p ++ (y - 1) :: t.
Proof.
  intros [| p] y t Hy; simpl.
  - destruct y as [| [| y]]; [lia | lia | reflexivity].
  - rewrite predlead_ones by exact Hy. reflexivity.
Qed.

(** deep in-block step (b0 pending, J-acc X >= x - 1): the potential does not decrease *)
Lemma T_deep : forall g, good g -> forall p e r X x, x <= X + 1 ->
  evalP g 0 (1 :: repeat 1 p ++ S (S e) :: r) x <= evalP g 0 (pre (repeat 1 p ++ (X + 3) :: S e :: r)) x.
Proof.
  intros g G p e r X x Hx. rewrite pre_shape by lia. replace (X + 3 - 1) with (X + 2) by lia.
  change (1 :: repeat 1 p ++ S (S e) :: r) with (repeat 1 (S p) ++ S (S e) :: r).
  rewrite !evalP_ones. cbn [evalP]. replace (0 + S p) with (S p) by lia. replace (0 + p) with p by lia.
  replace (S (S e) - 1) with (S e) by lia. replace (S e - 1) with e by lia. replace (X + 2 - 1) with (X + 1) by lia.
  apply evalP_mono; [exact G |]. rewrite iter_S'. apply iter_mono_arg; [apply (proj2 (good_Lev g G (S p))) |].
  change (Lev g (S p) x) with (iter x (Lev g p) x).
  apply iter_mono_cnt; [apply (proj1 (good_Lev g G p)) | exact Hx].
Qed.

(** small in-block step (b0 pure): the precharged potential does not decrease *)
Lemma T_small : forall g, good g -> forall p e r y x,
  evalP g 0 (pre (1 :: repeat 1 p ++ S (S e) :: r)) x <= evalP g 0 (pre (repeat 1 p ++ (y + 3) :: S e :: r)) x.
Proof.
  intros g G p e r y x. rewrite (pre_shape p) by lia.
  change (1 :: repeat 1 p ++ S (S e) :: r) with (repeat 1 (S p) ++ S (S e) :: r). rewrite pre_shape by lia.
  apply evalP_le; [exact G |]. replace (S (S e) - 1) with (S e) by lia.
  replace (repeat 1 (S p) ++ S e :: r) with (repeat 1 p ++ 1 :: S e :: r) by (clear; induction p; simpl; [reflexivity | rewrite IHp; reflexivity]).
  replace (y + 3 - 1) with (y + 2) by lia.
  apply Forall2_app; [apply Forall2_refl |]. constructor; [lia | apply Forall2_refl].
Qed.

(** decrement of the first digit *)
Lemma T_dec : forall g, good g -> forall d rest x y, g x <= y ->
  evalP g 0 (S (S d) :: rest) x <= evalP g 0 (S d :: rest) y.
Proof.
  intros g G d rest x y H. cbn [evalP]. apply evalP_mono; [exact G |]. replace (S (S d) - 1) with (S d) by lia.
  replace (S d - 1) with d by lia. rewrite iter_S'. apply iter_mono_arg; [apply (proj2 (good_Lev g G 0)) | exact H].
Qed.

Lemma T_dec_small : forall g, good g -> forall d rest x y, x <= y ->
  evalP g 0 (pre (S (S d) :: rest)) x <= evalP g 0 (S d :: rest) y.
Proof.
  intros g G d rest x y H. change (pre (S (S d) :: rest)) with (S (S d) - 1 :: rest). replace (S (S d) - 1) with (S d) by lia.
  apply evalP_mono; [exact G | exact H].
Qed.

Lemma evalP_allones : forall g T i x, all1 T = true -> evalP g i T x = x.
Proof.
  intros g T. induction T as [| d T IH]; intros i x H; simpl; [reflexivity |].
  simpl in H. apply andb_true_iff in H as [H1 H2]. apply Nat.eqb_eq in H1. subst. simpl. apply IH. exact H2.
Qed.

(** lower bounds for the blocks created by big merges *)
Lemma B_merged : forall g, good g -> forall a k x, 1 <= x ->
  Lev g (S k) x <= evalP g 0 (pre (repeat 1 (S a) ++ Xl (S k))) x.
Proof.
  intros g G a k x Hx. change (repeat 1 (S a) ++ Xl (S k)) with (repeat 1 (S a) ++ 4 :: repeat 1 k ++ [2]).
  rewrite pre_shape by lia.
  rewrite evalP_ones. cbn [evalP]. replace (4 - 1 - 1) with 2 by lia.
  rewrite evalP_ones. cbn [evalP]. replace (2 - 1) with 1 by lia.
  set (z := iter 2 (Lev g (0 + S a)) x).
  assert (x <= z) by (apply iter_ge_id; apply (proj1 (good_Lev g G _))).
  cbn [iter]. transitivity (Lev g (S k) z); [apply (proj2 (good_Lev g G (S k))); exact H |].
  apply Lev_index; [exact G | lia | lia].
Qed.

Lemma B_fresh : forall g, good g -> forall k x, 1 <= x -> Lev g (S k) x <= evalP g 0 (pre (Xl (S k))) x.
Proof.
  intros g G k x Hx. unfold Xl. change ([4] ++ repeat 1 k ++ [2]) with (repeat 1 0 ++ 4 :: repeat 1 k ++ [2]).
  rewrite pre_shape by lia. simpl app. cbn [evalP]. replace (4 - 1 - 1) with 2 by lia. replace (3 - 1) with 2 by lia.
  rewrite evalP_ones. cbn [evalP]. replace (2 - 1) with 1 by lia.
  set (z := iter 2 (Lev g 0) x).
  assert (x <= z) by (apply iter_ge_id; apply (proj1 (good_Lev g G _))).
  cbn [iter]. transitivity (Lev g (S k) z); [apply (proj2 (good_Lev g G (S k))); exact H |].
  apply Lev_index; [exact G | lia | lia].
Qed.
