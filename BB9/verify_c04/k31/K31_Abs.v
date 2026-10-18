(** * K31_Abs.v : free-far-side champion rules on Kx, the clearing CDPf, the counter COUNT, and the ones count.

    Kx / Kgx / lftx are Step.v's (far end e arbitrary).  R2f / R3f (K_rf.v) are the machine rules R2 / R3 with a FREE
    far side: the cell beyond the borrowed token may be anything (the machine never reads it), and R3f holds for x = 0
    too (the counter's last step 3 -> 0, also when a z2 gap lies beyond).  So no [good e] side condition is needed. *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From Dev Require Import Base G_rules Abs Lift Step.
From K31 Require Import K_rf.
Opaque U arrow.

(** ** Free-far-side token rules *)
Lemma Kx_R2f : forall x ds r t e, 0 < r -> Kx ((3 + x) :: ds) 1 r t e -->+ Kx (x :: ds) (2 * r + 3) 2 t e.
Proof. intros x ds r t e Hr. unfold Kx. cbn [lftx]. rewrite acc3. exact (R2f r t x (lftx ds e) Hr). Qed.

Lemma Kx_R3f : forall k x ds r t e, 0 < r ->
  Kx (repeat 1%nat (S k) ++ (3 + x) :: ds) 1 r t e -->+ Kx (repeat 1%nat k ++ (2 * r + 3) :: x :: ds) 1 2 t e.
Proof.
  intros k x ds r t e Hr. unfold Kx. rewrite !lftx_app, !lftx_rep. cbn [lftx]. rewrite acc3.
  exact (R3f k r t x (lftx ds e) Hr).
Qed.

Lemma Kx_app : forall xs ys m r t e, Kx (xs ++ ys) m r t e = Kx xs m r t (lftx ys e).
Proof. intros. unfold Kx. rewrite lftx_app. reflexivity. Qed.

(** ** Digit form, free far side *)
Lemma KR2f : forall y ds suf b t e, Kgx (S y :: ds) suf O b t e -->+ Kgx (y :: ds) suf (2 * b + 2) O t e.
Proof.
  intros y ds suf b t e. unfold Kgx.
  change (map tokd (S y :: ds) ++ suf) with (tokd (S y) :: (map tokd ds ++ suf)).
  change (map tokd (y :: ds) ++ suf) with (tokd y :: (map tokd ds ++ suf)).
  replace (tokd (S y)) with (3 + tokd y) by (unfold tokd; lia).
  replace (3 * (2 * b + 2) + 1) with (2 * (3 * b + 2) + 3) by lia.
  change (3 * O + 1) with 1%nat. change (3 * O + 2) with 2%nat.
  apply Kx_R2f. lia.
Qed.

Lemma KR3f : forall M y ds suf b t e,
  Kgx (repeat O (S M) ++ S y :: ds) suf O b t e -->+ Kgx (repeat O M ++ (2 * b + 2) :: y :: ds) suf O O t e.
Proof.
  intros M y ds suf b t e. unfold Kgx. rewrite !map_rep, <- !app_assoc.
  change (map tokd (S y :: ds) ++ suf) with (tokd (S y) :: (map tokd ds ++ suf)).
  change (map tokd ((2 * b + 2) :: y :: ds) ++ suf) with (tokd (2 * b + 2) :: tokd y :: (map tokd ds ++ suf)).
  replace (tokd (S y)) with (3 + tokd y) by (unfold tokd; lia).
  replace (tokd (2 * b + 2)) with (2 * (3 * b + 2) + 3) by (unfold tokd; lia).
  change (3 * O + 1) with 1%nat. change (3 * O + 2) with 2%nat.
  apply Kx_R3f. lia.
Qed.

Lemma CHf : forall v Us suf B t e, Kgx (v :: Us) suf O B t e -->* Kgx (O :: Us) suf O (iter v (U 0) B) t e.
Proof.
  induction v; intros Us suf B t e.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, KR2f |].
    eapply evstep_trans; [apply R1ITERx, lftx_map_cons |].
    rewrite iter_S', U_0.
    apply IHv.
Qed.

(** The champion clearing with a free far side. *)
Lemma CDPf : forall j v Us suf B t e,
  Kgx (repeat O j ++ v :: Us) suf O B t e -->* Kgx (repeat O (S j) ++ Us) suf O (iter v (U j) B) t e.
Proof.
  induction j as [| n IHn].
  - intros. simpl. apply CHf.
  - intro v. induction v as [| w IHw]; intros Us suf B t e.
    + rewrite repeat_snoc. apply evstep_refl.
    + eapply evstep_trans; [apply progress_evstep, KR3f |].
      eapply evstep_trans; [apply (IHn (2 * B + 2) (w :: Us) suf O t e) |].
      rewrite <- U_S.
      eapply evstep_trans; [apply (IHw Us suf (U (S n) B) t e) |].
      rewrite iter_S'. apply evstep_refl.
Qed.

Lemma Kgx_Kx : forall ds suf b t e, Kgx ds suf O b t e = Kx (map tokd ds ++ suf) 1 (3 * b + 2) t e.
Proof. reflexivity. Qed.

(** CDPf on Kx: clear the digit token tokd v at depth j (all nearer digits zero, accumulator 2). *)
Lemma CLR : forall j v suf t e,
  Kx (repeat 1%nat j ++ tokd v :: suf) 1 2 t e -->* Kx (repeat 1%nat (S j) ++ suf) 1 (3 * iter v (U j) O + 2) t e.
Proof.
  intros j v suf t e.
  pose proof (CDPf j v [] suf O t e) as H. rewrite !Kgx_Kx in H.
  replace (map tokd (repeat O j ++ [v]) ++ suf) with (repeat 1%nat j ++ tokd v :: suf) in H
    by (rewrite map_rep, <- app_assoc; reflexivity).
  replace (map tokd (repeat O (S j) ++ []) ++ suf) with (repeat 1%nat (S j) ++ suf) in H
    by (rewrite app_nil_r, map_rep0; reflexivity).
  exact H.
Qed.

(** Two-digit clear: tokd v1 at depth j, tokd v2 right behind it. *)
Lemma CLR2d : forall j v1 v2 suf t e,
  Kx (repeat 1%nat j ++ tokd v1 :: tokd v2 :: suf) 1 2 t e -->*
  Kx (repeat 1%nat (S (S j)) ++ suf) 1 (3 * iter v2 (U (S j)) (iter v1 (U j) O) + 2) t e.
Proof.
  intros j v1 v2 suf t e.
  pose proof (CDPf j v1 [v2] suf O t e) as H1. rewrite !Kgx_Kx in H1.
  replace (map tokd (repeat O j ++ [v1; v2]) ++ suf) with (repeat 1%nat j ++ tokd v1 :: tokd v2 :: suf) in H1
    by (rewrite map_rep, <- app_assoc; reflexivity).
  replace (map tokd (repeat O (S j) ++ [v2]) ++ suf) with (repeat 1%nat (S j) ++ tokd v2 :: suf) in H1
    by (rewrite map_rep, <- app_assoc; reflexivity).
  eapply evstep_trans; [exact H1 |].
  pose proof (CDPf (S j) v2 [] suf (iter v1 (U j) O) t e) as H3. rewrite !Kgx_Kx in H3.
  replace (map tokd (repeat O (S j) ++ [v2]) ++ suf) with (repeat 1%nat (S j) ++ tokd v2 :: suf) in H3
    by (rewrite map_rep, <- app_assoc; reflexivity).
  replace (map tokd (repeat O (S (S j)) ++ []) ++ suf) with (repeat 1%nat (S (S j)) ++ suf) in H3
    by (rewrite app_nil_r, map_rep0; reflexivity).
  exact H3.
Qed.
(** ** The counter: a token 3c behind S n zeros counts down; each unit clears one deposited digit at depth n. *)
Lemma CTR : forall c n Q suf t e,
  Kx (repeat 1%nat (S n) ++ (3 * S c) :: suf) 1 (3 * Q + 2) t e -->*
  Kx (repeat 1%nat (S n) ++ (3 * c) :: suf) 1 (3 * U (S n) Q + 2) t e.
Proof.
  intros c n Q suf t e.
  replace (3 * S c) with (3 + 3 * c) by lia.
  eapply evstep_trans; [apply progress_evstep, (Kx_R3f n (3 * c) suf (3 * Q + 2) t e ltac:(lia)) |].
  replace (2 * (3 * Q + 2) + 3) with (tokd (2 * Q + 2)) by (unfold tokd; lia).
  eapply evstep_trans; [apply (CLR n (2 * Q + 2) ((3 * c)%nat :: suf) t e) |].
  rewrite <- U_S. apply evstep_refl.
Qed.

Lemma COUNT : forall c n Q suf t e,
  Kx (repeat 1%nat (S n) ++ (3 * c) :: suf) 1 (3 * Q + 2) t e -->*
  Kx (repeat 1%nat (S n) ++ 0%nat :: suf) 1 (3 * iter c (U (S n)) Q + 2) t e.
Proof.
  induction c as [| c IH]; intros n Q suf t e.
  - apply evstep_refl.
  - eapply evstep_trans; [apply CTR |].
    eapply evstep_trans; [apply IH |].
    rewrite iter_S'. apply evstep_refl.
Qed.

(** ** Growth facts *)
Lemma iter_ge_count : forall c j x, x + c <= iter c (U j) x.
Proof.
  induction c as [| c IH]; intros j x; [simpl; lia |].
  rewrite iter_S'. pose proof (U_lin j x). specialize (IH j (U j x)). lia.
Qed.

Lemma iter_ge_start : forall c j x, x <= iter c (U j) x.
Proof. intros. pose proof (iter_ge_count c j x). lia. Qed.

(** ** Counting ones (verbatim copy of BB9_fw2_bound.ones / count1) *)
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
Proof. induction xs; intros; simpl; [reflexivity | rewrite IHxs; lia]. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl; [reflexivity | rewrite count1_app, IHn; lia]. Qed.

(** lftx as a list in front of the far end *)
Fixpoint encl (ds : list nat) : list Sym :=
  match ds with
  | [] => []
  | d :: t => 1 :: [0;1]^^d ++ encl t
  end.

Lemma lftx_encl : forall ds e, lftx ds e = encl ds *> e.
Proof.
  induction ds as [| d t IH]; intros e; [reflexivity |].
  cbn [lftx encl]. rewrite IH. cbn [Str_app]. rewrite Str_app_assoc. reflexivity.
Qed.
