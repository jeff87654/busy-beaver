(** * KStep.v : the token family with an arbitrary far end (Kx, Kgx) and the champion clearing CDPx on it, for X'.
    Extracted unchanged from ../verify_f3/dev/Step.v (its generic part; C04's cascade lemmas are not used for C7). *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs.
Opaque U arrow.

Lemma prog_eq : forall c1 c1' c2 c2' : Q * tape, c1 = c1' -> c2 = c2' -> c1' -->+ c2' -> c1 -->+ c2.
Proof. intros; subst; assumption. Qed.

(** ** Token family with an arbitrary far end *)
Fixpoint lftx (ds : list nat) (e : side) : side :=
  match ds with
  | [] => e
  | d :: t => 1 >> [0;1]^^d *> lftx t e
  end.

Definition Kx (ds : list nat) (m r t : nat) (e : side) : Q * tape :=
  (1 >> 0 >> 0 >> 1 >> [0;0;1;1;1;1;1;1]^^t *> 1 >> 1 >> [0;1]^^r *> 1 >> [0;1]^^m *> lftx ds e) {{B}}> const 0.

Lemma lftx_app : forall xs ys e, lftx (xs ++ ys) e = lftx xs (lftx ys e).
Proof. induction xs; intros; simpl; [reflexivity | rewrite IHxs; reflexivity]. Qed.

Lemma lftx_rep : forall n e, lftx (repeat 1%nat n) e = [1;0;1]^^n *> e.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma lft_lftx : forall ds, lft ds = lftx ds (1 >> 1 >> const 0).
Proof. induction ds; simpl; [reflexivity | rewrite IHds; reflexivity]. Qed.

Lemma Kt_Kx : forall ds m r t, Kt ds m r t = Kx ds m r t (1 >> 1 >> const 0).
Proof. intros. unfold Kt, Kx. rewrite lft_lftx. reflexivity. Qed.

(** far ends the champion rules accept: a token (1..) or the gap 00 *)
Definition good (e : side) : Prop := (exists l, e = 1 >> l) \/ (exists l, e = 0 >> 0 >> l).

Lemma lftx_good : forall ds e, good e -> good (lftx ds e).
Proof. intros [| d ds] e He; [exact He | left; eexists; reflexivity]. Qed.

Lemma Kx_R1 : forall ds m r t e, 0 < r -> (exists l, lftx ds e = 1 >> l) ->
  Kx ds (3 + m) r t e -->+ Kx ds m (2 * r + 4) t e.
Proof. intros ds m r t e Hr [l Hl]. unfold Kx. rewrite Hl, acc4. exact (R1 m r t l Hr). Qed.

Lemma Kx_R2 : forall x ds r t e, 0 < r -> good (lftx ds e) ->
  Kx ((3 + x) :: ds) 1 r t e -->+ Kx (x :: ds) (2 * r + 3) 2 t e.
Proof.
  intros x ds r t e Hr [[l Hl] | [l Hl]]; unfold Kx; cbn [lftx]; rewrite Hl, acc3.
  - exact (G_rules.R2 r t x l Hr).
  - exact (R2z r t x l Hr).
Qed.

Lemma Kx_R3 : forall k x ds r t e, 0 < r -> 0 < x -> good (lftx ds e) ->
  Kx (repeat 1%nat (S k) ++ (3 + x) :: ds) 1 r t e -->+ Kx (repeat 1%nat k ++ (2 * r + 3) :: x :: ds) 1 2 t e.
Proof.
  intros k x ds r t e Hr Hx [[l Hl] | [l Hl]]; unfold Kx; rewrite !lftx_app, !lftx_rep; cbn [lftx]; rewrite Hl, acc3.
  - exact (R3 k r t x l Hr Hx).
  - exact (R3z k r t x l Hr).
Qed.

(** digit form *)
Definition Kgx (ds suf : list nat) (a b t : nat) (e : side) : Q * tape :=
  Kx (map tokd ds ++ suf) (3 * a + 1) (3 * b + 2) t e.

Lemma lftx_map_cons : forall d ds suf e, exists l, lftx (map tokd (d :: ds) ++ suf) e = 1 >> l.
Proof. intros. eexists. reflexivity. Qed.

Lemma KR1x : forall ds suf a b t e, (exists l, lftx (map tokd ds ++ suf) e = 1 >> l) ->
  Kgx ds suf (S a) b t e -->+ Kgx ds suf a (2 * b + 2) t e.
Proof.
  intros ds suf a b t e H. unfold Kgx.
  replace (3 * S a + 1) with (3 + (3 * a + 1)) by lia.
  replace (3 * (2 * b + 2) + 2) with (2 * (3 * b + 2) + 4) by lia.
  apply Kx_R1; [lia | exact H].
Qed.

Lemma KR2x : forall y ds suf b t e, good e -> Kgx (S y :: ds) suf O b t e -->+ Kgx (y :: ds) suf (2 * b + 2) O t e.
Proof.
  intros y ds suf b t e He. unfold Kgx.
  change (map tokd (S y :: ds) ++ suf) with (tokd (S y) :: (map tokd ds ++ suf)).
  change (map tokd (y :: ds) ++ suf) with (tokd y :: (map tokd ds ++ suf)).
  replace (tokd (S y)) with (3 + tokd y) by (unfold tokd; lia).
  replace (3 * (2 * b + 2) + 1) with (2 * (3 * b + 2) + 3) by lia.
  change (3 * O + 1) with 1%nat. change (3 * O + 2) with 2%nat.
  apply Kx_R2; [lia | apply lftx_good, He].
Qed.

Lemma KR3x : forall M y ds suf b t e, good e ->
  Kgx (repeat O (S M) ++ S y :: ds) suf O b t e -->+ Kgx (repeat O M ++ (2 * b + 2) :: y :: ds) suf O O t e.
Proof.
  intros M y ds suf b t e He. unfold Kgx. rewrite !map_rep, <- !app_assoc.
  change (map tokd (S y :: ds) ++ suf) with (tokd (S y) :: (map tokd ds ++ suf)).
  change (map tokd ((2 * b + 2) :: y :: ds) ++ suf) with (tokd (2 * b + 2) :: tokd y :: (map tokd ds ++ suf)).
  replace (tokd (S y)) with (3 + tokd y) by (unfold tokd; lia).
  replace (tokd (2 * b + 2)) with (2 * (3 * b + 2) + 3) by (unfold tokd; lia).
  change (3 * O + 1) with 1%nat. change (3 * O + 2) with 2%nat.
  apply Kx_R3; [lia | unfold tokd; lia | apply lftx_good, He].
Qed.

Lemma R1ITERx : forall a ds suf b t e, (exists l, lftx (map tokd ds ++ suf) e = 1 >> l) ->
  Kgx ds suf a b t e -->* Kgx ds suf O (dbl a b) t e.
Proof.
  induction a; intros ds suf b t e H.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, KR1x, H |]. apply IHa, H.
Qed.

Lemma CHx : forall v Us suf B t e, good e -> Kgx (v :: Us) suf O B t e -->* Kgx (O :: Us) suf O (iter v (U 0) B) t e.
Proof.
  induction v; intros Us suf B t e He.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, KR2x, He |].
    eapply evstep_trans; [apply R1ITERx, lftx_map_cons |].
    rewrite iter_S', U_0.
    apply IHv, He.
Qed.

Lemma CDPx : forall j v Us suf B t e, good e ->
  Kgx (repeat O j ++ v :: Us) suf O B t e -->* Kgx (repeat O (S j) ++ Us) suf O (iter v (U j) B) t e.
Proof.
  induction j as [| n IHn].
  - intros. simpl. apply CHx. assumption.
  - intro v. induction v as [| w IHw]; intros Us suf B t e He.
    + rewrite repeat_snoc. apply evstep_refl.
    + eapply evstep_trans; [apply progress_evstep, KR3x, He |].
      eapply evstep_trans; [apply (IHn (2 * B + 2) (w :: Us) suf O t e He) |].
      rewrite <- U_S.
      eapply evstep_trans; [apply (IHw Us suf (U (S n) B) t e He) |].
      rewrite iter_S'. apply evstep_refl.
Qed.

(** ** Machine lemmas restated on D0f / Kx *)

Lemma split_mod : forall n k, 0 < k -> exists q r, r < k /\ n = k * q + r.
Proof.
  intros n k Hk. exists (n / k), (n mod k). split; [apply Nat.mod_upper_bound; lia |].
  apply Nat.div_mod; lia.
Qed.
Lemma mod_of : forall n k q r, r < k -> n = k * q + r -> n mod k = r.
Proof.
  intros n k q r Hr ->. rewrite (Nat.add_comm (k * q) r), (Nat.mul_comm k q), Nat.Div0.mod_add.
  apply Nat.mod_small, Hr.
Qed.
Lemma U_lin : forall j x, 2 * x + 2 <= U j x.
Proof.
  assert (Hdbl : forall a b, a + b <= dbl a b).
  { induction a; intros b.
    - change (dbl O b) with b. lia.
    - change (dbl (S a) b) with (dbl a (2 * b + 2)). specialize (IHa (2 * b + 2)). lia. }
  assert (Hit : forall i n, (forall z, z + 1 <= U i z) -> n <= iter n (U i) O).
  { intros i n Hi. induction n.
    - lia.
    - change (iter (S n) (U i) O) with (U i (iter n (U i) O)). specialize (Hi (iter n (U i) O)). lia. }
  intros [| i] x.
  - rewrite U_0. specialize (Hdbl (2 * x + 2) O). lia.
  - rewrite U_S. apply Hit. intro z.
    pose proof (U_closed i z) as E. pose proof (arrow_gt_arg (S i) (2 * z + 4) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma U0_ge : forall j, j + 2 <= U j O.
Proof.
  induction j.
  - pose proof (U_lin 0 O). lia.
  - rewrite U_S. change (2 * O + 2) with 2%nat. cbn [iter].
    pose proof (U_lin j (U j O)). lia.
Qed.
