(** C04 R0 abstract layer: token family Kt/Kg, champion rules on tokens, clearing (CDP, CLR2), U, arrows, Bx,
    level 0 (init_reach: 2369 literal steps), run_to_exhaustion.  Reused from the BB(9) record development. *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From Dev Require Import Base G_rules.

(** ** R0 abstract layer (reused from the BB9 record; C04 R1/R2/R3 above are identical) *)

(** ** The token family *)

(** Tokens nearest-first: [lft (d :: ds)] is the token D(d) = (10)^d 1 read from the head side, i.e. 1 (01)^d. *)
Fixpoint lft (ds : list nat) : side :=
  match ds with
  | [] => 1 >> 1 >> const 0
  | d :: t => 1 >> [0;1]^^d *> lft t
  end.

(** Kt ds m r t = 0^inf 11 D(d_n) .. D(d_1) D(m) (10)^r 11 (11111100)^t 1001 B> 0^inf
    (ds = [d_1; ..; d_n] nearest-first; m is the a-token, r the accumulator run, t the number of tail blocks). *)
Definition Kt (ds : list nat) (m r t : nat) : Q * tape :=
  (1 >> 0 >> 0 >> 1 >> [0;0;1;1;1;1;1;1]^^t *> 1 >> 1 >> [0;1]^^r *> 1 >> [0;1]^^m *> lft ds) {{B}}> const 0.

Lemma lft_cons : forall d t, lft (d :: t) = 1 >> [0;1]^^d *> lft t.
Proof. reflexivity. Qed.

Lemma lft_1 : forall ds, exists l, lft ds = 1 >> l.
Proof. destruct ds; simpl; eexists; reflexivity. Qed.

Lemma lft_ones : forall n P, lft (repeat 1%nat n ++ P) = [1;0;1]^^n *> lft P.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma pow_add : forall (xs : list Sym) n m Y, xs^^(n + m) *> Y = xs^^n *> xs^^m *> Y.
Proof. intros. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma pow_S : forall (xs : list Sym) n Y, xs^^(S n) *> Y = xs *> xs^^n *> Y.
Proof. intros. simpl. apply Str_app_assoc. Qed.

Lemma pow_mul : forall (xs : list Sym) k n Y, xs^^(k * n) *> Y = (xs^^k)^^n *> Y.
Proof.
  induction n; intros.
  - rewrite Nat.mul_0_r. reflexivity.
  - rewrite Nat.mul_succ_r, Nat.add_comm, pow_add, IHn.
    change ((xs^^k)^^(S n)) with (xs^^k ++ (xs^^k)^^n). rewrite Str_app_assoc. reflexivity.
Qed.

Lemma pow0101 : forall n Y, [0;1;0;1]^^n *> Y = [0;1]^^(2 * n) *> Y.
Proof.
  induction n; intros.
  - reflexivity.
  - replace (2 * S n) with (S (S (2 * n))) by lia.
    change ([0;1;0;1]^^(S n) *> Y) with (0 >> 1 >> 0 >> 1 >> [0;1;0;1]^^n *> Y).
    change ([0;1]^^(S (S (2 * n))) *> Y) with (0 >> 1 >> 0 >> 1 >> [0;1]^^(2 * n) *> Y).
    rewrite IHn. reflexivity.
Qed.

Lemma acc4 : forall n Y, [0;1]^^(2 * n + 4) *> Y = 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1;0;1]^^n *> Y.
Proof. intros. rewrite pow0101. replace (2 * n + 4) with (4 + 2 * n) by lia. reflexivity. Qed.

Lemma acc3 : forall n Y, [0;1]^^(2 * n + 3) *> Y = 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> [0;1;0;1]^^n *> Y.
Proof. intros. rewrite pow0101. replace (2 * n + 3) with (3 + 2 * n) by lia. reflexivity. Qed.

(** ** Token-level champion rules *)

Lemma Kt_R1 : forall ds m r t, 0 < r -> Kt ds (3 + m) r t -->+ Kt ds m (2 * r + 4) t.
Proof.
  intros ds m r t Hr. destruct (lft_1 ds) as [l Hl]. unfold Kt. rewrite Hl, acc4.
  exact (R1 m r t l Hr).
Qed.

Lemma Kt_R2 : forall x ds r t, 0 < r -> Kt ((3 + x) :: ds) 1 r t -->+ Kt (x :: ds) (2 * r + 3) 2 t.
Proof.
  intros x ds r t Hr. destruct (lft_1 ds) as [l Hl]. unfold Kt. rewrite !lft_cons, Hl, acc3.
  exact (R2 r t x l Hr).
Qed.

Lemma Kt_R3 : forall k x ds r t, 0 < r -> 0 < x ->
  Kt (repeat 1%nat (S k) ++ (3 + x) :: ds) 1 r t -->+ Kt (repeat 1%nat k ++ (2 * r + 3) :: x :: ds) 1 2 t.
Proof.
  intros k x ds r t Hr Hx. destruct (lft_1 ds) as [l Hl]. unfold Kt. rewrite !lft_ones, !lft_cons, Hl, acc3.
  exact (R3 k r t x l Hr Hx).
Qed.

(** ** Digit form: residue-1 digits ds (token 3d+1) followed by fixed tokens suf *)

Definition tokd (d : nat) : nat := 3 * d + 1.

Definition Kg (ds suf : list nat) (a b t : nat) : Q * tape :=
  Kt (map tokd ds ++ suf) (3 * a + 1) (3 * b + 2) t.

Lemma map_rep : forall n L, map tokd (repeat O n ++ L) = repeat 1%nat n ++ map tokd L.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma map_single : forall x, map tokd [x] = [tokd x].
Proof. reflexivity. Qed.

Lemma single_app : forall (x : nat) L, [x] ++ L = x :: L.
Proof. reflexivity. Qed.

Lemma map_rep0 : forall n, map tokd (repeat O n) = repeat 1%nat n.
Proof. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma KR1 : forall ds suf a b t, Kg ds suf (S a) b t -->+ Kg ds suf a (2 * b + 2) t.
Proof.
  intros. unfold Kg.
  replace (3 * S a + 1) with (3 + (3 * a + 1)) by lia.
  replace (3 * (2 * b + 2) + 2) with (2 * (3 * b + 2) + 4) by lia.
  apply Kt_R1. lia.
Qed.

Lemma KR2 : forall y ds suf b t, Kg (S y :: ds) suf O b t -->+ Kg (y :: ds) suf (2 * b + 2) O t.
Proof.
  intros. unfold Kg.
  change (map tokd (S y :: ds) ++ suf) with (tokd (S y) :: (map tokd ds ++ suf)).
  change (map tokd (y :: ds) ++ suf) with (tokd y :: (map tokd ds ++ suf)).
  replace (tokd (S y)) with (3 + tokd y) by (unfold tokd; lia).
  replace (3 * (2 * b + 2) + 1) with (2 * (3 * b + 2) + 3) by lia.
  change (3 * O + 1) with 1%nat. change (3 * O + 2) with 2%nat.
  apply Kt_R2. lia.
Qed.

Lemma KR3 : forall M y ds suf b t,
  Kg (repeat O (S M) ++ S y :: ds) suf O b t -->+ Kg (repeat O M ++ (2 * b + 2) :: y :: ds) suf O O t.
Proof.
  intros. unfold Kg. rewrite !map_rep, <- !app_assoc.
  change (map tokd (S y :: ds) ++ suf) with (tokd (S y) :: (map tokd ds ++ suf)).
  change (map tokd ((2 * b + 2) :: y :: ds) ++ suf) with (tokd (2 * b + 2) :: tokd y :: (map tokd ds ++ suf)).
  replace (tokd (S y)) with (3 + tokd y) by (unfold tokd; lia).
  replace (tokd (2 * b + 2)) with (2 * (3 * b + 2) + 3) by (unfold tokd; lia).
  change (3 * O + 1) with 1%nat. change (3 * O + 2) with 2%nat.
  apply Kt_R3; unfold tokd; lia.
Qed.

(** The borrow from a residue-2 token 3v+2 (v >= 1) when every digit is zero. *)
Lemma KR3s : forall M v P b t,
  Kg (repeat O (S M)) (3 * S v + 2 :: P) O b t -->+ Kg (repeat O M ++ [2 * b + 2]) (3 * v + 2 :: P) O O t.
Proof.
  intros. unfold Kg. rewrite map_rep0, (map_rep M [2 * b + 2]), map_single, <- !app_assoc, single_app.
  replace (3 * S v + 2) with (3 + (3 * v + 2)) by lia.
  replace (tokd (2 * b + 2)) with (2 * (3 * b + 2) + 3) by (unfold tokd; lia).
  change (3 * O + 1) with 1%nat. change (3 * O + 2) with 2%nat.
  apply Kt_R3; lia.
Qed.

(** ** Clearing (as in BB8_champ35_bound.v) *)

Fixpoint dbl (a b : nat) : nat :=
  match a with
  | O => b
  | S a' => dbl a' (2 * b + 2)
  end.

Lemma R1ITER : forall a ds suf b t, Kg ds suf a b t -->* Kg ds suf O (dbl a b) t.
Proof.
  induction a; intros.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, KR1 |]. apply IHa.
Qed.

Fixpoint iter (n : nat) (g : nat -> nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n' => g (iter n' g x)
  end.

Lemma iter_S' : forall n g x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

(** U j x: the counter after clearing one unit of a digit at depth j from b = x (zeros restored). *)
Fixpoint U (j : nat) : nat -> nat :=
  match j with
  | O => fun x => dbl (2 * x + 2) 0
  | S i => fun x => iter (2 * x + 2) (U i) 0
  end.

Lemma U_0 : forall x, U 0 x = dbl (2 * x + 2) 0.
Proof. reflexivity. Qed.

Lemma U_S : forall j x, U (S j) x = iter (2 * x + 2) (U j) 0.
Proof. reflexivity. Qed.

Opaque U.

Lemma repeat_snoc : forall (x : nat) n Us, repeat x n ++ x :: Us = repeat x (S n) ++ Us.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Lemma CH : forall v Us suf B t, Kg (v :: Us) suf O B t -->* Kg (O :: Us) suf O (iter v (U 0) B) t.
Proof.
  induction v; intros Us suf B t.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, KR2 |].
    eapply evstep_trans; [apply R1ITER |].
    rewrite iter_S', U_0.
    apply IHv.
Qed.

Lemma CDP : forall j v Us suf B t,
  Kg (repeat O j ++ v :: Us) suf O B t -->* Kg (repeat O (S j) ++ Us) suf O (iter v (U j) B) t.
Proof.
  induction j as [| n IHn].
  - intros. simpl. apply CH.
  - intro v. induction v as [| w IHw]; intros Us suf B t.
    + rewrite repeat_snoc. apply evstep_refl.
    + eapply evstep_trans; [apply progress_evstep, KR3 |].
      eapply evstep_trans; [apply (IHn (2 * B + 2) (w :: Us) suf O t) |].
      rewrite <- U_S.
      eapply evstep_trans; [apply (IHw Us suf (U (S n) B) t) |].
      rewrite iter_S'. apply evstep_refl.
Qed.

(** Clearing the residue-2 token 3v+2 behind M+1 zero digits, down to 2 (its zero). *)
Lemma CLR2 : forall v M P B t,
  Kg (repeat O (S M)) (3 * v + 2 :: P) O B t -->* Kg (repeat O (S M)) (2 :: P) O (iter v (U (S M)) B) t.
Proof.
  induction v; intros M P B t.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, KR3s |].
    eapply evstep_trans; [apply (CDP M (2 * B + 2) [] (3 * v + 2 :: P) O t) |].
    rewrite app_nil_r, <- U_S.
    eapply evstep_trans; [apply (IHv M P (U (S M) B) t) |].
    rewrite iter_S'. apply evstep_refl.
Qed.

Lemma init_reach : c0 -->* Kg (repeat O 10 ++ [2]) [] O O 0.
Proof.
  unfold c0, Kg, Kt.
  do 2369 step.
  apply evstep_refl'. reflexivity.
Qed.

Local Open Scope nat_scope.

Fixpoint arrow (k a b : nat) : nat :=
  match k with
  | O => a * b
  | S k' => Nat.iter b (arrow k' a) 1
  end.

Lemma arrow_1_pow : forall a b, arrow 1 a b = a ^ b.
Proof. intros a b. induction b; simpl. - reflexivity. - simpl in IHb. rewrite IHb. reflexivity. Qed.

Lemma arrow_S0 : forall k a, arrow (S k) a 0 = 1.
Proof. reflexivity. Qed.

Lemma arrow_SS : forall k a b, arrow (S k) a (S b) = arrow k a (arrow (S k) a b).
Proof. reflexivity. Qed.

Lemma arrow_0 : forall a b, arrow 0 a b = a * b.
Proof. reflexivity. Qed.

Lemma arrow_S_iter : forall k a b, arrow (S k) a b = iter b (arrow k a) 1.
Proof. induction b. - reflexivity. - rewrite arrow_SS, IHb. reflexivity. Qed.

Opaque arrow.

Lemma arrow_one : forall k, arrow k 2 1 = 2.
Proof.
  induction k. - reflexivity.
  - change 1 with (S 0) at 2. rewrite arrow_SS, arrow_S0. exact IHk.
Qed.

Lemma arrow_two : forall k, arrow k 2 2 = 4.
Proof.
  induction k. - reflexivity.
  - change 2 with (S 1) at 2. rewrite arrow_SS, arrow_one. exact IHk.
Qed.

Lemma dbl_closed : forall a b, dbl a b + 2 = 2 ^ a * (b + 2).
Proof.
  induction a; intros b; simpl dbl. - simpl. lia.
  - rewrite IHa. rewrite Nat.pow_succ_r'. lia.
Qed.

(** 2 * U j x + 4 = 2 ^(j+1 arrows) (2 x + 4)  (BB8_champ35_exact.v) *)
Lemma U_closed : forall j x, 2 * U j x + 4 = arrow (S j) 2 (2 * x + 4).
Proof.
  induction j as [| j IH]; intros x.
  - rewrite (U_0 x), (arrow_1_pow 2 (2 * x + 4)).
    pose proof (dbl_closed (2 * x + 2) 0) as Hd.
    replace (2 * x + 4) with (S (S (2 * x + 2))) by lia.
    rewrite !Nat.pow_succ_r'. lia.
  - assert (Hit : forall n, 2 * iter n (U j) 0 + 4 = iter n (arrow (S j) 2) 4).
    { induction n as [| n IHn].
      - reflexivity.
      - simpl iter. rewrite (IH (iter n (U j) 0)), IHn. reflexivity. }
    rewrite (U_S j x), (arrow_S_iter (S j) 2 (2 * x + 4)).
    replace (2 * x + 4) with (S (S (2 * x + 2))) by lia.
    rewrite (iter_S' (S (2 * x + 2)) (arrow (S j) 2) 1).
    rewrite (iter_S' (2 * x + 2) (arrow (S j) 2) (arrow (S j) 2 1)).
    rewrite (arrow_one (S j)), (arrow_two (S j)).
    exact (Hit (2 * x + 2)).
Qed.

(** Powers of two: arrow k 2 n = 2^e with e >= 2 (k >= 1, n >= 2). *)
Definition pow2ge2 (x : nat) : Prop := exists e, x = 2 ^ e /\ 2 <= e.

Lemma pow2ge2_ge4 : forall x, pow2ge2 x -> 4 <= x.
Proof.
  intros x [e [-> He]]. replace e with (2 + (e - 2)) by lia. rewrite Nat.pow_add_r.
  change (2 ^ 2) with 4. pose proof (Nat.pow_nonzero 2 (e - 2) ltac:(lia)). lia.
Qed.

Lemma arrow_pow2 : forall k n, 1 <= k -> 2 <= n -> pow2ge2 (arrow k 2 n).
Proof.
  induction k as [| k IHk]; intros n Hk Hn; [lia |].
  destruct k as [| k'].
  - rewrite arrow_1_pow. exists n. split; [reflexivity | exact Hn].
  - induction n as [| n IHn]; [lia |].
    rewrite arrow_SS. apply IHk; [lia |].
    destruct (Nat.eq_dec n 1) as [-> | Hne].
    + rewrite arrow_one. lia.
    + specialize (IHn ltac:(lia)). apply pow2ge2_ge4 in IHn. lia.
Qed.

Lemma pow16_mod5 : forall y, 16 ^ y mod 5 = 1.
Proof.
  induction y. - reflexivity.
  - rewrite Nat.pow_succ_r', Nat.Div0.mul_mod, IHy. reflexivity.
Qed.

Lemma pow2_pow2_mod5 : forall e, 2 <= e -> 2 ^ (2 ^ e) mod 5 = 1.
Proof.
  intros e He.
  assert (E : 2 ^ e = 4 * 2 ^ (e - 2)).
  { destruct e as [| [| e']]; [lia | lia |].
    replace (S (S e') - 2) with e' by lia. rewrite !Nat.pow_succ_r'. lia. }
  rewrite E, Nat.pow_mul_r. change (2 ^ 4) with 16. apply pow16_mod5.
Qed.

(** arrow k 2 n = 1 (mod 5) for k >= 2, n >= 3 *)
Lemma arrow_mod5 : forall k n, 2 <= k -> 3 <= n -> arrow k 2 n mod 5 = 1.
Proof.
  induction k as [| k IHk]; intros n Hk Hn; [lia |].
  destruct n as [| n']; [lia |]. rewrite arrow_SS.
  destruct (Nat.eq_dec k 1) as [-> | Hk1].
  - rewrite arrow_1_pow.
    destruct (arrow_pow2 2 n' ltac:(lia) ltac:(lia)) as [e [He He2]].
    rewrite He. apply pow2_pow2_mod5. exact He2.
  - apply IHk; [lia |].
    destruct (arrow_pow2 (S k) n' ltac:(lia) ltac:(lia)) as [e [He He2]].
    pose proof (pow2ge2_ge4 (arrow (S k) 2 n') (ex_intro _ e (conj He He2))). lia.
Qed.

Lemma arrow_gt_arg : forall k n, 1 <= k -> 2 <= n -> n < arrow k 2 n.
Proof.
  induction k as [| k IHk]; intros n Hk Hn; [lia |].
  destruct k as [| k'].
  - rewrite arrow_1_pow. clear IHk Hk. induction n as [| n IHn]; [lia |].
    destruct (Nat.eq_dec n 1) as [-> | Hne]; [simpl; lia |].
    rewrite Nat.pow_succ_r'. specialize (IHn ltac:(lia)). lia.
  - induction n as [| n IHn]; [lia |].
    rewrite arrow_SS.
    destruct (Nat.eq_dec n 1) as [-> | Hne].
    + rewrite arrow_one, arrow_two. lia.
    + specialize (IHn ltac:(lia)).
      pose proof (IHk (arrow (S (S k')) 2 n) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma U_pos : forall j x, 1 <= U j x.
Proof.
  intros j x. pose proof (U_closed j x) as E.
  pose proof (arrow_gt_arg (S j) (2 * x + 4) ltac:(lia) ltac:(lia)) as G.
  rewrite <- E in G. lia.
Qed.

(** ** The first exhaustion: B = U 10 (U 10 0) = (2 ^13 3 - 4) / 2 *)

(** Sealed (no tactic or kernel check can unfold it into a computation). *)
Lemma Bx_sig : { b : nat | b = U 10 (U 10 O) }.
Proof. exists (U 10 (U 10 O)). reflexivity. Qed.

Definition Bx : nat := proj1_sig Bx_sig.

Lemma Bx_def : Bx = U 10 (U 10 O).
Proof. exact (proj2_sig Bx_sig). Qed.

Lemma Bx_closed : 2 * Bx + 4 = arrow 11 2 (arrow 11 2 4).
Proof.
  rewrite Bx_def, (U_closed 10 (U 10 O)), (U_closed 10 O).
  change (2 * O + 4) with 4. reflexivity.
Qed.

Opaque Bx.

Lemma Bx_mod5 : Bx mod 5 = 1.
Proof.
  pose proof Bx_closed as HB.
  pose proof (arrow_gt_arg 11 4 ltac:(lia) ltac:(lia)) as H4.
  pose proof (arrow_mod5 11 (arrow 11 2 4) ltac:(lia) ltac:(lia)) as Hm.
  rewrite <- HB in Hm. clear HB H4.
  pose proof (Nat.div_mod (2 * Bx + 4) 5 ltac:(lia)) as E1.
  pose proof (Nat.div_mod Bx 5 ltac:(lia)) as E2.
  pose proof (Nat.mod_upper_bound Bx 5 ltac:(lia)) as E3.
  rewrite Hm in E1. clear Hm.
  (* keep lia away from div/mod (busycoq turns them into division equations) *)
  generalize dependent ((2 * Bx + 4) / 5). generalize dependent (Bx / 5).
  generalize dependent (Bx mod 5). intros. lia.
Qed.

Lemma Bx_ge6 : 6 <= Bx.
Proof.
  pose proof Bx_closed as HB.
  pose proof (arrow_gt_arg 11 4 ltac:(lia) ltac:(lia)) as H4.
  destruct (arrow_pow2 11 (arrow 11 2 4) ltac:(lia) ltac:(lia)) as [e [He He2]].
  pose proof Bx_mod5 as Hm.
  rewrite He in HB. clear He H4.
  assert (E : e = 2 \/ e = 3 \/ 4 <= e) by lia.
  destruct E as [-> | [-> | E]].
  - simpl in HB. assert (E0 : Bx = 0) by (clear Hm; lia). rewrite E0 in Hm. simpl in Hm. discriminate.
  - simpl in HB. assert (E0 : Bx = 2) by (clear Hm; lia). rewrite E0 in Hm. simpl in Hm. discriminate.
  - assert (16 <= 2 ^ e).
    { replace e with (4 + (e - 4)) by lia. rewrite Nat.pow_add_r.
      pose proof (Nat.pow_nonzero 2 (e - 4) ltac:(lia)). change (2 ^ 4) with 16. lia. }
    clear Hm. lia.
Qed.
Lemma run_to_exhaustion : c0 -->* Kg (repeat O 11) [] O Bx 0.
Proof.
  eapply evstep_trans; [apply init_reach |].
  eapply evstep_trans; [apply (CDP 10 2 [] [] O 0) |].
  rewrite Bx_def. apply evstep_refl.
Qed.
