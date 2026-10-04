(** * A machine-checked lower bound on the score of the 35-digit BB(8) champion-rule machine *)

(** Machine: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_---0LC_1RG1LD_1LC0RH_1RG1LF  (E0 undefined = the halt).
    The machine table [tm], the digit family [Kc], the rules R1-R3, R1ITER, the phase lemmas and the start-up
    lemma [init_reach] are imported unchanged from BB8_champ35_1RB0RA.v (which proves [halt : halts tm c0]
    and passes check.py).  Written for bb8_list/investigations/bb8_champ35_bound.md.

    Main results (no axioms):
      Theorem score_exact :
        exists c, c0 -->* c /\ halted tm c /\ ones c (24 * bf + 106).
      Theorem sigma_lower_bound :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ arrow 11 2 (arrow 11 2 3) < N.
      Theorem sigma_lower_bound_strong :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ arrow 35 2 (arrow 35 2 3) < N.
      Theorem sigma_gt_arrow36 :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ arrow 36 2 3 < N.

    Definitions (standard forms, see below):
      arrow k a b : Knuth's a ^(k arrows) b, with arrow 0 a b = a * b, arrow 1 a b = a ^ b (lemma [arrow_1_pow]),
                    arrow (S k) a 0 = 1, arrow (S k) a (S b) = arrow k a (arrow (S k) a b) (lemma [arrow_eqns]).
      ones c N    : the configuration c has exactly N cells equal to 1 (both tape sides are finite lists
                    followed by const 0; N counts the left list, the head cell and the right list).

    Score convention.  busycoq stops BEFORE the halting transition: E0 is [None] in [tm], so the configuration
    c with [halted tm c] is the one in state E reading a 0 (see [c_end]).  N counts the ones of that tape.
    The standard score, which counts the 1 written by the halting transition (treated as 1RZ), is N + 1.

    Exact value: with the clearing functions U j defined below,
      bf = U 34 (U 34 0)   (the counter b when the 35-digit list becomes all zero),
      ones at the halt = 24 bf + 106,  score = 24 bf + 107,  and  bf + 2 >= arrow 35 2 (arrow 35 2 3). *)

From BB8 Require Import Individual82.
From BB8 Require Import BB8_champ35_1RB0RA.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** The imported [tm] is the declared machine (BB8_champ35_1RB0RA.v passes check.py, which checks this). *)
(* machine: 1RB0RA_1LC1LF_1RD0LB_1RA1LE_---0LC_1RG1LD_1LC0RH_1RG1LF *)
Lemma tm_table :
  tm (A, 0) = Some (1, R, B) /\ tm (A, 1) = Some (0, R, A) /\
  tm (B, 0) = Some (1, L, C) /\ tm (B, 1) = Some (1, L, F) /\
  tm (C, 0) = Some (1, R, D) /\ tm (C, 1) = Some (0, L, B) /\
  tm (D, 0) = Some (1, R, A) /\ tm (D, 1) = Some (1, L, E) /\
  tm (E, 0) = None           /\ tm (E, 1) = Some (0, L, C) /\
  tm (F, 0) = Some (1, R, G) /\ tm (F, 1) = Some (1, L, D) /\
  tm (G, 0) = Some (1, L, C) /\ tm (G, 1) = Some (0, R, H) /\
  tm (H, 0) = Some (1, R, G) /\ tm (H, 1) = Some (1, L, F).
Proof. repeat split. Qed.

(** ** Stage (a): the halting configuration, explicitly *)

(** The configuration reached by the imported phase [FIN] (state E reading 0). *)
Definition c_end (J t : nat) : Q * tape :=
  (0 >> [1;1;0]^^t *> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> const 0) <{{E}}
  (1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >>
   [1;0;1]^^J *> 1 >> 0 >> 1 >> const 0).

Lemma c_end_halted : forall J t, halted tm (c_end J t).
Proof. intros. unfold c_end. simpl. reflexivity. Qed.

(** [FIN] of the halting file with its existential witness made explicit (same tactic script). *)
Lemma FINx : forall J t, (1 >> 1 >> const 0) <{{C}} (1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> 1 >> 0 >> 1 >> [1;0;1]^^(t) *> 1 >> 0 >> 0 >> 1 >> 0 >> 0 >> 1 >> [0;0;1]^^(J) *> 0 >> 1 >> 0 >> const 0) -->* c_end J t.
Proof.
  intros. unfold c_end.
  do 28 step. follow cx_HR_101_101_c0. do 8 step. rewrite (align_lpow 1 [0;1] _ t). simpl app.
  do 1 step. rewrite (align_lpow 0 [1;1] _ t). simpl app. do 24 step. follow cx_HR_001_101_c0110.
  do 29 step. rewrite (align_lpow 1 [0;1] _ J). simpl app. do 1 step.
  rewrite (align_lpow 0 [1;1] _ J). simpl app. do 27 step.
  rewrite (align_lpow 1 [1;0] _ J). simpl app. do 1 step.
  rewrite (align_lpow 1 [0;1] _ J). simpl app. do 1 step.
  rewrite (align_lpow 0 [1;1] _ J). simpl app. do 67 step. follow cx_BL_110_101_c0101010101010100.
  do 1 step. rewrite (align_lpow 1 [1;0] _ t). simpl app. do 1 step.
  rewrite (align_lpow 1 [0;1] _ t). simpl app. do 1 step.
  rewrite (align_lpow 0 [1;1] _ t). simpl app. apply evstep_refl.
Qed.

(** [R4] of the halting file with the halting configuration made explicit (same proof, ending in [FINx]). *)
Lemma R4x : forall M b, Kc (repeat O (S M)) O b -->* c_end M (2 * S (S (S (S (6 * b)))) + 1).
Proof.
  intros. unfold Kc. rewrite lft_blank.
  follow (ROUNDS (S (3 * b)) O 2 ([1;0]^^(S (3 * O)) *> 1 >> [1;0;1]^^(S M) *> const 0)).
  replace (2 * S (3 * b) + 2) with (S (S (S (S (6 * b))))) by lia.
  eapply evstep_trans; [apply progress_evstep, (E3 M (S (S (S (S (6 * b))))) (const 0)) |].
  follow (HOPS M 1 (S (S (S (S (6 * b))))) (const 0)).
  follow (X4 M (S (S (S (S (6 * b)))))).
  follow (TLPS (S (S (S (S (6 * b))))) 6 M).
  replace (2 * S (S (S (S (6 * b)))) + 6) with (S (S (S (S (S (2 * S (S (S (S (6 * b)))) + 1)))))) by lia.
  exact (FINx M (2 * S (S (S (S (6 * b)))) + 1)).
Qed.

Local Open Scope nat_scope.

(** *** Counting ones *)

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
Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl. - reflexivity. - rewrite IHxs. lia. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl. - reflexivity. - rewrite count1_app, IHn. lia. Qed.

Lemma ones_c_end : forall J t, ones (c_end J t) (2 * t + 2 * J + 20).
Proof.
  intros J t.
  exists E, ([S1;S1;S0]^^t ++ [S1;S1;S0;S1;S1;S0;S1;S1;S0;S1;S0;S1]),
            ([S1;S1;S1;S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S0;S1;S0;S0] ++ [S1;S0;S1]^^J ++ [S1;S0;S1]), S0.
  split.
  - unfold c_end. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, !count1_pow. simpl. lia.
Qed.

(** The halt from an all-zero list of M+1 digits with counter b: exactly 24 b + 2 M + 38 ones. *)
Lemma halt_count : forall M b, Kc (repeat O (S M)) O b -->* c_end M (2 * S (S (S (S (6 * b)))) + 1) /\
  halted tm (c_end M (2 * S (S (S (S (6 * b)))) + 1)) /\
  ones (c_end M (2 * S (S (S (S (6 * b)))) + 1)) (24 * b + 2 * M + 38).
Proof.
  intros M b. split; [apply R4x |]. split; [apply c_end_halted |].
  replace (24 * b + 2 * M + 38) with (2 * (2 * S (S (S (S (6 * b)))) + 1) + 2 * M + 20) by lia.
  apply ones_c_end.
Qed.

(** ** Stage (b): exact clearing functions and the clearing lemma *)

Fixpoint iter (n : nat) (g : nat -> nat) (x : nat) : nat :=
  match n with
  | O => x
  | S n' => g (iter n' g x)
  end.

Lemma iter_S' : forall n g x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

(** U j x : the counter b after clearing ONE unit of a digit at depth j (j zero digits nearer the counters)
    from b = x; the zero digits are restored afterwards.
      U 0 x = dbl (2x+2) 0  (R2 sets a = 2x+2, then R1 a times: b -> 2b+2; this is 2^(2x+3) - 2),
      U (j+1) x = (U j)^(2x+2) (0)  (R3 at depth j+1 writes the digit 2x+2 at depth j with b = 0,
                                      which is then cleared unit by unit). *)
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

(** clearing the nearest digit *)
Lemma CH : forall v Us B, Kc (v :: Us) O B -->* Kc (O :: Us) O (iter v (U 0) B).
Proof.
  induction v; intros Us B.
  - apply evstep_refl.
  - eapply evstep_trans; [apply progress_evstep, R2 |].
    eapply evstep_trans; [apply R1ITER |].
    rewrite iter_S', U_0.
    apply IHv.
Qed.

(** clearing a digit v at depth j *)
Lemma CDP : forall j v Us B,
  Kc (repeat O j ++ v :: Us) O B -->* Kc (repeat O (S j) ++ Us) O (iter v (U j) B).
Proof.
  induction j as [| n IHn].
  - intros. simpl. apply CH.
  - intro v. induction v as [| w IHw]; intros Us B.
    + rewrite repeat_snoc. apply evstep_refl.
    + eapply evstep_trans; [apply progress_evstep, R3 |].
      follow (IHn (2 * B + 2) (w :: Us) O).
      rewrite <- U_S.
      follow (IHw Us (U (S n) B)).
      rewrite iter_S'. apply evstep_refl.
Qed.

(** ** Stage (c): the run from the blank tape, with the exact score *)

Definition bf : nat := U 34 (U 34 O).

Lemma bf_def : bf = U 34 (U 34 O).
Proof. reflexivity. Qed.

Opaque bf.

Lemma run_to_zero : c0 -->* Kc (repeat O 35) O bf.
Proof.
  follow init_reach.
  follow (CDP 34 2 [] O).
  rewrite app_nil_r, bf_def. apply evstep_refl.
Qed.

Lemma count_arith : forall b, 24 * b + 2 * 34 + 38 = 24 * b + 106.
Proof. intros. lia. Qed.

Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (24 * bf + 106).
Proof.
  destruct (halt_count 34 bf) as [H1 [H2 H3]].
  rewrite count_arith in H3.
  eexists. split; [| split; [exact H2 | exact H3]].
  follow run_to_zero. exact H1.
Qed.

(** ** Knuth's up-arrows *)

(** arrow k a b = a ^(k arrows) b, with 0 arrows = multiplication. *)
Fixpoint arrow (k a b : nat) : nat :=
  match k with
  | O => a * b
  | S k' => Nat.iter b (arrow k' a) 1
  end.

Lemma arrow_eqns : forall a b k,
  arrow 1 a b = a ^ b /\ arrow (S k) a 0 = 1 /\ arrow (S k) a (S b) = arrow k a (arrow (S k) a b).
Proof.
  intros a b k. split; [| split; reflexivity].
  induction b; simpl. - reflexivity. - simpl in IHb. rewrite IHb. reflexivity.
Qed.

Lemma arrow_1_pow : forall a b, arrow 1 a b = a ^ b.
Proof. intros. apply (arrow_eqns a b 0). Qed.

Lemma arrow_S0 : forall k a, arrow (S k) a 0 = 1.
Proof. reflexivity. Qed.

Lemma arrow_SS : forall k a b, arrow (S k) a (S b) = arrow k a (arrow (S k) a b).
Proof. reflexivity. Qed.

Lemma arrow_0 : forall a b, arrow 0 a b = a * b.
Proof. reflexivity. Qed.

Lemma arrow_S_iter : forall k a b, arrow (S k) a b = iter b (arrow k a) 1.
Proof. induction b. - reflexivity. - rewrite arrow_SS, IHb. reflexivity. Qed.

Opaque arrow.

(** *** Iteration facts *)

Lemma iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

Lemma iter_add : forall a b g x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

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

(** *** Up-arrows with base 2: monotonicity *)

Lemma arrow_props : forall k,
  (forall x y, x <= y -> arrow k 2 x <= arrow k 2 y) /\ (forall x, 1 <= x -> x + 1 <= arrow k 2 x) /\
  (forall x, x <= arrow k 2 x).
Proof.
  induction k as [| k [Hm [Hs Hi]]].
  - split; [intros x y Hxy | split; [intros x Hx | intros x]];
    rewrite ?(arrow_0 2 x); rewrite ?(arrow_0 2 y); lia.
  - assert (Hm' : forall x y, x <= y -> arrow (S k) 2 x <= arrow (S k) 2 y).
    { intros x y Hxy. rewrite !arrow_S_iter. apply iter_mono_n; assumption. }
    assert (Hs' : forall x, 1 <= x -> x + 1 <= arrow (S k) 2 x).
    { intros x Hx. rewrite arrow_S_iter.
      pose proof (iter_lin1 (arrow k 2) Hs x 1 ltac:(lia)) as Hl.
      destruct x as [| x']; [lia |].
      simpl iter. pose proof (Hs (iter x' (arrow k 2) 1)).
      pose proof (iter_lin1 (arrow k 2) Hs x' 1 ltac:(lia)). lia. }
    split; [exact Hm' | split; [exact Hs' |]].
    intros x. destruct x as [| x']; [lia |]. pose proof (Hs' (S x') ltac:(lia)). lia.
Qed.

Lemma arrow_mono : forall k x y, x <= y -> arrow k 2 x <= arrow k 2 y.
Proof. intros. apply arrow_props. assumption. Qed.

Lemma arrow_gt : forall k x, 1 <= x -> x + 1 <= arrow k 2 x.
Proof. intros. apply arrow_props. assumption. Qed.

Lemma arrow_id : forall k x, x <= arrow k 2 x.
Proof. intros. apply arrow_props. Qed.

Lemma arrow_level : forall k x, arrow k 2 x <= arrow (S k) 2 x.
Proof.
  intros k x. destruct x as [| x'].
  - rewrite arrow_S0. destruct k; [rewrite (arrow_0 2 0); lia | rewrite arrow_S0; lia].
  - rewrite arrow_SS. apply arrow_mono.
    rewrite arrow_S_iter.
    pose proof (iter_lin1 (arrow k 2) (arrow_gt k) x' 1 ltac:(lia)). lia.
Qed.

Lemma arrow_level_mono : forall d k x, arrow k 2 x <= arrow (d + k) 2 x.
Proof.
  induction d; intros k x. - reflexivity.
  - specialize (IHd k x). pose proof (arrow_level (d + k) x). change (S d + k) with (S (d + k)). lia.
Qed.

Lemma arrow_one : forall k, arrow k 2 1 = 2.
Proof.
  induction k. - reflexivity.
  - change 1 with (S 0) at 2. rewrite arrow_SS, arrow_S0. exact IHk.
Qed.

(** *** The clearing functions grow like up-arrows *)

Lemma dbl_closed : forall a b, dbl a b + 2 = 2 ^ a * (b + 2).
Proof.
  induction a; intros b; simpl dbl. - simpl. lia.
  - rewrite IHa. rewrite Nat.pow_succ_r'. lia.
Qed.

(** U j x + 2 >= 2 ^(j+1 arrows) (2x+3) *)
Lemma U_bound : forall j x, arrow (S j) 2 (2 * x + 3) <= U j x + 2.
Proof.
  induction j as [| j IH]; intros x.
  - rewrite arrow_1_pow, U_0, dbl_closed.
    replace (2 * x + 3) with (S (2 * x + 2)) by lia. rewrite Nat.pow_succ_r'. lia.
  - assert (Hit : forall n, iter n (arrow (S j) 2) 2 <= iter n (U j) 0 + 2).
    { induction n as [| n IHn]. - simpl. lia.
      - simpl iter.
        transitivity (arrow (S j) 2 (2 * iter n (U j) 0 + 3)).
        + apply arrow_mono. lia.
        + apply IH. }
    rewrite U_S, arrow_S_iter.
    replace (2 * x + 3) with (S (2 * x + 2)) by lia.
    rewrite iter_S', arrow_one. apply Hit.
Qed.

(** ** Main theorems *)

(** bf + 2 >= 2 ^(35 arrows) (2 ^(35 arrows) 3) *)
Lemma bf_big : arrow 35 2 (arrow 35 2 3) <= bf + 2.
Proof.
  rewrite bf_def.
  pose proof (U_bound 34 0) as H1. replace (2 * 0 + 3) with 3 in H1 by lia.
  pose proof (U_bound 34 (U 34 0)) as H2.
  pose proof (arrow_mono 35 (arrow 35 2 3) (2 * U 34 0 + 3) ltac:(lia)) as H3.
  lia.
Qed.

Theorem sigma_lower_bound_strong :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ arrow 35 2 (arrow 35 2 3) < N.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (24 * bf + 106). split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  pose proof bf_big. lia.
Qed.

(** 2 ^11 (2 ^11 3) <= 2 ^35 (2 ^11 3) <= 2 ^35 (2 ^35 3)  (arrows) *)
Lemma arrow_11_35 : arrow 11 2 (arrow 11 2 3) <= arrow 35 2 (arrow 35 2 3).
Proof.
  pose proof (arrow_level_mono 24 11 (arrow 11 2 3)) as L1. change (24 + 11) with 35 in L1.
  pose proof (arrow_level_mono 24 11 3) as L2. change (24 + 11) with 35 in L2.
  pose proof (arrow_mono 35 _ _ L2) as L3.
  lia.
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ arrow 11 2 (arrow 11 2 3) < N.
Proof.
  destruct sigma_lower_bound_strong as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  pose proof arrow_11_35. lia.
Qed.

(** A corollary in the form 2 ^36 3 < N  (2 ^36 3 = 2 ^35 4 <= 2 ^35 (2 ^35 3), arrows). *)
Lemma arrow_two : forall k, arrow k 2 2 = 4.
Proof.
  induction k. - reflexivity.
  - change 2 with (S 1) at 2. rewrite arrow_SS, arrow_one. exact IHk.
Qed.

Theorem sigma_gt_arrow36 : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ arrow 36 2 3 < N.
Proof.
  destruct sigma_lower_bound_strong as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  change 3 with (S 2) at 1. rewrite arrow_SS, arrow_two.
  pose proof (arrow_level_mono 34 1 3) as L1. change (34 + 1) with 35 in L1.
  rewrite arrow_1_pow in L1. change (2 ^ 3) with 8 in L1.
  pose proof (arrow_mono 35 4 (arrow 35 2 3) ltac:(lia)). lia.
Qed.

Print Assumptions score_exact.
Print Assumptions sigma_lower_bound.
Print Assumptions sigma_lower_bound_strong.
Print Assumptions sigma_gt_arrow36.
