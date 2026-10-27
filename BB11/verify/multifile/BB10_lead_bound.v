(** * Exact score of the BB(10) candidate 1RB0RA_1LC1LF_1RD0LB_1RA1LE_0LJ0LC_1RG1LD_0RI0RH_1RG1LF_1RE1RI_---1LC *)

(** Imports the halting proof BB10_lead_1RB0RA.v (Theorem halt; run_to_halt : c0 -->* cH (2 b2 + 1) (4 bf + 32)).
    Main results (no axioms):
      Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (2 * b2 + 2 * (4 * bf + 33) + 5).
      Lemma bf_closed : bf + 4 = arrow 27 2 3.
      Lemma b2_closed : b2 + 4 = arrow (4 * bf + 33) 2 5.
      Theorem score_closed : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
                             N + 1 = 2 * arrow (4 * bf + 33) 2 5 + 2 * (4 * bf + 33) - 2.
    [ones c N]: the tape of c holds exactly N ones; busycoq stops before the halting transition J0 (undefined, the
    head reads a 0), which writes one more 1 in the standard convention, so sigma = N + 1
      = 2 * (2 ^(L arrows) 5) + 2 L - 2,  L = 4 * (2 ^(27 arrows) 3) + 17.
    arrow k a b = a ^(k arrows) b with 0 arrows = multiplication (as in BB8_champ35_bound.v). *)

From BB8 Require Import Individual102.
From BB8 Require Import BB10_lead_1RB0RA.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

(** ** Counting ones *)

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

(** [ones c n]: the tape of c is L (reversed, left of the head), s (head cell), R (right of the head), with 0s
    beyond both lists, and n = number of 1s in L, s, R. *)
Definition ones (c : state * tape) (n : nat) : Prop :=
  exists (q : state) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ n = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl; [reflexivity | rewrite IHxs; lia]. Qed.

Lemma count1_pow : forall xs m, count1 (xs^^m) = m * count1 xs.
Proof. intros xs m. induction m; simpl; [reflexivity | rewrite count1_app, IHm; lia]. Qed.

Lemma ones_cH : forall a i, ones (cH a i) (a + 2 * i + 6).
Proof.
  intros a i.
  exists J, (@nil Sym), ([S0; S1; S1; S1] ++ [S0; S1]^^a ++ [S0; S1; S0; S1; S0; S1; S0; S0] ++ [S1; S0; S1]^^i), S0.
  split.
  - unfold cH. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, !count1_pow. simpl. lia.
Qed.

Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (2 * b2 + 2 * (4 * bf + 33) + 5).
Proof.
  exists (cH (2 * b2 + 1) (4 * bf + 32)). split; [exact run_to_halt |]. split; [apply cH_halted |].
  replace (2 * b2 + 2 * (4 * bf + 33) + 5) with ((2 * b2 + 1) + 2 * (4 * bf + 32) + 6) by lia.
  apply ones_cH.
Qed.

(** ** Knuth's up-arrows (as in BB8_champ35_bound.v) *)

Fixpoint arrow (k a b : nat) : nat :=
  match k with
  | O => a * b
  | S k' => Nat.iter b (arrow k' a) 1
  end.

Lemma arrow_S0 : forall k a, arrow (S k) a 0 = 1.
Proof. reflexivity. Qed.

Lemma arrow_SS : forall k a b, arrow (S k) a (S b) = arrow k a (arrow (S k) a b).
Proof. reflexivity. Qed.

Lemma arrow_0 : forall a b, arrow 0 a b = a * b.
Proof. reflexivity. Qed.

Lemma arrow_S_iter : forall k a b, arrow (S k) a b = iter b (arrow k a) 1.
Proof. induction b. - reflexivity. - rewrite arrow_SS, IHb. reflexivity. Qed.

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

Opaque arrow.

Lemma iter_add : forall a b g x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

(** ** Closed forms of the clearing functions:  F (k+1) x + 4 = 2 ^(k arrows) (x + 4) *)

Lemma iter_F0 : forall n x, iter n (F 0) x = x + 2 * n.
Proof. induction n; intros; simpl. - lia. - rewrite IHn. lia. Qed.

Lemma F_closed : forall k x, F (S k) x + 4 = arrow k 2 (x + 4).
Proof.
  induction k as [| k IH]; intros x.
  - rewrite F_S, iter_F0, (arrow_0 2 (x + 4)). lia.
  - assert (Hit : forall n, iter n (F (S k)) 0 + 4 = iter n (arrow k 2) 4).
    { induction n as [| n IHn]. - reflexivity.
      - change (iter (S n) (F (S k)) 0) with (F (S k) (iter n (F (S k)) 0)).
        change (iter (S n) (arrow k 2) 4) with (arrow k 2 (iter n (arrow k 2) 4)).
        rewrite IH, IHn. reflexivity. }
    rewrite F_S, Hit, (arrow_S_iter k 2 (x + 4)).
    replace (x + 4) with ((x + 2) + 2) by lia. rewrite (iter_add (x + 2) 2 (arrow k 2) 1).
    change (iter 2 (arrow k 2) 1) with (arrow k 2 (arrow k 2 1)).
    rewrite (arrow_one k), (arrow_two k). reflexivity.
Qed.

Lemma iter3 : forall k, iter 3 (F (S k)) 0 + 4 = arrow (S k) 2 5.
Proof.
  intros k.
  change (iter 3 (F (S k)) 0) with (F (S k) (F (S k) (F (S k) 0))).
  rewrite (F_closed k (F (S k) (F (S k) 0))), (F_closed k (F (S k) 0)), (F_closed k 0).
  change (0 + 4) with 4.
  rewrite (arrow_S_iter k 2 5).
  change (iter 5 (arrow k 2) 1) with (arrow k 2 (arrow k 2 (arrow k 2 (arrow k 2 (arrow k 2 1))))).
  rewrite (arrow_one k), (arrow_two k). reflexivity.
Qed.

Lemma bf_closed : bf + 4 = arrow 27 2 3.
Proof.
  rewrite bf_eq.
  change (iter 2 (F 26) 0) with (F 26 (F 26 0)).
  rewrite (F_closed 25 (F 26 0)), (F_closed 25 0).
  change (0 + 4) with 4.
  (* 2 ^27 3 = 2 ^26 (2 ^27 2) = 2 ^26 4 = 2 ^25 (2 ^26 3) = 2 ^25 (2 ^25 (2 ^26 2)) = 2 ^25 (2 ^25 4) *)
  change 3 with (S 2) at 1. rewrite (arrow_SS 26 2 2), (arrow_two 27).
  change 4 with (S 3) at 3. rewrite (arrow_SS 25 2 3).
  change 3 with (S 2) at 2. rewrite (arrow_SS 25 2 2), (arrow_two 26).
  reflexivity.
Qed.

Lemma b2_closed : b2 + 4 = arrow (4 * bf + 33) 2 5.
Proof.
  rewrite b2_eq. replace (4 * bf + 33) with (S (4 * bf + 32)) by lia. apply iter3.
Qed.

Theorem score_closed : exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
  n + 1 = 2 * arrow (4 * bf + 33) 2 5 + 2 * (4 * bf + 33) - 2.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (2 * b2 + 2 * (4 * bf + 33) + 5).
  split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  pose proof b2_closed as E. generalize dependent (arrow (4 * bf + 33) 2 5). intros A E. lia.
Qed.

Print Assumptions score_exact.
Print Assumptions score_closed.
Print Assumptions bf_closed.
