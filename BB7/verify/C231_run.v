From BB7 Require Import Individual72 C231_rules1 C231_rules2 C231_rules3 C231_init Clr C231_clear.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** b when the 20-digit list is all zero *)
Definition bf : nat := W 20 5.
Lemma bf_def : bf = W 20 5.
Proof. reflexivity. Qed.
Lemma bf_ge : 25 <= bf.
Proof. rewrite bf_def. pose proof (W_ge 20 5). lia. Qed.
Opaque bf.

Lemma run_to_zero : c0 -->* Kc (repeat O 20) 0 bf.
Proof.
  follow init_reach.
  eapply evstep_trans; [apply R1ITER |].
  replace (2 + 3 * 1) with 5 by lia.
  rewrite bf_def. apply (clear_ones 19 5).
Qed.

Lemma run_to_end : c0 -->* cfin 20 bf.
Proof.
  follow run_to_zero. apply R4x. pose proof bf_ge. lia.
Qed.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl. - reflexivity. - rewrite IHxs. lia. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl. - reflexivity. - rewrite count1_app, IHn. lia. Qed.

Lemma ones_cfin : forall k b, k <= b -> ones (cfin k b) (2 * b + 7).
Proof.
  intros k b Hk.
  exists C, ([S1;S0;S0;S1] ++ [S1;S0;S1;S0]^^k), ([S1;S0;S0] ++ [S1;S1;S0;S0]^^(b + 1 - k) ++ [S1]), S1.
  split.
  - unfold cfin. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, !count1_pow. simpl. lia.
Qed.

(** (sym_val, count1, ones are defined in Defs.v.) *)

(** ** Main results for 1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_0LD0RB *)
Theorem score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (2 * W 20 5 + 7).
Proof.
  exists (cfin 20 bf). split; [exact run_to_end |]. split; [apply cfin_halted |].
  rewrite <- bf_def. apply ones_cfin. pose proof bf_ge. lia.
Qed.

Theorem c231_halts : halts tm c0.
Proof.
  destruct (with_counter run_to_end) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply cfin_halted.
Qed.
