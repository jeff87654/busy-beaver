(** * BB30_vs_BB29: Argon's 30-state hydra machine (BB30) beats the published BB(29) machine + 1.

    Depends on: the published BB29 files (busy-beaver BB29/verify/multifile, unchanged: BB292, Individual292,
    BB29_tm, BB29_rules, BB29_scan, BB29_round, BB29_hydra, BB29_halt, Ord, Ufun, BB29_bound), the new
    BB29_upper.v, and the verified BB30 files (argon_scout/H30: BB302, Individual302, BB30_tm, BB30_rules, Hardy,
    HydraOrd, BB30_scan, BB30_round, BB30_game, BB30_halt, BB30_bound).

    BB30_bound.hardy_score : BB30 halts with N ones, f_(omega^9)(10) <= N + 2.
    BB29_upper.halts_with_upper : if BB29 halts with NB ones (NB = T 4 S 1 + 1, BB29_upper.halts_with_exact),
                                  then NB + 24 <= f_(omega^9)(10).
    Hence NB + 22 <= N.  Both machines halt in state B reading 0 (B0 undefined), the same sigma convention. *)

From BB8 Require Import Ord.
From BB8 Require BB29_upper.
From BB8 Require Import BB30_tm BB30_game BB30_bound.
From Coq Require Import Lia.
Set Default Goal Selector "!".

(** sigma(BB30) > sigma(BB29) + 1 *)
Theorem BB30_beats_BB29 : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  forall NB, BB29_upper.halts_with NB -> NB + 22 <= N.
Proof.
  destruct hardy_score as (c & N & H1 & H2 & H3 & H4). exists c, N.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros NB HB. pose proof (BB29_upper.halts_with_upper NB HB). lia.
Qed.

Print Assumptions BB30_beats_BB29.
