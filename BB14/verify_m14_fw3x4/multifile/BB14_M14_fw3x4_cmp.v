(** Comparison of M14_fw3x4 (Gemini 4 Neon) with the EXACT score of the previous BB(14) entry M14_fw3.

    M14_fw3's published proof (BB14/verify_m14_fw3, file BB14_M14_fw3.v, byte-identical copy here) proves
      BB14_M14_fw3.score_exact :
        exists c, c0 -[ BB14_M14_fw3.tm ]->* c /\ halted BB14_M14_fw3.tm c /\
                  BB14_M14_fw3.ones c (fst pa_final + snd pa_final + 6).
    Neon's file BB14_M14_fw3x4.v re-proves M14_fw3 from scratch in its module [M14_Old] (its own run, its own exact
    count [N_old], and the upper bound N_old <= f_(omega+3)(f_omega(13))), and proves N_old < N_final.
    This file connects the two: the machines are deterministic, so the halting configuration reached from c0 and
    its count of ones are unique; hence the published exact score of M14_fw3 equals Neon's N_old
    ([M14_fw3_score_agrees]), and every halting tape of M14_fw3 holds fewer ones than every halting tape of
    M14_fw3x4 ([beats_M14_fw3_all]).  Both machines halt reading a 0 with a halting transition that writes a 1, so
    sigma = ones at the halt + 1 for both, and the comparison of ones is the comparison of sigma. *)

From BB8 Require Import Individual142.
From BB8 Require BB14_M14_fw3 BB14_M14_fw3x4 BB14_M14_fw3x4_entry.
From Coq Require Import Lia PeanoNat.
Set Default Goal Selector "!".

Local Open Scope nat_scope.

(** ** Pointwise-equal tables have the same runs *)

Lemma ext_step : forall t1 t2, (forall q s, t1 (q, s) = t2 (q, s)) ->
  forall c c', c -[ t1 ]-> c' -> c -[ t2 ]-> c'.
Proof.
  intros t1 t2 E c c' H. destruct H as [q q' s s' l r Ht | q q' s s' l r Ht].
  - apply step_left. rewrite <- E. exact Ht.
  - apply step_right. rewrite <- E. exact Ht.
Qed.

Lemma ext_evstep : forall t1 t2, (forall q s, t1 (q, s) = t2 (q, s)) ->
  forall c c', c -[ t1 ]->* c' -> c -[ t2 ]->* c'.
Proof.
  intros t1 t2 E c c' H. induction H as [c | c c1 c2 H1 _ IH].
  - apply evstep_refl.
  - eapply evstep_step; [eapply ext_step; [exact E | exact H1] | exact IH].
Qed.

Lemma ext_halted : forall t1 t2, (forall q s, t1 (q, s) = t2 (q, s)) ->
  forall c, halted t1 c -> halted t2 c.
Proof. intros t1 t2 E [q [[l s] r]] H. unfold halted in *. rewrite <- E. exact H. Qed.

(** The published M14_fw3 table is Neon's copy [tm_M14_fw3] (both are the string's table, started in A). *)
Lemma old_tables_eq : forall q s, BB14_M14_fw3.tm (q, s) = BB14_M14_fw3x4.tm_M14_fw3 (q, s).
Proof. intros [] []; reflexivity. Qed.

(** The two files' [ones] have the same text; they agree. *)
Lemma count1_agree : forall xs, BB14_M14_fw3.count1 xs = BB14_M14_fw3x4.count1 xs.
Proof. induction xs as [| x xs IH]; cbn; [reflexivity | rewrite IH; destruct x; reflexivity]. Qed.

Lemma ones_agree : forall c n, BB14_M14_fw3.ones c n -> BB14_M14_fw3x4.ones c n.
Proof.
  intros c n [q [l [r [s [Hc Hn]]]]]. exists q, l, r, s. split; [exact Hc |].
  rewrite Hn, !count1_agree. destruct s; reflexivity.
Qed.

(** ** Every halting count of M14_fw3 is Neon's N_old *)

Lemma M14_fw3_unique_score : forall c n,
  c0 -[ BB14_M14_fw3.tm ]->* c -> halted BB14_M14_fw3.tm c -> BB14_M14_fw3.ones c n ->
  n = BB14_M14_fw3x4.M14_Old.N_old.
Proof.
  intros c n Hr Hh Ho.
  apply (ext_evstep _ _ old_tables_eq) in Hr. apply (ext_halted _ _ old_tables_eq) in Hh.
  apply ones_agree in Ho.
  destruct BB14_M14_fw3x4.M14_Old.score_exact_old as [c' [Hr' [Hh' Ho']]].
  assert (c = c') by exact (BB14_M14_fw3x4.evstep_halted_unique _ _ _ _ Hr Hh Hr' Hh'). subst c'.
  exact (BB14_M14_fw3x4.ones_unique _ _ _ Ho Ho').
Qed.

(** The published exact score formula and Neon's independent re-proof give the same number. *)
Theorem M14_fw3_score_agrees :
  fst BB14_M14_fw3.pa_final + snd BB14_M14_fw3.pa_final + 6 = BB14_M14_fw3x4.M14_Old.N_old.
Proof.
  destruct BB14_M14_fw3.score_exact as [c [Hr [Hh Ho]]].
  exact (M14_fw3_unique_score _ _ Hr Hh Ho).
Qed.

(** ** Every halting count of M14_fw3x4 is N_final *)

Lemma M14_fw3x4_unique_score : forall c n,
  c0 -[ BB14_M14_fw3x4_entry.tm ]->* c -> halted BB14_M14_fw3x4_entry.tm c -> BB14_M14_fw3x4.ones c n ->
  n = BB14_M14_fw3x4.N_final.
Proof.
  intros c n Hr Hh Ho.
  destruct BB14_M14_fw3x4_entry.score_exact as [c' [Hr' [Hh' Ho']]].
  assert (c = c') by exact (BB14_M14_fw3x4.evstep_halted_unique _ _ _ _ Hr Hh Hr' Hh'). subst c'.
  exact (BB14_M14_fw3x4.ones_unique _ _ _ Ho Ho').
Qed.

(** ** The comparisons *)

(** Every halting tape of M14_fw3 holds fewer ones than every halting tape of M14_fw3x4. *)
Theorem beats_M14_fw3_all : forall c1 n1 c2 n2,
  c0 -[ BB14_M14_fw3.tm ]->* c1 -> halted BB14_M14_fw3.tm c1 -> BB14_M14_fw3.ones c1 n1 ->
  c0 -[ BB14_M14_fw3x4_entry.tm ]->* c2 -> halted BB14_M14_fw3x4_entry.tm c2 -> BB14_M14_fw3x4.ones c2 n2 ->
  n1 < n2.
Proof.
  intros c1 n1 c2 n2 Hr1 Hh1 Ho1 Hr2 Hh2 Ho2.
  rewrite (M14_fw3_unique_score _ _ Hr1 Hh1 Ho1), (M14_fw3x4_unique_score _ _ Hr2 Hh2 Ho2).
  exact BB14_M14_fw3x4.N_old_lt_N_final.
Qed.

(** In the form of the earlier entries: above M14_fw3's published exact score p + a + 6 for (p, a) = pa_final. *)
Theorem beats_M14_fw3_exact :
  exists c n, c0 -[ BB14_M14_fw3x4_entry.tm ]->* c /\ halted BB14_M14_fw3x4_entry.tm c /\
              BB14_M14_fw3x4.ones c n /\
              fst BB14_M14_fw3.pa_final + snd BB14_M14_fw3.pa_final + 6 < n.
Proof.
  destruct BB14_M14_fw3x4_entry.score_exact as [c [Hr [Hh Ho]]].
  exists c, BB14_M14_fw3x4.N_final. split; [exact Hr |]. split; [exact Hh |]. split; [exact Ho |].
  rewrite M14_fw3_score_agrees. exact BB14_M14_fw3x4.N_old_lt_N_final.
Qed.

Theorem beats_M14_fw3_score :
  exists N3,
    (exists c, c0 -[ BB14_M14_fw3.tm ]->* c /\ halted BB14_M14_fw3.tm c /\ BB14_M14_fw3.ones c N3) /\
    (exists c n, c0 -[ BB14_M14_fw3x4_entry.tm ]->* c /\ halted BB14_M14_fw3x4_entry.tm c /\
                 BB14_M14_fw3x4.ones c n /\ N3 < n).
Proof.
  exists (fst BB14_M14_fw3.pa_final + snd BB14_M14_fw3.pa_final + 6).
  split; [exact BB14_M14_fw3.score_exact | exact beats_M14_fw3_exact].
Qed.

Print Assumptions M14_fw3_score_agrees.
Print Assumptions beats_M14_fw3_all.
Print Assumptions beats_M14_fw3_exact.
Print Assumptions beats_M14_fw3_score.
