(** Bridge from c04-coq2's endgame data to the score bounds.
    Endgame (c04-coq2, 2026-10-17): at the key, parked count P >= Pm + L (Step.reachP), clear depth K = P - c_key,
    R_last >= R1 = iter 2 (U K) 0, halting tape has >= 6 R_last + 2 ones.
      K_ge_R2       : Pm + L <= P -> P <= K + c -> c <= 1000 -> 11 * R2 Bx <= K
      beats_fw2_end : the same hypotheses + iter 2 (U K) 0 <= Rl -> 6 * Rl + 2 <= N ->
                      f_omega (f_omega (465 * 1000 + 9)) < N  (Score's copy)  /\
                      BB9_fw2_bound.f_omega (BB9_fw2_bound.f_omega (465 * 1000 + 9)) < N  /\
                      exists cf Nf, fw2 halts in cf with Nf ones and Nf + 1 < N
    Build: python coqc_score.py ScoreK.v 600 --fw2 *)
From BB8 Require Import Individual92.
From BB8 Require BB9_fw2_1RB0RD BB9_fw2_bound.
From Coq Require Import Lia PeanoNat List.
Set Default Goal Selector "!".
From Dev Require Import Abs Chain Step.
From Score Require Import Score Fw2Link Fw2Upper.

Local Open Scope nat_scope.
Opaque U arrow Bx.

Lemma K_ge_R2 : forall L P K c, Pm + L <= P -> P <= K + c -> c <= 1000 -> 11 * R2 Bx <= K.
Proof.
  intros L P K c HP HK Hc. unfold Pm in HP.
  destruct L1_val as [b [EB E1]].
  pose proof (R2_ge Bx) as HR.
  pose proof Bx_big as HB.
  rewrite E1 in HP.
  generalize dependent (R2 Bx). intros R HR HP. lia.
Qed.

Theorem beats_fw2_end : forall L P K c Rl N, Pm + L <= P -> P <= K + c -> c <= 1000 ->
  iter 2 (U K) 0 <= Rl -> 6 * Rl + 2 <= N ->
  f_omega (f_omega (465 * 1000 + 9)) < N /\
  BB9_fw2_bound.f_omega (BB9_fw2_bound.f_omega (465 * 1000 + 9)) < N /\
  exists cf Nf, c0 -[ BB9_fw2_1RB0RD.tm ]->* cf /\ halted BB9_fw2_1RB0RD.tm cf /\
    BB9_fw2_bound.ones cf Nf /\ Nf + 1 < N.
Proof.
  intros L P K c Rl N HP HK Hc HR HN.
  pose proof (K_ge_R2 L P K c HP HK Hc) as HK11.
  pose proof (iter_U_ge 2 K 0 ltac:(lia)) as HU.
  split; [| split].
  - apply (beats_fw2 K Rl N HK11); lia.
  - apply (beats_fw2_link K Rl N HK11); lia.
  - apply (fw2_side N K Rl HK11); lia.
Qed.

Print Assumptions K_ge_R2.
Print Assumptions beats_fw2_end.
