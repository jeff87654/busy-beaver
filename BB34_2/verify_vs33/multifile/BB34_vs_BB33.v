(** * BB34_vs_BB33: Argon's 34-state hydra machine (BB34) beats the published BB(33) machine + 1.

    Depends on: the published BB33 files (busy-beaver BB33/verify/multifile, unchanged: BB332, Individual332,
    BB33_tm, BB33_rules, Ord, Hardy, HydraOrd, BB33_scan, BB33_round, BB33_game, BB33_halt), the verified
    BB34 files (argon_scout/H34: BB342, Individual342, BB34_tm, BB34_rules, BB34_scan, BB34_round, BB34_game,
    BB34_halt, BB34_bound) and the new HydraUpper.v, BB33_upper.v.

    BB34_bound.hardy_score : BB34 halts with N ones, f_(omega^omega^omega^omega^omega^4)(5) <= N + 2.
    BB33_upper.halts_with_upper : if BB33 halts with NB ones, NB + 2 <= f_(omega^omega^omega^omega^omega^3)(6).
    Here (cmp_33_34): f_(omega^omega^omega^omega^omega^3)(6) + 3 <= f_(omega^omega^omega^omega^omega^4)(5),
    hence NB + 3 <= N.  Both machines halt in state B reading 0 (B0 undefined), so sigma is N (resp. NB) or
    N + 1 (resp. NB + 1) under the same convention for both, and sigma(BB34) >= sigma(BB33) + 3 > sigma(BB33) + 1. *)

From BB8 Require Import Ord Hardy HydraOrd HydraUpper.
From BB8 Require BB33_upper.
From BB8 Require Import BB34_tm BB34_game BB34_bound.
From Coq Require Import Lia.
Set Default Goal Selector "!".

Lemma cmp_33_34 : FGH (powtower 5 (ofin 3)) 6 + 3 <= FGH (powtower 5 (ofin 4)) 5.
Proof.
  assert (HX : nf (powtower 6 (ofin 4))) by (apply nf_powtower, nf_ofin).
  assert (HXl : okind (powtower 6 (ofin 4)) = KLim) by reflexivity.
  assert (E1 : FGH (powtower 5 (ofin 4)) 5 = HH (powtower 6 (ofin 4)) 5).
  { change (powtower 6 (ofin 4)) with (opow (powtower 5 (ofin 4))). symmetry. apply HH_pow.
    apply nf_powtower, nf_ofin. }
  rewrite E1, (HH_lim _ 5 HX HXl).
  pose proof (HH_fs_shift _ HX HXl 4 1 5 ltac:(lia)) as H.
  replace (fs (powtower 6 (ofin 4)) 1) with (opow (powtower 5 (ofin 3))) in H by reflexivity.
  replace (1 + 4) with 5 in H by reflexivity. replace (5 + 4) with 9 in H by reflexivity.
  rewrite HH_pow in H by (apply nf_powtower, nf_ofin).
  assert (Hl3 : okind (powtower 5 (ofin 3)) = KLim) by reflexivity.
  pose proof (FGH_lim_plus (powtower 5 (ofin 3)) 6 3 (nf_powtower _ _ (nf_ofin 3)) Hl3 ltac:(lia)) as H2.
  replace (6 + 3) with 9 in H2 by reflexivity.
  lia.
Qed.

(** sigma(BB34) > sigma(BB33) + 1: every halting run of BB33 from the blank tape leaves at least 3 fewer
    ones than BB34's halting run. *)
Theorem BB34_beats_BB33 : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  forall NB, BB33_upper.halts_with NB -> NB + 3 <= N.
Proof.
  destruct hardy_score as (c & N & H1 & H2 & H3 & H4). exists c, N.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros NB HB. pose proof (BB33_upper.halts_with_upper NB HB) as H5. pose proof cmp_33_34 as H6. lia.
Qed.

Print Assumptions cmp_33_34.
Print Assumptions BB34_beats_BB33.
