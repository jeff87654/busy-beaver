(** * BB32_vs_BB31: Argon's 32-state hydra machine (BB32) beats the published BB(31) machine + 1.

    Depends on: the published BB31 files (busy-beaver BB31/verify/multifile, unchanged: BB312, Individual312,
    BB31_tm, BB31_rules, Ord, Hardy, HydraOrd, BB31_scan, BB31_round, BB31_game, BB31_halt), the verified
    BB32 files (argon_scout/H32: BB322, Individual322, BB32_tm, BB32_rules, BB32_scan, BB32_round, BB32_game,
    BB32_halt, BB32_bound) and the new HydraUpper.v, BB31_upper.v.

    BB32_bound.hardy_score : BB32 halts with N ones, f_(a32)(4) <= N + 2, a32 = omega^omega^(omega^8 * 3).
    BB31_upper.halts_with_upper : if BB31 halts with NB ones, NB + 2 <= f_(omega^omega^omega^4)(6).
    Here (cmp_31_32): f_(omega^omega^omega^4)(6) + 6 <= f_(a32)(4), hence NB + 6 <= N.  Both machines halt in
    state B reading 0 (B0 undefined): the same sigma convention for both, sigma(BB32) > sigma(BB31) + 1. *)

From BB8 Require Import Ord Hardy HydraOrd HydraUpper.
From BB8 Require BB31_upper.
From BB8 Require Import BB32_tm BB32_game BB32_bound.
From Coq Require Import Lia.
Set Default Goal Selector "!".

(** omega^omega^(omega^8 * 3) descends to omega^omega^omega^5 by 1-steps (a closed computation). *)
Lemma desc_a : desc 1 (powtower 3 (orep (ofin 8) 3 oz)) (powtower 4 (ofin 5)).
Proof.
  vm_compute.
  repeat (first [ apply desc_refl | apply desc_step; [discriminate | vm_compute] ]).
Qed.

Lemma cmp_31_32 : FGH (powtower 3 (ofin 4)) 6 + 6 <= FGH a32 4.
Proof.
  assert (Ha : nf (powtower 3 (orep (ofin 8) 3 oz))) by prove_nf.
  assert (E1 : FGH a32 4 = HH (powtower 3 (orep (ofin 8) 3 oz)) 4).
  { change (powtower 3 (orep (ofin 8) 3 oz)) with (opow a32). symmetry. apply HH_pow. prove_nf. }
  rewrite E1.
  pose proof (HH_desc_le 1 _ _ 4 Ha desc_a ltac:(lia) ltac:(lia)) as H1.
  assert (HX : nf (powtower 4 (ofin 5))) by (apply nf_powtower, nf_ofin).
  assert (HXl : okind (powtower 4 (ofin 5)) = KLim) by reflexivity.
  rewrite (HH_lim _ 4 HX HXl) in H1.
  pose proof (HH_fs_shift _ HX HXl 3 1 4 ltac:(lia)) as H2.
  replace (fs (powtower 4 (ofin 5)) 1) with (opow (powtower 3 (ofin 4))) in H2 by reflexivity.
  replace (1 + 3) with 4 in H2 by reflexivity. replace (4 + 3) with 7 in H2 by reflexivity.
  rewrite HH_pow in H2 by (apply nf_powtower, nf_ofin).
  assert (Hl : okind (powtower 3 (ofin 4)) = KLim) by reflexivity.
  pose proof (FGH_lim_step (powtower 3 (ofin 4)) 6 (nf_powtower _ _ (nf_ofin 4)) Hl ltac:(lia)) as H3.
  lia.
Qed.

(** sigma(BB32) > sigma(BB31) + 1. *)
Theorem BB32_beats_BB31 : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  forall NB, BB31_upper.halts_with NB -> NB + 6 <= N.
Proof.
  destruct hardy_score as (c & N & H1 & H2 & H3 & H4). exists c, N.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros NB HB. pose proof (BB31_upper.halts_with_upper NB HB) as H5. pose proof cmp_31_32 as H6. lia.
Qed.

Print Assumptions cmp_31_32.
Print Assumptions BB32_beats_BB31.
