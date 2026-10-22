(** * C7Count.v : the counter loop after phase D and its end, down to the cascade start (BB9/verify_c7).

    Counter state: Kx (1^N ++ [6R+7; C]) 1 2 t eD (a digit 2R+2 at depth N, then the counter token C).
    One round: clear the digit (CDPx, R -> U (S N) R), then the champion borrow R3 (C -> C-3, deposit 6R'+7).
    End: C = 3 -> r30 (3 -> 0), clear, e2, clear, e3, clear -> Kx (1^N; 1; 3R+2; t; blank). *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From XDev Require Import Base G_rules Abs KStep C7Phases.
Opaque U arrow.
Local Open Scope nat_scope.

Lemma good_eD : good eD.
Proof. left. eexists. reflexivity. Qed.

Lemma good_eE : good eE.
Proof. right. eexists. reflexivity. Qed.

Lemma good_blank : good (const S0).
Proof. right. exists (const S0). rewrite const_unfold at 1. rewrite const_unfold at 1. reflexivity. Qed.

Lemma good_lftx0 : forall e, good (lftx [0] e).
Proof. intros. left. eexists. reflexivity. Qed.

(** clearing the digit d at depth N (any good far end, any suffix of fixed tokens) *)
Lemma clear_dig : forall N d suf t e, good e ->
  Kx (repeat 1 N ++ tokd d :: suf) 1 2 t e -->* Kx (repeat 1 (S N) ++ suf) 1 (3 * iter d (U N) O + 2) t e.
Proof.
  intros N d suf t e He.
  pose proof (CDPx N d [] suf O t e He) as H. unfold Kgx in H. rewrite !map_rep in H. cbn [map] in H.
  rewrite !app_nil_r, <- app_assoc in H. cbn [app] in H. exact H.
Qed.

Lemma tokd_6 : forall R, tokd (2 * R + 2) = 6 * R + 7.
Proof. intros. unfold tokd. lia. Qed.

Lemma count_round : forall N R x t, 1 <= N ->
  Kx (repeat 1 N ++ [6 * R + 7; 3 + S x]) 1 2 t eD -->+ Kx (repeat 1 N ++ [6 * U (S N) R + 7; S x]) 1 2 t eD.
Proof.
  intros N R x t HN. rewrite <- (tokd_6 R).
  eapply evstep_progress_trans; [apply (clear_dig N (2 * R + 2) [3 + S x] t eD good_eD) |].
  rewrite <- U_S.
  pose proof (Kx_R3 N (S x) [] (3 * U (S N) R + 2) t eD ltac:(lia) ltac:(lia) good_eD) as H.
  replace (2 * (3 * U (S N) R + 2) + 3) with (6 * U (S N) R + 7) in H by lia. exact H.
Qed.

Lemma count_loop : forall i N R t, 1 <= N ->
  Kx (repeat 1 N ++ [6 * R + 7; 3 + 3 * i]) 1 2 t eD -->* Kx (repeat 1 N ++ [6 * iter i (U (S N)) R + 7; 3]) 1 2 t eD.
Proof.
  induction i as [| i IH]; intros N R t HN.
  - replace (3 + 3 * 0) with 3 by lia. apply evstep_refl.
  - replace (3 + 3 * S i) with (3 + S (2 + 3 * i)) by lia.
    eapply evstep_trans; [apply progress_evstep, count_round, HN |].
    replace (S (2 + 3 * i)) with (3 + 3 * i) by lia. rewrite iter_S'. apply IH, HN.
Qed.

Lemma iter_U_pos : forall v j x, 1 <= v -> 1 <= iter v (U j) x.
Proof. intros [| v] j x Hv; [lia |]. cbn [iter]. apply U_pos. Qed.

(** The end of the counter: from C = 3 down to the cascade start, with far end blank.
    R1' = U (S N) R (clear), R2' = U (S N) R1' (r30 deposit 6R1'+7, clear), R3' = iter (2R2'+1) (U N) 0 (e2 deposit
    6R2'+4, clear), R4' = iter (2R3'+3) (U (N-1)) 0 (e3 deposit 6R3'+10 one level shallower, clear). *)
Definition cend (N R : nat) : nat :=
  iter (2 * iter (2 * U (S N) (U (S N) R) + 1) (U N) 0 + 3) (U (N - 1)) 0.

Lemma count_end : forall N R t, 6 <= N ->
  Kx (repeat 1 N ++ [6 * R + 7; 3]) 1 2 t eD -->+ Kx (repeat 1 N) 1 (3 * cend N R + 2) t (const S0).
Proof.
  intros N R t HN. unfold cend. rewrite <- (tokd_6 R).
  eapply evstep_progress_trans; [apply (clear_dig N (2 * R + 2) [3] t eD good_eD) |].
  rewrite <- U_S.
  eapply progress_evstep_trans; [apply (r30 (U (S N) R) N t (U_pos _ _) ltac:(lia)) |].
  rewrite <- (tokd_6 (U (S N) R)).
  eapply evstep_trans; [apply (clear_dig N _ [0] t eD good_eD) |].
  rewrite <- U_S.
  assert (Ef : Kx (repeat 1 (S N) ++ [0]) 1 (3 * U (S N) (U (S N) R) + 2) t eD =
               Kx (repeat 1 (S N)) 1 (3 * U (S N) (U (S N) R) + 2) t (lftx [0] eD)).
  { unfold Kx. rewrite lftx_app. reflexivity. }
  rewrite Ef.
  eapply evstep_trans; [apply progress_evstep, (e2 (U (S N) (U (S N) R)) (S N) t (U_pos _ _) ltac:(lia)) |].
  replace (S N - 1) with N by lia.
  replace (6 * U (S N) (U (S N) R) + 4) with (tokd (2 * U (S N) (U (S N) R) + 1)) by (unfold tokd; lia).
  eapply evstep_trans; [apply (clear_dig N _ [] t eE good_eE) |].
  rewrite app_nil_r.
  eapply evstep_trans; [apply progress_evstep, (e3 _ (S N) t (iter_U_pos (2 * U (S N) (U (S N) R) + 1) N 0 ltac:(lia)) ltac:(lia)) |].
  replace (S N - 2) with (N - 1) by lia.
  replace (6 * iter (2 * U (S N) (U (S N) R) + 1) (U N) 0 + 10) with
          (tokd (2 * iter (2 * U (S N) (U (S N) R) + 1) (U N) 0 + 3)) by (unfold tokd; lia).
  eapply evstep_trans; [apply (clear_dig (N - 1) _ [] t (const S0) good_blank) |].
  rewrite app_nil_r. replace (S (N - 1)) with N by lia. apply evstep_refl.
Qed.
