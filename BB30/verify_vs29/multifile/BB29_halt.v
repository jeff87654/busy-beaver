(** * BB29 halts from the blank tape.

    Structure: 175 literal TM steps reach C(1) = K(1,0,w0) with hydra root -> A -> B -> 4 leaves
    (marked node = the last leaf); the processing lemma [process] runs the hydra game to the
    empty hydra, C(W [4] 1, []); rule R3 halts (state B reads 0, B0 is undefined). *)

From BB8 Require Import BB29_tm BB29_rules BB29_scan BB29_round BB29_hydra.
From Coq Require Import List.
Import ListNotations.
Set Default Goal Selector "!".

(** The hydra word at TM step 175: O O (O C)^3 O X. *)
Definition w0 : list pr := [pO; pO] ++ leaf^^3 ++ [pO; pX].

Lemma w0_enc : Enc ([] ++ [[4]]) w0.
Proof. apply (Enc_L' [] [] 3 0). reflexivity. Qed.

(** TM steps 0..175 (literal execution). *)
Lemma init : c0 -->* Cf 1 w0.
Proof. unfold Cf, K, w0. simpl. execute. Qed.

Lemma reach_end : c0 -->* c_end (W [4] 1).
Proof.
  eapply evstep_trans; [apply init|].
  eapply evstep_trans; [apply (process [] [4] 1 w0 w0_enc)|].
  apply progress_evstep, R3.
Qed.

Theorem halt : halts tm c0.
Proof.
  apply halted_evstep_halts with (c' := c_end (W [4] 1)).
  - apply reach_end.
  - apply c_end_halted.
Qed.

Print Assumptions halt.
