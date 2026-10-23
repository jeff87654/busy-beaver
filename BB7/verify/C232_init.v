From BB7 Require Import Individual72 C232_rules1 C232_rules2.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Lemma init_reach : c0 -->* Kc (repeat 1%nat 20) 1 2.
Proof.
  unfold c0, Kc.
  do 3775 step.
  apply evstep_refl'. reflexivity.
Qed.
