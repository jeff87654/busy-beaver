(** * ProgCodesPA: the code constructors as the program's subroutines build them (the four-tag base:
    wim = 4P+0, wel = 4P+1, wal = 4P+2, weq = 4P+3; F = 1), re-exporting the logic layer's coding. *)
From Coq Require Import Arith Lia.
From PAGB Require Export PA_Pair PA_Codes.

Definition wel (a b : nat) : nat := 4 * P a b + 1.
Definition wex (x a : nat) : nat := wn (wal x (wn a)).
Definition wa (a b : nat) : nat := wn (wim a (wn b)).

Lemma tri_S n : tri (S n) = S n + tri n.
Proof. reflexivity. Qed.
