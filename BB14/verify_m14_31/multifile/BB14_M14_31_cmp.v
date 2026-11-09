(** Comparison of M14_31 (BB14_M14_31.v) with the previous BB(14) entry M14d_18.
    M14d_18's proved bounds (BB14/verify_m14d, BB14_M14d_18.v) are
      sigma_bound      : n > iter 18 f_omega2 (iter 2 f_omega 3)
      sigma_bound_fw1  : n > iter 17 f_omega2 (iter 2 f_omega1 3)
    with iter, f, f_omega, f_omega1, f_omega2 defined exactly as in BB14_M14_31.v (the same text).
    M14_31's halting tape holds more ones than either bound. *)

From BB8 Require Import Individual142.
From BB8 Require Import BB14_M14_31.
From Coq Require Import Lia PeanoNat.

Theorem beats_M14d_18 :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ n > iter 18 f_omega2 (iter 2 f_omega 3).
Proof.
  destruct sigma_bound as (c & n & H1 & H2 & H3 & H4).
  exists c, n. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  assert (iter 18 f_omega2 (iter 2 f_omega 3) <= iter 31 f_omega2 (iter 2 f_omega 3))
    by (apply iter_mono_n; [apply f_omega2_id | lia]).
  lia.
Qed.

Theorem beats_M14d_18_fw1 :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\ n > iter 17 f_omega2 (iter 2 f_omega1 3).
Proof.
  destruct sigma_bound_fw1 as (c & n & H1 & H2 & H3 & H4).
  exists c, n. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  assert (iter 17 f_omega2 (iter 2 f_omega1 3) <= iter 30 f_omega2 (iter 2 f_omega1 3))
    by (apply iter_mono_n; [apply f_omega2_id | lia]).
  lia.
Qed.
