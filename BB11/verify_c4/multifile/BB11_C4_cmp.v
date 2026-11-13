(** Comparison of C4 (BB11_C4.v, BB11_C4_bound.v) with the EXACT score of the previous BB(11) entry M11b.

    M11b (BB11/verify, files BB11_M11b.v, BB11_M11b_fgh.v, BB11_M11b_upper.v, byte-identical copies here) proves
      BB11_M11b_upper.sigma_bracket_m11 :
        exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
        f_omega1 (f_omega (f_omega 5)) < N /\ N + 1 < f_omega1 (f_omega (f_omega 6))
    where N is the number of ones on M11b's (unique) halting tape and sigma(M11b) = N + 1.
    BB11_C4_bound.beats_M11b proves that C4's halting tape holds more than f_omega1 (f_omega (f_omega 6)) ones.
    The two files define iter, f, f_omega, f_omega1 with the same text; the equalities below are proved for
    variables (no closed term of the hierarchy is ever computed), and the theorem joins the two statements:
    M11b's halting tape holds NM ones, C4's holds n ones, and NM + 1 < n, so sigma(M11b) = NM + 1 < n < n + 1 = sigma(C4). *)

From BB8 Require Import Individual112.
From BB8 Require BB11_M11b BB11_M11b_fgh BB11_M11b_upper.
From BB8 Require Import BB11_C4 BB11_C4_bound.
From Coq Require Import Lia PeanoNat.

Lemma cmp_iter_M : forall (X : Type) n (g : X -> X) x, BB11_M11b.iter n g x = iter n g x.
Proof.
  intros X n g x. induction n as [| n IH]; cbn [BB11_M11b.iter iter]; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma cmp_iter_ext : forall (g h : nat -> nat), (forall y, g y = h y) -> forall n x, iter n g x = iter n h x.
Proof.
  intros g h Hgh n x. induction n as [| n IH]; cbn [iter]; [reflexivity |].
  rewrite IH. apply Hgh.
Qed.

Transparent BB11_M11b_fgh.f BB11_M11b_fgh.f_omega BB11_M11b_fgh.f_omega1 f f_omega f_omega1.

Lemma cmp_f_M : forall k n, BB11_M11b_fgh.f k n = f k n.
Proof.
  induction k as [| k IH]; intros n; [reflexivity |].
  change (BB11_M11b_fgh.f (S k) n) with (BB11_M11b.iter n (BB11_M11b_fgh.f k) n).
  change (f (S k) n) with (iter n (f k) n).
  rewrite cmp_iter_M. apply cmp_iter_ext. exact IH.
Qed.

Lemma cmp_fw_M : forall n, BB11_M11b_fgh.f_omega n = f_omega n.
Proof.
  intros n. change (BB11_M11b_fgh.f_omega n) with (BB11_M11b_fgh.f n n).
  change (f_omega n) with (f n n). apply cmp_f_M.
Qed.

Lemma cmp_fw1_M : forall n, BB11_M11b_fgh.f_omega1 n = f_omega1 n.
Proof.
  intros n. change (BB11_M11b_fgh.f_omega1 n) with (BB11_M11b.iter n BB11_M11b_fgh.f_omega n).
  change (f_omega1 n) with (iter n f_omega n).
  rewrite cmp_iter_M. apply cmp_iter_ext. exact cmp_fw_M.
Qed.

Opaque BB11_M11b_fgh.f BB11_M11b_fgh.f_omega BB11_M11b_fgh.f_omega1 f f_omega f_omega1.

(** M11b's upper bound, restated with C4's definitions; every rewrite has an explicit instance (no evar). *)
Lemma cmp_M11b_upper :
  exists c N, c0 -[ BB11_M11b.tm ]->* c /\ halted BB11_M11b.tm c /\ BB11_M11b_fgh.ones c N /\
  N + 1 < f_omega1 (f_omega (f_omega 6)).
Proof.
  destruct BB11_M11b_upper.sigma_bracket_m11 as (c & N & H1 & H2 & H3 & _ & H5).
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  rewrite (cmp_fw1_M (BB11_M11b_fgh.f_omega (BB11_M11b_fgh.f_omega 6))) in H5.
  rewrite (cmp_fw_M (BB11_M11b_fgh.f_omega 6)) in H5.
  rewrite (cmp_fw_M 6) in H5.
  exact H5.
Qed.

Theorem beats_M11b_score :
  exists NM,
    (exists c, c0 -[ BB11_M11b.tm ]->* c /\ halted BB11_M11b.tm c /\ BB11_M11b_fgh.ones c NM) /\
    (exists c n, c0 -[ tm ]->* c /\ halted tm c /\ ones c n /\ NM + 1 < n).
Proof.
  destruct cmp_M11b_upper as (c & N & H1 & H2 & H3 & H4).
  destruct beats_M11b as (c' & n & H1' & H2' & H3' & H4').
  exists N. split.
  - exists c. split; [exact H1 |]. split; [exact H2 | exact H3].
  - exists c', n. split; [exact H1' |]. split; [exact H2' |]. split; [exact H3' |].
    revert H4 H4'. generalize (f_omega1 (f_omega (f_omega 6))). intros x Ha Hb. lia.
Qed.

Print Assumptions beats_M11b_score.
