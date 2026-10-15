(** * Closed indexed PA238 register excursions.

    These statements instantiate the accepted split-file proofs at physical
    register indices. Every old block is retained, including arbitrary spare
    values. A positive decrement constructs one additional zero spare block.
    The exits and selector gates are the literal PA238 states. *)

From Coq Require Import Lists.List Arith.Arith Lia.
From P238.tm Require Import Table238 Finite238 Symbolic238 Box238
  Increment238 Decrement238 PositiveDecrement238 RegisterTape238.
Local Unset Implicit Arguments.
Import ListNotations.

Definition indexed_exit238 (zero nonzero r : nat) : nat :=
  if Nat.eqb r 0 then zero else nonzero.

Lemma reverse_prefix_exit238 (pre : list nat) zero nonzero :
  (match rev pre with [] => zero | _ => nonzero end) =
  indexed_exit238 zero nonzero (length pre).
Proof.
  destruct pre as [|v pre]; [reflexivity|].
  unfold indexed_exit238. cbn [length Nat.eqb].
  destruct (rev (v :: pre)) as [|u tail] eqn:E; [|reflexivity].
  pose proof (f_equal (@length nat) E) as H.
  rewrite rev_length in H. cbn [length] in H. lia.
Qed.

Lemma indexed_mark_exit238 pre :
  marked_return238 (rev pre) = indexed_exit238 2 8 (length pre).
Proof. unfold marked_return238. apply reverse_prefix_exit238. Qed.

Lemma indexed_zero_exit238 pre :
  zero_decrement_return238 (rev pre) = indexed_exit238 3 7 (length pre).
Proof. unfold zero_decrement_return238. apply reverse_prefix_exit238. Qed.

Lemma indexed_positive_exit238 pre :
  positive_decrement_return238 (rev pre) = indexed_exit238 15 11 (length pre).
Proof. unfold positive_decrement_return238. apply reverse_prefix_exit238. Qed.

Definition selector_index238 (q : nat) : option nat :=
  if Nat.eqb q 119 then Some 0 else
  if Nat.eqb q 100 then Some 1 else
  if Nat.eqb q 80 then Some 2 else
  if Nat.eqb q 75 then Some 3 else
  if Nat.eqb q 60 then Some 4 else
  if Nat.eqb q 71 then Some 5 else
  if Nat.eqb q 52 then Some 6 else
  if Nat.eqb q 126 then Some 7 else
  if Nat.eqb q 147 then Some 8 else None.

Lemma selector_index238_exact q r : selector_index238 q = Some r ->
  q = selector238 r /\ r < 9.
Proof.
  intro H. unfold selector_index238 in H.
  destruct (Nat.eqb q 119) eqn:E;
    [apply Nat.eqb_eq in E; subst q; injection H as <-;
     split; [reflexivity|lia] | clear E].
  destruct (Nat.eqb q 100) eqn:E;
    [apply Nat.eqb_eq in E; subst q; injection H as <-;
     split; [reflexivity|lia] | clear E].
  destruct (Nat.eqb q 80) eqn:E;
    [apply Nat.eqb_eq in E; subst q; injection H as <-;
     split; [reflexivity|lia] | clear E].
  destruct (Nat.eqb q 75) eqn:E;
    [apply Nat.eqb_eq in E; subst q; injection H as <-;
     split; [reflexivity|lia] | clear E].
  destruct (Nat.eqb q 60) eqn:E;
    [apply Nat.eqb_eq in E; subst q; injection H as <-;
     split; [reflexivity|lia] | clear E].
  destruct (Nat.eqb q 71) eqn:E;
    [apply Nat.eqb_eq in E; subst q; injection H as <-;
     split; [reflexivity|lia] | clear E].
  destruct (Nat.eqb q 52) eqn:E;
    [apply Nat.eqb_eq in E; subst q; injection H as <-;
     split; [reflexivity|lia] | clear E].
  destruct (Nat.eqb q 126) eqn:E;
    [apply Nat.eqb_eq in E; subst q; injection H as <-;
     split; [reflexivity|lia] | clear E].
  destruct (Nat.eqb q 147) eqn:E;
    [apply Nat.eqb_eq in E; subst q; injection H as <-;
     split; [reflexivity|lia] | clear E].
  discriminate.
Qed.

Theorem indexed_mark238 q r l vs :
  selector_index238 q = Some r -> 9 <= length vs ->
  exists n, exact_steps (S n)
    (denote (FC q l (register_file238 vs)))
    (left_view (indexed_exit238 2 8 r) l (marked_file238 r vs)).
Proof.
  intros G V. destruct (selector_index238_exact q r G) as [-> B].
  assert (R : r < length vs) by lia.
  destruct (register238_split vs r R) as [pre [v [rest [E L]]]].
  subst vs r. rewrite marked_file238_split, <- indexed_mark_exit238.
  exists (register_span238 pre + 2 + register_span238 (rev pre)).
  replace (S (register_span238 pre + 2 + register_span238 (rev pre))) with
    (register_span238 pre + (3 + register_span238 (rev pre))) by lia.
  apply selector238_marks_register. exact B.
Qed.

Theorem indexed_increment238 r l vs :
  r < 9 -> 9 <= length vs ->
  exists n, exact_steps (S n)
    (denote (FC 99 l (marked_file238 r vs)))
    (left_view 11 l (register_file238 (update_register238 r S vs))).
Proof.
  intros B V. assert (R : r < length vs) by lia.
  destruct (register238_split vs r R) as [pre [v [rest [E L]]]].
  subst vs r. rewrite marked_file238_split, update_register238_split.
  destruct (box_increment238 pre v rest l) as [n H]. exists (S n). exact H.
Qed.

Theorem indexed_decrement_zero238 r l vs :
  r < 9 -> 9 <= length vs -> nth r vs 0 = 0 ->
  exists n, exact_steps (S n)
    (denote (FC 78 l (marked_file238 r vs)))
    (left_view (indexed_exit238 3 7 r) l (register_file238 vs)).
Proof.
  intros B V Z. assert (R : r < length vs) by lia.
  destruct (register238_split vs r R) as [pre [v [rest [E L]]]].
  subst vs r. rewrite register238_value_split in Z. subst v.
  rewrite marked_file238_split, <- indexed_zero_exit238. cbn [repeat app].
  exists (register_span238 pre + 4 + register_span238 (rev pre)).
  replace (S (register_span238 pre + 4 + register_span238 (rev pre))) with
    (register_span238 pre + (5 + register_span238 (rev pre))) by lia.
  apply box_decrement_zero238.
Qed.

Theorem indexed_decrement_positive238 r l vs :
  r < 9 -> 9 <= length vs -> nth r vs 0 <> 0 ->
  exists n, exact_steps (S n)
    (denote (FC 78 l (marked_file238 r vs)))
    (left_view (indexed_exit238 15 11 r) l
      (register_file238 (update_register238 r Nat.pred vs ++ [0]))).
Proof.
  intros B V Z. assert (R : r < length vs) by lia.
  destruct (register238_split vs r R) as [pre [v [rest [E L]]]].
  subst vs r. rewrite register238_value_split in Z.
  destruct v as [|v]; [contradiction|].
  rewrite marked_file238_split, update_register238_split, <- indexed_positive_exit238.
  cbn [Nat.pred]. rewrite <- app_assoc. apply box_decrement_positive238.
Qed.
