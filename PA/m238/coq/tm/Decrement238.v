(** * Original PA238 zero decrement excursion.

    State 78 locates the erased first one of the selected block. If that
    register is zero, states 117/0 restore the erased bit and states 3/4/7
    return across the earlier blocks. Every step uses the literal PA238
    table. Positive decrement is a separate obligation. *)

From Coq Require Import Lists.List Arith.Arith Lia.
From P238.tm Require Import Table238 Finite238 Symbolic238 Box238 Increment238.
Local Unset Implicit Arguments.
Import ListNotations.

Lemma decrement_cross_one238 v l r :
  exact_steps (S (S v))
    (denote (FC 78 l (false :: true :: repeat true v ++ r)))
    (denote (FC 78 (repeat true (S v) ++ false :: l) r)).
Proof.
  eapply exact_next with (d := denote (FC 98 (false :: l) (true :: repeat true v ++ r))).
  - apply literal_cell_right. reflexivity.
  - eapply exact_next with (d := denote (FC 78 (true :: false :: l) (repeat true v ++ r))).
    + apply literal_cell_right. reflexivity.
    + cbn [repeat app]. rewrite <- repeat_before_cell. apply literal_run_right. reflexivity.
Qed.

Lemma decrement_cross_prefix238 pre l r :
  exact_steps (register_span238 pre)
    (denote (FC 78 l (register_file238 pre ++ r)))
    (denote (FC 78 (rev (register_file238 pre) ++ l) r)).
Proof.
  revert l. induction pre as [|v pre IH]; intro l.
  - cbn [register_span238 register_file238]. apply exact_zero.
  - cbn [register_span238].
    change (register_file238 (v :: pre)) with
      (false :: true :: repeat true v ++ register_file238 pre) at 1.
    cbn [app]. rewrite <- app_assoc.
    eapply (exact_append (S (S v)) (register_span238 pre)) with
      (d := denote (FC 78 (repeat true (S v) ++ false :: l)
               (register_file238 pre ++ r))).
    + apply decrement_cross_one238.
    + rewrite reverse_register_cons238. apply IH.
Qed.

Definition zero_decrement_return238 (reversed_prefix : list nat) : nat :=
  match reversed_prefix with [] => 3 | _ => 7 end.

Lemma decrement_zero_restores238 l r :
  exact_steps 5 (denote (FC 78 l (false :: false :: false :: r)))
    (left_view 3 l (false :: true :: false :: r)).
Proof.
  eapply exact_next with (d := denote (FC 98 (false :: l) (false :: false :: r))).
  - apply literal_cell_right. reflexivity.
  - eapply exact_next with (d := denote (FC 117 (false :: false :: l) (false :: r))).
    + apply literal_cell_right. reflexivity.
    + eapply exact_next with (d := left_view 0 (false :: false :: l) (false :: r)).
      * apply literal_cell_left. reflexivity.
      * rewrite left_view_cons.
        eapply exact_next with (d := left_view 1 (false :: l) (true :: false :: r)).
        -- apply literal_cell_left. reflexivity.
        -- rewrite left_view_cons.
           eapply exact_next; [apply literal_cell_left; reflexivity|apply exact_zero].
Qed.

Lemma decrement_zero_returns238 vs l r :
  exact_steps (register_span238 vs)
    (left_view 3 (register_left_file238 vs ++ l) r)
    (left_view (zero_decrement_return238 vs) l (register_file238 (rev vs) ++ r)).
Proof.
  destruct vs as [|v vs].
  - cbn [register_span238 register_left_file238 register_file238 zero_decrement_return238].
    apply exact_zero.
  - cbn [zero_decrement_return238].
    apply (register_return_started238 4 7 3 (v :: vs));
      first [discriminate|reflexivity].
Qed.

(** The third cell of a marked zero register is its following separator. This
    premise also permits the last encoded block by explicit blank completion. *)
Lemma decrement_zero_suffix238 pre r l :
  exact_steps (register_span238 pre + (5 + register_span238 (rev pre)))
    (denote (FC 78 l
       (register_file238 pre ++ false :: false :: false :: r)))
    (left_view (zero_decrement_return238 (rev pre)) l
       (register_file238 pre ++ false :: true :: false :: r)).
Proof.
  eapply (exact_append (register_span238 pre) (5 + register_span238 (rev pre))) with
    (d := denote (FC 78 (rev (register_file238 pre) ++ l)
              (false :: false :: false :: r))).
  - apply decrement_cross_prefix238.
  - eapply (exact_append 5 (register_span238 (rev pre))) with
      (d := left_view 3 (rev (register_file238 pre) ++ l)
              (false :: true :: false :: r)).
    + apply decrement_zero_restores238.
    + rewrite reverse_register_file238.
      pose proof (decrement_zero_returns238 (rev pre) l
        (false :: true :: false :: r)) as R.
      rewrite rev_involutive in R. exact R.
Qed.

Lemma decrement_zero_tail238 pre rest l :
  exact_steps (register_span238 pre + (5 + register_span238 (rev pre)))
    (denote (FC 78 l
       (register_file238 pre ++ false :: false :: false :: register_file238 rest)))
    (left_view (zero_decrement_return238 (rev pre)) l
       (register_file238 pre ++ false :: true :: false :: register_file238 rest)).
Proof. exact (decrement_zero_suffix238 pre (register_file238 rest) l). Qed.



Theorem box_decrement_zero238 pre rest l :
  exact_steps (register_span238 pre + (5 + register_span238 (rev pre)))
    (denote (FC 78 l (register_file238 pre ++ false :: false :: register_file238 rest)))
    (left_view (zero_decrement_return238 (rev pre)) l
       (register_file238 (pre ++ 0 :: rest))).
Proof.
  destruct rest as [|v rest].
  - cbn [register_file238 flat_map]. rewrite register_file238_app.
    cbn [register_file238 flat_map repeat].
    rewrite <- (right_padding238 78 l (register_file238 pre ++ [false; false])).
    rewrite ?app_nil_r.
    rewrite <- (left_padding_right238 (zero_decrement_return238 (rev pre)) l
                 (register_file238 pre ++ [false; true])).
    rewrite <- !app_assoc. cbn [app]. exact (decrement_zero_tail238 pre [] l).
  - rewrite register_file238_app.
    change (register_file238 (v :: rest)) with
      (false :: true :: repeat true v ++ register_file238 rest).
    cbn [register_file238 flat_map repeat app].
    exact (decrement_zero_suffix238 pre (true :: repeat true v ++ register_file238 rest) l).
Qed.
