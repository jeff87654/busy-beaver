(** * Original PA238 positive decrement excursion.

    The literal states 10/6 find the file's right boundary. States 9/13 then
    shift cells left until the erased first one is restored. The returned
    file has the selected value decremented and one spare zero block added.
    All register values and contextual cells remain universally quantified. *)

From Coq Require Import Lists.List Arith.Arith Lia.
From P238.tm Require Import Table238 Finite238 Symbolic238 Box238 Increment238 Decrement238.
Local Unset Implicit Arguments.
Import ListNotations.

Lemma decrement_end_crosses238 pre l r :
  exact_steps (register_span238 pre)
    (denote (FC 10 l (register_file238 pre ++ r)))
    (denote (FC 10 (rev (register_file238 pre) ++ l) r)).
Proof.
  revert l. induction pre as [|v pre IH]; intro l.
  - cbn [register_span238 register_file238]. apply exact_zero.
  - cbn [register_span238].
    change (register_file238 (v :: pre)) with
      (false :: true :: repeat true v ++ register_file238 pre) at 1.
    cbn [app]. rewrite <- app_assoc.
    eapply exact_next with
      (d := denote (FC 6 (false :: l) (true :: repeat true v ++ (register_file238 pre ++ r)))).
    + apply literal_cell_right. reflexivity.
    + eapply exact_next with
        (d := denote (FC 10 (true :: false :: l) (repeat true v ++ (register_file238 pre ++ r)))).
      * apply literal_cell_right. reflexivity.
      * eapply (exact_append v (register_span238 pre)) with
          (d := denote (FC 10 (repeat true v ++ true :: false :: l) (register_file238 pre ++ r))).
        -- apply literal_run_right. reflexivity.
        -- rewrite reverse_register_cons238, repeat_before_cell. cbn [repeat app]. apply IH.
Qed.

Lemma decrement_finds_end238 rest a k :
  literal_reaches238 (denote (FC 10 k (repeat true a ++ register_file238 rest)))
    (left_view 9 (false :: rev (repeat true a ++ register_file238 rest) ++ k) []).
Proof.
  eapply reaches238_trans with
    (d := denote (FC 10 (repeat true a ++ k) (register_file238 rest))).
  - exists a. apply literal_run_right. reflexivity.
  - eapply reaches238_trans with
      (d := denote (FC 10 (rev (register_file238 rest) ++ repeat true a ++ k) [])).
    + exists (register_span238 rest).
      rewrite <- (app_nil_r (register_file238 rest)) at 1.
      apply decrement_end_crosses238.
    + rewrite right_view_nil.
      eapply reaches238_step with
        (d := denote (FC 6 (false :: rev (register_file238 rest) ++ repeat true a ++ k) [])).
      * apply literal_cell_right. reflexivity.
      * rewrite right_view_nil.
        eapply reaches238_step with
          (d := left_view 9 (false :: rev (register_file238 rest) ++ repeat true a ++ k) [false]).
        -- apply literal_cell_left. reflexivity.
        -- change (literal_reaches238
             (left_view 9 (false :: rev (register_file238 rest) ++ repeat true a ++ k) ([] ++ [false]))
             (left_view 9 (false :: rev (repeat true a ++ register_file238 rest) ++ k) [])).
           rewrite left_padding_right238, rev_app_distr, reverse_repeat_true.
           rewrite <- app_assoc. apply reaches238_refl.
Qed.

Lemma decrement_shifts_one238 v l r :
  exact_steps (S (S v))
    (left_view 9 (false :: repeat true (S v) ++ false :: l) r)
    (left_view 9 (false :: l) (repeat true v ++ false :: true :: r)).
Proof.
  rewrite left_view_cons.
  eapply exact_next with
    (d := left_view 13 (repeat true (S v) ++ false :: l) (true :: r)).
  - apply literal_cell_left. reflexivity.
  - cbn [repeat app]. rewrite left_view_cons.
    eapply exact_next with
      (d := left_view 9 (repeat true v ++ false :: l) (false :: true :: r)).
    + apply literal_cell_left. reflexivity.
    + apply literal_run_left. reflexivity.
Qed.

Definition shifted_tail238 (vs : list nat) (r : list bool) : list bool :=
  fold_left (fun tail v => repeat true v ++ false :: true :: tail) vs r.

Lemma decrement_shifts_blocks238 vs l r :
  literal_reaches238
    (left_view 9 (false :: register_left_file238 vs ++ l) r)
    (left_view 9 (false :: l) (shifted_tail238 vs r)).
Proof.
  revert r. induction vs as [|v vs IH]; intro r.
  - cbn [register_left_file238 shifted_tail238]. apply reaches238_refl.
  - cbn [register_left_file238 flat_map]. rewrite <- !app_assoc. cbn [app].
    eapply reaches238_trans with
      (d := left_view 9 (false :: register_left_file238 vs ++ l)
             (repeat true v ++ false :: true :: r)).
    + exists (S (S v)). apply decrement_shifts_one238.
    + change (shifted_tail238 (v :: vs) r) with
        (shifted_tail238 vs (repeat true v ++ false :: true :: r)). apply IH.
Qed.

Lemma shifted_tail_file238 vs r :
  false :: true :: shifted_tail238 (rev vs) r =
    register_file238 vs ++ false :: true :: r.
Proof.
  induction vs as [|v vs IH]; [reflexivity|].
  cbn [rev]. unfold shifted_tail238. rewrite fold_left_app. cbn [fold_left].
  fold (shifted_tail238 (rev vs) r).
  change (register_file238 (v :: vs)) with
    (false :: true :: repeat true v ++ register_file238 vs).
  cbn [app]. rewrite <- app_assoc. rewrite <- IH. reflexivity.
Qed.

Lemma decrement_left_shape238 rest a k :
  rev (repeat true a ++ register_file238 rest) ++ true :: false :: false :: k =
  register_left_file238 (rev rest) ++ repeat true (S a) ++ false :: false :: k.
Proof.
  rewrite rev_app_distr, reverse_repeat_true, reverse_register_file238.
  rewrite <- app_assoc, repeat_before_cell. reflexivity.
Qed.

Lemma decrement_positive_shift238 rest a k :
  literal_reaches238
    (denote (FC 10 (true :: false :: false :: k) (repeat true a ++ register_file238 rest)))
    (left_view 15 k (register_file238 (a :: rest ++ [0]))).
Proof.
  eapply reaches238_trans with
    (d := left_view 9
      (false :: register_left_file238 (rev rest) ++ repeat true (S a) ++ false :: false :: k) []).
  - pose proof (decrement_finds_end238 rest a (true :: false :: false :: k)) as E.
    rewrite decrement_left_shape238 in E. exact E.
  - eapply reaches238_trans with
      (d := left_view 9 (false :: repeat true (S a) ++ false :: false :: k)
             (shifted_tail238 (rev rest) [])).
    + exact (decrement_shifts_blocks238 (rev rest)
        (repeat true (S a) ++ false :: false :: k) []).
    + eapply reaches238_trans with
        (d := left_view 9 (false :: false :: k)
               (repeat true a ++ false :: true :: shifted_tail238 (rev rest) [])).
      * exists (S (S a)). apply decrement_shifts_one238.
      * rewrite left_view_cons.
        eapply reaches238_step with
          (d := left_view 13 (false :: k)
                 (true :: repeat true a ++ false :: true :: shifted_tail238 (rev rest) [])).
        -- apply literal_cell_left. reflexivity.
        -- rewrite left_view_cons.
           eapply reaches238_step with
             (d := left_view 15 k
                    (false :: true :: repeat true a ++ false :: true :: shifted_tail238 (rev rest) [])).
           ++ apply literal_cell_left. reflexivity.
           ++ rewrite shifted_tail_file238.
              change (register_file238 (a :: rest ++ [0])) with
                (false :: true :: repeat true a ++ register_file238 (rest ++ [0])).
              rewrite register_file238_app. cbn [register_file238 flat_map repeat app].
              rewrite <- ?app_assoc. apply reaches238_refl.
Qed.

Definition positive_decrement_return238 (vs : list nat) : nat :=
  match vs with [] => 15 | _ => 11 end.

Lemma decrement_positive_returns238 vs l r :
  exact_steps (register_span238 vs)
    (left_view 15 (register_left_file238 vs ++ l) r)
    (left_view (positive_decrement_return238 vs) l (register_file238 (rev vs) ++ r)).
Proof.
  destruct vs as [|v vs].
  - cbn [register_span238 register_left_file238 register_file238 positive_decrement_return238].
    apply exact_zero.
  - cbn [positive_decrement_return238].
    apply (register_return_started238 15 11 15 (v :: vs));
      first [discriminate|reflexivity].
Qed.

Theorem box_decrement_positive238 pre a rest l :
  exists n, exact_steps (S n)
    (denote (FC 78 l
       (register_file238 pre ++ false :: false :: repeat true (S a) ++ register_file238 rest)))
    (left_view (positive_decrement_return238 (rev pre)) l
       (register_file238 (pre ++ a :: rest ++ [0]))).
Proof.
  destruct (decrement_positive_shift238 rest a (rev (register_file238 pre) ++ l))
    as [nshift Shift].
  exists (register_span238 pre + 2 + nshift + register_span238 (rev pre)).
  replace (S (register_span238 pre + 2 + nshift + register_span238 (rev pre))) with
    (register_span238 pre + (3 + (nshift + register_span238 (rev pre)))) by lia.
  eapply (exact_append (register_span238 pre) (3 + (nshift + register_span238 (rev pre)))) with
    (d := denote (FC 78 (rev (register_file238 pre) ++ l)
              (false :: false :: repeat true (S a) ++ register_file238 rest))).
  - apply decrement_cross_prefix238.
  - eapply (exact_append 3 (nshift + register_span238 (rev pre))) with
      (d := denote (FC 10 (true :: false :: false :: rev (register_file238 pre) ++ l)
                (repeat true a ++ register_file238 rest))).
    + cbn [repeat app].
      eapply exact_next with
        (d := denote (FC 98 (false :: rev (register_file238 pre) ++ l)
                  (false :: true :: repeat true a ++ register_file238 rest))).
      * apply literal_cell_right. reflexivity.
      * eapply exact_next with
          (d := denote (FC 117 (false :: false :: rev (register_file238 pre) ++ l)
                    (true :: repeat true a ++ register_file238 rest))).
        -- apply literal_cell_right. reflexivity.
        -- eapply exact_next; [apply literal_cell_right; reflexivity|apply exact_zero].
    + eapply (exact_append nshift (register_span238 (rev pre))) with
        (d := left_view 15 (rev (register_file238 pre) ++ l)
                (register_file238 (a :: rest ++ [0]))).
      * exact Shift.
      * rewrite reverse_register_file238, register_file238_app.
        pose proof (decrement_positive_returns238 (rev pre) l
          (register_file238 (a :: rest ++ [0]))) as R.
        rewrite rev_involutive in R. exact R.
Qed.
