(** * Original PA238 register increment excursion.

    State 99 crosses ordinary register blocks until the marked block. States
    137/149 shift its following cells right by one, and states 15/11 return.
    Every gate below is checked against the literal PA238 table. The proof
    preserves arbitrary earlier and later register values, including spares. *)

From Coq Require Import Lists.List Lists.Streams Arith.Arith Lia.
From BusyCoq Require Import TM.
From P238.tm Require Import Table238 Finite238 Symbolic238 Box238.
Local Unset Implicit Arguments.
Import ListNotations.

Definition literal_reaches238 (c d : literal_configuration) : Prop :=
  exists n, exact_steps n c d.

Lemma reaches238_refl c : literal_reaches238 c c.
Proof. exists 0. apply exact_zero. Qed.

Lemma reaches238_trans c d e :
  literal_reaches238 c d -> literal_reaches238 d e -> literal_reaches238 c e.
Proof.
  intros [n A] [m B]. exists (n + m). eapply exact_append; eassumption.
Qed.

Lemma reaches238_step c d e :
  literal_step c d -> literal_reaches238 d e -> literal_reaches238 c e.
Proof.
  intros A [n B]. exists (S n). eapply exact_next; eassumption.
Qed.

Lemma complete_trailing_blank238 cells :
  Str_app (cells ++ [false]) (const false) = Str_app cells (const false).
Proof.
  induction cells as [|b cells IH]; cbn [app Str_app].
  - symmetry. apply const_unfold.
  - rewrite IH. reflexivity.
Qed.

Lemma right_padding238 q l r :
  denote (FC q l (r ++ [false])) = denote (FC q l r).
Proof.
  unfold denote; cbn [control left_cells right_cells].
  rewrite complete_trailing_blank238. reflexivity.
Qed.

Lemma left_padding_right238 q l r :
  left_view q l (r ++ [false]) = left_view q l r.
Proof.
  unfold left_view.
  change (denote (FC q (List.tl l) ((List.hd false l :: r) ++ [false])) =
          denote (FC q (List.tl l) (List.hd false l :: r))).
  apply right_padding238.
Qed.

Lemma register_return_one238 qa qb q v l r :
  tmn238 q true = Some (true, L, qa) ->
  tmn238 qa true = Some (true, L, qa) ->
  tmn238 qa false = Some (false, L, qb) ->
  exact_steps (S (S v))
    (left_view q (repeat true (S v) ++ false :: l) r)
    (left_view qb l (false :: repeat true (S v) ++ r)).
Proof.
  intros T A B. cbn [repeat app]. rewrite left_view_cons.
  eapply exact_next with (d := left_view qa (repeat true v ++ false :: l) (true :: r)).
  - apply literal_cell_left. exact T.
  - replace (S v) with (v + 1) at 1 by lia.
    eapply (exact_append v 1) with
      (d := left_view qa (false :: l) (repeat true v ++ true :: r)).
    + apply literal_run_left. exact A.
    + rewrite left_view_cons.
      eapply exact_next with (d := left_view qb l (false :: repeat true v ++ true :: r)).
      * apply literal_cell_left. exact B.
      * rewrite repeat_before_cell. apply exact_zero.
Qed.

Lemma register_return_file238 qa qb vs l r :
  tmn238 qa true = Some (true, L, qa) ->
  tmn238 qa false = Some (false, L, qb) ->
  tmn238 qb true = Some (true, L, qa) ->
  exact_steps (register_span238 vs)
    (left_view qb (register_left_file238 vs ++ l) r)
    (left_view qb l (register_file238 (rev vs) ++ r)).
Proof.
  intros A B T. revert r. induction vs as [|v vs IH]; intro r.
  - cbn [register_span238 register_left_file238 register_file238]. apply exact_zero.
  - cbn [register_span238 register_left_file238 flat_map].
    rewrite <- !app_assoc. cbn [app].
    eapply (exact_append (S (S v)) (register_span238 vs)) with
      (d := left_view qb (register_left_file238 vs ++ l)
             (false :: repeat true (S v) ++ r)).
    + apply (register_return_one238 qa qb); assumption.
    + cbn [rev]. rewrite register_file238_app. cbn [register_file238 flat_map].
      rewrite <- !app_assoc. cbn [app]. rewrite ?app_nil_r. apply IH.
Qed.

Lemma register_return_started238 qa qb q vs l r :
  vs <> [] ->
  tmn238 q true = Some (true, L, qa) ->
  tmn238 qa true = Some (true, L, qa) ->
  tmn238 qa false = Some (false, L, qb) ->
  tmn238 qb true = Some (true, L, qa) ->
  exact_steps (register_span238 vs)
    (left_view q (register_left_file238 vs ++ l) r)
    (left_view qb l (register_file238 (rev vs) ++ r)).
Proof.
  intros N T A B C. destruct vs as [|v vs]; [contradiction|].
  cbn [register_span238 register_left_file238 flat_map].
  rewrite <- !app_assoc. cbn [app].
  eapply (exact_append (S (S v)) (register_span238 vs)) with
    (d := left_view qb (register_left_file238 vs ++ l)
           (false :: repeat true (S v) ++ r)).
  - apply (register_return_one238 qa qb); assumption.
  - cbn [rev]. rewrite register_file238_app. cbn [register_file238 flat_map].
    rewrite <- !app_assoc. cbn [app]. rewrite ?app_nil_r.
    apply (register_return_file238 qa qb); assumption.
Qed.

Lemma increment_cross_one238 v l r :
  exact_steps (S (S v))
    (denote (FC 99 l (false :: true :: repeat true v ++ r)))
    (denote (FC 99 (repeat true (S v) ++ false :: l) r)).
Proof.
  eapply exact_next with (d := denote (FC 118 (false :: l) (true :: repeat true v ++ r))).
  - apply literal_cell_right. reflexivity.
  - eapply exact_next with (d := denote (FC 99 (true :: false :: l) (repeat true v ++ r))).
    + apply literal_cell_right. reflexivity.
    + cbn [repeat app]. rewrite <- repeat_before_cell. apply literal_run_right. reflexivity.
Qed.

Lemma increment_cross_prefix238 pre l r :
  exact_steps (register_span238 pre)
    (denote (FC 99 l (register_file238 pre ++ r)))
    (denote (FC 99 (rev (register_file238 pre) ++ l) r)).
Proof.
  revert l. induction pre as [|v pre IH]; intro l.
  - cbn [register_span238 register_file238]. apply exact_zero.
  - cbn [register_span238].
    change (register_file238 (v :: pre)) with
      (false :: true :: repeat true v ++ register_file238 pre) at 1.
    cbn [app]. rewrite <- app_assoc.
    eapply (exact_append (S (S v)) (register_span238 pre)) with
      (d := denote (FC 99 (repeat true (S v) ++ false :: l)
               (register_file238 pre ++ r))).
    + apply increment_cross_one238.
    + rewrite reverse_register_cons238. apply IH.
Qed.

Lemma increment_shift238 rest a k :
  literal_reaches238
    (denote (FC 137 k (repeat true a ++ register_file238 rest)))
    (left_view 15 (rev (repeat true (S a) ++ register_file238 rest) ++ k) []).
Proof.
  revert a k. induction rest as [|v rest IH]; intros a k.
  - change (register_file238 []) with (@nil bool). rewrite !app_nil_r.
    eapply reaches238_trans with (d := denote (FC 137 (repeat true a ++ k) [])).
    + exists a.
      pose proof (literal_run_right 137 true true a k [] eq_refl) as Scan.
      rewrite ?app_nil_r in Scan. exact Scan.
    + rewrite right_view_nil.
      eapply reaches238_step with (d := denote (FC 149 (true :: repeat true a ++ k) [])).
      * apply literal_cell_right. reflexivity.
      * rewrite right_view_nil.
        eapply reaches238_step with (d := left_view 15 (true :: repeat true a ++ k) [false]).
        -- apply literal_cell_left. reflexivity.
        -- change (literal_reaches238
             (left_view 15 (true :: repeat true a ++ k) ([] ++ [false]))
             (left_view 15 (rev (repeat true (S a)) ++ k) [])).
           rewrite left_padding_right238, reverse_repeat_true. cbn [repeat app].
           apply reaches238_refl.
  - change (register_file238 (v :: rest)) with
      (false :: true :: repeat true v ++ register_file238 rest).
    eapply reaches238_trans with
      (d := denote (FC 137 (repeat true a ++ k)
               (false :: true :: repeat true v ++ register_file238 rest))).
    + exists a. apply literal_run_right. reflexivity.
    + eapply reaches238_step with
        (d := denote (FC 149 (true :: repeat true a ++ k)
                 (true :: repeat true v ++ register_file238 rest))).
      * apply literal_cell_right. reflexivity.
      * eapply reaches238_step with
          (d := denote (FC 137 (false :: true :: repeat true a ++ k)
                   (repeat true v ++ register_file238 rest))).
        -- apply literal_cell_right. reflexivity.
        -- replace (rev (repeat true (S a) ++
                     (false :: true :: repeat true v ++ register_file238 rest)) ++ k)
             with (rev (repeat true (S v) ++ register_file238 rest) ++
                     false :: true :: repeat true a ++ k).
           ++ apply IH.
           ++ change (false :: true :: repeat true v ++ register_file238 rest)
                with ((false :: repeat true (S v)) ++ register_file238 rest).
              rewrite !rev_app_distr. cbn [rev]. rewrite !reverse_repeat_true.
              cbn [repeat]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma increment_left_shape238 pre v rest l :
  rev (repeat true (S v) ++ register_file238 rest) ++
    true :: false :: rev (register_file238 pre) ++ l =
  rev (register_file238 (pre ++ S v :: rest)) ++ l.
Proof.
  rewrite register_file238_app.
  rewrite (rev_app_distr (register_file238 pre) (register_file238 (S v :: rest))).
  rewrite <- (app_assoc (rev (register_file238 (S v :: rest)))
                       (rev (register_file238 pre)) l).
  rewrite (reverse_register_cons238 (S v) rest (rev (register_file238 pre) ++ l)).
  rewrite (rev_app_distr (repeat true (S v)) (register_file238 rest)), reverse_repeat_true.
  rewrite <- !app_assoc, repeat_before_cell. reflexivity.
Qed.

Lemma increment_returns238 pre v rest l :
  exact_steps (register_span238 (rev (pre ++ S v :: rest)))
    (left_view 15 (rev (register_file238 (pre ++ S v :: rest)) ++ l) [])
    (left_view 11 l (register_file238 (pre ++ S v :: rest))).
Proof.
  rewrite reverse_register_file238.
  assert (N : rev (pre ++ S v :: rest) <> []).
  { intro E. pose proof (f_equal (@length nat) E) as H.
    rewrite rev_length, app_length in H. cbn [length] in H. lia. }
  pose proof (register_return_started238 15 11 15 (rev (pre ++ S v :: rest)) l []
    N eq_refl eq_refl eq_refl eq_refl) as R.
  rewrite rev_involutive in R. rewrite ?app_nil_r in R. exact R.
Qed.

(** This constructive excursion changes just the selected register. The two
    entry transitions ensure strict physical progress even when every value
    and every contextual run is zero. *)
Theorem box_increment238 pre v rest l :
  exists n, exact_steps (S (S n))
    (denote (FC 99 l
      (register_file238 pre ++ false :: false :: repeat true v ++ register_file238 rest)))
    (left_view 11 l (register_file238 (pre ++ S v :: rest))).
Proof.
  destruct (increment_shift238 rest v (true :: false :: rev (register_file238 pre) ++ l))
    as [nshift Shift].
  rewrite increment_left_shape238 in Shift.
  exists (register_span238 pre + nshift + register_span238 (rev (pre ++ S v :: rest))).
  replace (S (S (register_span238 pre + nshift +
             register_span238 (rev (pre ++ S v :: rest))))) with
    (register_span238 pre + (2 + (nshift + register_span238 (rev (pre ++ S v :: rest)))))
    by lia.
  eapply (exact_append (register_span238 pre)
            (2 + (nshift + register_span238 (rev (pre ++ S v :: rest))))) with
    (d := denote (FC 99 (rev (register_file238 pre) ++ l)
              (false :: false :: repeat true v ++ register_file238 rest))).
  - apply increment_cross_prefix238.
  - eapply (exact_append 2 (nshift + register_span238 (rev (pre ++ S v :: rest)))) with
      (d := denote (FC 137 (true :: false :: rev (register_file238 pre) ++ l)
                (repeat true v ++ register_file238 rest))).
    + eapply exact_next with
        (d := denote (FC 118 (false :: rev (register_file238 pre) ++ l)
                  (false :: repeat true v ++ register_file238 rest))).
      * apply literal_cell_right. reflexivity.
      * eapply exact_next; [apply literal_cell_right; reflexivity|apply exact_zero].
    + eapply (exact_append nshift (register_span238 (rev (pre ++ S v :: rest)))) with
        (d := left_view 15 (rev (register_file238 (pre ++ S v :: rest)) ++ l) []).
      * exact Shift.
      * apply increment_returns238.
Qed.

