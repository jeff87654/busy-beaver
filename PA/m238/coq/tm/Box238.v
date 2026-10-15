(** * Original PA238 register selector proof.

    Each register is a separator 0 followed by [value+1] one-cells. The
    selected register's first one is erased. The selector constants are
    checked against the literal PA238 table, and the proof covers arbitrary
    values, arbitrary later blocks, and arbitrary left tape contexts.
    No source-state name map, concrete replay, or oracle is a premise. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From P238.tm Require Import Table238 Finite238 Symbolic238.
Local Unset Implicit Arguments.
Import ListNotations.

Definition register_file238 (vs : list nat) : list bool :=
  flat_map (fun v => false :: repeat true (S v)) vs.

Definition register_left_file238 (vs : list nat) : list bool :=
  flat_map (fun v => repeat true (S v) ++ [false]) vs.

Fixpoint register_span238 (vs : list nat) : nat :=
  match vs with [] => 0 | v :: vs => S (S v) + register_span238 vs end.

Definition selector238 (r : nat) : nat :=
  nth r [119; 100; 80; 75; 60; 71; 52; 126; 147] 0.

Lemma selector238_loop r : r < 9 ->
  tmn238 (selector238 r) true = Some (true, R, selector238 r).
Proof. intro H. do 9 (destruct r as [|r]; [reflexivity|]). lia. Qed.

Lemma selector238_link r : r < 8 ->
  tmn238 (selector238 (S r)) false = Some (false, R, selector238 r).
Proof. intro H. do 8 (destruct r as [|r]; [reflexivity|]). lia. Qed.

Lemma selector238_base : tmn238 (selector238 0) false = Some (false, R, 0).
Proof. reflexivity. Qed.

Lemma register_file238_app a b :
  register_file238 (a ++ b) = register_file238 a ++ register_file238 b.
Proof. unfold register_file238. apply flat_map_app. Qed.

Lemma reverse_repeat_true n : rev (repeat true n) = repeat true n.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat rev]. rewrite IH.
  rewrite repeat_before_cell, app_nil_r. reflexivity.
Qed.

Lemma reverse_register_cons238 v vs l :
  rev (register_file238 (v :: vs)) ++ l =
  rev (register_file238 vs) ++ (repeat true (S v) ++ false :: l).
Proof.
  change (register_file238 (v :: vs)) with
    ((false :: repeat true (S v)) ++ register_file238 vs).
  rewrite rev_app_distr. cbn [rev]. rewrite reverse_repeat_true.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma reverse_register_file238 vs :
  rev (register_file238 vs) = register_left_file238 (rev vs).
Proof.
  induction vs as [|v vs IH]; [reflexivity|].
  rewrite <- (app_nil_r (rev (register_file238 (v :: vs)))).
  rewrite reverse_register_cons238, IH.
  cbn [rev]. unfold register_left_file238 at 2. rewrite flat_map_app.
  cbn [flat_map]. rewrite ?app_nil_r. reflexivity.
Qed.

(** Crossing each earlier block lowers the selector by one. The exact count
    is its encoded cell length; no bound is imposed on register values. *)
Theorem selector238_crosses pre offset l r :
  length pre + offset < 9 ->
  exact_steps (register_span238 pre)
    (denote (FC (selector238 (length pre + offset)) l (register_file238 pre ++ r)))
    (denote (FC (selector238 offset) (rev (register_file238 pre) ++ l) r)).
Proof.
  revert l. induction pre as [|v pre IH]; intros l H.
  - cbn [register_span238 register_file238]. apply exact_zero.
  - cbn [register_span238 length] in *.
    change (register_file238 (v :: pre)) with
      (false :: repeat true (S v) ++ register_file238 pre) at 1.
    cbn [app]. rewrite <- app_assoc.
    eapply exact_next with
      (d := denote (FC (selector238 (length pre + offset)) (false :: l)
                 (repeat true (S v) ++ (register_file238 pre ++ r)))).
    + apply literal_cell_right. apply selector238_link. lia.
    + eapply (exact_append (S v) (register_span238 pre)) with
        (d := denote (FC (selector238 (length pre + offset))
                     (repeat true (S v) ++ false :: l) (register_file238 pre ++ r))).
      * apply literal_run_right. apply selector238_loop. lia.
      * rewrite reverse_register_cons238. apply IH. lia.
Qed.

Lemma register238_return_one q v l r :
  tmn238 q true = Some (true, L, 5) ->
  exact_steps (S (S v))
    (left_view q (repeat true (S v) ++ false :: l) r)
    (left_view 8 l (false :: repeat true (S v) ++ r)).
Proof.
  intro T. cbn [repeat app]. rewrite left_view_cons.
  eapply exact_next with (d := left_view 5 (repeat true v ++ false :: l) (true :: r)).
  - apply literal_cell_left. exact T.
  - replace (S v) with (v + 1) at 1 by lia.
    eapply (exact_append v 1) with
      (d := left_view 5 (false :: l) (repeat true v ++ true :: r)).
    + apply literal_run_left. reflexivity.
    + rewrite left_view_cons.
      eapply exact_next with (d := left_view 8 l (false :: repeat true v ++ true :: r)).
      * apply literal_cell_left. reflexivity.
      * rewrite repeat_before_cell. apply exact_zero.
Qed.

Lemma register238_return_all vs l r :
  exact_steps (register_span238 vs)
    (left_view 8 (register_left_file238 vs ++ l) r)
    (left_view 8 l (register_file238 (rev vs) ++ r)).
Proof.
  revert r. induction vs as [|v vs IH]; intro r.
  - cbn [register_span238 register_left_file238 register_file238]. apply exact_zero.
  - cbn [register_span238 register_left_file238 flat_map].
    rewrite <- !app_assoc. cbn [app].
    eapply (exact_append (S (S v)) (register_span238 vs)) with
      (d := left_view 8 (register_left_file238 vs ++ l)
             (false :: repeat true (S v) ++ r)).
    + apply register238_return_one. reflexivity.
    + cbn [rev]. rewrite register_file238_app. cbn [register_file238 flat_map].
      rewrite <- !app_assoc. cbn [app]. rewrite ?app_nil_r. apply IH.
Qed.

Definition marked_return238 (reversed_prefix : list nat) : nat :=
  match reversed_prefix with [] => 2 | _ => 8 end.

Lemma register238_return_marked vs l r :
  exact_steps (register_span238 vs)
    (left_view 2 (register_left_file238 vs ++ l) r)
    (left_view (marked_return238 vs) l (register_file238 (rev vs) ++ r)).
Proof.
  destruct vs as [|v vs].
  - cbn [register_span238 register_left_file238 register_file238 marked_return238].
    apply exact_zero.
  - cbn [register_span238 marked_return238 register_left_file238 flat_map].
    rewrite <- !app_assoc. cbn [app].
    eapply (exact_append (S (S v)) (register_span238 vs)) with
      (d := left_view 8 (register_left_file238 vs ++ l)
             (false :: repeat true (S v) ++ r)).
    + apply register238_return_one. reflexivity.
    + cbn [rev]. rewrite register_file238_app. cbn [register_file238 flat_map].
      rewrite <- !app_assoc. cbn [app]. rewrite ?app_nil_r.
      apply register238_return_all.
Qed.

Lemma selector238_marks_first v rest l :
  exact_steps 3 (denote (FC (selector238 0) l (register_file238 (v :: rest))))
    (left_view 2 l (false :: false :: repeat true v ++ register_file238 rest)).
Proof.
  change (register_file238 (v :: rest)) with
    (false :: true :: repeat true v ++ register_file238 rest).
  eapply exact_next with
    (d := denote (FC 0 (false :: l) (true :: repeat true v ++ register_file238 rest))).
  - apply literal_cell_right. exact selector238_base.
  - eapply exact_next with
      (d := left_view 2 (false :: l) (false :: repeat true v ++ register_file238 rest)).
    + apply literal_cell_left. reflexivity.
    + rewrite left_view_cons.
      eapply exact_next; [apply literal_cell_left; reflexivity|apply exact_zero].
Qed.

(** The selected register is marked and every other cell is preserved. The
    extra blocks are arbitrary, so a nonzero spare block is covered too. *)
Theorem selector238_marks_register pre v rest l :
  length pre < 9 ->
  exact_steps (register_span238 pre + (3 + register_span238 (rev pre)))
    (denote (FC (selector238 (length pre)) l
       (register_file238 (pre ++ v :: rest))))
    (left_view (marked_return238 (rev pre)) l
       (register_file238 pre ++ false :: false :: repeat true v ++ register_file238 rest)).
Proof.
  intro H. rewrite register_file238_app.
  eapply (exact_append (register_span238 pre) (3 + register_span238 (rev pre))) with
    (d := denote (FC (selector238 0) (rev (register_file238 pre) ++ l)
             (register_file238 (v :: rest)))).
  - replace (length pre) with (length pre + 0) by lia.
    apply selector238_crosses. lia.
  - eapply (exact_append 3 (register_span238 (rev pre))) with
      (d := left_view 2 (rev (register_file238 pre) ++ l)
             (false :: false :: repeat true v ++ register_file238 rest)).
    + apply selector238_marks_first.
    + rewrite reverse_register_file238.
      pose proof (register238_return_marked (rev pre) l
        (false :: false :: repeat true v ++ register_file238 rest)) as R.
      rewrite rev_involutive in R. exact R.
Qed.
