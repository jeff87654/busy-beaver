(** Original PA238 finite execution interface.

    Each successful evaluator result produces a literal transition derivation
    with its exact binary-recursive transition count. The imported BusyCoq
    direction/stream helpers retain their vendor MIT license. No m254 proof
    source is incorporated here. The literal table is P238.Table238. *)

From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.Arith
  PArith.BinPos Lia.
From BusyCoq Require Import TM.
From P238.tm Require Import Table238.
Local Unset Implicit Arguments.
Import ListNotations.

Record finite_configuration := FC {
  control : nat;
  left_cells : list bool;
  right_cells : list bool
}.

Definition centered_tape := (Stream bool * bool * Stream bool)%type.
Definition literal_configuration := (nat * centered_tape)%type.

Definition denote (c : finite_configuration) : literal_configuration :=
  (control c,
   (Str_app (left_cells c) (const false),
    Streams.hd (Str_app (right_cells c) (const false)),
    Streams.tl (Str_app (right_cells c) (const false)))).

(** State labels remain numeric; rows outside the exact table cannot step. *)
Inductive literal_step : literal_configuration -> literal_configuration -> Prop :=
| literal_left q w q' l b r :
    tmn238 q b = Some (w, L, q') ->
    literal_step (q, (l, b, r)) (q', (Streams.tl l, Streams.hd l, Cons w r))
| literal_right q w q' l b r :
    tmn238 q b = Some (w, R, q') ->
    literal_step (q, (l, b, r)) (q', (Cons w l, Streams.hd r, Streams.tl r)).

Definition advance (c : finite_configuration) : option finite_configuration :=
  match tmn238 (control c) (List.hd false (right_cells c)) with
  | None => None
  | Some (w, L, q) =>
      Some (FC q (List.tl (left_cells c))
            (List.hd false (left_cells c) :: w :: List.tl (right_cells c)))
  | Some (w, R, q) =>
      Some (FC q (w :: left_cells c) (List.tl (right_cells c)))
  end.

Lemma finite_stream_head cells :
  Streams.hd (Str_app cells (const false)) = List.hd false cells.
Proof. destruct cells; reflexivity. Qed.

Lemma finite_stream_tail cells :
  Streams.tl (Str_app cells (const false)) =
  Str_app (List.tl cells) (const false).
Proof. destruct cells; reflexivity. Qed.

Lemma advance_literal c c' :
  advance c = Some c' -> literal_step (denote c) (denote c').
Proof.
  destruct c as [q l r]. unfold advance; cbn.
  destruct (tmn238 q (List.hd false r)) as [[[w direction] q']|] eqn:E;
    [|discriminate].
  destruct direction.
  - intros H. injection H as <-.
    unfold denote; cbn [control left_cells right_cells].
    rewrite !finite_stream_head, !finite_stream_tail.
    cbn [List.hd List.tl Str_app].
    rewrite <- (finite_stream_head l), <- (finite_stream_tail l).
    apply literal_left. exact E.
  - intros H. injection H as <-.
    unfold denote; cbn [control left_cells right_cells].
    rewrite !finite_stream_head, !finite_stream_tail.
    cbn [List.hd List.tl Str_app].
    rewrite <- (finite_stream_head (List.tl r)), <- (finite_stream_tail (List.tl r)).
    apply literal_right. exact E.
Qed.

Inductive exact_steps : nat -> literal_configuration -> literal_configuration -> Prop :=
| exact_zero c : exact_steps 0 c c
| exact_next n c d e : literal_step c d -> exact_steps n d e -> exact_steps (S n) c e.

Lemma exact_append n m c d e :
  exact_steps n c d -> exact_steps m d e -> exact_steps (n + m) c e.
Proof.
  intros H. induction H; intros G; cbn.
  - exact G.
  - eapply exact_next; eauto.
Qed.

(** Binary recursion avoids a 799504-deep recursion stack. *)
Fixpoint binary_steps (p : positive) : nat :=
  match p with
  | xH => 1
  | xO p => binary_steps p + binary_steps p
  | xI p => S (binary_steps p + binary_steps p)
  end.

Definition then_run (f : finite_configuration -> option finite_configuration)
    (c : option finite_configuration) : option finite_configuration :=
  match c with None => None | Some d => f d end.

Fixpoint execute (p : positive) (c : finite_configuration) : option finite_configuration :=
  match p with
  | xH => advance c
  | xO p => then_run (execute p) (execute p c)
  | xI p => then_run (fun d => then_run (execute p) (execute p d)) (advance c)
  end.

Theorem execute_literal p c d :
  execute p c = Some d -> exact_steps (binary_steps p) (denote c) (denote d).
Proof.
  revert c d. induction p as [p IH|p IH|]; intros c d H.
  - change (then_run (fun c1 => then_run (execute p) (execute p c1))
      (advance c) = Some d) in H.
    unfold then_run in H.
    destruct (advance c) as [c1|] eqn:A; [|discriminate H].
    destruct (execute p c1) as [c2|] eqn:B; [|discriminate H].
    eapply exact_next.
    + apply advance_literal, A.
    + eapply exact_append; apply IH; eassumption.
  - change (then_run (execute p) (execute p c) = Some d) in H.
    unfold then_run in H.
    destruct (execute p c) as [c1|] eqn:A; [|discriminate H].
    eapply exact_append; apply IH; eassumption.
  - change (advance c = Some d) in H.
    eapply exact_next.
    + apply advance_literal. exact H.
    + apply exact_zero.
Qed.

(** Concrete run segments form the first symbolic interface. The cells stay
    symbolic in [b] and the run length [n]; each transition remains literal. *)
Lemma literal_scan_right q b w n l r :
  tmn238 q b = Some (w, R, q) ->
  exact_steps n
    (denote (FC q l (repeat b n ++ r)))
    (denote (FC q (repeat w n ++ l) r)).
Proof.
  intros E. revert l. induction n as [|n IH]; intros l.
  - cbn [repeat]. apply exact_zero.
  - change (exact_steps (S n)
      (denote (FC q l (b :: repeat b n ++ r)))
      (denote (FC q (repeat w (S n) ++ l) r))).
    eapply exact_next with (d := denote (FC q (w :: l) (repeat b n ++ r))).
    + apply (advance_literal (FC q l (b :: repeat b n ++ r))
                            (FC q (w :: l) (repeat b n ++ r))).
      unfold advance; cbn. rewrite E. reflexivity.
    + assert (Rrepeat : repeat w (S n) ++ l = repeat w n ++ w :: l).
      { change ((w :: repeat w n) ++ l = repeat w n ++ w :: l).
        rewrite (repeat_cons n w), <- app_assoc. reflexivity. }
      rewrite Rrepeat. apply IH.
Qed.
