(** * Restored-tape equality for the original PA238 boxed executor.

    Matching compares the complete symbolic tape and file phase. The left
    stream permits trailing blank cells, which denote the same completed
    stream. Every successful comparison below implies literal equality for
    every gap and complete register list. *)

From Coq Require Import Lists.List Lists.Streams Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From P238.tm Require Import Finite238 Symbolic238 Boxed238.
Local Unset Implicit Arguments.
Import ListNotations.

Lemma repeat_sum238 (b : bool) n m :
  repeat b (n + m) = repeat b n ++ repeat b m.
Proof. induction n; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.

Definition push_run238 (b : bool) (a c : nat) (ss : list symbolic_segment)
    : list symbolic_segment :=
  if andb (Nat.eqb a 0) (Nat.eqb c 0) then ss else
  match ss with
  | SRun b' a' c' :: rest =>
      if Bool.eqb b b' then SRun b (a + a') (c + c') :: rest
      else SRun b a c :: ss
  | _ => SRun b a c :: ss
  end.

Lemma push_run238_cells gap b a c ss :
  segments_cells gap (push_run238 b a c ss) =
  repeat b (a * gap + c) ++ segments_cells gap ss.
Proof.
  unfold push_run238. destruct (andb (Nat.eqb a 0) (Nat.eqb c 0)) eqn:Z.
  - apply andb_true_iff in Z as [A C].
    apply Nat.eqb_eq in A. apply Nat.eqb_eq in C. subst a c. reflexivity.
  - destruct ss as [|[b'|b' a' c'|cells] rest];
      try reflexivity.
    destruct (Bool.eqb b b') eqn:E; [|reflexivity].
    assert (B : b = b') by (destruct b, b'; cbn in E; congruence).
    subst b'.
    cbn [segments_cells flat_map segment_cells].
    replace ((a + a') * gap + (c + c')) with
      ((a * gap + c) + (a' * gap + c')) by
      (rewrite Nat.mul_add_distr_r; lia).
    rewrite repeat_sum238, app_assoc. reflexivity.
Qed.

Fixpoint normalize_segments238 (ss : list symbolic_segment) : list symbolic_segment :=
  match ss with
  | [] => []
  | SCell b :: rest => push_run238 b 0 1 (normalize_segments238 rest)
  | SRun b a c :: rest => push_run238 b a c (normalize_segments238 rest)
  | SPayload cells :: rest => SPayload cells :: normalize_segments238 rest
  end.

Lemma normalize_segments238_cells gap ss :
  segments_cells gap (normalize_segments238 ss) = segments_cells gap ss.
Proof.
  induction ss as [|[b|b a c|cells] rest IH]; cbn [normalize_segments238].
  - reflexivity.
  - rewrite push_run238_cells, IH. reflexivity.
  - rewrite push_run238_cells, IH. reflexivity.
  - change (cells ++ segments_cells gap (normalize_segments238 rest) =
      cells ++ segments_cells gap rest).
    rewrite IH. reflexivity.
Qed.

Lemma stream_append238 (xs ys : list bool) (s : Stream bool) :
  Str_app (xs ++ ys) s = Str_app xs (Str_app ys s).
Proof. induction xs; cbn; [reflexivity|]. rewrite IHxs. reflexivity. Qed.

Lemma complete_blank_run238 n :
  Str_app (repeat false n) (const false) = const false.
Proof. induction n; cbn; [reflexivity|]. rewrite IHn, <- const_unfold. reflexivity. Qed.

Fixpoint trim_left238 (ss : list symbolic_segment) : list symbolic_segment :=
  match ss with
  | [] => []
  | s :: rest =>
      match trim_left238 rest with
      | [] =>
          match s with
          | SCell false | SRun false _ _ => []
          | _ => [s]
          end
      | rest' => s :: rest'
      end
  end.

Lemma segments_complete_cons238 gap s ss :
  Str_app (segments_cells gap (s :: ss)) (const false) =
  Str_app (segment_cells gap s)
    (Str_app (segments_cells gap ss) (const false)).
Proof. cbn [segments_cells flat_map]. apply stream_append238. Qed.

Lemma trim_left238_stream gap ss :
  Str_app (segments_cells gap (trim_left238 ss)) (const false) =
  Str_app (segments_cells gap ss) (const false).
Proof.
  induction ss as [|s rest IH]; [reflexivity|].
  cbn [trim_left238]. destruct (trim_left238 rest) as [|t rest'] eqn:E.
  - cbn [segments_cells flat_map] in IH.
    rewrite segments_complete_cons238, <- IH.
    destruct s as [[|]|[|] a c|cells];
      cbn [segments_cells flat_map segment_cells Str_app];
      rewrite ?app_nil_r, ?complete_blank_run238;
      try rewrite <- const_unfold; reflexivity.
  - rewrite (segments_complete_cons238 gap s (t :: rest')),
      (segments_complete_cons238 gap s rest), IH. reflexivity.
Qed.

Definition normalize_left238 (ss : list symbolic_segment) : list symbolic_segment :=
  trim_left238 (normalize_segments238 ss).

Lemma normalize_left238_stream gap ss :
  Str_app (segments_cells gap (normalize_left238 ss)) (const false) =
  Str_app (segments_cells gap ss) (const false).
Proof. unfold normalize_left238. rewrite trim_left238_stream, normalize_segments238_cells.
  reflexivity. Qed.

Definition stream_view238 (q : nat) (on_left : bool) (l r : Stream bool)
    : literal_configuration :=
  if on_left then (q, (Streams.tl l, Streams.hd l, r))
  else (q, (l, Streams.hd r, Streams.tl r)).

Lemma symbolic_denote_stream238 gap q on_left l r :
  symbolic_denote gap (SC q on_left l r) =
  stream_view238 q on_left
    (Str_app (segments_cells gap l) (const false))
    (Str_app (segments_cells gap r) (const false)).
Proof.
  unfold symbolic_denote, stream_view238.
  cbn [symbolic_control head_left symbolic_left symbolic_right].
  destruct on_left; [|reflexivity].
  unfold left_view, denote. cbn [control left_cells right_cells Str_app].
  rewrite finite_stream_head, finite_stream_tail. reflexivity.
Qed.

Definition symbolic_segment_eq_dec238 : forall x y : symbolic_segment, {x = y} + {x <> y}.
Proof.
  decide equality; try apply Nat.eq_dec; try apply Bool.bool_dec;
    apply list_eq_dec; apply Bool.bool_dec.
Defined.

Definition file_phase_eq_dec238 : forall x y : file_phase238, {x = y} + {x <> y}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition boxed_fingerprint238 (s : boxed_configuration238) :
    (nat * (bool * (list symbolic_segment * (list symbolic_segment * file_phase238))))%type :=
  let '(BConfig238 (SC q on_left l r) phase) := s in
  (q, (on_left, (normalize_left238 l, (normalize_segments238 r, phase)))).

Definition product_eq_dec238 (A B : Type)
    (decA : forall x y : A, {x = y} + {x <> y})
    (decB : forall x y : B, {x = y} + {x <> y}) :
    forall x y : (A * B)%type, {x = y} + {x <> y}.
Proof.
  intros [a b] [a' b'].
  destruct (decA a a') as [EA|NA]; destruct (decB b b') as [EB|NB].
  - left. subst a' b'. reflexivity.
  - right. intro E. injection E as E1 E2. contradiction.
  - right. intro E. injection E as E1 E2. contradiction.
  - right. intro E. injection E as E1 E2. contradiction.
Defined.

Definition fingerprint_eq_dec238 : forall x y :
  (nat * (bool * (list symbolic_segment * (list symbolic_segment * file_phase238))))%type,
  {x = y} + {x <> y}.
Proof.
  refine (product_eq_dec238 nat _ Nat.eq_dec _).
  refine (product_eq_dec238 bool _ Bool.bool_dec _).
  refine (product_eq_dec238 (list symbolic_segment) _
    (@list_eq_dec symbolic_segment symbolic_segment_eq_dec238) _).
  exact (product_eq_dec238 (list symbolic_segment) file_phase238
    (@list_eq_dec symbolic_segment symbolic_segment_eq_dec238) file_phase_eq_dec238).
Defined.

Definition boxed_matches238 (target s : boxed_configuration238) : bool :=
  if fingerprint_eq_dec238 (boxed_fingerprint238 target) (boxed_fingerprint238 s)
  then true else false.

Lemma segments_cells_append238 gap xs ys :
  segments_cells gap (xs ++ ys) = segments_cells gap xs ++ segments_cells gap ys.
Proof. unfold segments_cells. apply flat_map_app. Qed.

Theorem boxed_matches238_literal target s gap vs :
  boxed_matches238 target s = true -> boxed_denote238 gap vs target = boxed_denote238 gap vs s.
Proof.
  unfold boxed_matches238.
  destruct (fingerprint_eq_dec238 (boxed_fingerprint238 target) (boxed_fingerprint238 s))
    as [E|E]; [|discriminate]. intros _.
  destruct target as [[q on_left l r] phase], s as [[q' on_left' l' r'] phase'].
  cbn [boxed_fingerprint238] in E. injection E as Q O L R P.
  subst q' on_left' phase'.
  unfold boxed_denote238, extend_right238. cbn [boxed_core238 boxed_phase238].
  rewrite !symbolic_denote_stream238.
  assert (EL : Str_app (segments_cells gap l) (const false) =
      Str_app (segments_cells gap l') (const false)).
  { rewrite <- (normalize_left238_stream gap l),
      <- (normalize_left238_stream gap l'). rewrite L. reflexivity. }
  assert (ER : segments_cells gap r = segments_cells gap r').
  { rewrite <- (normalize_segments238_cells gap r),
      <- (normalize_segments238_cells gap r'). rewrite R. reflexivity. }
  rewrite EL, !segments_cells_append238, ER. reflexivity.
Qed.
