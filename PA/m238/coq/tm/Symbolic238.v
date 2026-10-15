(** * Original PA238 symbolic tape interface.

    The affine runs below denote actual finite Boolean lists for every value
    of the gap parameter. Macro steps carry exact counts of literal PA238
    transitions. Opaque payloads permit arbitrary register-file contexts;
    no register excursion, bootstrap fact, or oracle is assumed here.

    This is original PA238 proof source. The local m254 symbolic executor
    was read as a mathematical reference; no m254 proof source is copied. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From P238.tm Require Import Table238 Finite238.
Local Unset Implicit Arguments.
Import ListNotations.

(** [left_view] puts the head on the first left cell, with blank completion
    if the left list is empty. [denote] puts it on the first right cell. *)
Definition left_view (q : nat) (l r : list bool) : literal_configuration :=
  denote (FC q (List.tl l) (List.hd false l :: r)).

Lemma left_view_cons q b l r :
  left_view q (b :: l) r = denote (FC q l (b :: r)).
Proof. reflexivity. Qed.

Lemma left_view_nil q r :
  left_view q [] r = denote (FC q [] (false :: r)).
Proof. reflexivity. Qed.

Lemma right_view_nil q l :
  denote (FC q l []) = denote (FC q l [false]).
Proof. reflexivity. Qed.

Lemma repeat_before_cell (b : bool) n l :
  repeat b n ++ b :: l = b :: repeat b n ++ l.
Proof. induction n as [|n IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma literal_cell_left q b w q' l r :
  tmn238 q b = Some (w, L, q') ->
  literal_step (denote (FC q l (b :: r))) (left_view q' l (w :: r)).
Proof.
  intro E. apply advance_literal. unfold advance; cbn. rewrite E. reflexivity.
Qed.

Lemma literal_cell_right q b w q' l r :
  tmn238 q b = Some (w, R, q') ->
  literal_step (denote (FC q l (b :: r))) (denote (FC q' (w :: l) r)).
Proof.
  intro E. apply advance_literal. unfold advance; cbn. rewrite E. reflexivity.
Qed.

Lemma literal_run_left q b w n l r :
  tmn238 q b = Some (w, L, q) ->
  exact_steps n (left_view q (repeat b n ++ l) r)
    (left_view q l (repeat w n ++ r)).
Proof.
  intro E. revert r. induction n as [|n IH]; intro r.
  - cbn [repeat]. apply exact_zero.
  - cbn [repeat app]. rewrite left_view_cons.
    eapply exact_next with
      (d := left_view q (repeat b n ++ l) (w :: r)).
    + apply literal_cell_left. exact E.
    + rewrite <- repeat_before_cell. apply IH.
Qed.

Lemma literal_run_right q b w n l r :
  tmn238 q b = Some (w, R, q) ->
  exact_steps n (denote (FC q l (repeat b n ++ r)))
    (denote (FC q (repeat w n ++ l) r)).
Proof.
  intro E. revert l. induction n as [|n IH]; intro l.
  - cbn [repeat]. apply exact_zero.
  - cbn [repeat app].
    eapply exact_next with
      (d := denote (FC q (w :: l) (repeat b n ++ r))).
    + apply literal_cell_right. exact E.
    + rewrite <- repeat_before_cell. apply IH.
Qed.

Inductive symbolic_segment : Type :=
| SCell (b : bool)
| SRun (b : bool) (coefficient constant : nat)
| SPayload (cells : list bool).

Definition segment_cells (gap : nat) (s : symbolic_segment) : list bool :=
  match s with
  | SCell b => [b]
  | SRun b a c => repeat b (a * gap + c)
  | SPayload cells => cells
  end.

Definition segments_cells (gap : nat) (ss : list symbolic_segment) : list bool :=
  flat_map (segment_cells gap) ss.

Record symbolic_configuration := SC {
  symbolic_control : nat;
  head_left : bool;
  symbolic_left : list symbolic_segment;
  symbolic_right : list symbolic_segment
}.

Definition symbolic_denote (gap : nat) (s : symbolic_configuration)
    : literal_configuration :=
  let l := segments_cells gap (symbolic_left s) in
  let r := segments_cells gap (symbolic_right s) in
  if head_left s then left_view (symbolic_control s) l r
  else denote (FC (symbolic_control s) l r).

Definition affine_count := (nat * nat)%type.
Definition count_at (gap : nat) (count : affine_count) : nat :=
  fst count * gap + snd count.
Definition add_count (x y : affine_count) : affine_count :=
  (fst x + fst y, snd x + snd y).

Lemma count_at_add gap x y :
  count_at gap (add_count x y) = count_at gap x + count_at gap y.
Proof.
  destruct x as [a c], y as [a' c']; unfold count_at, add_count; cbn.
  rewrite Nat.mul_add_distr_r. lia.
Qed.

Lemma symbolic_scan_left gap q b w a c l r :
  tmn238 q b = Some (w, L, q) ->
  exact_steps (count_at gap (a, c))
    (symbolic_denote gap (SC q true (SRun b a c :: l) r))
    (symbolic_denote gap (SC q true l (SRun w a c :: r))).
Proof. unfold symbolic_denote, count_at; cbn [symbolic_control head_left symbolic_left symbolic_right
       segments_cells flat_map segment_cells].
  apply literal_run_left. Qed.

Lemma symbolic_scan_right gap q b w a c l r :
  tmn238 q b = Some (w, R, q) ->
  exact_steps (count_at gap (a, c))
    (symbolic_denote gap (SC q false l (SRun b a c :: r)))
    (symbolic_denote gap (SC q false (SRun w a c :: l) r)).
Proof. unfold symbolic_denote, count_at; cbn [symbolic_control head_left symbolic_left symbolic_right
       segments_cells flat_map segment_cells].
  apply literal_run_right. Qed.

(** Exposing a known positive constant part is a change of representation,
    with zero physical transitions. A purely variable nonempty run cannot be
    exposed this way; it needs a proved table self-loop. *)
Definition expose_left q b a c l r
    : option (symbolic_configuration * affine_count) :=
  match c, a with
  | S c, _ => Some (SC q true (SCell b :: SRun b a c :: l) r, (0, 0))
  | 0, 0 => Some (SC q true l r, (0, 0))
  | 0, S _ => None
  end.

Definition expose_right q b a c l r
    : option (symbolic_configuration * affine_count) :=
  match c, a with
  | S c, _ => Some (SC q false l (SCell b :: SRun b a c :: r), (0, 0))
  | 0, 0 => Some (SC q false l r, (0, 0))
  | 0, S _ => None
  end.

Lemma affine_repeat_succ (b : bool) a gap c :
  repeat b (a * gap + S c) = b :: repeat b (a * gap + c).
Proof. rewrite Nat.add_succ_r. reflexivity. Qed.

Lemma expose_left_sound q b a c l r s k gap :
  expose_left q b a c l r = Some (s, k) ->
  exact_steps (count_at gap k)
    (symbolic_denote gap (SC q true (SRun b a c :: l) r))
    (symbolic_denote gap s).
Proof.
  unfold expose_left. destruct c as [|c], a as [|a]; intro E;
    try discriminate; injection E as <- <-;
    unfold count_at, symbolic_denote;
    cbn [symbolic_control head_left symbolic_left symbolic_right
       segments_cells flat_map segment_cells];
    rewrite ?affine_repeat_succ; apply exact_zero.
Qed.

Lemma expose_right_sound q b a c l r s k gap :
  expose_right q b a c l r = Some (s, k) ->
  exact_steps (count_at gap k)
    (symbolic_denote gap (SC q false l (SRun b a c :: r)))
    (symbolic_denote gap s).
Proof.
  unfold expose_right. destruct c as [|c], a as [|a]; intro E;
    try discriminate; injection E as <- <-;
    unfold count_at, symbolic_denote;
    cbn [symbolic_control head_left symbolic_left symbolic_right
       segments_cells flat_map segment_cells];
    rewrite ?affine_repeat_succ; apply exact_zero.
Qed.

Definition symbolic_advance (s : symbolic_configuration)
    : option (symbolic_configuration * affine_count) :=
  let '(SC q on_left l r) := s in
  if on_left then
    match l with
    | [] => Some (SC q false [] (SCell false :: r), (0, 0))
    | SCell b :: l => Some (SC q false l (SCell b :: r), (0, 0))
    | SRun b a c :: l =>
        match tmn238 q b with
        | Some (w, L, q') =>
            if Nat.eqb q' q then Some (SC q true l (SRun w a c :: r), (a, c))
            else expose_left q b a c l r
        | _ => expose_left q b a c l r
        end
    | SPayload _ :: _ => None
    end
  else
    match r with
    | [] => None
    | SCell b :: r =>
        match tmn238 q b with
        | Some (w, L, q') => Some (SC q' true l (SCell w :: r), (0, 1))
        | Some (w, R, q') => Some (SC q' false (SCell w :: l) r, (0, 1))
        | None => None
        end
    | SRun b a c :: r =>
        match tmn238 q b with
        | Some (w, R, q') =>
            if Nat.eqb q' q then Some (SC q false (SRun w a c :: l) r, (a, c))
            else expose_right q b a c l r
        | _ => expose_right q b a c l r
        end
    | SPayload _ :: _ => None
    end.

Theorem symbolic_advance_literal s s' k gap :
  symbolic_advance s = Some (s', k) ->
  exact_steps (count_at gap k) (symbolic_denote gap s) (symbolic_denote gap s').
Proof.
  destruct s as [q on_left l r]. destruct on_left; cbn [symbolic_advance].
  - destruct l as [|[b|b a c|cells] l].
    + intro E. injection E as <- <-.
      unfold count_at, symbolic_denote; cbn [symbolic_control head_left symbolic_left symbolic_right
       segments_cells flat_map segment_cells].
      apply exact_zero.
    + intro E. injection E as <- <-.
      unfold count_at, symbolic_denote; cbn [symbolic_control head_left symbolic_left symbolic_right
       segments_cells flat_map segment_cells].
      apply exact_zero.
    + destruct (tmn238 q b) as [[[w direction] q']|] eqn:T.
      * destruct direction.
        -- destruct (Nat.eqb q' q) eqn:Q.
           ++ apply Nat.eqb_eq in Q. subst q'. intro E. injection E as <- <-.
              apply symbolic_scan_left. exact T.
           ++ apply expose_left_sound.
        -- apply expose_left_sound.
      * apply expose_left_sound.
    + discriminate.
  - destruct r as [|[b|b a c|cells] r]; [discriminate| | |discriminate].
    + destruct (tmn238 q b) as [[[w direction] q']|] eqn:T; [|discriminate].
      destruct direction; intro E; injection E as <- <-.
      * unfold count_at, symbolic_denote;
          cbn [symbolic_control head_left symbolic_left symbolic_right
       segments_cells flat_map segment_cells].
        eapply exact_next; [|apply exact_zero].
        apply literal_cell_left. exact T.
      * unfold count_at, symbolic_denote;
          cbn [symbolic_control head_left symbolic_left symbolic_right
       segments_cells flat_map segment_cells].
        eapply exact_next; [|apply exact_zero].
        apply literal_cell_right. exact T.
    + destruct (tmn238 q b) as [[[w direction] q']|] eqn:T.
      * destruct direction.
        -- apply expose_right_sound.
        -- destruct (Nat.eqb q' q) eqn:Q.
           ++ apply Nat.eqb_eq in Q. subst q'. intro E. injection E as <- <-.
              apply symbolic_scan_right. exact T.
           ++ apply expose_right_sound.
      * apply expose_right_sound.
Qed.

(** A successful bounded symbolic search is a checkable certificate, rather
    than an assumed site theorem. Its result contains the affine count of all
    literal transitions, including those absorbed by run scans. *)
Fixpoint symbolic_execute (fuel : nat) (target : symbolic_configuration -> bool)
    (s : symbolic_configuration) : option (symbolic_configuration * affine_count) :=
  if target s then Some (s, (0, 0))
  else match fuel with
       | 0 => None
       | S f =>
           match symbolic_advance s with
           | None => None
           | Some (s1, k1) =>
               match symbolic_execute f target s1 with
               | None => None
               | Some (s2, k2) => Some (s2, add_count k1 k2)
               end
           end
       end.

Theorem symbolic_execute_literal fuel target s s' k gap :
  symbolic_execute fuel target s = Some (s', k) ->
  target s' = true /\
  exact_steps (count_at gap k) (symbolic_denote gap s) (symbolic_denote gap s').
Proof.
  revert s s' k. induction fuel as [|fuel IH]; intros s s' k H;
    cbn [symbolic_execute] in H; destruct (target s) eqn:E.
  - injection H as <- <-. split; [exact E|]. apply exact_zero.
  - discriminate.
  - injection H as <- <-. split; [exact E|]. apply exact_zero.
  - destruct (symbolic_advance s) as [[s1 k1]|] eqn:A; [|discriminate].
    destruct (symbolic_execute fuel target s1) as [[s2 k2]|] eqn:B;
      [|discriminate]. injection H as <- <-.
    destruct (IH _ _ _ B) as [Ht Hr]. split; [exact Ht|].
    rewrite count_at_add. eapply exact_append.
    + apply symbolic_advance_literal. exact A.
    + exact Hr.
Qed.
