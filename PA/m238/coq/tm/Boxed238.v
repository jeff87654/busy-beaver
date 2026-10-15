(** * Original closed boxed executor for the literal PA238 table.

    Ordinary segments use the accepted affine executor. The final file is
    represented by a checked phase over a universally quantified complete
    physical register list. File excursions are supplied by proved PA238
    transitions, including preservation of arbitrary old spare values. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From P238.tm Require Import Table238 Finite238 Symbolic238 LiteralHalting238
  Box238 Increment238 Decrement238 PositiveDecrement238 RegisterTape238 IndexedBoxes238.
Local Unset Implicit Arguments.
Import ListNotations.

Inductive file_phase238 : Type :=
| FilePlain238
| FileMarked238 (r : nat)
| FileIncremented238 (r : nat)
| FileDecremented238 (r : nat).

Definition phase_cells238 (p : file_phase238) (vs : list nat) : list bool :=
  match p with
  | FilePlain238 => register_file238 vs
  | FileMarked238 r => marked_file238 r vs
  | FileIncremented238 r => register_file238 (update_register238 r S vs)
  | FileDecremented238 r => register_file238 (update_register238 r Nat.pred vs ++ [0])
  end.

Definition file_branch238 := option (nat * bool).
Definition branch_valid238 (br : file_branch238) (vs : list nat) : Prop :=
  9 <= length vs /\
  match br with
  | None => True
  | Some (r, zero) => if zero then nth r vs 0 = 0 else nth r vs 0 <> 0
  end.

Definition file_gate238 (br : file_branch238) (q : nat) (p : file_phase238)
    : option (nat * file_phase238) :=
  match p with
  | FilePlain238 =>
      match selector_index238 q with
      | Some r => Some (indexed_exit238 2 8 r, FileMarked238 r)
      | None => None
      end
  | FileMarked238 r =>
      if Nat.ltb r 9 then
        if Nat.eqb q 99 then Some (11, FileIncremented238 r)
        else if Nat.eqb q 78 then
          match br with
          | Some (r', zero) =>
              if Nat.eqb r r' then
                if zero then Some (indexed_exit238 3 7 r, FilePlain238)
                else Some (indexed_exit238 15 11 r, FileDecremented238 r)
              else None
          | None => None
          end
        else None
      else None
  | _ => None
  end.

Theorem file_gate238_literal br q p q' p' vs l :
  file_gate238 br q p = Some (q', p') -> branch_valid238 br vs ->
  exists n, exact_steps (S n)
    (denote (FC q l (phase_cells238 p vs)))
    (left_view q' l (phase_cells238 p' vs)).
Proof.
  intros G [V B]. destruct p as [|r|r|r]; cbn [file_gate238] in G; try discriminate.
  - destruct (selector_index238 q) as [r|] eqn:E; [|discriminate].
    injection G as <- <-. apply indexed_mark238; assumption.
  - destruct (Nat.ltb r 9) eqn:R; [|discriminate]. apply Nat.ltb_lt in R.
    destruct (Nat.eqb q 99) eqn:Q99.
    + apply Nat.eqb_eq in Q99. subst q. injection G as <- <-.
      apply indexed_increment238; assumption.
    + destruct (Nat.eqb q 78) eqn:Q78; [|discriminate].
      apply Nat.eqb_eq in Q78. subst q.
      destruct br as [[r' zero]|]; [|discriminate].
      destruct (Nat.eqb r r') eqn:E; [|discriminate].
      apply Nat.eqb_eq in E. subst r'.
      destruct zero; injection G as <- <-.
      * apply indexed_decrement_zero238; assumption.
      * apply indexed_decrement_positive238; assumption.
Qed.

Lemma register_file238_head vs : vs <> [] ->
  exists cells, register_file238 vs = false :: cells.
Proof. destruct vs as [|v rest]; [contradiction|]. intros _. eexists. reflexivity. Qed.

Lemma phase_cells238_head p vs : 9 <= length vs ->
  exists cells, phase_cells238 p vs = false :: cells.
Proof.
  intro V. assert (N : vs <> []) by (intro E; subst vs; cbn [length] in V; lia).
  destruct p as [|r|r|r]; cbn [phase_cells238].
  - apply register_file238_head. exact N.
  - destruct vs as [|v rest]; [contradiction|]. destruct r; eexists; reflexivity.
  - apply register_file238_head. intro E.
    pose proof (f_equal (@length nat) E) as L.
    rewrite update_register238_length in L. cbn [length] in L. lia.
  - apply register_file238_head. intro E.
    apply app_eq_nil in E as [_ E]. discriminate.
Qed.

Definition extend_right238 (tail : list symbolic_segment) (s : symbolic_configuration)
    : symbolic_configuration :=
  match s with SC q on_left l r => SC q on_left l (r ++ tail) end.

Lemma expose_left238_tail q b a c l r s k tail :
  expose_left q b a c l r = Some (s, k) ->
  expose_left q b a c l (r ++ tail) = Some (extend_right238 tail s, k).
Proof.
  unfold expose_left. destruct c as [|c], a as [|a]; intro E;
    try discriminate; injection E as <- <-; reflexivity.
Qed.

Lemma expose_right238_tail q b a c l r s k tail :
  expose_right q b a c l r = Some (s, k) ->
  expose_right q b a c l (r ++ tail) = Some (extend_right238 tail s, k).
Proof.
  unfold expose_right. destruct c as [|c], a as [|a]; intro E;
    try discriminate; injection E as <- <-; reflexivity.
Qed.

Lemma symbolic_advance238_tail s s' k tail :
  symbolic_advance s = Some (s', k) ->
  symbolic_advance (extend_right238 tail s) = Some (extend_right238 tail s', k).
Proof.
  destruct s as [q on_left l r]. destruct on_left;
    cbn [extend_right238 symbolic_advance].
  - destruct l as [|[b|b a c|cells] l].
    + intro E. injection E as <- <-. reflexivity.
    + intro E. injection E as <- <-. reflexivity.
    + destruct (tmn238 q b) as [[[w direction] q']|] eqn:T.
      * destruct direction.
        -- destruct (Nat.eqb q' q).
           ++ intro E. injection E as <- <-. reflexivity.
           ++ apply expose_left238_tail.
        -- apply expose_left238_tail.
      * apply expose_left238_tail.
    + discriminate.
  - destruct r as [|[b|b a c|cells] r]; cbn [app]; [discriminate| | |discriminate].
    + destruct (tmn238 q b) as [[[w direction] q']|]; [|discriminate].
      destruct direction; intro E; injection E as <- <-; reflexivity.
    + destruct (tmn238 q b) as [[[w direction] q']|].
      * destruct direction.
        -- apply expose_right238_tail.
        -- destruct (Nat.eqb q' q).
           ++ intro E. injection E as <- <-. reflexivity.
           ++ apply expose_right238_tail.
      * apply expose_right238_tail.
Qed.

Record boxed_configuration238 := BConfig238 {
  boxed_core238 : symbolic_configuration;
  boxed_phase238 : file_phase238
}.

Definition boxed_denote238 gap vs (s : boxed_configuration238) : literal_configuration :=
  symbolic_denote gap
    (extend_right238 [SPayload (phase_cells238 (boxed_phase238 s) vs)] (boxed_core238 s)).

Lemma boxed_file_right238 gap vs q l p :
  boxed_denote238 gap vs (BConfig238 (SC q false l []) p) =
  denote (FC q (segments_cells gap l) (phase_cells238 p vs)).
Proof.
  unfold boxed_denote238, symbolic_denote, extend_right238.
  cbn [boxed_core238 boxed_phase238 symbolic_control head_left symbolic_left symbolic_right
       segments_cells flat_map segment_cells app]. rewrite ?app_nil_r. reflexivity.
Qed.

Lemma boxed_file_left238 gap vs q l p :
  boxed_denote238 gap vs (BConfig238 (SC q true l []) p) =
  left_view q (segments_cells gap l) (phase_cells238 p vs).
Proof.
  unfold boxed_denote238, symbolic_denote, extend_right238.
  cbn [boxed_core238 boxed_phase238 symbolic_control head_left symbolic_left symbolic_right
       segments_cells flat_map segment_cells app]. rewrite ?app_nil_r. reflexivity.
Qed.

Definition boxed_advance238 (br : file_branch238) (s : boxed_configuration238)
    : option (boxed_configuration238 * bool) :=
  let '(BConfig238 core phase) := s in
  match core with
  | SC q false l [] =>
      match file_gate238 br q phase with
      | Some (q', phase') => Some (BConfig238 (SC q' true l []) phase', true)
      | None =>
          match tmn238 q false with
          | Some (false, L, q') => Some (BConfig238 (SC q' true l []) phase, true)
          | _ => None
          end
      end
  | _ =>
      match symbolic_advance core with
      | Some (core', k) => Some (BConfig238 core' phase, Nat.ltb 0 (snd k))
      | None => None
      end
  end.

Definition boxed_step_ok238 gap vs s s' moved : Prop :=
  exists n, exact_steps n (boxed_denote238 gap vs s) (boxed_denote238 gap vs s') /\
    (moved = true -> 0 < n).

Lemma boxed_regular_sound238 core phase core' k gap vs :
  symbolic_advance core = Some (core', k) ->
  boxed_step_ok238 gap vs (BConfig238 core phase) (BConfig238 core' phase)
    (Nat.ltb 0 (snd k)).
Proof.
  intro E. exists (count_at gap k). split.
  - apply symbolic_advance_literal.
    apply symbolic_advance238_tail. exact E.
  - intro K. apply Nat.ltb_lt in K. unfold count_at. lia.
Qed.

Theorem boxed_advance238_literal br s s' moved gap vs :
  boxed_advance238 br s = Some (s', moved) -> branch_valid238 br vs ->
  boxed_step_ok238 gap vs s s' moved.
Proof.
  destruct s as [[q on_left l r] phase]. unfold boxed_advance238.
  destruct on_left.
  - destruct (symbolic_advance (SC q true l r)) as [[core' k]|] eqn:E;
      [|discriminate]. intro A. injection A as <- <-. intro V.
    apply boxed_regular_sound238. exact E.
  - destruct r as [|cell r].
    + destruct (file_gate238 br q phase) as [[q' phase']|] eqn:G.
      * intro A. injection A as <- <-. intro V.
        destruct (file_gate238_literal br q phase q' phase' vs (segments_cells gap l) G V)
          as [n R]. exists (S n). split; [|lia].
        rewrite boxed_file_right238, boxed_file_left238. exact R.
      * destruct (tmn238 q false) as [[[[|] direction] q']|] eqn:T; try discriminate.
        destruct direction; [|discriminate]. intro A. injection A as <- <-.
        intros [V B]. exists 1. split; [|lia].
        rewrite boxed_file_right238, boxed_file_left238.
        destruct (phase_cells238_head phase vs V) as [cells E]. rewrite E.
        eapply exact_next; [apply literal_cell_left; exact T|apply exact_zero].
    + destruct (symbolic_advance (SC q false l (cell :: r))) as [[core' k]|] eqn:E;
        [|discriminate]. intro A. injection A as <- <-. intro V.
      apply boxed_regular_sound238. exact E.
Qed.
