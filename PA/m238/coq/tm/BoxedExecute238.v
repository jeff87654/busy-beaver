(** * Positive execution of the proved PA238 boxed rules.

    This executor stops only when its full target predicate is satisfied
    after a proved positive physical segment. Representation changes alone
    cannot establish progress. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From P238.tm Require Import Table238 Table238Facts Finite238 Symbolic238
  LiteralHalting238 Boxed238 BoxedNormalize238.
Local Unset Implicit Arguments.
Import ListNotations.

Fixpoint boxed_execute238 fuel br (accept : boxed_configuration238 -> bool) s moved
    : option boxed_configuration238 :=
  match fuel with
  | 0 => None
  | S fuel =>
      if andb moved (accept s) then Some s else
      match boxed_advance238 br s with
      | None => None
      | Some (next, progress) =>
          boxed_execute238 fuel br accept next (orb moved progress)
      end
  end.

Theorem boxed_execute238_literal fuel br accept s moved result gap vs :
  boxed_execute238 fuel br accept s moved = Some result ->
  branch_valid238 br vs ->
  accept result = true /\
  exists n, exact_steps n (boxed_denote238 gap vs s) (boxed_denote238 gap vs result) /\
    (moved = false -> 0 < n).
Proof.
  revert s moved result. induction fuel as [|fuel IH]; intros s moved result E V;
    [discriminate|].
  cbn [boxed_execute238] in E.
  destruct (andb moved (accept s)) eqn:A.
  - injection E as <-. apply andb_true_iff in A as [M T]. split; [exact T|].
    exists 0. split; [apply exact_zero|]. intro F. rewrite F in M. discriminate.
  - destruct (boxed_advance238 br s) as [[next progress]|] eqn:B; [|discriminate].
    destruct (IH next (orb moved progress) result E V) as [T [m [R P]]].
    destruct (boxed_advance238_literal br s next progress gap vs B V) as [n [S Q]].
    split; [exact T|]. exists (n + m). split.
    + eapply exact_append; eassumption.
    + intros F. subst moved. destruct progress.
      * assert (0 < n) by (apply Q; reflexivity). lia.
      * assert (0 < m) by (apply P; reflexivity). lia.
Qed.

Theorem boxed_execute238_restored fuel br target s result gap vs :
  boxed_execute238 fuel br (boxed_matches238 target) s false = Some result ->
  branch_valid238 br vs ->
  exists n, exact_steps (S n) (boxed_denote238 gap vs s) (boxed_denote238 gap vs target).
Proof.
  intros E V. destruct (boxed_execute238_literal fuel br (boxed_matches238 target)
    s false result gap vs E V) as [T [n [R P]]].
  pose proof (boxed_matches238_literal target result gap vs T) as Q.
  rewrite <- Q in R. assert (N : 0 < n) by (apply P; reflexivity).
  destruct n as [|n]; [lia|]. exists n. exact R.
Qed.

Definition boxed_terminal238 (s : boxed_configuration238) : bool :=
  Nat.eqb (symbolic_control (boxed_core238 s)) 238.

Lemma boxed_terminal238_halted s gap vs :
  boxed_terminal238 s = true -> literal_halted238 (boxed_denote238 gap vs s).
Proof.
  destruct s as [[q on_left l r] phase]. unfold boxed_terminal238.
  cbn [boxed_core238 symbolic_control]. intro E. apply Nat.eqb_eq in E. subst q.
  unfold boxed_denote238, extend_right238, symbolic_denote.
  cbn [boxed_core238 boxed_phase238 symbolic_control head_left symbolic_left symbolic_right].
  destruct on_left; unfold left_view, denote;
    cbn [literal_halted238 control left_cells right_cells]; apply tmn238_terminal.
Qed.

Theorem boxed_execute238_halts fuel br s result gap vs :
  boxed_execute238 fuel br boxed_terminal238 s false = Some result ->
  branch_valid238 br vs -> literal_halts238 (boxed_denote238 gap vs s).
Proof.
  intros E V. destruct (boxed_execute238_literal fuel br boxed_terminal238
    s false result gap vs E V) as [T [n [R P]]].
  exists n, (boxed_denote238 gap vs result). split; [exact R|].
  apply boxed_terminal238_halted. exact T.
Qed.
