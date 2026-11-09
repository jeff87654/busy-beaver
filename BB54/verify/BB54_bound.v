(** * The runtime bounds of the wiki's Champions page, and the descent
    parameter of this machine.

    The Champions page listed, for BB(5,4), the runtime bound

        > f_w^2 (10 ↑^4 10 ↑↑ 65533) ,

    discovered by Jacobzheng in 2026; that number is [target] of
    [BB54_score.v].  It is the *original* bound of the wiki -- **Jacobzheng's
    original lower bound** -- and it is the smaller of the two.

    The value computed from the structure of this machine is

        f_w^2 (2 ↑^4 2 ↑^3 4) ,

    whose inner argument is *exactly* the descent parameter of the main
    regime: with [X = g_5 (g_4 0)] (see [BB54_halt.v]),

        2 ↑^4 2 ↑^3 4  =  2 X + 4                       ([X_inner]).

    That is the reason the second number is the accurate one: it is a
    number of the machine itself and not of a generic tower.  It is also
    the number of twos that the first D/E phase of the main regime has to
    erase ([bb54_dchain] of [BB54_dphase.v]).

    Comparing the levels of the three numbers (a hand calculation on the
    closed forms, *not* a Coq proof -- see the write-up) gives

        f_w^2 (10 ↑^4 10 ↑↑ 65533)  <  σ  <  f_w^2 (2 ↑^4 2 ↑^3 4) ,

    so the sigma of the machine lies *above* Jacobzheng's original bound and
    *below* the refined one.

    Everything below is symbolic: no large number is ever evaluated.

    The arrow convention is [knuth n a b = a ↑^n b] with
    [knuth 0 a b = a * b], so

        knuth 2 2 m = 2 ↑↑ m   (a tower of twos of height m),
        knuth 3 2 m = 2 ↑↑↑ m,
        knuth 4 2 m = 2 ↑↑↑↑ m. *)

From TM54 Require Import BB54_rules BB54_score BB54_halt.
From Coq Require Import Lia PeanoNat.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(** ** The shapes of the arrows.

    [knuth 3 2 4] is the third arrow applied to 4; it unfolds to a tower
    of twos of height 65536, and [knuth 4 2 3] (the level of the score of
    the configuration [c_score]) is the same number. *)

Lemma knuth_3_2_4 : knuth 3 2 4 = knuth 2 2 65536.
Proof.
  rewrite (knuth_S 2 2 3).
  rewrite (knuth_S 2 2 2).
  rewrite (knuth_S 2 2 1).
  rewrite (knuth_S 2 2 0).
  reflexivity.
Qed.

Lemma knuth_4_2_3 : knuth 4 2 3 = knuth 3 2 4.
Proof.
  rewrite (knuth_S 3 2 2).
  rewrite (knuth_S 3 2 1).
  rewrite (knuth_S 3 2 0).
  reflexivity.
Qed.

(** ** The descent parameter of the main regime, in closed form.

    [X = g 5 (g 4 0)] is the parameter of the main regime; the closed
    form of the [g] hierarchy (Ligocki's theorem, [g_closed] of
    [BB54_score.v]) gives

        2 X + 4 = 2 ↑^4 (2 ↑^3 4) .

    The proof goes through the level-5 form of [g_closed] and the level-4
    form of [g_iter_closed_gen]; both are stated for variables, so that
    no [g] is ever unfolded. *)

Lemma g5_closed_gen : forall m, 2 * g 5 m + 4 = knuth 4 2 (2 * m + 4).
Proof. intros m. rewrite (g_closed 4 m). reflexivity. Qed.

(** [g 4 0 = Nat.iter 2 (g 3) 0]: the level-3 function iterated twice. *)
Lemma g4_zero_iter : g 4 0 = Nat.iter 2 (g 3) 0%nat.
Proof. reflexivity. Qed.

Lemma g4_zero_closed : 2 * g 4 0 + 4 = knuth 3 2 4.
Proof.
  rewrite (g_iter_closed_gen 3 2 (g 4 0) g4_zero_iter).
  reflexivity.
Qed.

(** ** The main identity of this file.

    The inner argument of the accurate runtime bound is the descent
    parameter of the machine:

        2 ↑^4 2 ↑^3 4  =  2 X + 4 . *)
Theorem X_inner : 2 * X + 4 = knuth 4 2 (knuth 3 2 4).
Proof.
  rewrite (g5_closed_gen (g 4 0)).
  rewrite g4_zero_closed.
  reflexivity.
Qed.

(** ** The two runtime bounds.

    [target] (of [BB54_score.v]) is the bound of the wiki; the refined
    one is built from the machine. *)

(** The wiki's entry is Jacobzheng's original bound, on the runtime. *)
Lemma target_is_jacobzheng :
  target = f_omega2 (knuth 4 10 (knuth 2 10 65533)).
Proof. unfold target, tower65533. reflexivity. Qed.

(** The refined runtime bound. *)
Definition target_refined : nat := f_omega2 (knuth 4 2 (knuth 3 2 4)).

(** The refined bound is [f_w^2 (2 X + 4)]: its inner argument is the
    descent parameter of the machine, not a generic tower. *)
Theorem target_refined_eq : target_refined = f_omega2 (2 * X + 4).
Proof.
  unfold target_refined.
  rewrite <- X_inner.
  reflexivity.
Qed.
