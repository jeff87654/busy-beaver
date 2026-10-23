(** * champ_232 = 1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_1LC0RB halts, with its exact score and bounds *)
From BB7 Require Import Individual72 C232_rules1 C232_rules2 C232_rules3 C232_init Clr C232_clear C232_run Bound Bound3.
From Coq Require Import Lia PeanoNat List.
Set Default Goal Selector "!".

(** N counts the ones of the halting configuration (state C reading a 1; C1 is undefined).  The standard
    score treats C1 as 1RZ, which writes a 1 over the 1 already there, so sigma = N. *)

Theorem c232_score_exact : exists c, c0 -->* c /\ halted tm c /\ ones c (2 * W 20 5 + 7).
Proof. exact score_exact. Qed.

(** 3 ^20 3 = 3 ^19 (3 ^19 3) (arrows); Lc 20 = 3 ^19 3 ^18 ... 3 ^2 3 ^1 15 is a weaker nested form. *)
Theorem c232_lower : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  arrow 20 3 3 < N /\ Lc 20 < N /\ arrow 19 3 (arrow 18 3 3) < N.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  destruct (N_lower (2 * W 20 5 + 7) eq_refl) as [L1 [L2 _]].
  pose proof (N_lower3 (2 * W 20 5 + 7) eq_refl) as L0.
  exists c, (2 * W 20 5 + 7). repeat split; assumption.
Qed.

(** The BB(7) champion 1RB0RA_1LC1LF_1RD0LB_1RA1LE_---0LC_1RG1LD_0RG0RF has sigma = 3 * (2 ^13 3) + 22
    (our analysis; see BB7/README.md) and the wiki's lower bound 2 ^11 (2 ^11 3) (arrows). *)
Theorem c232_beats_bb7_champion : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
  3 * arrow 13 2 3 + 22 < N /\ arrow 11 2 (arrow 11 2 3) < N.
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  destruct (N_lower (2 * W 20 5 + 7) eq_refl) as [_ [_ [_ [L4 L5]]]].
  exists c, (2 * W 20 5 + 7). repeat split; assumption.
Qed.

Check c232_halts.
