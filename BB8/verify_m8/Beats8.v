(** * Beats8.v (optional) : M8 beats the current BB(8) entry's machine-checked exact count.

    Loads, besides the M8 layer and the C04 tree, the repo's BB8/verify files (logical path BB8): the BB(8) champion
    1RB0RA_1LC1LF_1RD0LB_1RA1LE_---0LC_1RG1LD_1LC0RH_1RG1LF with its exact count
      BB8_champ35_exact.score_closed : ones at the halt = 12 * (2 ^37 3) + 58   (score = that + 1, the halting write).
    The champion is a machine over BB8/verify's own 8-state context (BB8.Individual82); M8 is over M8.Individual82 (a
    copy, so that the core layer needs only the C04 tree).  The two runs are stated separately and compared by their
    counts only.

    arrow_same      : BB8_champ35_bound.arrow = Abs.arrow (the same Fixpoint, pointwise).
    m8_beats_bb8r   : every halting count N of M8 has 12 * BB8_champ35_bound.arrow 37 2 3 + 59 < N.
    m8_beats_champ35: M8 halts with count N, the champion halts with count Nf, and Nf + 1 < N. *)
From M8 Require Import Individual82.
From Coq Require Import Lia PeanoNat List.
Set Default Goal Selector "!".
From BB8 Require BB8_champ35_1RB0RA BB8_champ35_bound BB8_champ35_exact.
From Dev Require Abs.
From Fgh Require Exact.
From M8 Require Import Tm8.
From M8 Require Transfer.

(** The champion's busycoq context (BB8/verify's Individual82). *)
Module C8 := BB8.Individual82.Individual82.Permute.Flip.Compute.TM.

Local Open Scope nat_scope.

Lemma arrow_same : forall k a b, BB8_champ35_bound.arrow k a b = Abs.arrow k a b.
Proof.
  induction k as [| k IH]; intros a b; [reflexivity |].
  change (Nat.iter b (BB8_champ35_bound.arrow k a) 1 = Nat.iter b (Abs.arrow k a) 1).
  induction b as [| b IHb]; [reflexivity |]. rewrite !Nat.iter_succ, IHb, IH. reflexivity.
Qed.

Opaque Abs.arrow BB8_champ35_bound.arrow.

Theorem m8_beats_bb8r : forall c N, c0 -[ tm8 ]->* c -> halted tm8 c -> ones c N ->
  12 * BB8_champ35_bound.arrow 37 2 3 + 59 < N.
Proof.
  intros c N H1 H2 H3. rewrite (arrow_same 37 2 3). exact (Transfer.m8_beats_bb8 c N H1 H2 H3).
Qed.

Theorem m8_beats_champ35 : exists c N, c0 -[ tm8 ]->* c /\ halted tm8 c /\ ones c N /\
  exists cf Nf, C8.evstep BB8_champ35_1RB0RA.tm C8.c0 cf /\ C8.halted BB8_champ35_1RB0RA.tm cf /\
    BB8_champ35_bound.ones cf Nf /\ Nf + 1 < N.
Proof.
  destruct Transfer.m8_score_reached as [c [H1 [H2 H3]]].
  exists c, Exact.sigma_c04. split; [exact H1 | split; [exact H2 | split; [exact H3 |]]].
  destruct BB8_champ35_exact.score_closed as [cf [G1 [G2 G3]]].
  exists cf, (12 * BB8_champ35_bound.arrow 37 2 3 + 58).
  split; [exact G1 | split; [exact G2 | split; [exact G3 |]]].
  pose proof (m8_beats_bb8r c _ H1 H2 H3) as H.
  set (A := BB8_champ35_bound.arrow 37 2 3) in *. clearbody A. lia.
Qed.
