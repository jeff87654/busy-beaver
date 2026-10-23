(** * Uniq.v : the halting configuration and its ones count are unique (generic over 7-state machines). *)
From BB7 Require Import Individual72 Defs.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

Theorem halted_unique : forall (tm : TM) c c1 c2, c -[ tm ]->* c1 -> c -[ tm ]->* c2 ->
  halted tm c1 -> halted tm c2 -> c1 = c2.
Proof.
  intros tm c c1 c2 H1. revert c2. induction H1 as [c | c c' c1 Hs H1 IH]; intros c2 H2 Hh1 Hh2.
  - inversion H2 as [| ? c'' ? Hs' H2']; subst; [reflexivity |].
    exfalso. exact (halted_no_step _ _ _ Hh1 Hs').
  - inversion H2 as [| ? c'' ? Hs' H2']; subst.
    + exfalso. exact (halted_no_step _ _ _ Hh2 Hs).
    + pose proof (step_deterministic _ _ _ _ Hs Hs') as E. subst c''. apply IH; assumption.
Qed.

Lemma zeros_count : forall L : list Sym, const S0 = L *> const S0 -> count1 L = O.
Proof.
  induction L as [| a L IH]; intro H; [reflexivity |].
  cbn [Str_app] in H.
  pose proof (f_equal (@Streams.hd Sym) H) as Ha. pose proof (f_equal (@Streams.tl Sym) H) as Ht. cbn in Ha, Ht. subst a.
  cbn [count1 sym_val]. apply IH. exact Ht.
Qed.

Lemma side_count : forall L1 L2 : list Sym, L1 *> const S0 = L2 *> const S0 -> count1 L1 = count1 L2.
Proof.
  induction L1 as [| a L1 IH]; intros L2 H.
  - symmetry. exact (zeros_count L2 H).
  - destruct L2 as [| b L2].
    + symmetry in H. exact (zeros_count (a :: L1) H).
    + cbn [Str_app] in H. injection H as Hab Ht. subst b. cbn [count1]. rewrite (IH L2 Ht). reflexivity.
Qed.

Theorem ones_unique : forall c N1 N2, ones c N1 -> ones c N2 -> N1 = N2.
Proof.
  intros c N1 N2 [q1 [L1 [R1 [s1 [E1 F1]]]]] [q2 [L2 [R2 [s2 [E2 F2]]]]].
  rewrite E1 in E2. injection E2 as Eq EL Es ER. subst.
  rewrite (side_count L1 L2 EL), (side_count R1 R2 ER). reflexivity.
Qed.

(** From one halting configuration with N ones to every one. *)
Theorem score_of : forall (tm : TM) c' N', c0 -[ tm ]->* c' -> halted tm c' -> ones c' N' ->
  forall c N, c0 -[ tm ]->* c -> halted tm c -> ones c N -> N = N'.
Proof.
  intros tm c' N' H1 H2 H3 c N G1 G2 G3.
  pose proof (halted_unique tm c0 c c' G1 H1 G2 H2) as E. subst c'.
  exact (ones_unique c N N' G3 H3).
Qed.
