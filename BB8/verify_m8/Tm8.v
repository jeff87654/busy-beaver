(** * Tm8.v : the 8-state machine M8 over busycoq's 8-state context BB82 (M8.BB82 = copy of bb8_list/proofs/BB82.v).

    M8 = 1RB0RA_1LC1LF_1RD0LB_1RA1LE_1LH0LC_1RG1LD_0RG0RF_1RG---
    (H1 undefined = the halt; the table is in Defs.v).  Also: the ones count (in Defs.v) (verbatim copy of BB8_champ35_bound.ones / BB9_fw2_bound.ones,
    over the 8-state Sym), and three generic facts about 8-state runs used by Sim.v: determinism of the halting
    configuration, ones uniqueness (padding a tape list with blanks does not change its count), and multistep -> evstep. *)
From M8 Require Import Individual82.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* The machine tm8 and sym_val / count1 / ones are defined in Defs.v (re-exported here); these abbreviations keep
   the names Tm8.tm8, Tm8.sym_val, Tm8.count1, Tm8.ones working.  They are the same constants as Defs.tm8, ... *)
From M8 Require Export Defs.
Notation tm8 := Defs.tm8 (only parsing).
Notation sym_val := Defs.sym_val (only parsing).
Notation count1 := Defs.count1 (only parsing).
Notation ones := Defs.ones (only parsing).

(** ** Generic facts about 8-state runs *)
Theorem halted_unique8 : forall (tm : TM) c c1 c2, c -[ tm ]->* c1 -> c -[ tm ]->* c2 ->
  halted tm c1 -> halted tm c2 -> c1 = c2.
Proof.
  intros tm c c1 c2 H1. revert c2. induction H1 as [c | c c' c1 Hs H1 IH]; intros c2 H2 Hh1 Hh2.
  - inversion H2 as [| ? c'' ? Hs' H2']; subst; [reflexivity |].
    exfalso. exact (halted_no_step _ _ _ Hh1 Hs').
  - inversion H2 as [| ? c'' ? Hs' H2']; subst.
    + exfalso. exact (halted_no_step _ _ _ Hh2 Hs).
    + pose proof (step_deterministic _ _ _ _ Hs Hs') as E. subst c''. apply IH; assumption.
Qed.

Lemma zeros_count8 : forall L : list Sym, const S0 = L *> const S0 -> count1 L = 0%nat.
Proof.
  induction L as [| a L IH]; intro H; [reflexivity |].
  cbn [Str_app] in H.
  pose proof (f_equal (@Streams.hd Sym) H) as Ha. pose proof (f_equal (@Streams.tl Sym) H) as Ht. cbn in Ha, Ht. subst a.
  cbn [count1 sym_val]. apply IH. exact Ht.
Qed.

Lemma side_count8 : forall L1 L2 : list Sym, L1 *> const S0 = L2 *> const S0 -> count1 L1 = count1 L2.
Proof.
  induction L1 as [| a L1 IH]; intros L2 H.
  - symmetry. exact (zeros_count8 L2 H).
  - destruct L2 as [| b L2].
    + symmetry in H. exact (zeros_count8 (a :: L1) H).
    + cbn [Str_app] in H. injection H as Hab Ht. subst b. cbn [count1]. rewrite (IH L2 Ht). reflexivity.
Qed.

Lemma multistep_evstep8 : forall (tm : TM) n c c', c -[ tm ]->> n / c' -> c -[ tm ]->* c'.
Proof. intros tm n c c' H. induction H as [c | n c c' c'' Hs _ IH]; [apply evstep_refl | eapply evstep_step; eassumption]. Qed.

Lemma evstep_multistep8 : forall (tm : TM) c c', c -[ tm ]->* c' -> exists n, c -[ tm ]->> n / c'.
Proof.
  intros tm c c' H. induction H as [c | c c' c'' Hs _ [n IH]].
  - exists 0%nat. apply multistep_0.
  - exists (S n). eapply multistep_S; eassumption.
Qed.

Print Assumptions halted_unique8.
Print Assumptions side_count8.
