(** * Uniq.v : the halting configuration and its ones count are unique.
    tm is deterministic, so at most one halted configuration is reachable from c0; and [ones c N] (K31_Abs.ones =
    BB9_fw2_bound.ones verbatim) determines N, because padding a tape list with blanks does not change its count.
    Also: the exact ones count of the shared halting tape K31_End.Hc. *)
From BB8 Require Import Individual92.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".
From Dev Require Import Base Abs Step.
From K31 Require Import K31_Abs K31_Mach K31_End.

Theorem halted_unique : forall c c1 c2, c -->* c1 -> c -->* c2 -> halted tm c1 -> halted tm c2 -> c1 = c2.
Proof.
  intros c c1 c2 H1. revert c2. induction H1 as [c | c c' c1 Hs H1 IH]; intros c2 H2 Hh1 Hh2.
  - inversion H2 as [| ? c'' ? Hs' H2']; subst; [reflexivity |].
    exfalso. exact (halted_no_step _ _ _ Hh1 Hs').
  - inversion H2 as [| ? c'' ? Hs' H2']; subst.
    + exfalso. exact (halted_no_step _ _ _ Hh2 Hs).
    + pose proof (step_deterministic _ _ _ _ Hs Hs') as E. subst c''. apply IH; assumption.
Qed.

Lemma zeros_count : forall L : list Sym, const S0 = L *> const S0 -> count1 L = 0%nat.
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

(** ** The halting tape Hc, counted exactly *)
Lemma count1_encl_cons : forall d G, count1 (encl (d :: G)) = 1 + d + count1 (encl G).
Proof.
  intros d G. cbn [encl count1 sym_val]. rewrite count1_app, count1_pow. cbn [count1 sym_val]. lia.
Qed.

Definition Hc_N (d s : nat) (G : list nat) (Ll : list Sym) (R n t : nat) : nat :=
  d + s + count1 (encl G) + count1 Ll + 6 * R + 2 * n + 4 * t + 15.

Lemma Hc_ones_exact : forall d s G Ll R n t, ones (Hc d s G (Ll *> const 0) R n t) (Hc_N d s G Ll R n t).
Proof.
  intros d s G Ll R n t.
  set (Lw := [0;1]^^d ++ [1] ++ [0;1]^^s ++ encl G ++ [1] ++ Ll).
  set (Rw := [1;1;1;1;0;1;0;1;0] ++ [1;0;1;0;1;0;1;0;1;0;1;0]^^R ++ [0;1;0;1;1;0;1;1] ++ [0;1;1]^^n ++
             [1;1;0;0;1;0;0;1]^^t ++ [0;1]).
  exists H, Lw, Rw, 1. split.
  - unfold Hc, HR, Lw, Rw. rewrite lftx_encl. rewrite !Str_app_assoc. reflexivity.
  - unfold Hc_N, Lw, Rw. rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

(** Any count of an Hc tape is the exact one. *)
Lemma Hc_count : forall d s G Ll R n t N, ones (Hc d s G (Ll *> const 0) R n t) N -> N = Hc_N d s G Ll R n t.
Proof. intros. eapply ones_unique; [eassumption | apply Hc_ones_exact]. Qed.

Print Assumptions halted_unique.
Print Assumptions ones_unique.
Print Assumptions Hc_ones_exact.
