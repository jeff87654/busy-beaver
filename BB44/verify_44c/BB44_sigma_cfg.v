(** * BB44_sigma_cfg: the score of Argon's BB(4,4) machine 44-C 1RB3LB1RZ2RA_1LC3RB1LD2RA_3RB2LC1LC3LC_3RB1LB3LD2RD
    read off its halting configuration by a Coq theorem (no inspection step).

    Depends on argon_scout/M44 (logical root Local): BB44, Individual44, BB44_rules, BB44_run, unchanged.
    BB44_run proves c0 -->* c_final, halted tm c_final, and defines sigma = 2 M44_final + 2 g30 + 4 together with
    a list final_cells of that length; the link between final_cells and the tape of c_final was by inspection.

    Here, with [nonzero_cells c N] := "the tape of c is a finite word padded with blanks, with N nonzero cells":
      Theorem c_final_nonzero : nonzero_cells c_final sigma.
      Theorem nonzero_cells_unique : nonzero_cells c N -> nonzero_cells c N' -> N = N'.
      Theorem c_final_head : c_final = (A, (l, S2, r)) for some l r, and tm (A, S2) = None.
    The machine string's halting transition A2 is 1RZ: it overwrites the scanned 2 (nonzero) by 1 (nonzero), so
    the number of nonzero cells after the halting write is the same N = sigma.
      Corollary sigma_is_score : exists c, c0 -->* c /\ halted tm c /\ nonzero_cells c sigma /\
                                  (forall N, nonzero_cells c N -> N = sigma). *)

From Local Require Import Individual44 BB44_rules BB44_run.
From Coq Require Import Lia PeanoNat List Streams.
Import ListNotations.
Set Default Goal Selector "!".
Local Open Scope nat_scope.

Definition nzv (s : sym) : nat := match s with S0 => 0 | _ => 1 end.

Fixpoint cnt (xs : list sym) : nat :=
  match xs with [] => 0 | x :: t => nzv x + cnt t end.

Definition nonzero_cells (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list sym) (s : sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = cnt L + nzv s + cnt R.

Lemma cnt_app : forall xs ys, cnt (xs ++ ys) = cnt xs + cnt ys.
Proof. induction xs as [|x xs IH]; intros ys; simpl; [reflexivity | rewrite IH; lia]. Qed.

Lemma cnt_lpow : forall (xs : list sym) n, cnt (xs ^^ n) = n * cnt xs.
Proof. intros xs n. induction n as [|n IH]; simpl; [reflexivity | rewrite cnt_app, IH; lia]. Qed.

Lemma str_cnt0 : forall L : list sym, const S0 = L *> const S0 -> cnt L = 0.
Proof.
  induction L as [|b L IH]; intros H; [reflexivity|].
  assert (Hb : S0 = b) by exact (f_equal (@Streams.hd sym) H).
  assert (Ht : const S0 = L *> const S0) by exact (f_equal (@Streams.tl sym) H).
  subst b. simpl. apply IH. exact Ht.
Qed.

Lemma str_cnt : forall L1 L2 : list sym, L1 *> const S0 = L2 *> const S0 -> cnt L1 = cnt L2.
Proof.
  induction L1 as [|a L1 IH]; intros L2 H.
  - symmetry. apply str_cnt0. exact H.
  - destruct L2 as [|b L2].
    + apply str_cnt0. symmetry. exact H.
    + assert (Hb : a = b) by exact (f_equal (@Streams.hd sym) H).
      assert (Ht : L1 *> const S0 = L2 *> const S0) by exact (f_equal (@Streams.tl sym) H).
      subst b. cbn [cnt]. rewrite (IH L2 Ht). reflexivity.
Qed.

Theorem nonzero_cells_unique : forall c N N', nonzero_cells c N -> nonzero_cells c N' -> N = N'.
Proof.
  intros c N N' (q & L & R & s & E & HN) (q' & L' & R' & s' & E' & HN').
  rewrite E in E'. injection E' as E1 E2 E3 E4. subst.
  rewrite (str_cnt _ _ E2), (str_cnt _ _ E4). reflexivity.
Qed.

Theorem c_final_nonzero : nonzero_cells c_final sigma.
Proof.
  exists A, ([S2]^^(S (2 * g30)) ++ [S3]^^(2 * M44_final + 1)), [S1], S2.
  split.
  - unfold c_final, Bcfg. rewrite Str_app_assoc. reflexivity.
  - unfold sigma. rewrite cnt_app, !cnt_lpow. cbn [cnt nzv]. lia.
Qed.

Theorem c_final_head : exists l r, c_final = (A, (l, S2, r)) /\ tm (A, S2) = None.
Proof.
  exists ([S2]^^(S (2 * g30)) *> [S3]^^(2 * M44_final + 1) *> const S0), (S1 >> const S0).
  split; reflexivity.
Qed.

Corollary sigma_is_score : exists c, c0 -->* c /\ halted tm c /\ nonzero_cells c sigma /\
  (forall N, nonzero_cells c N -> N = sigma).
Proof.
  exists c_final. split; [exact reaches_final|]. split; [exact final_halted|].
  split; [exact c_final_nonzero|].
  intros N H. exact (nonzero_cells_unique _ _ _ H c_final_nonzero).
Qed.

Print Assumptions c_final_nonzero.
Print Assumptions c_final_head.
Print Assumptions sigma_is_score.
