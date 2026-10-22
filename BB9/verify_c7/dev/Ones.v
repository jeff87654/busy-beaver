(** * Ones.v : the ones count of an X' configuration (BB9/verify_c7).

    sym_val / count1 / ones: verbatim copies of ../verify_f3/k31/K31_Abs.v (themselves verbatim copies of
    BB9_fw2_bound.ones / count1), over XL.Individual112 (X' configurations Q * tape). *)
From XL Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(** ** Counting ones *)
Definition sym_val (s : Sym) : nat :=
  match s with
  | S0 => 0
  | S1 => 1
  end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with
  | [] => 0
  | x :: t => sym_val x + count1 t
  end.

Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl; [reflexivity | rewrite IHxs; lia]. Qed.
