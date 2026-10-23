From BB7 Require Import Individual72.
From BB7 Require Export Defs.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB0RG_1RC1RB_0RD---_0LE0LD_0LF1LE_1RA1LF_1LC0RB *)
(* the table tm232 is in Defs.v *)
Notation tm := tm232 (only parsing).

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : Sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof. intros. rewrite const_unfold at 1. apply align_lpow. Qed.

Ltac align_tape := repeat ((rewrite align_lpow || rewrite align_lpow_const); simpl app).
Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
Ltac finish_norm := apply evstep_refl'; norm_nat; align_tape; try reflexivity; lia_refl.
Ltac ex := repeat (try solve [finish_norm]; step).

(** crossings *)
Lemma crB : forall n l r, l {{B}}> [1]^^n *> r -->* [1]^^n *> l {{B}}> r.
Proof. induction n; intros. - finish. - step. follow IHn. finish_norm. Qed.

Lemma crE : forall n l r, [1]^^n *> l <{{E}} r -->* l <{{E}} [1]^^n *> r.
Proof. induction n; intros. - finish. - step. follow IHn. finish_norm. Qed.

Lemma crF : forall n l r, [1]^^n *> l <{{F}} r -->* l <{{F}} [1]^^n *> r.
Proof. induction n; intros. - finish. - step. follow IHn. finish_norm. Qed.

(** mini-cycle: one 1 moves from the a-block to the b-block (+3) *)
Lemma MC : forall p r,
  const 0 {{E}}> 0 >> [1]^^p *> 0 >> 0 >> 1 >> r -->+ const 0 {{E}}> 0 >> [1]^^(3 + p) *> 0 >> 0 >> r.
Proof.
  intros. eapply progress_intro; [prove_step | simpl_tape]. ex.
  follow crB. ex. follow crE. ex.
Qed.
