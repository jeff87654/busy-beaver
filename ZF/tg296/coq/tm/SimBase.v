(** * SimBase: a list-zipper view of busycoq tapes for the ZF machine, and generic scanning lemmas.

    [zc q l r] is the configuration in state [q] whose head is on the first cell of [r]
    ([r] read rightwards, [l] read leftwards from the head), both sides completed with
    blanks.  [zl q l r] has the head on the first cell of [l] instead. *)

From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From M254TGT Require Import RM DagTG ZFTM.
Import ListNotations.

Notation zeros n := (repeat false n).
Notation ones n := (repeat true n).

Definition zc (q : state) (l r : list bool) : Q * tape :=
  (q, (Str_app l (const false), hd false r, Str_app (tl r) (const false))).

Definition zl (q : state) (l r : list bool) : Q * tape := zc q (tl l) (hd false l :: r).

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** ** Single steps *)

Lemma zR q l (b : bool) r (w : bool) q' : tm (q, b) = Some (w, R, q') -> zc q l (b :: r) -[ tm ]-> zc q' (w :: l) r.
Proof. intros H. destruct r; exact (step_right H). Qed.

Lemma zL q l (b : bool) r (w : bool) q' : tm (q, b) = Some (w, L, q') -> zc q l (b :: r) -[ tm ]-> zl q' l (w :: r).
Proof. intros H. destruct l; exact (step_left H). Qed.

Lemma zl_cons q x l r : zl q (x :: l) r = zc q l (x :: r).
Proof. reflexivity. Qed.

Lemma zl_nil q r : zl q [] r = zc q [] (false :: r).
Proof. reflexivity. Qed.

Lemma zc_nil q l : zc q l [] = zc q l [false].
Proof. reflexivity. Qed.

(** ** Blank padding *)

Lemma rep_snoc {A} (x : A) n : repeat x (S n) = repeat x n ++ [x].
Proof. induction n as [|n IH]; [reflexivity|]. simpl in *. rewrite IH. reflexivity. Qed.

Lemma rep_comm {A} (x : A) n l : repeat x n ++ x :: l = x :: repeat x n ++ l.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma rep_add {A} (x : A) n m : repeat x (n + m) = repeat x n ++ repeat x m.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. reflexivity. Qed.

Lemma str_app_false l : Str_app (l ++ [false]) (const false) = Str_app l (const false).
Proof.
  induction l as [|x l IH]; simpl.
  - symmetry. apply const_unfold.
  - rewrite IH. reflexivity.
Qed.

Lemma str_app_zeros l n : Str_app (l ++ zeros n) (const false) = Str_app l (const false).
Proof.
  induction n as [|n IH].
  - rewrite app_nil_r. reflexivity.
  - rewrite rep_snoc, app_assoc, str_app_false. exact IH.
Qed.

Lemma zc_padl q l r n : zc q (l ++ zeros n) r = zc q l r.
Proof. unfold zc. rewrite str_app_zeros. reflexivity. Qed.

Lemma zc_padr q l r n : zc q l (r ++ zeros n) = zc q l r.
Proof.
  unfold zc. destruct r as [|x r].
  - destruct n as [|n]; [reflexivity|]. simpl.
    rewrite <- (app_nil_l (zeros n)), str_app_zeros. reflexivity.
  - simpl. rewrite str_app_zeros. reflexivity.
Qed.

Lemma zl_padl q l r n : zl q (l ++ zeros n) r = zl q l r.
Proof.
  unfold zl. destruct l as [|x l].
  - destruct n as [|n]; [reflexivity|]. simpl. apply (zc_padl q [] _ n).
  - simpl. apply zc_padl.
Qed.

Lemma zl_padr q l r n : zl q l (r ++ zeros n) = zl q l r.
Proof. unfold zl. rewrite app_comm_cons. apply zc_padr. Qed.

Lemma ev_eq c c' : c = c' -> c -->* c'.
Proof. intros ->. apply evstep_refl. Qed.

(** ** Stepping tactic.  [zstep] performs one step of a goal [zc q l (b :: r) -->* _] (or [-->+])
    when [tm (q, b)] computes. *)
Ltac zstep :=
  lazymatch goal with
  | |- zl _ _ _ -[ tm ]->* _ => unfold zl; cbn [List.hd List.tl]
  | |- zl _ _ _ -[ tm ]->+ _ => unfold zl; cbn [List.hd List.tl]
  | |- zc ?q ?l [] -[ tm ]->* _ => rewrite (zc_nil q l)
  | |- zc ?q ?l [] -[ tm ]->+ _ => rewrite (zc_nil q l)
  | |- zc _ _ (_ :: _) -[ tm ]->* _ =>
      eapply evstep_step; [ first [ apply zR; reflexivity | apply zL; reflexivity ] | ]
  | |- zc _ _ (_ :: _) -[ tm ]->+ _ =>
      eapply progress_intro; [ first [ apply zR; reflexivity | apply zL; reflexivity ] | ]
  end.

(* normalize list expressions: right-associate appends, push conses out *)
Ltac lnorm := repeat (rewrite <- app_assoc || rewrite <- app_comm_cons); cbn [app].
Ltac lnorm_in H := repeat (rewrite <- app_assoc in H || rewrite <- app_comm_cons in H); cbn [app] in H.

Ltac zfinish := first [ apply evstep_refl | apply ev_eq; reflexivity ].
Ltac zrun := repeat (first [ zfinish | zstep ]).

(** ** Scanning runs *)

Lemma scanR q (b : bool) n l r : tm (q, b) = Some (b, R, q) -> zc q l (repeat b n ++ r) -->* zc q (repeat b n ++ l) r.
Proof.
  intros H. revert l. induction n as [|n IH]; intros l; simpl.
  - apply evstep_refl.
  - eapply evstep_step; [apply zR, H|]. rewrite <- rep_comm. apply IH.
Qed.

Lemma scanL q (b : bool) n l r : tm (q, b) = Some (b, L, q) -> zl q (repeat b n ++ l) r -->* zl q l (repeat b n ++ r).
Proof.
  intros H. revert r. induction n as [|n IH]; intros r; simpl.
  - apply evstep_refl.
  - rewrite zl_cons. eapply evstep_step; [apply zL, H|].
    rewrite <- rep_comm. apply IH.
Qed.

(** ** Register-file encodings.  A register of value [v] is [1^(v+1)]; [sepsR vs] lists the
    registers left to right, each preceded by its single-0 separator; [sepsL vs] is the same
    seen leftwards (each register followed by its separator), so [rev (sepsR vs) = sepsL (rev vs)]. *)
Definition sepsR (vs : list nat) : list bool := flat_map (fun v => false :: ones (S v)) vs.
Definition sepsL (vs : list nat) : list bool := flat_map (fun v => ones (S v) ++ [false]) vs.

Lemma rev_ones n : rev (ones n) = ones n.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. symmetry. apply (rep_snoc true n). Qed.

Lemma rev_zeros n : rev (zeros n) = zeros n.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. symmetry. apply (rep_snoc false n). Qed.

Lemma sepsR_app A B : sepsR (A ++ B) = sepsR A ++ sepsR B.
Proof. unfold sepsR. apply flat_map_app. Qed.

Lemma sepsL_app A B : sepsL (A ++ B) = sepsL A ++ sepsL B.
Proof. unfold sepsL. apply flat_map_app. Qed.

Lemma rev_sepsR vs : rev (sepsR vs) = sepsL (rev vs).
Proof.
  induction vs as [|v vs IH]; [reflexivity|].
  change (sepsR (v :: vs)) with ((false :: ones (S v)) ++ sepsR vs).
  rewrite rev_app_distr, IH.
  change (rev (false :: ones (S v))) with (rev (ones (S v)) ++ [false]).
  rewrite rev_ones. change (rev (v :: vs)) with (rev vs ++ [v]).
  rewrite sepsL_app. f_equal. unfold sepsL. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma rev_sepsL vs : rev (sepsL vs) = sepsR (rev vs).
Proof.
  rewrite <- (rev_involutive vs) at 1. rewrite <- rev_sepsR. apply rev_involutive.
Qed.

(** ** Zero runs: [nz c U] holds when walking [U] (nearest first) with [c] zeros already
    counted never reaches 8 consecutive zeros (the dispatch scan's turning condition). *)
Fixpoint nz (c : nat) (U : list bool) : bool :=
  match U with
  | [] => true
  | true :: U => nz 0 U
  | false :: U => andb (Nat.ltb c 7) (nz (S c) U)
  end.
