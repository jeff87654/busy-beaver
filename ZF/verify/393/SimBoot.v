(** * SimBoot: the boot phase of the ZF machine (39773 steps), by certified computation. *)

From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From ZF Require Import RM ZF2Dag ZFTM SimBase.
Import ListNotations.

(* the register file written by boot: (01)^132 011 (01)^68 *)
Definition boot_regs : list nat := repeat 0 132 ++ 1 :: repeat 0 68.

(** ** A computable step on list zippers [(q, l, r)], mirroring [zc q l r]. *)
Definition lconf := (state * list bool * list bool)%type.

Definition lstep (s : lconf) : option lconf :=
  let '(q, l, r) := s in
  match tm (q, hd false r) with
  | None => None
  | Some (w, R, q') => Some (q', w :: l, tl r)
  | Some (w, L, q') => Some (q', tl l, hd false l :: w :: tl r)
  end.

Fixpoint lrun (n : nat) (s : lconf) : option lconf :=
  match n with
  | 0 => Some s
  | S n => match lstep s with None => None | Some s' => lrun n s' end
  end.

Lemma lstep_sound q l r q' l' r' :
  lstep (q, l, r) = Some (q', l', r') -> zc q l r -[ tm ]-> zc q' l' r'.
Proof.
  unfold lstep. intros H.
  assert (E : zc q l r = zc q l (hd false r :: tl r)) by (destruct r; reflexivity).
  rewrite E. clear E.
  destruct (tm (q, hd false r)) as [[[w [|]] q1]|] eqn:T; [| |discriminate];
    injection H as <- <- <-.
  - apply zL. exact T.
  - apply zR. exact T.
Qed.

Lemma lrun_sound n q l r q' l' r' :
  lrun n (q, l, r) = Some (q', l', r') -> zc q l r -->* zc q' l' r'.
Proof.
  revert q l r. induction n as [|n IH]; intros q l r H; cbn [lrun] in H.
  - injection H as <- <- <-. apply evstep_refl.
  - destruct (lstep (q, l, r)) as [[[q1 l1] r1]|] eqn:S1; [|discriminate].
    eapply evstep_step; [apply lstep_sound, S1|]. apply IH, H.
Qed.

(** ** Trailing blanks *)
Fixpoint dropf (l : list bool) : list bool :=
  match l with false :: l => dropf l | _ => l end.
Definition trim (l : list bool) : list bool := rev (dropf (rev l)).

Lemma dropf_spec l : exists n, l = zeros n ++ dropf l.
Proof.
  induction l as [|[|] l IH]; [exists 0; reflexivity | exists 0; reflexivity|].
  destruct IH as [n E]. exists (S n). simpl. rewrite <- E. reflexivity.
Qed.

Lemma trim_spec l : exists n, l = trim l ++ zeros n.
Proof.
  destruct (dropf_spec (rev l)) as [n E]. exists n. unfold trim.
  rewrite <- rev_zeros, <- rev_app_distr, <- E. symmetry. apply rev_involutive.
Qed.

Lemma zc_trim q l r : zc q l r = zc q (trim l) (trim r).
Proof.
  destruct (trim_spec l) as [n El]. destruct (trim_spec r) as [m Er].
  rewrite El at 1. rewrite Er at 1. rewrite zc_padl, zc_padr. reflexivity.
Qed.

(** ** The certified boot run *)
Local Set Warnings "-abstract-large-number".
Definition boot_steps := 39773.

Definition boot_ok : bool :=
  match lrun boot_steps (QBootA, [], []) with
  | Some (q, l, r) =>
      andb (if state_eq_dec q (Node 0) then true else false)
        (andb (if list_eq_dec bool_dec (trim l) [true] then true else false)
              (if list_eq_dec bool_dec (trim r) (trim (zeros 18 ++ sepsR boot_regs)) then true else false))
  | None => false
  end.

Lemma boot_ok_true : boot_ok = true.
Proof. vm_compute. reflexivity. Qed.

(** After boot the machine is at the first dispatch: state main().0 (= [Node 0]), head on the
    first IP cell, the IP marker 1 to its left, all-zero IP, then the register file. *)
Theorem boot : c0 -->* zc (Node 0) [true] (zeros 18 ++ sepsR boot_regs).
Proof.
  pose proof boot_ok_true as H. unfold boot_ok in H.
  destruct (lrun boot_steps (QBootA, [], [])) as [[[q l] r]|] eqn:E; [|discriminate].
  destruct (state_eq_dec q (Node 0)) as [Hq|]; [|discriminate].
  destruct (list_eq_dec bool_dec (trim l) [true]) as [Hl|]; [|discriminate].
  destruct (list_eq_dec bool_dec (trim r) (trim (zeros 18 ++ sepsR boot_regs))) as [Hr|];
    [|discriminate].
  apply lrun_sound in E.
  change c0 with (zc QBootA [] []).
  rewrite (zc_trim q l r), Hq, Hl, Hr in E.
  rewrite (zc_trim (Node 0) [true]). exact E.
Qed.
