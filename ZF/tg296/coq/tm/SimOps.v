(** * SimOps: the framework routines of the ZF machine on symbolic tapes
    (register chains, 1.sel / 1.inc / 1.decnz with the return scans 2.ret1 / 2.ret2). *)

From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From M254TGT Require Import RM DagTG ZFTM SimBase.
Import ListNotations.

Lemma sepsL_cons v B : sepsL (v :: B) = true :: ones v ++ false :: sepsL B.
Proof. unfold sepsL. simpl. rewrite <- app_assoc. reflexivity. Qed.

Lemma sepsR_cons v B : sepsR (v :: B) = false :: true :: ones v ++ sepsR B.
Proof. reflexivity. Qed.

(** ** Transitions of the parametrized states *)

Lemma tm_RInc_S r : r <= 7 -> tm (RInc (S r), true) = Some (true, R, RInc r).
Proof. intros H. unfold RInc. cbn - [bmk bval]. rewrite bval_bmk by lia. reflexivity. Qed.

Lemma tm_RInc_0 : tm (RInc 0, true) = Some (true, R, QInc).
Proof. reflexivity. Qed.

Lemma tm_RDec_S r : r <= 7 -> tm (RDec (S r), true) = Some (true, R, RDec r).
Proof. intros H. unfold RDec. cbn - [bmk bval]. rewrite bval_bmk by lia. reflexivity. Qed.

Lemma tm_RDec_0 : tm (RDec 0, true) = Some (true, R, QDec).
Proof. reflexivity. Qed.

(** ** Register chains: [3.<reg r>.inc] reads up to [r+1] ones. *)

Lemma chain_sel_inc r j lft X : r <= 8 -> j <= r ->
  zc (RInc r) lft (ones j ++ false :: X) -->+ zc QSel (false :: ones j ++ lft) X.
Proof.
  revert r lft. induction j as [|j IH]; intros r lft Hr Hj.
  - apply progress_base. apply zR. reflexivity.
  - destruct r as [|r]; [lia|]. simpl.
    eapply progress_step; [apply zR, tm_RInc_S; lia|].
    rewrite <- (rep_comm true j lft). apply (IH r (true :: lft)); lia.
Qed.

Lemma chain_sel_dec r j lft X : r <= 8 -> j <= r ->
  zc (RDec r) lft (ones j ++ false :: X) -->+ zc QSel (false :: ones j ++ lft) X.
Proof.
  revert r lft. induction j as [|j IH]; intros r lft Hr Hj.
  - apply progress_base. apply zR. reflexivity.
  - destruct r as [|r]; [lia|]. simpl.
    eapply progress_step; [apply zR, tm_RDec_S; lia|].
    rewrite <- (rep_comm true j lft). apply (IH r (true :: lft)); lia.
Qed.

Lemma chain_inc r lft X : r <= 8 ->
  zc (RInc r) lft (ones (S r) ++ X) -->+ zc QInc (ones (S r) ++ lft) X.
Proof.
  revert lft. induction r as [|r IH]; intros lft Hr.
  - apply progress_base. apply zR. reflexivity.
  - simpl. eapply progress_step; [apply zR, tm_RInc_S; lia|].
    rewrite <- (rep_comm true r lft). apply (IH (true :: lft)); lia.
Qed.

Lemma chain_dec r lft X : r <= 8 ->
  zc (RDec r) lft (ones (S r) ++ X) -->+ zc QDec (ones (S r) ++ lft) X.
Proof.
  revert lft. induction r as [|r IH]; intros lft Hr.
  - apply progress_base. apply zR. reflexivity.
  - simpl. eapply progress_step; [apply zR, tm_RDec_S; lia|].
    rewrite <- (rep_comm true r lft). apply (IH (true :: lft)); lia.
Qed.

(** ** The return scan 2.ret1 / 2.ret2: from a 0 cell, pass the registers [B] (leftwards),
    at least one gap zero, erase the temporary marker 1 and enter [6.break.k]. *)

Section Ret.
  Variables (r ra rb t : state).
  Hypothesis H0 : tm (r, false) = Some (false, L, ra).
  Hypothesis H1 : tm (r, true) = Some (true, L, r).
  Hypothesis Ha0 : tm (ra, false) = Some (false, L, rb).
  Hypothesis Ha1 : tm (ra, true) = Some (true, L, r).
  Hypothesis Hb0 : tm (rb, false) = Some (false, L, rb).
  Hypothesis Hb1 : tm (rb, true) = Some (false, L, t).

  Lemma ret_gen B m Lft Y :
    zc r (sepsL B ++ zeros (S m) ++ true :: Lft) (false :: Y) -->+
    zl t Lft (false :: zeros (S m) ++ rev (sepsL B) ++ false :: Y).
  Proof.
    revert Y. induction B as [|v B IH]; intros Y.
    - simpl.
      eapply progress_step; [apply zL, H0|]. rewrite zl_cons.
      eapply progress_step; [apply zL, Ha0|].
      eapply evstep_progress_trans; [apply scanL, Hb0|]. rewrite zl_cons.
      apply progress_base. rewrite <- (rep_comm false m (false :: Y)).
      apply zL, Hb1.
    - rewrite sepsL_cons.
      assert (E : rev (true :: ones v ++ false :: sepsL B) ++ false :: Y =
                  rev (sepsL B) ++ false :: ones v ++ true :: false :: Y).
      { simpl rev. rewrite rev_app_distr. simpl rev. rewrite rev_ones, <- !app_assoc. reflexivity. }
      rewrite E. clear E.
      lnorm.
      eapply progress_step; [apply zL, H0|]. rewrite zl_cons.
      eapply evstep_progress_trans.
      { eapply evstep_step; [apply zL, Ha1|]. apply scanL, H1. }
      rewrite zl_cons. apply IH.
  Qed.
End Ret.

Lemma ret1 B m Lft Y :
  zc QRet1 (sepsL B ++ zeros (S m) ++ true :: Lft) (false :: Y) -->+
  zl (Brk 0) Lft (false :: zeros (S m) ++ rev (sepsL B) ++ false :: Y).
Proof. apply ret_gen with QRet1a QRet1b; reflexivity. Qed.

Lemma ret2 B m Lft Y :
  zc QRet2 (sepsL B ++ zeros (S m) ++ true :: Lft) (false :: Y) -->+
  zl (Brk 1) Lft (false :: zeros (S m) ++ rev (sepsL B) ++ false :: Y).
Proof. apply ret_gen with QRet2a QRet2b; reflexivity. Qed.
