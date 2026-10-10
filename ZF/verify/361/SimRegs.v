(** * SimRegs: the register operations 1.sel / 1.inc / 1.decnz of the ZF machine on symbolic
    register files, from the operation's first state to the IP-arithmetic state 6.break.k.

    Conventions (SimBase.v): [zc q l r] = state [q], head on the first cell of [r], [l] is the
    left side read leftwards; [zl q l r] = head on the first cell of [l].  A register of value [v]
    is [1^(v+1)]; [sepsR vs] = each register preceded by a single 0 separator.  The extra
    [false] before a register (a "00") marks the selected register.  The first cell of each
    right list below is the cell where the chain left the head (it becomes the temporary
    marker 1 and is erased again by 2.ret1 / 2.ret2). *)

From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From ZF Require Import RM ZF2Dag ZFTM SimBase SimOps.
Import ListNotations.

(** ** Helper loops *)

Lemma sepsL_rev_cons b B : sepsL (rev (b :: B)) = sepsL (rev B) ++ ones (S b) ++ [false].
Proof. simpl rev. rewrite sepsL_app. f_equal. unfold sepsL. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma sepsR_snoc C : sepsR C ++ [false] = false :: sepsL C.
Proof.
  induction C as [|c C IH]; [reflexivity|].
  rewrite sepsR_cons, sepsL_cons. simpl. rewrite <- app_assoc, IH. reflexivity.
Qed.

Lemma sepsL_one v : sepsL [v] = ones (S v) ++ [false].
Proof. unfold sepsL. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma selC B l X :
  zc QSelC l (sepsR B ++ false :: false :: X) -->+ zc QSelE (sepsL (rev B) ++ l) (false :: false :: X).
Proof.
  revert l. induction B as [|b B IH]; intros l.
  - cbn. zrun.
  - rewrite sepsR_cons. lnorm.
    eapply progress_step; [apply zR; reflexivity|].
    eapply progress_step; [apply zR; reflexivity|].
    eapply evstep_progress_trans; [apply scanR; reflexivity|].
    rewrite sepsL_rev_cons.
    replace ((sepsL (rev B) ++ ones (S b) ++ [false]) ++ l) with (sepsL (rev B) ++ ones b ++ true :: false :: l).
    + apply IH.
    + rewrite <- !app_assoc. simpl. rewrite rep_comm. reflexivity.
Qed.

Lemma selB b B l X :
  zc QSelB l (sepsR (b :: B) ++ false :: false :: X) -->+
  zc QSelE (sepsL (rev (b :: B)) ++ l) (false :: false :: X).
Proof.
  rewrite sepsR_cons. lnorm.
  eapply progress_step; [apply zR; reflexivity|].
  eapply progress_step; [apply zR; reflexivity|].
  eapply evstep_progress_trans; [apply scanR; reflexivity|].
  rewrite sepsL_rev_cons.
  replace ((sepsL (rev B) ++ ones (S b) ++ [false]) ++ l) with (sepsL (rev B) ++ ones b ++ true :: false :: l).
  + apply selC.
  + rewrite <- !app_assoc. simpl. rewrite rep_comm. reflexivity.
Qed.

Lemma incC B l X :
  zc QIncC l (sepsR B ++ false :: false :: X) -->+ zc QRet1 (sepsL (rev B) ++ l) (false :: true :: X).
Proof.
  revert l. induction B as [|b B IH]; intros l.
  - cbn. zrun.
  - rewrite sepsR_cons. lnorm.
    eapply progress_step; [apply zR; reflexivity|].
    eapply progress_step; [apply zR; reflexivity|].
    eapply evstep_progress_trans; [apply scanR; reflexivity|].
    rewrite sepsL_rev_cons.
    replace ((sepsL (rev B) ++ ones (S b) ++ [false]) ++ l) with (sepsL (rev B) ++ ones b ++ true :: false :: l).
    + apply IH.
    + rewrite <- !app_assoc. simpl. rewrite rep_comm. reflexivity.
Qed.

Lemma incB b B l X :
  zc QIncB l (sepsR (b :: B) ++ false :: false :: X) -->+
  zc QRet1 (sepsL (rev (b :: B)) ++ l) (false :: true :: X).
Proof.
  rewrite sepsR_cons. lnorm.
  eapply progress_step; [apply zR; reflexivity|].
  eapply progress_step; [apply zR; reflexivity|].
  eapply evstep_progress_trans; [apply scanR; reflexivity|].
  rewrite sepsL_rev_cons.
  replace ((sepsL (rev B) ++ ones (S b) ++ [false]) ++ l) with (sepsL (rev B) ++ ones b ++ true :: false :: l).
  + apply incC.
  + rewrite <- !app_assoc. simpl. rewrite rep_comm. reflexivity.
Qed.

Lemma decC n B l X :
  zc QDecC l (ones n ++ sepsR B ++ false :: false :: X) -->+
  zc QDecE (false :: sepsL (rev B) ++ ones (S n) ++ l) X.
Proof.
  revert n l. induction B as [|b B IH]; intros n l.
  - eapply evstep_progress_trans; [apply scanR; reflexivity|].
    cbn [sepsR sepsL rev flat_map app].
    eapply progress_step; [apply zR; reflexivity|].
    apply progress_base. apply zR. reflexivity.
  - eapply evstep_progress_trans; [apply scanR; reflexivity|].
    rewrite sepsR_cons. lnorm.
    eapply progress_step; [apply zR; reflexivity|].
    eapply progress_step; [apply zR; reflexivity|].
    rewrite sepsL_rev_cons, <- !app_assoc. apply IH.
Qed.

Lemma decE m n k lft rest : m + n = S (S k) ->
  zc QDecE (ones m ++ lft) (ones n ++ false :: rest) -->+
  zc QDecI (true :: false :: ones (S k) ++ lft) rest.
Proof.
  intros H. eapply evstep_progress_trans; [apply scanR; reflexivity|].
  rewrite app_assoc, <- rep_add, Nat.add_comm, H.
  cbn [repeat app].
  zrun.
Qed.

Lemma decLoop C L Z :
  zc QDecI (true :: false :: L) (sepsL C ++ false :: Z) -->+
  zl QRet1 (false :: sepsL (rev C) ++ L) (false :: false :: Z).
Proof.
  revert L. induction C as [|c C IH]; intros L.
  - cbn [sepsL rev flat_map app]. zrun.
  - rewrite sepsL_cons. lnorm.
    eapply progress_step; [apply zR; reflexivity|].
    eapply progress_trans; [apply (decE 2 c c (false :: L)); lia|].
    rewrite sepsL_rev_cons, <- !app_assoc. apply IH.
Qed.

Lemma decB A l X : A <> [] ->
  zc QDecB l (sepsR A ++ false :: false :: X) -->+ zc QDecE (false :: sepsL (rev A) ++ false :: l) X.
Proof.
  intros HA. destruct A as [|a A]; [congruence|].
  rewrite sepsR_cons. lnorm.
  eapply progress_step; [apply zR; reflexivity|].
  eapply progress_step; [apply zR; reflexivity|].
  rewrite sepsL_rev_cons, <- !app_assoc. apply decC.
Qed.

Lemma decStart Lft z A X : A <> [] ->
  zc QDec Lft (false :: zeros z ++ sepsR A ++ false :: false :: X) -->+
  zc QDecE (false :: sepsL (rev A) ++ zeros (S z) ++ true :: Lft) X.
Proof.
  intros HA.
  eapply progress_step; [apply zR; reflexivity|].
  eapply evstep_progress_trans; [apply scanR; reflexivity|].
  apply decB, HA.
Qed.


(** 1.sel: the selector moves one register to the left. *)
Lemma sel_op Lft z A v X : 1 <= z ->
  zc QSel Lft (false :: zeros z ++ sepsR (A ++ [v]) ++ false :: false :: X) -->+
  zl (Brk 0) Lft (false :: zeros z ++ sepsR A ++ false :: false :: ones (S v) ++ false :: X).
Proof.
  intros Hz. destruct z as [|m]; [lia|].
  assert (E : exists b B, A ++ [v] = b :: B) by (destruct A; simpl; eauto).
  destruct E as [b [B E]].
  eapply progress_step; [apply zR; reflexivity|].
  eapply evstep_progress_trans; [apply scanR; reflexivity|].
  rewrite E. eapply progress_trans; [apply selB|]. rewrite <- E.
  rewrite rev_app_distr. change (rev [v] ++ rev A) with (v :: rev A).
  rewrite sepsL_cons. lnorm.
  eapply progress_step; [apply zL; reflexivity|].
  eapply evstep_progress_trans; [apply (scanL QSelF true (S v)); reflexivity|].
  rewrite zl_cons. cbn [repeat app].
  eapply progress_step; [apply zR; reflexivity|].
  eapply progress_step; [apply zL; reflexivity|].
  rewrite zl_cons.
  eapply progress_evstep_trans; [apply ret1|]. apply ev_eq.
  rewrite rev_sepsL, rev_involutive, rep_comm. reflexivity.
Qed.

(** 1.inc: increment the selected register, remove the selector. *)
Lemma inc_op Lft z A v Y : 1 <= z -> A <> [] ->
  zc QInc Lft (false :: zeros z ++ sepsR A ++ false :: false :: ones (S v) ++ Y) -->+
  zl (Brk 0) Lft (false :: zeros z ++ sepsR A ++ false :: ones (S (S v)) ++ Y).
Proof.
  intros Hz HA. destruct z as [|m]; [lia|]. destruct A as [|a A]; [congruence|].
  eapply progress_step; [apply zR; reflexivity|].
  eapply evstep_progress_trans; [apply scanR; reflexivity|].
  eapply progress_trans; [apply incB|].
  eapply progress_evstep_trans; [apply ret1|]. apply ev_eq.
  rewrite rev_sepsL, rev_involutive. reflexivity.
Qed.

(** 1.decnz on a positive register: decrement, remove the selector, the registers left of it
    move one cell right (the gap grows by one). *)
Lemma dec_pos_op Lft z A v C : A <> [] ->
  zc QDec Lft (false :: zeros z ++ sepsR A ++ false :: false :: ones (S (S v)) ++ sepsR C) -->+
  zl (Brk 0) Lft (false :: zeros (S z) ++ sepsR (A ++ v :: C)).
Proof.
  intros HA.
  rewrite <- (zc_padr QDec Lft _ 2), <- (zl_padr (Brk 0) Lft _ 3). lnorm.
  replace (sepsR C ++ zeros 2) with (false :: sepsL C ++ [false])
    by (change (zeros 2) with ([false] ++ [false]); rewrite app_assoc, sepsR_snoc; reflexivity).
  eapply progress_trans; [apply decStart; exact HA|].
  eapply progress_trans; [apply (decE 0 (S (S v)) v); reflexivity|].
  eapply progress_trans; [apply decLoop|].
  rewrite zl_cons.
  replace (sepsL (rev C) ++ ones (S v) ++ false :: sepsL (rev A) ++ zeros (S z) ++ true :: Lft)
    with (sepsL (rev (A ++ v :: C)) ++ zeros (S z) ++ true :: Lft).
  2: { rewrite rev_app_distr. cbn [rev]. rewrite !sepsL_app, sepsL_one. lnorm. reflexivity. }
  eapply progress_evstep_trans; [apply ret1|]. apply ev_eq.
  rewrite rev_sepsL, rev_involutive. lnorm. reflexivity.
Qed.

(** 1.decnz on a zero register: same shift, then 2.ret2 -> 6.break.1. *)
Lemma dec_zero_op Lft z A C : A <> [] ->
  zc QDec Lft (false :: zeros z ++ sepsR A ++ false :: false :: true :: sepsR C) -->+
  zl (Brk 1) Lft (false :: zeros (S z) ++ sepsR (A ++ 0 :: C)).
Proof.
  intros HA.
  rewrite <- (zc_padr QDec Lft _ 1), <- (zl_padr (Brk 1) Lft _ 1).
  rewrite sepsR_app, sepsR_cons. lnorm.
  replace (sepsR C ++ zeros 1) with (false :: sepsL C) by (symmetry; apply sepsR_snoc).
  eapply progress_trans; [apply decStart; exact HA|].
  eapply progress_step; [apply zR; reflexivity|].
  eapply progress_step; [apply zL; reflexivity|]. rewrite zl_cons.
  eapply progress_step; [apply zL; reflexivity|]. rewrite zl_cons.
  eapply progress_step; [apply zL; reflexivity|].
  replace (sepsR A) with (rev (sepsL (rev A))) by (rewrite rev_sepsL, rev_involutive; reflexivity).
  destruct (rev A) as [|a B] eqn:E.
  { apply (f_equal (@rev nat)) in E. rewrite rev_involutive in E. simpl in E. congruence. }
  rewrite sepsL_cons. lnorm.
  eapply evstep_progress_trans; [apply (scanL QRet2 true (S a)); reflexivity|].
  rewrite zl_cons.
  eapply progress_evstep_trans; [apply ret2|]. apply ev_eq.
  simpl rev. rewrite rev_app_distr. simpl rev. rewrite rev_ones. lnorm.
  rewrite rep_comm. reflexivity.
Qed.
