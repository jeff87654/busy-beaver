(** * SimIP: IP arithmetic of the ZF machine on symbolic tapes: the dispatch scan
    (6.continue.0 / 4.dispatch.* / 5.root back to main().0), 6.break.k and 6.continue.k.

    The IP sits right of the marker 1; the routines run with the head inside the IP, the IP
    (as a list read leftwards from the head) being [U] and the marker the [true] after it. *)

From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From M254TGT Require Import RM DagTG ZFTM SimBase.
Import ListNotations.

(** ** Zero runs *)
Lemma nz_mono c U : nz (S c) U = true -> nz c U = true.
Proof.
  revert c. induction U as [|[|] U IH]; intros c H; simpl in *; auto.
  apply andb_prop in H as [H1 H2]. apply Nat.ltb_lt in H1.
  apply andb_true_intro. split; [apply Nat.ltb_lt; lia | auto].
Qed.

Lemma nz_tail x U : nz 0 (x :: U) = true -> nz 0 U = true.
Proof.
  destruct x; simpl; [auto|]. apply nz_mono.
Qed.

Lemma nz_ones n U : nz 0 (ones n ++ U) = nz 0 U.
Proof. destruct n as [|n]; [reflexivity|]. induction n as [|n IH]; simpl in *; auto. Qed.

(** ** Transitions of the parametrized IP states *)

(* the dispatch counter: [c] zeros seen so far *)
Definition cs (c : nat) : state := match c with 0 => Cont 0 | S i => Disp i end.

Lemma tm_cs_1 c : c <= 7 -> tm (cs c, true) = Some (true, L, Cont 0).
Proof.
  intros H. do 8 (destruct c as [|c]; [reflexivity|]). lia.
Qed.

Lemma tm_cs_0 c : c < 7 -> tm (cs c, false) = Some (false, L, cs (S c)).
Proof.
  intros H. do 7 (destruct c as [|c]; [reflexivity|]). lia.
Qed.

Lemma tm_brk_1 k : tm (Brk k, true) = Some (false, L, Brk k).
Proof. reflexivity. Qed.

Lemma tm_brk_S k : k <= 0 -> tm (Brk (S k), false) = Some (false, L, Brk k).
Proof. intros H. do 1 (destruct k as [|k]; [reflexivity|]). lia. Qed.

Lemma tm_cont_S1 k : k <= 3 -> tm (Cont (S k), true) = Some (false, L, Cont k).
Proof. intros H. do 4 (destruct k as [|k]; [reflexivity|]). lia. Qed.

Lemma tm_cont_S0 k : k <= 3 -> tm (Cont (S k), false) = Some (false, L, Cont (S k)).
Proof. intros H. do 4 (destruct k as [|k]; [reflexivity|]). lia. Qed.

(** ** Dispatch *)

(* overflow / escape: the new marker is just right of the head *)
Lemma disp0 Y : zl (Cont 0) [] (true :: Y) -->+ zc (Node 0) [true] Y.
Proof.
  rewrite zl_nil. zrun.
  apply ev_eq. rewrite <- (zc_padl _ [true] _ 8). reflexivity.
Qed.

Lemma disp_gen U c Y : c <= 7 -> nz c U = true ->
  zl (cs c) (U ++ [true]) Y -->+ zc (Node 0) [true] (rev U ++ Y).
Proof.
  revert c Y. induction U as [|x U IH]; intros c Y Hc Hz.
  - simpl. rewrite zl_cons.
    eapply progress_step; [apply zL, tm_cs_1, Hc|].
    rewrite zl_nil. zrun.
    apply ev_eq. rewrite <- (zc_padl _ [true] _ 8). reflexivity.
  - simpl app. rewrite zl_cons. destruct x.
    + eapply progress_step; [apply zL, tm_cs_1, Hc|].
      simpl rev. rewrite <- app_assoc. simpl app.
      apply (IH 0); [lia|]. exact Hz.
    + simpl in Hz. apply andb_prop in Hz as [Hc' Hz]. apply Nat.ltb_lt in Hc'.
      eapply progress_step; [apply zL, tm_cs_0, Hc'|].
      simpl rev. rewrite <- app_assoc. simpl app.
      apply (IH (S c)); [lia|]. exact Hz.
Qed.

Lemma disp U Y : nz 0 U = true -> zl (Cont 0) (U ++ [true]) Y -->+ zc (Node 0) [true] (rev U ++ Y).
Proof. intros H. apply (disp_gen U 0 Y); [lia | exact H]. Qed.

(** ** 6.break.k: strip [k] zeros from the right end of the IP, then increment *)

Lemma strip_rev_0 b l : strip_rev b 0 l = l.
Proof. destruct l; reflexivity. Qed.

Lemma inc_rev_length l : length (inc_rev l) = length l.
Proof. induction l as [|[|] l IH]; simpl; auto. Qed.

Lemma brk_ip U k Y : k <= 1 -> nz 0 U = true ->
  exists m, zl (Brk k) (U ++ [true]) Y -->+
            zc (Node 0) [true] (rev (inc_rev (strip_rev false k U)) ++ zeros m ++ Y) /\
            length U <= length (strip_rev false k U) + m.
Proof.
  revert k Y. induction U as [|x U IH]; intros k Y Hk Hz.
  - exists (S k). split; [|simpl; lia].
    destruct k as [|[|k]]; [| |lia]; simpl;
      rewrite <- (zc_padl (Node 0) [true] _ 8); zrun.
  - simpl app. rewrite zl_cons. pose proof (nz_tail x U Hz) as Hz'.
    destruct x; destruct k as [|k].
    + (* 1, break.0: carry *)
      destruct (IH 0 (false :: Y) Hk Hz') as [m [H Hl]]. exists m. split; [|simpl in *; lia].
      eapply progress_step; [apply zL, tm_brk_1|].
      eapply progress_evstep_trans; [exact H|]. apply ev_eq. f_equal.
      rewrite strip_rev_0. simpl. rewrite <- app_assoc. simpl. rewrite rep_comm. reflexivity.
    + (* 1, break.(k+1): strip the one *)
      destruct (IH (S k) (false :: Y) Hk Hz') as [m [H Hl]]. exists (S m). split; [|simpl in *; lia].
      eapply progress_step; [apply zL, tm_brk_1|].
      eapply progress_evstep_trans; [exact H|]. apply ev_eq. f_equal.
      simpl strip_rev. rewrite rep_comm. reflexivity.
    + (* 0, break.0: increment done *)
      exists 0. split; [|simpl; lia].
      eapply progress_step; [apply zL; reflexivity|].
      eapply progress_evstep_trans; [apply disp, Hz'|]. apply ev_eq. f_equal.
      simpl. rewrite <- app_assoc. reflexivity.
    + (* 0, break.(k+1): one zero stripped *)
      destruct (IH k (false :: Y) ltac:(lia) Hz') as [m [H Hl]]. exists (S m). split; [|simpl in *; lia].
      eapply progress_step; [apply zL, tm_brk_S; lia|].
      eapply progress_evstep_trans; [exact H|]. apply ev_eq. f_equal.
      simpl strip_rev. rewrite rep_comm. reflexivity.
Qed.

(** ** 6.continue.k: strip bits from the right end until [k] ones are removed *)

Lemma cont_ip U k Y : k <= 4 -> nz 0 U = true -> k <= count_occ bool_dec U true ->
  exists m, zl (Cont k) (U ++ [true]) Y -->+
            zc (Node 0) [true] (rev (strip_rev true k U) ++ zeros m ++ Y) /\
            length U <= length (strip_rev true k U) + m.
Proof.
  revert k Y. induction U as [|x U IH]; intros k Y Hk Hz Hc.
  - destruct k as [|k]; [|simpl in Hc; lia].
    exists 0. split; [|simpl; lia]. apply (disp [] Y Hz).
  - destruct k as [|k].
    + exists 0. rewrite strip_rev_0. split; [|simpl; lia]. apply (disp (x :: U) Y Hz).
    + pose proof (nz_tail x U Hz) as Hz'. simpl app. rewrite zl_cons. destruct x.
      * simpl in Hc. destruct (IH k (false :: Y) ltac:(lia) Hz' ltac:(lia)) as [m [H Hl]].
        exists (S m). split; [|simpl in *; lia].
        eapply progress_step; [apply zL, tm_cont_S1; lia|].
        eapply progress_evstep_trans; [exact H|]. apply ev_eq. f_equal.
        simpl strip_rev. rewrite rep_comm. reflexivity.
      * simpl in Hc. destruct (IH (S k) (false :: Y) Hk Hz' Hc) as [m [H Hl]].
        exists (S m). split; [|simpl in *; lia].
        eapply progress_step; [apply zL, tm_cont_S0; lia|].
        eapply progress_evstep_trans; [exact H|]. apply ev_eq. f_equal.
        simpl strip_rev. rewrite rep_comm. reflexivity.
Qed.
