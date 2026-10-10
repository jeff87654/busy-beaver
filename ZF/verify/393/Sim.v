(** * Sim: the ZF machine [tm] simulates the RM path semantics of [zf2].

    Main theorem: [tm_halts_iff_rm : halts tm c0 <-> rm_halts zf2 ([], regs0)].

    Dispatch configurations: the machine is in main().0 (= [Node 0]) with the head on the first IP
    cell, the IP marker 1 to its left and blanks beyond, and to the right

        P  1^j  0^g  R-file

    where [P] is the IP (up to trailing zeros), [j] the chain ones of a register operation in
    progress, and the register file is [sepsR (junk ++ registers 10..0)] (the [junk] registers,
    written by boot, are never read).  A register operation on register [r] takes [r+2]
    dispatch cycles ([r+1] cycles of 1.sel, then the operation); a break / continue leaf takes one.
    The gap [g] grows by one with every executed decnz and never shrinks; [SimDag.ip_space]
    shows it is always large enough. *)

From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From ZF Require Import RM ZF2Dag RMEquiv ZFTM SimBase SimOps SimRegs SimIP SimDag SimBoot.
Import ListNotations.

(** ** Bits read by a walk *)
Definition pd (P : list bool) (d : nat) : list bool := firstn d (P ++ repeat false d).

Lemma pd_length P d : length (pd P d) = d.
Proof. unfold pd. rewrite pad_bits, length_map, length_seq. reflexivity. Qed.

Lemma pd_nth P d j : j < d -> nth j (pd P d) false = bit P j.
Proof.
  intros H. unfold pd. rewrite pad_bits.
  rewrite nth_indep with (d' := bit P 0) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Lemma skipn_nth_cons {A} (l : list A) i x : i < length l -> skipn i l = nth i l x :: skipn (S i) l.
Proof.
  revert i. induction l as [|a l IH]; intros i H; [simpl in H; lia|].
  destruct i as [|i]; [reflexivity|]. simpl in *. apply IH. lia.
Qed.

Lemma firstn_snoc_nth {A} (l : list A) i x : i < length l -> firstn (S i) l = firstn i l ++ [nth i l x].
Proof.
  revert i. induction l as [|a l IH]; intros i H; [simpl in H; lia|].
  destruct i as [|i]; [reflexivity|]. simpl in *. rewrite IH by lia. reflexivity.
Qed.

Lemma nz_nzd c U : nz c U = nzd c U.
Proof. revert c. induction U as [|[|] U IH]; intros c; simpl; rewrite ?IH; auto. Qed.

(** ** The machine walks the DAG *)
Lemma tm_Node n b : n < 324 -> tm (Node n, b) = edge_trans (dedge n b) b.
Proof.
  intros H. change (tm (Node n, b)) with (edge_trans (node_edge (bval (bmk 323 n)) b) b).
  rewrite bval_bmk by lia. reflexivity.
Qed.

Lemma tm_walk f n P i e d Lm X :
  n < 324 -> walk zf2 f n P i = Some (e, d) ->
  exists m, m < 324 /\ dedge m (bit P (d - 1)) = e /\ i < d /\
    zc (Node n) (rev (firstn i (pd P d)) ++ Lm) (skipn i (pd P d) ++ X) -->*
    zc (Node m) (rev (firstn (d - 1) (pd P d)) ++ Lm) (skipn (d - 1) (pd P d) ++ X).
Proof.
  revert n i. induction f as [|f IH]; intros n i Hn W; [discriminate|].
  pose proof (walk_gt _ _ _ _ _ _ _ W) as [Hid _].
  rewrite walk_S_zf2 in W. pose proof (zf2_edges n (bit P i) Hn) as Ed.
  destruct (dedge n (bit P i)) as [m'| | | | |] eqn:E;
    try (injection W as <- <-; exists n; replace (S i - 1) with i by lia;
         split; [exact Hn | split; [exact E | split; [lia | apply evstep_refl]]]).
  destruct (IH m' (S i) Ed W) as (m & Hm & He & Hi & Hrun).
  exists m. split; [exact Hm|]. split; [exact He|]. split; [lia|].
  eapply evstep_trans; [|exact Hrun].
  rewrite (skipn_nth_cons (pd P d) i false) by (rewrite pd_length; lia).
  rewrite (firstn_snoc_nth (pd P d) i false) by (rewrite pd_length; lia).
  rewrite pd_nth by lia. rewrite rev_app_distr. simpl.
  eapply evstep_step; [|apply evstep_refl].
  apply zR. rewrite tm_Node by exact Hn. rewrite E. reflexivity.
Qed.

(* from the root, up to the last node of the walk *)
Lemma tm_walk_root P e d X :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) ->
  exists m W' bl, pd P d = W' ++ [bl] /\ m < 324 /\ dedge m bl = e /\
    zc (Node 0) [true] (pd P d ++ X) -->* zc (Node m) (rev W' ++ [true]) (bl :: X).
Proof.
  intros W.
  destruct (tm_walk _ 0 P 0 e d [true] X ltac:(lia) W) as (m & Hm & He & Hd & Hrun).
  exists m, (firstn (d - 1) (pd P d)), (bit P (d - 1)).
  assert (Es : skipn (d - 1) (pd P d) = [bit P (d - 1)]).
  { rewrite (skipn_nth_cons (pd P d) (d - 1) false) by (rewrite pd_length; lia).
    rewrite pd_nth by lia. replace (S (d - 1)) with (length (pd P d)) by (rewrite pd_length; lia).
    rewrite skipn_all. reflexivity. }
  split.
  - rewrite <- (firstn_skipn (d - 1) (pd P d)) at 1. rewrite Es. reflexivity.
  - split; [exact Hm|]. split; [exact He|].
    rewrite Es in Hrun. exact Hrun.
Qed.

(** ** Register files *)
Definition junk : list nat := repeat 0 132 ++ 1 :: repeat 0 57.

(* registers lo+n-1, ..., lo (left to right) *)
Definition rl (Rg : regs) (lo n : nat) : list nat := map Rg (rev (seq lo n)).

Definition RF (Rg : regs) : list bool := sepsR (junk ++ rl Rg 0 11) ++ [false].

(* dispatch configuration during a register operation, after [j] selector moves *)
Definition DT (W : list bool) (j g : nat) (Rg : regs) : Q * tape :=
  zc (Node 0) [true]
     (W ++ ones j ++ zeros g ++ sepsR (junk ++ rl Rg j (11 - j)) ++ false :: sepsR (rl Rg 0 j) ++ [false]).

Lemma rl_split Rg j n : rl Rg j (S n) = rl Rg (S j) n ++ [Rg j].
Proof. unfold rl. simpl. rewrite map_app. reflexivity. Qed.

Lemma rl_S0 Rg j : rl Rg 0 (S j) = Rg j :: rl Rg 0 j.
Proof. unfold rl. rewrite seq_S, rev_app_distr. reflexivity. Qed.

Lemma rl_app Rg a b : rl Rg 0 (a + b) = rl Rg a b ++ rl Rg 0 a.
Proof. unfold rl. rewrite seq_app, rev_app_distr, map_app. reflexivity. Qed.

Lemma rl_ext Rg Rg' lo n : (forall x, lo <= x < lo + n -> Rg x = Rg' x) -> rl Rg lo n = rl Rg' lo n.
Proof.
  intros H. unfold rl. apply map_ext_in. intros x Hx.
  apply in_rev, in_seq in Hx. apply H. lia.
Qed.

Lemma rl_upd Rg r v : r <= 10 ->
  junk ++ rl Rg (S r) (10 - r) ++ v :: rl Rg 0 r = junk ++ rl (upd Rg r v) 0 11.
Proof.
  intros Hr. replace 11 with (S r + (10 - r)) by lia.
  rewrite rl_app, rl_S0. f_equal. f_equal.
  - apply rl_ext. intros x Hx. unfold upd. destruct (Nat.eqb_spec x r); [lia | reflexivity].
  - unfold upd. rewrite Nat.eqb_refl. f_equal.
    apply rl_ext. intros x Hx. destruct (Nat.eqb_spec x r); [lia | reflexivity].
Qed.

Lemma rl_same Rg r : r <= 10 ->
  junk ++ rl Rg (S r) (10 - r) ++ Rg r :: rl Rg 0 r = junk ++ rl Rg 0 11.
Proof.
  intros Hr. replace 11 with (S r + (10 - r)) by lia. rewrite rl_app, rl_S0. reflexivity.
Qed.

Lemma DT0 W g Rg : DT W 0 g Rg = zc (Node 0) [true] (W ++ zeros g ++ RF Rg).
Proof.
  unfold DT, RF. change (ones 0 ++ ?x) with x. change (11 - 0) with 11.
  change (sepsR (rl Rg 0 0)) with (@nil bool).
  rewrite <- (zc_padr _ _ (W ++ zeros g ++ sepsR (junk ++ rl Rg 0 11) ++ [false]) 1).
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma sepsR_pad C : sepsR C ++ [false] = false :: tl (sepsR C ++ [false]).
Proof. destruct C; reflexivity. Qed.

Lemma junk_ne Rg j n : junk ++ rl Rg j n <> [].
Proof. unfold junk. simpl. discriminate. Qed.

(** ** Register chains, either kind *)
Definition is_chain (q : state) (r : nat) : Prop := q = RInc r \/ q = RDec r.

Lemma chain_sel q r j lft X : is_chain q r -> r <= 10 -> j <= r ->
  zc q lft (ones j ++ false :: X) -->+ zc QSel (false :: ones j ++ lft) X.
Proof. intros [-> | ->] Hr Hj; [apply chain_sel_inc | apply chain_sel_dec]; assumption. Qed.

(** ** One selector cycle *)
Lemma sel_cycle P d e r Rg j g :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) ->
  (e = EInc r \/ e = EDecnz r) -> j <= r -> 3 <= g ->
  DT (pd P d) j g Rg -->+ DT (pd P d) (S j) (g - 1) Rg.
Proof.
  intros W He Hj Hg. unfold DT.
  set (Wd := pd P d). set (A := junk ++ rl Rg (S j) (10 - j)).
  set (X2 := tl (sepsR (rl Rg 0 j) ++ [false])).
  assert (Hr : r <= 10).
  { destruct (tm_walk_root P e d [] W) as (m & W' & bl & _ & Hm & Hme & _).
    pose proof (zf2_edges m bl Hm) as Ed. rewrite Hme in Ed. destruct He as [-> | ->]; exact Ed. }
  assert (EA : junk ++ rl Rg j (11 - j) = A ++ [Rg j]).
  { unfold A. replace (11 - j) with (S (10 - j)) by lia. rewrite rl_split, app_assoc. reflexivity. }
  replace (zeros g) with (false :: false :: zeros (g - 2)) by
    (destruct g as [|[|g]]; [lia|lia|]; simpl; rewrite Nat.sub_0_r; reflexivity).
  rewrite EA, sepsR_pad. fold X2.
  destruct (tm_walk_root P e d (ones j ++ false :: false :: zeros (g - 2) ++ sepsR (A ++ [Rg j]) ++
             false :: false :: X2) W) as (m & W' & bl & EW & Hm & Hme & Hrun).
  fold Wd in EW, Hrun.
  eapply evstep_progress_trans; [exact Hrun|].
  assert (Hleaf : exists q, is_chain q r /\ tm (Node m, bl) = Some (bl, R, q)).
  { rewrite tm_Node, Hme by exact Hm. destruct He as [-> | ->]; eexists; split;
      try reflexivity; [left | right]; reflexivity. }
  destruct Hleaf as (q & Hq & Ht).
  eapply progress_step; [apply zR, Ht|].
  eapply progress_trans; [apply (chain_sel q r j); assumption|].
  eapply progress_trans.
  { apply (sel_op _ (g - 2) A (Rg j) X2). lia. }
  rewrite zl_cons.
  eapply progress_step; [apply zL; reflexivity|].
  assert (EL : bl :: rev W' ++ [true] = rev Wd ++ [true]) by (rewrite EW, rev_app_distr; reflexivity).
  rewrite EL. rewrite app_assoc.
  eapply progress_evstep_trans; [apply disp|].
  { rewrite nz_ones, nz_nzd. apply (walk_nz P e d W). }
  apply ev_eq. f_equal.
  rewrite rev_app_distr, rev_involutive, rev_ones.
  replace (11 - S j) with (10 - j) by lia. fold A.
  replace (g - 1) with (S (g - 2)) by lia.
  rewrite rl_S0, sepsR_cons.
  assert (EX : false :: X2 = sepsR (rl Rg 0 j) ++ [false]) by (unfold X2; symmetry; apply sepsR_pad).
  lnorm. rewrite <- EX. rewrite (rep_snoc true j). lnorm. reflexivity.
Qed.

Lemma sel_cycles P d e r Rg gd j :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) ->
  (e = EInc r \/ e = EDecnz r) -> j <= S r -> r + 3 <= gd ->
  DT (pd P d) 0 gd Rg -->* DT (pd P d) j (gd - j) Rg.
Proof.
  intros W He. induction j as [|j IH]; intros Hj Hg.
  - rewrite Nat.sub_0_r. apply evstep_refl.
  - eapply evstep_trans; [apply IH; lia|].
    replace (gd - S j) with (gd - j - 1) by lia.
    apply progress_evstep. apply (sel_cycle P d e r); [exact W | exact He | lia | lia].
Qed.

(** ** The operation cycle of a register operation *)
Lemma leaf_reg P e d r :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) -> (e = EInc r \/ e = EDecnz r) -> r <= 10.
Proof.
  intros W He. destruct (tm_walk_root P e d [] W) as (m & W' & bl & _ & Hm & Hme & _).
  pose proof (zf2_edges m bl Hm) as Ed. rewrite Hme in Ed. destruct He as [-> | ->]; exact Ed.
Qed.

Lemma DT_nopad W j g Rg : DT W j g Rg =
  zc (Node 0) [true] (W ++ ones j ++ zeros g ++ sepsR (junk ++ rl Rg j (11 - j)) ++ false :: sepsR (rl Rg 0 j)).
Proof.
  unfold DT. rewrite <- (zc_padr _ _ (W ++ ones j ++ zeros g ++ sepsR (junk ++ rl Rg j (11 - j)) ++
                                       false :: sepsR (rl Rg 0 j)) 1).
  lnorm. reflexivity.
Qed.

Lemma inc_rev_ones n l : inc_rev (ones n ++ l) = zeros n ++ inc_rev l.
Proof. induction n as [|n IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma strip_rev_ones k n l : strip_rev false (S k) (ones n ++ l) = strip_rev false (S k) l.
Proof. induction n as [|n IH]; simpl; [reflexivity|]. exact IH. Qed.

(* walk to the leaf and take the leaf transition into the register chain *)
Lemma walk_to_chain P d r Y (inc : bool) :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (if inc then EInc r else EDecnz r, d) ->
  zc (Node 0) [true] (pd P d ++ Y) -->+ zc (if inc then RInc r else RDec r) (rev (pd P d) ++ [true]) Y.
Proof.
  intros W. destruct (tm_walk_root P _ d Y W) as (m & W' & bl & EW & Hm & Hme & Hrun).
  eapply evstep_progress_trans; [exact Hrun|].
  apply progress_base. rewrite EW, rev_app_distr. apply zR.
  rewrite tm_Node, Hme by exact Hm. destruct inc; reflexivity.
Qed.

(* walk to a cdr leaf of break / continue / halt kind and take the leaf transition *)
Lemma walk_to_cdr P d e Y :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) ->
  (forall m, m < 324 -> dedge m false <> e) ->
  exists W', pd P d = W' ++ [true] /\
    forall w d' q', edge_trans e true = Some (w, d', q') ->
    zc (Node 0) [true] (pd P d ++ Y) -->+ (if dir_is_R d' then zc q' (w :: rev W' ++ [true]) Y
                                           else zl q' (rev W' ++ [true]) (w :: Y)).
Proof.
  intros W Hc. destruct (tm_walk_root P e d Y W) as (m & W' & bl & EW & Hm & Hme & Hrun).
  destruct bl; [|exfalso; exact (Hc m Hm Hme)].
  exists W'. split; [exact EW|]. intros w d' q' Ht.
  eapply evstep_progress_trans; [exact Hrun|].
  apply progress_base. rewrite <- Hme in Ht. rewrite <- (tm_Node m true Hm) in Ht.
  destruct d'; simpl.
  - apply zL, Ht.
  - apply zR, Ht.
Qed.

Lemma zc_RF q l P g Rg : zc q l (P ++ zeros g ++ RF Rg) = zc q l (P ++ zeros g ++ sepsR (junk ++ rl Rg 0 11)).
Proof. unfold RF. rewrite !app_assoc. exact (zc_padr q l _ 1). Qed.

Lemma inc_path_length W : length (inc_path W) = length W.
Proof. unfold inc_path. rewrite length_rev, inc_rev_length, length_rev. reflexivity. Qed.

Lemma zeros_S_pred g : 1 <= g -> zeros g = false :: zeros (g - 1).
Proof. intros H. destruct g as [|g]; [lia|]. simpl. rewrite Nat.sub_0_r. reflexivity. Qed.

Lemma inc_cycle P d r Rg g :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (EInc r, d) -> 2 <= g ->
  exists g2, DT (pd P d) (S r) g Rg -->+
             zc (Node 0) [true] (inc_path (pd P d) ++ zeros g2 ++ RF (upd Rg r (S (Rg r)))) /\
             S r + g <= g2.
Proof.
  intros W Hg. pose proof (leaf_reg P _ d r W (or_introl eq_refl)) as Hr.
  set (Wd := pd P d). set (A := junk ++ rl Rg (S r) (10 - r)). set (C := rl Rg 0 r).
  rewrite DT_nopad. replace (11 - S r) with (10 - r) by lia. fold A. rewrite rl_S0. fold C.
  rewrite sepsR_cons. rewrite (zeros_S_pred g) by lia.
  assert (Hnz : nz 0 (ones (S r) ++ rev Wd) = true)
    by (rewrite nz_ones, nz_nzd; apply (walk_nz P _ d W)).
  destruct (brk_ip _ 0 (false :: zeros (g - 1) ++ sepsR A ++ false :: ones (S (S (Rg r))) ++ sepsR C)
              ltac:(lia) Hnz) as [m [Hb _]].
  exists (S r + (m + g)). split; [|lia].
  eapply progress_trans; [apply (walk_to_chain P d r _ true W)|]. cbv beta iota. fold Wd.
  eapply progress_trans; [apply chain_inc; exact Hr|].
  eapply progress_trans; [apply (inc_op _ (g - 1) A (Rg r) (sepsR C)); [lia | apply junk_ne]|].
  rewrite (app_assoc (ones (S r)) (rev Wd) [true]).
  eapply progress_evstep_trans; [exact Hb|]. apply ev_eq. rewrite zc_RF. f_equal.
  rewrite strip_rev_0, inc_rev_ones, rev_app_distr, rev_zeros.
  rewrite <- (rl_upd Rg r (S (Rg r)) Hr). fold C.
  replace (junk ++ rl Rg (S r) (10 - r) ++ S (Rg r) :: C) with (A ++ S (Rg r) :: C)
    by (unfold A; rewrite <- app_assoc; reflexivity).
  rewrite sepsR_app, sepsR_cons, !rep_add, (zeros_S_pred g) by lia.
  unfold inc_path. lnorm. reflexivity.
Qed.

Lemma decp_cycle P d r Rg g v :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (EDecnz r, d) -> Rg r = S v -> 1 <= g ->
  exists g2, DT (pd P d) (S r) g Rg -->+
             zc (Node 0) [true] (inc_path (pd P d) ++ zeros g2 ++ RF (upd Rg r v)) /\
             S r + g + 1 <= g2.
Proof.
  intros W Hv Hg. pose proof (leaf_reg P _ d r W (or_intror eq_refl)) as Hr.
  set (Wd := pd P d). set (A := junk ++ rl Rg (S r) (10 - r)). set (C := rl Rg 0 r).
  rewrite DT_nopad. replace (11 - S r) with (10 - r) by lia. fold A. rewrite rl_S0. fold C.
  rewrite Hv, sepsR_cons. rewrite (zeros_S_pred g) by lia.
  assert (Hnz : nz 0 (ones (S r) ++ rev Wd) = true)
    by (rewrite nz_ones, nz_nzd; apply (walk_nz P _ d W)).
  destruct (brk_ip _ 0 (false :: zeros (S (g - 1)) ++ sepsR (A ++ v :: C)) ltac:(lia) Hnz)
    as [m [Hb _]].
  exists (S r + (m + S g)). split; [|lia].
  eapply progress_trans; [apply (walk_to_chain P d r _ false W)|]. cbv beta iota. fold Wd.
  eapply progress_trans; [apply chain_dec; exact Hr|].
  eapply progress_trans; [apply (dec_pos_op _ (g - 1) A v C); apply junk_ne|].
  rewrite (app_assoc (ones (S r)) (rev Wd) [true]).
  eapply progress_evstep_trans; [exact Hb|]. apply ev_eq. rewrite zc_RF. f_equal.
  rewrite strip_rev_0, inc_rev_ones, rev_app_distr, rev_zeros.
  rewrite <- (rl_upd Rg r v Hr). fold C.
  replace (junk ++ rl Rg (S r) (10 - r) ++ v :: C) with (A ++ v :: C)
    by (unfold A; rewrite <- app_assoc; reflexivity).
  replace (S (g - 1)) with g by lia.
  rewrite !rep_add. unfold inc_path. lnorm. reflexivity.
Qed.

Lemma brk1_eq W : brk 1 W = rev (inc_rev (strip_rev false 1 (rev W))).
Proof. unfold brk, inc_path, strip_path. rewrite rev_involutive. reflexivity. Qed.

Lemma decz_cycle P d r Rg g :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (EDecnz r, d) -> Rg r = 0 -> 1 <= g ->
  exists g2, DT (pd P d) (S r) g Rg -->+
             zc (Node 0) [true] (brk 1 (pd P d) ++ zeros g2 ++ RF Rg) /\
             d + S r + g + 1 <= length (brk 1 (pd P d)) + g2.
Proof.
  intros W Hv Hg. pose proof (leaf_reg P _ d r W (or_intror eq_refl)) as Hr.
  set (Wd := pd P d). set (A := junk ++ rl Rg (S r) (10 - r)). set (C := rl Rg 0 r).
  rewrite DT_nopad. replace (11 - S r) with (10 - r) by lia. fold A. rewrite rl_S0. fold C.
  rewrite Hv, sepsR_cons. rewrite (zeros_S_pred g) by lia.
  assert (Hnz : nz 0 (ones (S r) ++ rev Wd) = true)
    by (rewrite nz_ones, nz_nzd; apply (walk_nz P _ d W)).
  destruct (brk_ip _ 1 (false :: zeros (S (g - 1)) ++ sepsR (A ++ 0 :: C)) ltac:(lia) Hnz)
    as [m [Hb Hl]].
  rewrite strip_rev_ones in Hb, Hl. rewrite <- brk1_eq in Hb.
  exists (m + S g). split.
  2:{ rewrite brk1_eq, length_rev, inc_rev_length. rewrite length_app, repeat_length, length_rev in Hl.
      assert (Ld : length Wd = d) by apply pd_length. lia. }
  eapply progress_trans; [apply (walk_to_chain P d r _ false W)|]. cbv beta iota. fold Wd.
  eapply progress_trans; [apply chain_dec; exact Hr|].
  eapply progress_trans; [apply (dec_zero_op _ (g - 1) A C); apply junk_ne|].
  rewrite (app_assoc (ones (S r)) (rev Wd) [true]).
  eapply progress_evstep_trans; [exact Hb|]. apply ev_eq. rewrite zc_RF. f_equal.
  rewrite <- (rl_same Rg r Hr), Hv. fold C.
  replace (junk ++ rl Rg (S r) (10 - r) ++ 0 :: C) with (A ++ 0 :: C)
    by (unfold A; rewrite <- app_assoc; reflexivity).
  replace (S (g - 1)) with g by lia.
  rewrite !rep_add. lnorm. reflexivity.
Qed.

(** ** Break / continue / halt leaves *)
Lemma not_car_edge e : (forall m b, m < 324 -> dedge m b = e -> b = true) ->
  forall m, m < 324 -> dedge m false <> e.
Proof. intros H m Hm E. specialize (H m false Hm E). discriminate. Qed.

Lemma nz_pd_cdr P e d W' :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) -> pd P d = W' ++ [true] ->
  nz 0 (rev W') = true.
Proof.
  intros W E. pose proof (walk_nz P e d W) as H. fold (pd P d) in H. rewrite E, rev_app_distr in H.
  simpl in H. rewrite nz_nzd. exact H.
Qed.

Lemma brk_cycle P d k Rg gd :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (EBreak k, d) ->
  exists P2 g2, zc (Node 0) [true] (pd P d ++ zeros gd ++ RF Rg) -->+
                zc (Node 0) [true] (P2 ++ zeros g2 ++ RF Rg) /\
                P2 = brk k (pd P d) /\ d + gd <= length P2 + g2.
Proof.
  intros W.
  assert (Hk : 1 <= k <= 2 /\ forall m b, m < 324 -> dedge m b = EBreak k -> b = true).
  { destruct (tm_walk_root P _ d [] W) as (m & W' & bl & _ & Hm & Hme & _).
    pose proof (zf2_edges m bl Hm) as Ed. rewrite Hme in Ed. split; [tauto|].
    intros m' b Hm' E. pose proof (zf2_edges m' b Hm') as Ed'. rewrite E in Ed'. tauto. }
  destruct Hk as [Hk Hcdr].
  destruct (walk_to_cdr P d _ (zeros gd ++ RF Rg) W (not_car_edge _ Hcdr)) as (W' & EW & Hst).
  specialize (Hst false L (Brk k) eq_refl). cbn [dir_is_R] in Hst.
  destruct (brk_ip (rev W') k (false :: zeros gd ++ RF Rg) ltac:(lia) (nz_pd_cdr P _ d W' W EW))
    as [m [Hb Hl]].
  exists (rev (inc_rev (strip_rev false k (rev W')))), (m + S gd). split; [|split].
  - eapply progress_trans; [exact Hst|]. eapply progress_evstep_trans; [exact Hb|].
    apply ev_eq. f_equal. rewrite rep_add. simpl. lnorm. reflexivity.
  - rewrite EW. destruct k as [|k]; [lia|]. rewrite brk_cdr.
    unfold brk, inc_path, strip_path. rewrite rev_involutive. reflexivity.
  - rewrite length_rev, inc_rev_length. rewrite length_rev in Hl.
    assert (Ld : length (pd P d) = d) by apply pd_length.
    rewrite EW, length_app in Ld. simpl in Ld. lia.
Qed.

Lemma count_occ_rev l : count_occ bool_dec (rev l) true = count_occ bool_dec l true.
Proof.
  induction l as [|x l IH]; [reflexivity|]. simpl. rewrite count_occ_app, IH. simpl.
  destruct x; simpl; lia.
Qed.

Lemma cont_cycle P d k Rg gd :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (EContinue k, d) ->
  exists P2 g2, zc (Node 0) [true] (pd P d ++ zeros gd ++ RF Rg) -->+
                zc (Node 0) [true] (P2 ++ zeros g2 ++ RF Rg) /\
                P2 = cont k (pd P d) /\ d + gd <= length P2 + g2.
Proof.
  intros W.
  assert (Hk : 1 <= k <= 5 /\ forall m b, m < 324 -> dedge m b = EContinue k -> b = true).
  { destruct (tm_walk_root P _ d [] W) as (m & W' & bl & _ & Hm & Hme & _).
    pose proof (zf2_edges m bl Hm) as Ed. rewrite Hme in Ed. split; [tauto|].
    intros m' b Hm' E. pose proof (zf2_edges m' b Hm') as Ed'. rewrite E in Ed'. tauto. }
  destruct Hk as [Hk Hcdr].
  destruct (walk_to_cdr P d _ (zeros gd ++ RF Rg) W (not_car_edge _ Hcdr)) as (W' & EW & Hst).
  specialize (Hst false L (Cont (k - 1)) eq_refl). cbn [dir_is_R] in Hst.
  assert (Hc : k - 1 <= count_occ bool_dec (rev W') true).
  { pose proof (walk_cont P k d W) as Hc. fold (pd P d) in Hc. rewrite EW, count_occ_app in Hc.
    simpl in Hc. rewrite count_occ_rev. lia. }
  destruct (cont_ip (rev W') (k - 1) (false :: zeros gd ++ RF Rg) ltac:(lia)
              (nz_pd_cdr P _ d W' W EW) Hc) as [m [Hb Hl]].
  exists (rev (strip_rev true (k - 1) (rev W'))), (m + S gd). split; [|split].
  - eapply progress_trans; [exact Hst|]. eapply progress_evstep_trans; [exact Hb|].
    apply ev_eq. f_equal. rewrite rep_add. simpl. lnorm. reflexivity.
  - rewrite EW. destruct k as [|[|k]]; [lia| |].
    + rewrite cont_cdr1. simpl. rewrite strip_rev_0, rev_involutive. reflexivity.
    + rewrite cont_cdrS. unfold cont, strip_path. replace (S (S k) - 1) with (S k) by lia. reflexivity.
  - rewrite length_rev. rewrite length_rev in Hl.
    assert (Ld : length (pd P d) = d) by apply pd_length.
    rewrite EW, length_app in Ld. simpl in Ld. lia.
Qed.

Lemma halt_cycle P d Rg gd :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (EHalt, d) ->
  halts tm (zc (Node 0) [true] (pd P d ++ zeros gd ++ RF Rg)).
Proof.
  intros W.
  assert (Hcdr : forall m b, m < 324 -> dedge m b = EHalt -> b = true).
  { intros m' b Hm' E. pose proof (zf2_edges m' b Hm') as Ed'. rewrite E in Ed'. exact Ed'. }
  destruct (walk_to_cdr P d _ (zeros gd ++ RF Rg) W (not_car_edge _ Hcdr)) as (W' & EW & Hst).
  specialize (Hst true R QHalt eq_refl). cbn [dir_is_R] in Hst.
  eapply halted_evstep_halts; [apply progress_evstep, Hst|]. reflexivity.
Qed.

(** ** One RM step *)
Lemma cycle_step P Rg e d gd c' :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) ->
  need (P, Rg) <= d + gd -> rm_step zf2 (P, Rg) = Some c' ->
  exists P2 g2, zc (Node 0) [true] (pd P d ++ zeros gd ++ RF Rg) -->+
                zc (Node 0) [true] (P2 ++ zeros g2 ++ RF (snd c')) /\
                P2 = fst c' /\ d + gd + is_dec (P, Rg) <= length P2 + g2.
Proof.
  intros W Hn Hs. unfold need, is_dec in *. cbn [fst] in *. rewrite W in Hn |- *.
  unfold rm_step in Hs. rewrite W in Hs. fold (pd P d) in Hs.
  destruct e as [n|r|r|k|k|]; try discriminate Hs.
  - (* inc *)
    injection Hs as <-. cbn [fst snd].
    destruct (inc_cycle P d r Rg (gd - S r) W ltac:(lia)) as [g2 [H1 H2]].
    exists (inc_path (pd P d)), g2. split; [|split; [reflexivity|]].
    + rewrite <- DT0. eapply evstep_progress_trans; [|exact H1].
      apply (sel_cycles P d (EInc r) r); [exact W | left; reflexivity | lia | lia].
    + rewrite inc_path_length, pd_length. lia.
  - (* decnz *)
    destruct (Rg r) as [|v] eqn:Hv; injection Hs as <-; cbn [fst snd].
    + destruct (decz_cycle P d r Rg (gd - S r) W Hv ltac:(lia)) as [g2 [H1 H2]].
      exists (brk 1 (pd P d)), g2. split; [|split; [reflexivity|lia]].
      rewrite <- DT0. eapply evstep_progress_trans; [|exact H1].
      apply (sel_cycles P d (EDecnz r) r); [exact W | right; reflexivity | lia | lia].
    + destruct (decp_cycle P d r Rg (gd - S r) v W Hv ltac:(lia)) as [g2 [H1 H2]].
      exists (inc_path (pd P d)), g2. split; [|split; [reflexivity|]].
      * rewrite <- DT0. eapply evstep_progress_trans; [|exact H1].
        apply (sel_cycles P d (EDecnz r) r); [exact W | right; reflexivity | lia | lia].
      * rewrite inc_path_length, pd_length. lia.
  - (* break *)
    injection Hs as <-. cbn [fst snd].
    destruct (brk_cycle P d k Rg gd W) as (P2 & g2 & H1 & -> & H2).
    exists (brk k (pd P d)), g2. split; [exact H1|]. split; [reflexivity | lia].
  - (* continue *)
    injection Hs as <-. cbn [fst snd].
    destruct (cont_cycle P d k Rg gd W) as (P2 & g2 & H1 & -> & H2).
    exists (cont k (pd P d)), g2. split; [exact H1|]. split; [reflexivity | lia].
Qed.

(** ** The IP on the tape vs. the RM's IP (equal up to trailing zeros) *)
Lemma all_false l : (forall i, nth i l false = false) -> l = zeros (length l).
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  pose proof (H 0) as H0. simpl in H0. subst x. simpl. f_equal.
  apply IH. intros i. apply (H (S i)).
Qed.

Lemma skipn_zeros l d : (forall i, d <= i -> nth i l false = false) -> skipn d l = zeros (length l - d).
Proof.
  revert l. induction d as [|d IH]; intros l H.
  - rewrite Nat.sub_0_r. apply all_false. intros i. apply H. lia.
  - destruct l as [|x l]; [reflexivity|]. simpl. apply IH. intros i Hi. apply (H (S i)). lia.
Qed.

Lemma firstn_rep {A} (x : A) k n : firstn k (repeat x n) = repeat x (Nat.min k n).
Proof.
  revert n. induction k as [|k IH]; intros n; [reflexivity|].
  destruct n as [|n]; [reflexivity|]. simpl. rewrite IH. reflexivity.
Qed.

Lemma conf_split P P' g d :
  ipeq P' P -> (forall i, d <= i -> bit P i = false) -> d <= length P' + g ->
  P' ++ zeros g = pd P d ++ zeros (length P' + g - d).
Proof.
  intros E Hs Hd.
  assert (Epd : pd P d = pd P' d).
  { unfold pd. rewrite !pad_bits. apply map_ext. intros i. symmetry. apply E. }
  rewrite Epd. unfold pd.
  destruct (Nat.le_gt_cases (length P') d) as [Hle | Hgt].
  - rewrite firstn_app, firstn_all2 by lia. rewrite firstn_rep.
    replace (Nat.min (d - length P') d) with (d - length P') by lia.
    rewrite <- app_assoc, <- rep_add. f_equal. f_equal. lia.
  - rewrite firstn_app. replace (d - length P') with 0 by lia. rewrite app_nil_r.
    rewrite <- (firstn_skipn d P') at 1. rewrite <- app_assoc. f_equal.
    rewrite (skipn_zeros P' d).
    + rewrite <- rep_add. f_equal. lia.
    + intros i Hi. change (bit P' i = false). rewrite E. apply Hs, Hi.
Qed.

(** ** The simulation invariant *)
Definition c_init : conf := ([], regs0).

Definition TMc (P : list bool) (g : nat) (Rg : regs) : Q * tape := zc (Node 0) [true] (P ++ zeros g ++ RF Rg).

Definition Inv (n : nat) (T : Q * tape) : Prop :=
  exists P Rg P' g, rm_run zf2 n c_init = Some (P, Rg) /\ ipeq P' P /\ T = TMc P' g Rg /\
                    18 + ndec n c_init <= length P' + g.

Lemma junk_boot : junk ++ rl regs0 0 11 = boot_regs.
Proof. reflexivity. Qed.

Lemma inv_boot : Inv 0 (zc (Node 0) [true] (zeros 18 ++ sepsR boot_regs)).
Proof.
  unfold Inv. exists (@nil bool), regs0, (@nil bool), 18. split; [reflexivity|]. split; [apply ipeq_refl|]. split; [|simpl; lia].
  unfold TMc. rewrite zc_RF, junk_boot. reflexivity.
Qed.

Lemma rm_run_snoc n c c1 c2 : rm_run zf2 n c = Some c1 -> rm_step zf2 c1 = Some c2 ->
  rm_run zf2 (S n) c = Some c2.
Proof.
  intros H1 H2. replace (S n) with (n + 1) by lia. rewrite rm_run_add, H1. simpl. rewrite H2. reflexivity.
Qed.

Lemma rm_run_last n c c2 : rm_run zf2 (S n) c = Some c2 ->
  exists c1, rm_run zf2 n c = Some c1 /\ rm_step zf2 c1 = Some c2.
Proof.
  replace (S n) with (n + 1) by lia. rewrite rm_run_add.
  destruct (rm_run zf2 n c) as [c1|]; [|discriminate]. simpl.
  destruct (rm_step zf2 c1) as [c3|] eqn:E; [|discriminate]. intros H. injection H as ->. eauto.
Qed.

Lemma ndec_snoc n c c1 c2 : rm_run zf2 n c = Some c1 -> rm_step zf2 c1 = Some c2 ->
  ndec (S n) c = ndec n c + is_dec c1.
Proof.
  revert c. induction n as [|n IH]; intros c H1 H2.
  - injection H1 as ->. simpl. rewrite H2. lia.
  - rewrite rm_run_S in H1. destruct (rm_step zf2 c) as [c0|] eqn:E; [|discriminate].
    change (ndec (S (S n)) c) with
      (match rm_step zf2 c with None => 0 | Some c' => is_dec c + ndec (S n) c' end).
    change (ndec (S n) c) with
      (match rm_step zf2 c with None => 0 | Some c' => is_dec c + ndec n c' end).
    rewrite E, (IH c0 H1 H2). lia.
Qed.

Lemma need_ge P Rg e d : walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) -> d <= need (P, Rg).
Proof. intros W. unfold need. cbn [fst]. rewrite W. destruct e; lia. Qed.

Lemma stray n P Rg e d : rm_run zf2 n c_init = Some (P, Rg) ->
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) -> forall i, d <= i -> bit P i = false.
Proof.
  intros Hr W i Hi. pose proof (no_stray zf2 regs0 n P Rg e d Hr W) as F.
  unfold bit. destruct (Nat.lt_ge_cases i (length P)) as [Hlt | Hge].
  - rewrite <- (firstn_skipn d P), app_nth2; rewrite length_firstn; [|lia].
    replace (Nat.min d (length P)) with d by lia.
    rewrite Forall_forall in F. apply F, nth_In. rewrite length_skipn. lia.
  - apply nth_overflow, Hge.
Qed.

(* put an invariant configuration in walk form *)
Lemma inv_walk n T : Inv n T ->
  exists P Rg e d gd, rm_run zf2 n c_init = Some (P, Rg) /\
    walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) /\
    T = zc (Node 0) [true] (pd P d ++ zeros gd ++ RF Rg) /\
    need (P, Rg) <= d + gd /\ 18 + ndec n c_init <= d + gd.
Proof.
  intros (P & Rg & P' & g & Hr & Hip & -> & Hg).
  destruct (wf_walk zf2 zf2_wf P) as (e & d & W).
  pose proof (ip_space n (P, Rg) Hr) as Hsp. pose proof (need_ge P Rg e d W) as Hd.
  change ([], regs0) with c_init in Hsp.
  exists P, Rg, e, d, (length P' + g - d). split; [exact Hr|]. split; [exact W|]. split.
  - unfold TMc. rewrite app_assoc, (conf_split P P' g d Hip (stray n P Rg e d Hr W)) by lia.
    rewrite <- app_assoc. reflexivity.
  - lia.
Qed.

Lemma inv_step n T : Inv n T ->
  (exists c, rm_run zf2 n c_init = Some c /\ at_halt zf2 c /\ halts tm T) \/
  (exists T', Inv (S n) T' /\ T -->+ T').
Proof.
  intros HI. destruct (inv_walk n T HI) as (P & Rg & e & d & gd & Hr & W & -> & Hn & Hg).
  destruct (rm_step zf2 (P, Rg)) as [[P2 R2]|] eqn:Es.
  - right. destruct (cycle_step P Rg e d gd (P2, R2) W Hn Es) as (P2' & g2 & H1 & E2 & H2).
    cbn [fst snd] in *. subst P2'.
    exists (TMc P2 g2 R2). split; [|exact H1].
    exists P2, R2, P2, g2. split; [apply (rm_run_snoc n c_init (P, Rg)); assumption|].
    split; [apply ipeq_refl|]. split; [reflexivity|].
    rewrite (ndec_snoc n c_init (P, Rg) (P2, R2) Hr Es). lia.
  - left. exists (P, Rg). split; [exact Hr|].
    pose proof (walk_gt _ _ _ _ _ _ _ W) as [_ Hnode].
    unfold rm_step in Es. rewrite W in Es.
    destruct e as [m|r|r|k|k|]; try discriminate Hnode;
      try (destruct (Rg r); discriminate Es); try discriminate Es.
    split; [exists d; exact W|]. apply (halt_cycle P d Rg gd W).
Qed.

Lemma inv_halt n T c : Inv n T -> rm_run zf2 n c_init = Some c -> at_halt zf2 c -> halts tm T.
Proof.
  intros HI Hr [d' Ha]. destruct (inv_walk n T HI) as (P & Rg & e & d & gd & Hr' & W & -> & _ & _).
  rewrite Hr in Hr'. injection Hr' as ->. cbn [fst] in Ha. rewrite W in Ha. injection Ha as -> <-.
  apply (halt_cycle P d Rg gd W).
Qed.

Lemma reach n c : rm_run zf2 n c_init = Some c -> exists T, c0 -->* T /\ Inv n T.
Proof.
  revert c. induction n as [|n IH]; intros c Hr.
  - exists (zc (Node 0) [true] (zeros 18 ++ sepsR boot_regs)). split; [exact boot | exact inv_boot].
  - destruct (rm_run_last n c_init c Hr) as (c1 & Hr1 & Hs).
    destruct (IH c1 Hr1) as (T & HT & HI).
    destruct (inv_step n T HI) as [(c2 & Hr2 & [d Ha] & _) | (T' & HI' & HT')].
    + exfalso. rewrite Hr1 in Hr2. injection Hr2 as <-.
      destruct c1 as [P Rg]. unfold rm_step in Hs. cbn [fst] in Ha. rewrite Ha in Hs. discriminate.
    + exists T'. split; [|exact HI']. eapply evstep_trans; [exact HT | apply progress_evstep, HT'].
Qed.

(** ** Main theorem *)
Theorem tm_halts_iff_rm : halts tm c0 <-> rm_halts zf2 ([], regs0).
Proof.
  split.
  - intros H.
    assert (Hb : halts tm (zc (Node 0) [true] (zeros 18 ++ sepsR boot_regs)))
      by exact (halts_evstep' tm _ _ H boot).
    destruct (progress_halts tm (fun T => exists n, Inv n T) (fun _ => rm_halts zf2 c_init)
                (zc (Node 0) [true] (zeros 18 ++ sepsR boot_regs))) as (T & _ & HZ).
    + intros T [n HI]. destruct (inv_step n T HI) as [(c & Hr & Ha & _) | (T' & HI' & HT')].
      * left. exists n, c. split; assumption.
      * right. exists T'. split; [exists (S n); exact HI' | exact HT'].
    + exists 0. exact inv_boot.
    + exact Hb.
    + exact HZ.
  - intros (n & c & Hr & Ha).
    destruct (reach n c Hr) as (T & HT & HI).
    exact (halts_evstep tm _ _ (inv_halt n T c HI Hr Ha) HT).
Qed.

Print Assumptions tm_halts_iff_rm.
