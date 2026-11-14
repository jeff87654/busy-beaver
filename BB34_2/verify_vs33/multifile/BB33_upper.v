(** * BB33_upper: an UPPER bound for the score of the published BB(33) hydra machine (mxdys).

    Published files used unchanged (busy-beaver BB33/verify/multifile): BB332, Individual332, BB33_tm,
    BB33_rules, Ord, Hardy, HydraOrd, BB33_scan, BB33_round, BB33_game, BB33_halt.  New: HydraUpper.v.

    The published proof gives the lower bound f_(omega^omega^omega^omega^omega^3)(4) <= N + 2
    (BB33_bound.hardy_score).  Here, for EVERY halting configuration reachable from the blank tape:

      Theorem upper_bound :
        forall c N, c0 -->* c -> halted tm c -> ones c N -> N + 2 <= FGH (powtower 5 (ofin 3)) 6.

    i.e. N + 2 <= f_(omega^omega^omega^omega^omega^3)(6) = H_(omega^^6 topped by 3)(6).
    [ones] is BB33_game.ones (number of 1s on the finite tape).  Method: the machine is deterministic,
    so every halting configuration is reached through the published rounds (BB33_game.round_succ,
    round_lim, BB33_round.R3); by HydraUpper.chop_exact each limit round moves the hydra ordinal x to x[n]
    or x[n+1] (n = counter + 3), and U(x, n) = H_x(n+2) never increases (HydraUpper.HH_up_lim). *)

From BB8 Require Import BB33_tm BB33_rules BB33_scan BB33_round BB33_game BB33_halt Ord Hardy HydraOrd HydraUpper.
From Coq Require Import Lia List PeanoNat Streams.
Import ListNotations.
Set Default Goal Selector "!".
Local Open Scope nat_scope.

(** ** Determinism *)

Lemma det_halt : forall a b h, a -->* b -> a -->* h -> halted tm h -> b -->* h.
Proof.
  intros a b h Hab Hah Hh.
  apply with_counter in Hab as [n Hn]. apply with_counter in Hah as [k Hk].
  destruct (Nat.le_gt_cases n k) as [Hle|Hgt].
  - destruct (rewind_split' n (k - n) tm k a h Hk ltac:(lia)) as (c' & H1 & H2).
    pose proof (multistep_deterministic tm n a b c' Hn H1) as E. subst c'.
    eapply without_counter. exact H2.
  - destruct (rewind_split' k (n - k) tm n a b Hn ltac:(lia)) as (c' & H1 & H2).
    pose proof (multistep_deterministic tm k a h c' Hk H1) as E. subst c'.
    exfalso. exact (halted_no_multistep tm h b (n - k) ltac:(lia) Hh H2).
Qed.

Lemma halted_evstep_eq : forall h c, halted tm h -> h -->* c -> c = h.
Proof.
  intros h c Hh H. inversion H; subst; [reflexivity|].
  exfalso. eapply halted_no_step; eassumption.
Qed.

(** ** The number of ones of a configuration is well defined *)

Lemma str_count0 : forall L : list Sym, const S0 = L *> const S0 -> count1 L = 0.
Proof.
  induction L as [|b L IH]; intros H; [reflexivity|].
  assert (Hb : S0 = b) by exact (f_equal (@Streams.hd Sym) H).
  assert (Ht : const S0 = L *> const S0) by exact (f_equal (@Streams.tl Sym) H).
  subst b. simpl. apply IH. exact Ht.
Qed.

Lemma str_count : forall L1 L2 : list Sym, L1 *> const S0 = L2 *> const S0 -> count1 L1 = count1 L2.
Proof.
  induction L1 as [|a L1 IH]; intros L2 H.
  - symmetry. apply str_count0. exact H.
  - destruct L2 as [|b L2].
    + apply str_count0. symmetry. exact H.
    + assert (Hb : a = b) by exact (f_equal (@Streams.hd Sym) H).
      assert (Ht : L1 *> const S0 = L2 *> const S0) by exact (f_equal (@Streams.tl Sym) H).
      subst b. cbn [count1]. rewrite (IH L2 Ht). reflexivity.
Qed.

Lemma ones_unique : forall c N N', ones c N -> ones c N' -> N = N'.
Proof.
  intros c N N' (q & L & R & s & E & HN) (q' & L' & R' & s' & E' & HN').
  rewrite E in E'. injection E' as E1 E2 E3 E4. subst.
  rewrite (str_count _ _ E2), (str_count _ _ E4). reflexivity.
Qed.

(** ** The initial hydra is good *)

Lemma hs0_good : good (node hs0).
Proof.
  unfold hs0, sp0. cbn [plug app].
  repeat apply good_one. apply good_lead. apply good_one. exact (good_leaves 3).
Qed.

(** ** The upper-bound game *)

Theorem upper : forall x, nf x -> forall m hs w c N,
  x = olist hs -> Forall (hb E) hs -> good (node hs) -> HRep hs w ->
  Cf m w -->* c -> halted tm c -> ones c N -> N + 2 <= HH x (m + 5).
Proof.
  intros x. induction x as [x IH] using (well_founded_ind wf_ltn).
  intros Hx m hs w c N Ex Hb Hg Hr Hc Hh Ho.
  destruct Hr as [|sp j Hsp].
  - (* the empty hydra: rule R3 halts *)
    assert (Hend : c_end m -->* c) by (eapply det_halt; [apply progress_evstep, R3 | exact Hc | exact Hh]).
    apply halted_evstep_eq in Hend; [| apply c_end_halted]. subst c.
    rewrite (ones_unique _ _ _ Ho (ones_c_end m)). subst x. change (olist []) with oz. rewrite HH_zero. lia.
  - destruct (spine_cases sp Hsp) as [[L0 ->] | (sp0 & L & L' & ->)].
    + (* successor: the rightmost head is a child of the root *)
      rewrite plug_root in Ex, Hb, Hg.
      assert (Hb0 : Forall (hb E) L0) by (apply Forall_app in Hb as [Hb0 _]; exact Hb0).
      assert (Hc' : Cf (S m) (encL L0 ++ [pX]) -->* c)
        by (eapply det_halt; [apply progress_evstep, (round_succ m L0 j Hb0) | exact Hc | exact Hh]).
      subst x. rewrite olist_leaf_snoc in Hx |- *. rewrite HH_osucc by apply nf_olist.
      replace (S (m + 5)) with (S m + 5) by lia.
      apply (IH (olist L0)) with (hs := L0) (w := encL L0 ++ [pX]) (c := c);
        [ split; [apply nf_olist | split; [apply nf_olist | rewrite olist_leaf_snoc; apply olt_osucc]]
        | apply nf_olist | reflexivity | exact Hb0 | apply good_succ; exact Hg | apply HRep_root
        | exact Hc' | exact Hh | exact Ho ].
    + (* limit: the rightmost head's parent p = node (L' ++ [leaf]) is copied m + 3 times *)
      rewrite plug_deep in Ex, Hb, Hg.
      destruct (round_lim m sp0 L L' j Hb) as (w' & Hr' & Hstep).
      assert (Hc' : Cf (S m) w' -->* c)
        by (eapply det_halt; [apply progress_evstep, Hstep | exact Hc | exact Hh]).
      destruct (chop_ord sp0 L L' (m + 3)) as [Hlim [Hlt _]].
      destruct (chop_ord [] L L' (m + 3)) as [_ [Hlt0 _]].
      set (hs' := plug sp0 (L ++ repeat (node L') (m + 3))) in *.
      assert (Hg' : good (node hs')).
      { apply (good_plug_repl sp0 (L ++ [node (L' ++ [leaf])])); [| right; exact Hlt0 | exact Hg].
        apply good_chop_node. exact (good_plug_bottom _ _ Hg). }
      assert (Hb' : Forall (hb E) hs').
      { eapply hb_plug_repl; [| exact Hb]. intros h'. apply hb_chop. }
      assert (Hup : N + 2 <= HH (olist hs') (S m + 5)).
      { apply (IH (olist hs')) with (hs := hs') (w := w') (c := c);
          [ subst x; repeat split; [apply nf_olist | apply nf_olist | exact Hlt]
          | apply nf_olist | reflexivity | exact Hb' | exact Hg' | exact Hr' | exact Hc' | exact Hh | exact Ho ]. }
      subst x. destruct (HH_up_lim _ (m + 3) Hx Hlim) as [U1 U2].
      replace (m + 5) with (m + 3 + 2) by lia. replace (S m + 5) with (m + 3 + 3) in Hup by lia.
      destruct (chop_exact sp0 L L' (m + 3) ltac:(lia) Hg) as [E1|E1]; fold hs' in E1; rewrite E1 in Hup; lia.
Qed.

(** ** The score bound *)

Theorem upper_bound : forall c N, c0 -->* c -> halted tm c -> ones c N -> N + 2 <= FGH (powtower 5 (ofin 3)) 6.
Proof.
  intros c N Hc Hh Ho.
  assert (H1 : Cf 1 w0 -->* c) by (eapply det_halt; [exact init | exact Hc | exact Hh]).
  pose proof (upper (olist hs0) (nf_olist hs0) 1 hs0 w0 c N eq_refl hs0_hb hs0_good hs0_rep H1 Hh Ho) as H.
  rewrite x0_eq in H. change (powtower 6 (ofin 3)) with (opow (powtower 5 (ofin 3))) in H.
  rewrite HH_pow in H by (apply nf_powtower, nf_ofin). exact H.
Qed.

(** [halts_with NB]: hydra33 halts from the blank tape with NB ones on the tape. *)
Definition halts_with (NB : nat) : Prop := exists c, c0 -->* c /\ halted tm c /\ ones c NB.

Corollary halts_with_upper : forall NB, halts_with NB -> NB + 2 <= FGH (powtower 5 (ofin 3)) 6.
Proof. intros NB (c & H1 & H2 & H3). exact (upper_bound c NB H1 H2 H3). Qed.

(** Both bounds together: the score is pinned between the published lower bound and this upper bound. *)
Corollary score_window : exists N, halts_with N /\
  FGH (powtower 5 (ofin 3)) 4 <= N + 2 /\ N + 2 <= FGH (powtower 5 (ofin 3)) 6.
Proof.
  destruct hardy_bound as (c & N & H1 & H2 & H3 & H4). exists N.
  split; [exists c; split; [exact H1 | split; assumption]|].
  split; [| exact (upper_bound c N H1 H2 H3)].
  rewrite x0_eq in H4. change (powtower 6 (ofin 3)) with (opow (powtower 5 (ofin 3))) in H4.
  rewrite HH_pow in H4 by (apply nf_powtower, nf_ofin). exact H4.
Qed.

Print Assumptions upper_bound.
Print Assumptions halts_with_upper.
Print Assumptions score_window.
