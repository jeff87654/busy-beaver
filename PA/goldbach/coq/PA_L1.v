(** * PA_L1: the abstract enumerator halts iff the code-level calculus derives F = 1.
    Ported from zf/m254/logic/coq/L1_Sound254.v and L1_Comp254.v (21 AX slots instead of 10;
    DISCARD closes the occurs-check gate with b = Var 1 = 7, c = 1). *)
From Coq Require Import Arith Lia Bool List.
From PAGB Require Import PA_Pair PA_Codes PA_Rows PA_Sound PA_Thm PA_Enum.
Import ListNotations.
Unset Implicit Arguments.

Lemma unP_le z : fst (unP z) <= z /\ snd (unP z) <= z.
Proof.
  pose proof (P_unP z) as E. pose proof (P_ge_l (fst (unP z)) (snd (unP z))).
  pose proof (P_ge_r (fst (unP z)) (snd (unP z))). lia.
Qed.

(** ** Soundness: the current formula, the cache and the stack stream are theorems *)
Definition popn (k w : nat) : nat := Nat.iter k (fun w => snd (unP w)) w.
Definition goodstack (w : nat) : Prop := forall k, thm (fst (unP (popn k w))).

Lemma popn_S k w : popn (S k) w = popn k (snd (unP w)).
Proof.
  unfold popn. revert w. induction k as [|k IH]; intro w; [reflexivity|].
  change (snd (unP (Nat.iter (S k) (fun w => snd (unP w)) w)) =
          snd (unP (Nat.iter k (fun w => snd (unP w)) (snd (unP w))))).
  now rewrite IH.
Qed.

Lemma good_push x w : thm x -> goodstack w -> goodstack (P x w).
Proof.
  intros Hx Hw [|k].
  - cbn. now rewrite unP_P.
  - rewrite popn_S, unP_P. apply Hw.
Qed.

Lemma good_pop w : goodstack w -> thm (fst (unP w)) /\ goodstack (snd (unP w)).
Proof. intro H. split; [exact (H 0)|]. intro k. specialize (H (S k)). now rewrite popn_S in H. Qed.

Lemma good_0 : goodstack 0.
Proof.
  assert (E : forall k, popn k 0 = 0) by (induction k; [reflexivity|]; rewrite popn_S; exact IHk).
  intro k. rewrite E. exact T_true.
Qed.

Definition Inv (s : state) : Prop := thm (tw s) /\ thm (h s) /\ goodstack (ws s).

Lemma Inv_s0 : Inv s0.
Proof. repeat split; [exact T_true | exact T_true | exact good_0]. Qed.

Lemma ax_stack_good a hh b c u t w : thm hh -> thm t -> goodstack w -> goodstack (ax_stack a hh b c u t w).
Proof.
  intros Hh Ht Hw. unfold ax_stack.
  apply good_push; [apply T_QZS|]. apply good_push; [apply T_QM0|]. apply good_push; [apply T_R1|].
  apply good_push; [apply T_QI|]. apply good_push; [apply T_CA2|]. apply good_push; [apply T_EUC|].
  apply good_push; [apply T_CM2|]. apply good_push; [apply T_L|]. apply good_push; [apply T_QA0|].
  apply good_push; [apply T_COMM|]. apply good_push; [apply T_CA1|]. apply good_push; [apply T_CS|].
  apply good_push; [apply T_EX|]. apply good_push; [apply T_QMS|]. apply good_push; [apply T_NG|].
  apply good_push; [apply T_CM1|]. apply good_push; [apply T_B6c|]. apply good_push; [apply T_QSI|].
  apply good_push; [apply T_QAS|]. apply good_push; [now apply T_gen|].
  now apply good_push.
Qed.

Lemma Inv_step s s' : Inv s -> enum_step s = Some s' -> Inv s'.
Proof.
  intros [Ht [Hh Hw]]. unfold enum_step.
  destruct (if Nat.eqb (pl s) 0 then _ else _) as [pl1 np1].
  destruct (unP pl1) as [ac pl2]. destruct (unP pl2) as [x pl3].
  destruct ac as [|[|[|c]]].
  - destruct (Nat.eqb (wim (tw s) (d s + x)) (h s)) eqn:E; intro H; injection H as <-.
    + apply Nat.eqb_eq in E. repeat split; cbn [tw h ws].
      * apply (T_mp (tw s)); [exact Ht | now rewrite E].
      * exact T_true.
      * apply good_push; [exact T_true | exact Hw].
    + repeat split; cbn [tw h ws]; [exact T_true | exact T_true | exact Hw].
  - intro H; injection H as <-. repeat split; cbn [tw h ws]; [exact Hh | exact Hh | now apply good_push].
  - destruct (Nat.eqb (h s) 1); [discriminate|].
    destruct (good_pop _ Hw) as [H1 H2]. destruct (unP (ws s)) as [h1 w1] eqn:E.
    intro H; injection H as <-. repeat split; cbn [tw h ws]; [exact Ht | exact H1 | exact H2].
  - destruct (unP pl3) as [y pl4]. destruct (unP pl4) as [u pl5].
    intro H; injection H as <-. repeat split; cbn [tw h ws].
    + apply T_bundle.
    + exact T_true.
    + now apply ax_stack_good.
Qed.

Lemma Inv_run n s s' : Inv s -> run n s = Some s' -> Inv s'.
Proof.
  revert s. induction n as [|n IH]; intros s Hs H; cbn in H.
  - now injection H as <-.
  - destruct (enum_step s) as [s1|] eqn:E; [|discriminate].
    exact (IH s1 (Inv_step s s1 Hs E) H).
Qed.

Lemma halt_step s : Inv s -> enum_step s = None -> thm F.
Proof.
  intros [Ht [Hh Hw]]. unfold enum_step.
  destruct (if Nat.eqb (pl s) 0 then _ else _) as [pl1 np1].
  destruct (unP pl1) as [ac pl2]. destruct (unP pl2) as [x pl3].
  destruct ac as [|[|[|c]]]; try discriminate.
  - destruct (Nat.eqb (h s) 1) eqn:E.
    + intros _. apply Nat.eqb_eq in E. unfold F. now rewrite <- E.
    + destruct (unP (ws s)); discriminate.
  - destruct (unP pl3) as [y pl4]. destruct (unP pl4). discriminate.
Qed.

Theorem enum_sound : enum_halts -> thm F.
Proof. intros [n [s [H1 H2]]]. exact (halt_step s (Inv_run n s0 s Inv_s0 H1) H2). Qed.

(** ** Completeness: a derivation compiles to a command list *)
Inductive cmd : Type := CMP (x : nat) | CDROP | CNIP | CAX (c x y u : nat).

Definition fields (k : cmd) : list nat :=
  match k with
  | CMP x => [0; x] | CDROP => [1; 0] | CNIP => [2; 0] | CAX c x y u => [S (S (S c)); x; y; u]
  end.

Definition enc_fields (fs : list nat) (r : nat) : nat := fold_right P r fs.

Fixpoint enc_tail (L : list cmd) : nat :=
  match L with [] => 0 | k :: L => S (enc_fields (fields k) (enc_tail L)) end.

Definition tup : Type := (nat * nat * nat * nat)%type.

Definition xstep (k : cmd) (q : tup) : option tup :=
  let '(t, w, dd, hh) := q in
  match k with
  | CMP x => Some (if Nat.eqb (wim t (dd + x)) hh then (dd + x, P 0 w, dd + x, 0) else (0, w, dd + x, 0))
  | CDROP => Some (hh, P t w, dd, hh)
  | CNIP => if Nat.eqb hh 1 then None else Some (t, snd (unP w), dd, fst (unP w))
  | CAX c x y u => Some (bundle (dd + x) (hh + y) c, ax_stack (dd + x) hh (hh + y) c u t w, 0, 0)
  end.

Fixpoint exec (L : list cmd) (q : tup) : option tup :=
  match L with
  | [] => Some q
  | k :: L => match xstep k q with Some q' => exec L q' | None => None end
  end.

Lemma exec_app L1 L2 q :
  exec (L1 ++ L2) q = match exec L1 q with Some q' => exec L2 q' | None => None end.
Proof.
  revert q; induction L1 as [|k L1 IH]; intro q; [reflexivity|].
  cbn. destruct (xstep k q); [apply IH | reflexivity].
Qed.

Definition tupof (s : state) : tup := (tw s, ws s, d s, h s).

Lemma step_read s k r np1 :
  (pl s = S (enc_fields (fields k) r) /\ np1 = np s) \/
  (pl s = 0 /\ np s = enc_fields (fields k) r /\ np1 = S (np s)) ->
  enum_step s = match xstep k (tupof s) with
                | Some (t, w, dd, hh) => Some (mkState r np1 t w dd hh)
                | None => None
                end.
Proof.
  intro H. unfold enum_step.
  assert (E : (if Nat.eqb (pl s) 0 then (np s, S (np s)) else (pred (pl s), np s))
              = (enc_fields (fields k) r, np1)).
  { destruct H as [[-> ->] | [-> [-> ->]]]; reflexivity. }
  rewrite E. clear E H. unfold tupof.
  destruct s as [pl0 np0 t w dd hh]; cbn [tw ws d h].
  destruct k as [x| | |c x y u]; cbn [fields enc_fields fold_right]; rewrite !unP_P; cbn [xstep].
  - destruct (Nat.eqb (wim t (dd + x)) hh); reflexivity.
  - now rewrite Nat.add_0_r.
  - rewrite Nat.add_0_r. destruct (Nat.eqb hh 1); [reflexivity|]. now destruct (unP w).
  - reflexivity.
Qed.

Definition halts_from (s : state) : Prop := exists n s', run n s = Some s' /\ enum_step s' = None.

Lemma halts_from_step s s' : enum_step s = Some s' -> halts_from s' -> halts_from s.
Proof. intros E [n [s2 [H1 H2]]]. exists (S n), s2. cbn. now rewrite E. Qed.

Lemma run_tail L : forall s, pl s = enc_tail L -> exec L (tupof s) = None -> halts_from s.
Proof.
  induction L as [|k L IH]; intros s Hp He; [discriminate|].
  cbn [exec] in He. pose proof (step_read s k (enc_tail L) (np s) (or_introl (conj Hp eq_refl))) as E.
  destruct (xstep k (tupof s)) as [[[[t w] dd] hh]|] eqn:X.
  - eapply halts_from_step; [exact E|]. apply IH; [reflexivity | exact He].
  - exists 0, s. split; [reflexivity | exact E].
Qed.

Lemma run_first k L s : pl s = 0 -> np s = enc_fields (fields k) (enc_tail L) ->
  exec (k :: L) (tupof s) = None -> halts_from s.
Proof.
  intros Hp Hn He. cbn [exec] in He.
  pose proof (step_read s k (enc_tail L) (S (np s)) (or_intror (conj Hp (conj Hn eq_refl)))) as E.
  destruct (xstep k (tupof s)) as [[[[t w] dd] hh]|] eqn:X.
  - eapply halts_from_step; [exact E|]. apply (run_tail L); [reflexivity | exact He].
  - exists 0, s. split; [reflexivity | exact E].
Qed.

Lemma step_pl s s' : enum_step s = Some s' ->
  pl s' <= (if Nat.eqb (pl s) 0 then np s else pred (pl s)) /\
  np s' = (if Nat.eqb (pl s) 0 then S (np s) else np s).
Proof.
  unfold enum_step. destruct (if Nat.eqb (pl s) 0 then _ else _) as [pl1 np1] eqn:E.
  assert (Hl : pl1 = (if Nat.eqb (pl s) 0 then np s else pred (pl s)) /\
               np1 = (if Nat.eqb (pl s) 0 then S (np s) else np s))
    by (destruct (Nat.eqb (pl s) 0); now injection E as <- <-).
  destruct Hl as [-> ->]. clear E.
  set (z := if Nat.eqb (pl s) 0 then np s else pred (pl s)).
  pose proof (unP_le z) as [_ L1].
  destruct (unP z) as [ac pl2] eqn:E2. cbn in L1.
  pose proof (unP_le pl2) as [_ L2].
  destruct (unP pl2) as [x pl3] eqn:E3. cbn in L2.
  destruct ac as [|[|[|c]]].
  - destruct (Nat.eqb (wim (tw s) (d s + x)) (h s)); intro H; injection H as <-; cbn [pl np]; lia.
  - intro H; injection H as <-; cbn [pl np]; lia.
  - destruct (Nat.eqb (h s) 1); [discriminate|]. destruct (unP (ws s)).
    intro H; injection H as <-; cbn [pl np]; lia.
  - pose proof (unP_le pl3) as [_ L3]. destruct (unP pl3) as [y pl4] eqn:E4. cbn in L3.
    pose proof (unP_le pl4) as [_ L4]. destruct (unP pl4) as [u pl5] eqn:E5. cbn in L4.
    intro H; injection H as <-; cbn [pl np]; lia.
Qed.

Lemma run_add n m s :
  run (n + m) s = match run n s with Some s' => run m s' | None => None end.
Proof.
  revert s; induction n as [|n IH]; intro s; [reflexivity|].
  cbn. destruct (enum_step s); [apply IH | reflexivity].
Qed.

Lemma drain k : forall s, pl s <= k ->
  halts_from s \/ exists n s', run n s = Some s' /\ pl s' = 0 /\ np s' = np s.
Proof.
  induction k as [|k IH]; intros s Hk.
  - right. exists 0, s. split; [reflexivity|]. split; [lia | reflexivity].
  - destruct (pl s) as [|p] eqn:Ep.
    + right. exists 0, s. split; [reflexivity | now split].
    + destruct (enum_step s) as [s1|] eqn:E.
      * pose proof (step_pl s s1 E) as [H1 H2]. rewrite Ep in H1, H2. cbn in H1, H2.
        destruct (IH s1 ltac:(lia)) as [Hh | [n [s2 [R [P0 N0]]]]].
        -- left. exact (halts_from_step s s1 E Hh).
        -- right. exists (S n), s2. cbn. rewrite E. split; [exact R|]. split; [exact P0|]. lia.
      * left. exists 0, s. split; [reflexivity | exact E].
Qed.

Lemma reach m : enum_halts \/ exists n s, run n s0 = Some s /\ pl s = 0 /\ np s = m.
Proof.
  induction m as [|m [Hh | [n [s [R [P0 N0]]]]]].
  - right. exists 0, s0. repeat split.
  - left. exact Hh.
  - destruct (enum_step s) as [s1|] eqn:E.
    + pose proof (step_pl s s1 E) as [H1 H2]. rewrite P0 in H1, H2. cbn in H1, H2.
      destruct (drain (pl s1) s1 (le_n _)) as [[k [s2 [R2 H2']]] | [k [s2 [R2 [P2 N2]]]]].
      * left. exists (n + S k), s2. split; [|exact H2'].
        rewrite run_add, R. cbn. now rewrite E.
      * right. exists (n + S k), s2. split; [rewrite run_add, R; cbn; now rewrite E|].
        split; [exact P2 | lia].
    + left. exists n, s. now split.
Qed.

Lemma halts_from_reach n s : run n s0 = Some s -> halts_from s -> enum_halts.
Proof.
  intros R [k [s' [R' H]]]. exists (n + k), s'. split; [|exact H].
  rewrite run_add, R. exact R'.
Qed.

(** ** No root code is F *)
Lemma wim_ne1 a b : wim a b <> 1.
Proof. unfold wim. lia. Qed.
Lemma weq_ne1 a b : weq a b <> 1.
Proof. unfold weq. lia. Qed.
Lemma wal_ne1 a b : wal a b <> 1.
Proof. unfold wal. lia. Qed.

Lemma bundle_ne1 a b c : bundle a b c <> 1.
Proof. unfold bundle. destruct (gate a b c); [cbn [cd r_bundle AAnd]; unfold wn; apply wim_ne1 | lia]. Qed.

Lemma slot6_ne1 a b c u : slot6 a b c u <> 1.
Proof. unfold slot6, r_NG, NGw. cbn [enc cd]. unfold wn. apply wim_ne1. Qed.

Lemma eqb_ne1 v : v <> 1 -> Nat.eqb v 1 = false.
Proof. apply Nat.eqb_neq. Qed.

Ltac ne1 := first
  [ apply bundle_ne1 | apply wim_ne1 | apply weq_ne1 | apply wal_ne1 | apply slot6_ne1
  | unfold slot2, slot3, slot4, slot5, slot7, slot8, slot9, slot10, slot11, slot12, slot13,
      slot14, slot15, slot16, slot17, slot18, slot19, slot20;
    cbn [cd r_QAS r_QSI r_B6c r_CM1 r_QMS r_EX r_CS r_CA1 r_COMM r_QA0 r_L r_CM2 r_EUC r_CA2
         r_QI r_R1 r_QM0 r_QZS AEx];
    unfold wn; first [apply wim_ne1 | apply weq_ne1 | apply wal_ne1]
  | lia ].

Lemma ex_nip t x w dd hh L : hh <> 1 -> exec (CNIP :: L) (t, P x w, dd, hh) = exec L (t, w, dd, x).
Proof. intro H. cbn [exec xstep]. rewrite (eqb_ne1 hh H), unP_P. reflexivity. Qed.
Lemma ex_nip1 t w dd L : exec (CNIP :: L) (t, w, dd, 1) = None.
Proof. reflexivity. Qed.
Lemma ex_drop t w dd hh L : exec (CDROP :: L) (t, w, dd, hh) = exec L (hh, P t w, dd, hh).
Proof. reflexivity. Qed.
Lemma ex_ax c x y u t w dd hh L : exec (CAX c x y u :: L) (t, w, dd, hh) =
  exec L (bundle (dd + x) (hh + y) c, ax_stack (dd + x) hh (hh + y) c u t w, 0, 0).
Proof. reflexivity. Qed.
Lemma ex_mp_ok t x w dd hh L : wim t (dd + x) = hh ->
  exec (CMP x :: L) (t, w, dd, hh) = exec L (dd + x, P 0 w, dd + x, 0).
Proof. intro H. cbn [exec xstep]. now rewrite H, Nat.eqb_refl. Qed.
Lemma ex_mp_fail t x w dd hh L : wim t (dd + x) <> hh ->
  exec (CMP x :: L) (t, w, dd, hh) = exec L (0, w, dd + x, 0).
Proof. intro H. cbn [exec xstep]. apply Nat.eqb_neq in H. now rewrite H. Qed.
Lemma ex_nil q : exec [] q = Some q.
Proof. reflexivity. Qed.

Ltac xrun :=
  repeat first
    [ progress cbn [repeat app Nat.sub]
    | rewrite ex_drop
    | rewrite ex_ax
    | rewrite ex_nip by ne1
    | rewrite ex_nil
    | progress unfold ax_stack
    | progress (cbn [Nat.add]; rewrite ?Nat.add_0_r) ].

Definition blk (X : nat) (L : list cmd) : Prop :=
  forall T w, exec L (T, w, 0, 0) = None \/ exec L (T, w, 0, 0) = Some (X, w, 0, 0).

(** DISCARD: a failed MP, then an AX whose gate is closed (c = 1 occurs in T 7 = v1) *)
Definition DISCARD : list cmd := [CMP 1; CAX 1 0 7 0] ++ repeat CNIP 21.

Lemma bundle_closed : bundle 1 7 1 = 0.
Proof. reflexivity. Qed.

Lemma wim_T1_ne0 T : wim T 1 <> 0.
Proof. unfold wim. pose proof (P_ge_r T 1). lia. Qed.

Lemma discard T w : exec DISCARD (T, w, 0, 0) = Some (0, w, 0, 0).
Proof.
  unfold DISCARD. cbn [repeat app]. rewrite ex_mp_fail by apply wim_T1_ne0. cbn [Nat.add].
  rewrite ex_ax. cbn [Nat.add]. rewrite bundle_closed. xrun. reflexivity.
Qed.

Lemma blk_true : blk 0 DISCARD.
Proof. intros T w. right. apply discard. Qed.

(** leaves: slot k (2 .. 20) is at depth 21 - k *)
Definition leaf (k a b c u : nat) : list cmd :=
  DISCARD ++ [CAX c a b u] ++ repeat CNIP (21 - k) ++ [CDROP] ++ repeat CNIP (S k).

Ltac leaf_tac := intros T w; right; unfold leaf; rewrite exec_app, discard; xrun; reflexivity.

Lemma blk_s2 a b c u : blk (slot2 a b c u) (leaf 2 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_s3 a b c u : blk (slot3 a b c u) (leaf 3 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_s4 a b c u : blk (slot4 a b c u) (leaf 4 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_s5 a b c u : blk (slot5 a b c u) (leaf 5 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_s6 a b c u : blk (slot6 a b c u) (leaf 6 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_s7 a b c u : blk (slot7 a b c u) (leaf 7 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_s8 a b c u : blk (slot8 a b c u) (leaf 8 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_s9 a b c u : blk (slot9 a b c u) (leaf 9 a b c u).     Proof. leaf_tac. Qed.
Lemma blk_s10 a b c u : blk (slot10 a b c u) (leaf 10 a b c u).  Proof. leaf_tac. Qed.
Lemma blk_s11 a b c u : blk (slot11 a b c u) (leaf 11 a b c u).  Proof. leaf_tac. Qed.
Lemma blk_s12 a b c u : blk (slot12 a b c u) (leaf 12 a b c u).  Proof. leaf_tac. Qed.
Lemma blk_s13 a b c u : blk (slot13 a b c u) (leaf 13 a b c u).  Proof. leaf_tac. Qed.
Lemma blk_s14 a b c u : blk (slot14 a b c u) (leaf 14 a b c u).  Proof. leaf_tac. Qed.
Lemma blk_s15 a b c u : blk (slot15 a b c u) (leaf 15 a b c u).  Proof. leaf_tac. Qed.
Lemma blk_s16 a b c u : blk (slot16 a b c u) (leaf 16 a b c u).  Proof. leaf_tac. Qed.
Lemma blk_s17 a b c u : blk (slot17 a b c u) (leaf 17 a b c u).  Proof. leaf_tac. Qed.
Lemma blk_s18 a b c u : blk (slot18 a b c u) (leaf 18 a b c u).  Proof. leaf_tac. Qed.
Lemma blk_s19 a b c u : blk (slot19 a b c u) (leaf 19 a b c u).  Proof. leaf_tac. Qed.
Lemma blk_s20 a b c u : blk (slot20 a b c u) (leaf 20 a b c u).  Proof. leaf_tac. Qed.

Definition leafB (a b c : nat) : list cmd := DISCARD ++ [CAX c a b 0] ++ repeat CNIP 21.

Lemma blk_bundle a b c : blk (bundle a b c) (leafB a b c).
Proof. intros T w. right. unfold leafB. rewrite exec_app, discard. xrun. reflexivity. Qed.

(** GEN *)
Definition genb (i : nat) (L : list cmd) : list cmd :=
  L ++ [CDROP; CNIP; CAX i i 0 0] ++ repeat CNIP 20 ++ [CDROP; CNIP; CNIP].

Lemma blk_gen i X L : blk X L -> blk (wal i X) (genb i L).
Proof.
  intros HL T w. unfold genb. rewrite exec_app.
  destruct (HL T w) as [-> | ->]; [now left|]. right.
  xrun. reflexivity.
Qed.

(** MP node *)
Definition mpb (B : nat) (LA LI : list cmd) : list cmd :=
  LA ++ [CDROP] ++ LI ++ [CNIP; CDROP; CNIP; CMP B; CAX B 0 0 0] ++ repeat CNIP 21 ++ [CDROP; CNIP; CNIP].

Lemma blk_mp A B LA LI : blk A LA -> blk (wim A B) LI -> blk B (mpb B LA LI).
Proof.
  intros HA HI T w. unfold mpb. rewrite exec_app.
  destruct (HA T w) as [-> | ->]; [now left|].
  cbn [app]. rewrite ex_drop, exec_app.
  destruct (HI 0 (P A w)) as [-> | ->]; [now left|].
  cbn [repeat app]. rewrite ex_nip by lia. rewrite ex_drop.
  destruct (Nat.eq_dec A 1) as [EA | EA].
  { left. subst A. apply ex_nip1. }
  rewrite (ex_nip _ _ _ _ _ _ EA). rewrite ex_mp_ok by reflexivity. cbn [Nat.add]. xrun.
  destruct (Nat.eq_dec B 1) as [EB | EB].
  { left. subst B. apply ex_nip1. }
  rewrite (ex_nip _ _ _ _ _ _ EB). xrun. right. reflexivity.
Qed.

(** ** Compilation of derivations *)
Lemma compile X : thm X -> exists L, blk X L.
Proof.
  induction 1 as [| t b _ [LA HA] _ [LI HI] | a hh _ [L HL]
                  | a b c u | a b c | a b c | a b | a b c | a b | a b c | a b c | a b c | a b c
                  | a b | c | x | x y | x | x y | x | x y | | a b c].
  - exists DISCARD. exact blk_true.
  - exists (mpb b LA LI). exact (blk_mp t b LA LI HA HI).
  - exists (genb a L). exact (blk_gen a hh L HL).
  - exists (leaf 13 a b c u). apply blk_s13.
  - exists (leaf 17 a b c 0). apply blk_s17.
  - exists (leaf 11 a b c 0). apply blk_s11.
  - exists (leaf 4 a b 0 0). apply blk_s4.
  - exists (leaf 15 a b c 0). apply blk_s15.
  - exists (leaf 9 a b 0 0). apply blk_s9.
  - exists (leaf 10 a b c 0). apply blk_s10.
  - exists (leaf 16 a b c 0). apply blk_s16.
  - exists (leaf 5 a b c 0). apply blk_s5.
  - exists (leaf 14 a b c 0). apply blk_s14.
  - exists (leaf 18 a b 0 0). apply blk_s18.
  - exists (leaf 8 0 0 c 0). apply blk_s8.
  - exists (leaf 20 x 0 0 0). apply blk_s20.
  - exists (leaf 3 x y 0 0). apply blk_s3.
  - exists (leaf 12 0 0 x 0). apply blk_s12.
  - exists (leaf 2 x y 0 0). apply blk_s2.
  - exists (leaf 19 x 0 0 0). apply blk_s19.
  - exists (leaf 7 x y 0 0). apply blk_s7.
  - exists (leaf 6 0 0 0 0). apply blk_s6.
  - exists (leafB a b c). apply blk_bundle.
Qed.

(** ** The whole program halts from every retained state *)
Definition START : cmd := CAX 0 1 1 0.
Definition SUFFIX : list cmd := [CDROP; CNIP; CNIP].

Lemma program_halts L : blk 1 L -> forall q, exec (START :: L ++ SUFFIX) q = None.
Proof.
  intros HL [[[t w] dd] hh]. unfold START. rewrite ex_ax, exec_app.
  destruct (HL (bundle (dd + 1) (hh + 1) 0) (ax_stack (dd + 1) hh (hh + 1) 0 0 t w)) as [-> | ->];
    [reflexivity|].
  unfold SUFFIX. rewrite ex_drop, ex_nip by lia. apply ex_nip1.
Qed.

Theorem enum_complete : thm F -> enum_halts.
Proof.
  intro H. destruct (compile F H) as [L HL].
  set (N := enc_fields (fields START) (enc_tail (L ++ SUFFIX))).
  destruct (reach N) as [Hh | [n [s [R [P0 N0]]]]]; [exact Hh|].
  apply (halts_from_reach n s R).
  apply (run_first START (L ++ SUFFIX) s P0 N0).
  apply program_halts. exact HL.
Qed.

Theorem L1 : enum_halts <-> thm F.
Proof. split; [exact enum_sound | exact enum_complete]. Qed.

Print Assumptions L1.
