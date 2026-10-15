(** * One complete PA238 dispatcher invariant.

    The invariant retains the actual MSB program counter, marker, gap,
    header, all nine physical active blocks, and every arbitrary spare.
    Every ordinary source instruction is a proved positive literal round.
    Positive decrement appends exactly one new zero spare. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From P238.tm Require Import RM238 RMEquiv238 Prog238 Finite238 Symbolic238
  Box238 RegisterTape238 Bootstrap238 LiteralHalting238 Boxed238 BoxedNormalize238 Site238 Coverage238
  PhysicalRegisters238.
Local Unset Implicit Arguments.
Import ListNotations.

Definition dispatch238 P k R ext :=
  denote (FC 25 [true] (P ++ repeat false k ++ true :: register_file238 (physical238 R ++ ext))).

Definition Inv238 N T : Prop :=
  exists P R k ext,
    rm_run p238 N ([], R_boot238) = Some (P,R) /\
    38 <= length P + k /\ T = dispatch238 P k R ext.

Lemma inv238_boot : Inv238 0 (denote checkpoint238).
Proof.
  exists [], R_boot238, 38, spare_boot_registers.
  split; [reflexivity|]. split; [cbn; lia|]. reflexivity.
Qed.

Lemma inc_path_length238 P : length (inc_path P) = length P.
Proof.
  assert (L : forall l, length (inc_rev l) = length l).
  { induction l as [|[|] l IH]; cbn; auto. }
  unfold inc_path. rewrite rev_length, L, rev_length. reflexivity.
Qed.

Lemma strip_path_length238 b k P : length (strip_path b k P) <= length P.
Proof.
  assert (L : forall l k, length (strip_rev b k l) <= length l).
  { induction l as [|x l IH]; intros [|j]; cbn; try lia.
    destruct (Bool.eqb x b); [specialize (IH j)|specialize (IH (S j))]; lia. }
  unfold strip_path. rewrite rev_length, <- (rev_length P). apply L.
Qed.

Lemma brk_length238 k P : length (brk k P) <= length P.
Proof. unfold brk. rewrite inc_path_length238. apply strip_path_length238. Qed.

Lemma cont_length238 k P : length (cont k P) <= length P.
Proof. apply strip_path_length238. Qed.

Lemma firstn_pad_length238 P d : length (firstn d (P ++ repeat false d)) = d.
Proof. rewrite length_firstn, length_app, repeat_length. lia. Qed.

Lemma list_all_false238 l : Forall (fun b => b = false) l -> l = repeat false (length l).
Proof. induction 1 as [|x l E H IH]; [reflexivity|]. cbn. rewrite E, <- IH. reflexivity. Qed.

Lemma repeat_firstn238 (x : bool) a b : firstn a (repeat x b) = repeat x (Nat.min a b).
Proof. revert b. induction a as [|a IH]; intros [|b]; cbn; try reflexivity.
  rewrite IH. reflexivity. Qed.

Lemma split_pc238 P k d :
  Forall (fun b => b = false) (skipn d P) -> d <= length P + k ->
  P ++ repeat false k =
    firstn d (P ++ repeat false d) ++ repeat false (length P + k - d).
Proof.
  intros Z B. destruct (le_lt_dec d (length P)) as [L|L].
  - rewrite firstn_app. replace (d - length P) with 0 by lia.
    cbn [firstn app]. rewrite ?app_nil_r.
    rewrite <- (firstn_skipn d P) at 1.
    rewrite (list_all_false238 _ Z), length_skipn.
    rewrite <- app_assoc, <- repeat_sum238. f_equal. f_equal. lia.
  - rewrite firstn_app, firstn_all2 by lia. rewrite repeat_firstn238.
    replace (Nat.min (d - length P) d) with (d - length P) by lia.
    rewrite <- app_assoc, <- repeat_sum238. f_equal. f_equal. lia.
Qed.

Lemma rm_run_snoc238 N c :
  rm_run p238 (S N) c =
  match rm_run p238 N c with Some c' => rm_step p238 c' | None => None end.
Proof.
  rewrite <- Nat.add_1_r, rm_run_add.
  destruct (rm_run p238 N c) as [c'|]; [|reflexivity].
  change ((match rm_step p238 c' with
    | Some c'' => Some c'' | None => None
    end) = rm_step p238 c').
  destruct (rm_step p238 c'); reflexivity.
Qed.

Lemma rm_step_concrete238 P R :
  rm_step p238 (P,R) =
  match walk p238 186 0 P 0 with
  | None => None
  | Some (e,d) =>
      let Q := firstn d (P ++ repeat false d) in
      match e with
      | ENode _ => None
      | EInc r => Some (inc_path Q, upd R r (S (R r)))
      | EDecnz r =>
          match R r with
          | 0 => Some (brk 1 Q, R)
          | S v => Some (inc_path Q, upd R r v)
          end
      | EBreak level => Some (brk level Q, R)
      | EContinue level => Some (cont level Q, R)
      | EHalt => None
      end
  end.
Proof. reflexivity. Qed.

Lemma inv238_view N T P R : Inv238 N T ->
  rm_run p238 N ([], R_boot238) = Some (P,R) ->
  exists e d k ext,
    walk p238 186 0 P 0 = Some (e,d) /\
    check_site238 (firstn d (P ++ repeat false d)) e = true /\
    edge_bound238 e = true /\ d <= 34 /\
    T = boxed_denote238 (length P + k - 38) (physical238 R ++ ext)
      (site_start238 (firstn d (P ++ repeat false d)) 0 FilePlain238) /\
    38 <= length P + k.
Proof.
  intros [P' [R' [k [ext [H [B ->]]]]]] H'. rewrite H in H'. injection H' as <- <-.
  destruct (wf_walk p238 p238_wf P') as [e [d W]].
  destruct (walk_complete238 P' e d W) as [L [C E]].
  rewrite firstn_pad_length238 in L.
  exists e, d, k, ext. split; [exact W|]. split; [exact C|]. split; [exact E|].
  split; [exact L|]. split; [|exact B].
  rewrite site_start238_literal. cbn [phase_cells238]. unfold dispatch238.
  rewrite firstn_pad_length238.
  replace (length P' + k - 38 + (38 + 0 - d)) with (length P' + k - d) by lia.
  rewrite app_assoc, (split_pc238 P' k d (no_stray p238 R_boot238 N P' R' e d H W)) by lia.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma inv238_step N T c' : Inv238 N T ->
  rm_run p238 (S N) ([], R_boot238) = Some c' ->
  exists T' n, Inv238 (S N) T' /\ exact_steps (S n) T T'.
Proof.
  intros Inv H. rewrite rm_run_snoc238 in H.
  destruct (rm_run p238 N ([], R_boot238)) as [[P R]|] eqn:A; [|discriminate].
  destruct (inv238_view N T P R Inv A) as [e [d [k [ext [W [C [B [D [V G]]]]]]]]].
  set (Q := firstn d (P ++ repeat false d)) in *.
  set (gap := length P + k - 38) in *.
  assert (LQ : length Q = d) by apply firstn_pad_length238.
  pose proof (physical238_length R ext) as L.
  rewrite rm_step_concrete238, W in H. fold Q in H.
  destruct e as [node|r|r|level|level|]; try discriminate.
  - cbn [edge_bound238] in B. apply Nat.ltb_lt in B. injection H as <-.
    pose proof (checked_site238_variant Q (EInc r) false C ltac:(discriminate)) as C0.
    destruct (checked_variant238_round Q (EInc r) false None (inc_path Q)
      (allones238 Q) (FileIncremented238 (slot_of238 r)) gap (physical238 R ++ ext)
      C0 eq_refl (conj L I)) as [n Segment]. rewrite <- V in Segment.
    exists (boxed_denote238 gap (physical238 R ++ ext)
      (site_start238 (inc_path Q) (bool_nat238 (allones238 Q))
        (FileIncremented238 (slot_of238 r)))), n.
    split; [|exact Segment].
    exists (inc_path Q), (upd R r (S (R r))),
      (gap + (38 + bool_nat238 (allones238 Q) - length (inc_path Q))), ext.
    split; [rewrite rm_run_snoc238, A, rm_step_concrete238, W; reflexivity|].
    split.
    + rewrite inc_path_length238, LQ. unfold gap. destruct (allones238 Q); cbn [bool_nat238]; lia.
    + rewrite site_start238_literal. cbn [phase_cells238].
      rewrite physical238_update by exact B. reflexivity.
  - cbn [edge_bound238] in B. apply Nat.ltb_lt in B. destruct (R r) as [|v] eqn:E.
    + injection H as <-.
      pose proof (checked_site238_variant Q (EDecnz r) true C ltac:(discriminate)) as C0.
      assert (Valid : branch_valid238 (Some (slot_of238 r,true)) (physical238 R ++ ext)).
      { split; [exact L|]. rewrite physical238_value by exact B. exact E. }
      destruct (checked_variant238_round Q (EDecnz r) true (Some (slot_of238 r,true))
        (brk 1 Q) (allones238 (strip_path false 1 Q)) FilePlain238 gap
        (physical238 R ++ ext) C0 eq_refl Valid) as [n Segment]. rewrite <- V in Segment.
      exists (boxed_denote238 gap (physical238 R ++ ext)
        (site_start238 (brk 1 Q) (bool_nat238 (allones238 (strip_path false 1 Q)))
          FilePlain238)), n.
      split; [|exact Segment].
      exists (brk 1 Q), R,
        (gap + (38 + bool_nat238 (allones238 (strip_path false 1 Q)) - length (brk 1 Q))), ext.
      split; [rewrite rm_run_snoc238, A, rm_step_concrete238, W; fold Q; rewrite E; reflexivity|].
      split.
      * pose proof (brk_length238 1 Q). unfold gap. rewrite <- LQ in D.
        destruct (allones238 (strip_path false 1 Q)); cbn [bool_nat238]; lia.
      * rewrite site_start238_literal. reflexivity.
    + injection H as <-.
      pose proof (checked_site238_variant Q (EDecnz r) false C ltac:(discriminate)) as C0.
      assert (Valid : branch_valid238 (Some (slot_of238 r,false)) (physical238 R ++ ext)).
      { split; [exact L|]. rewrite physical238_value by exact B. rewrite E. discriminate. }
      destruct (checked_variant238_round Q (EDecnz r) false (Some (slot_of238 r,false))
        (inc_path Q) (allones238 Q) (FileDecremented238 (slot_of238 r)) gap
        (physical238 R ++ ext) C0 eq_refl Valid) as [n Segment]. rewrite <- V in Segment.
      exists (boxed_denote238 gap (physical238 R ++ ext)
        (site_start238 (inc_path Q) (bool_nat238 (allones238 Q))
          (FileDecremented238 (slot_of238 r)))), n.
      split; [|exact Segment].
      exists (inc_path Q), (upd R r v),
        (gap + (38 + bool_nat238 (allones238 Q) - length (inc_path Q))), (ext ++ [0]).
      split; [rewrite rm_run_snoc238, A, rm_step_concrete238, W; fold Q; rewrite E; reflexivity|].
      split.
      * rewrite inc_path_length238, LQ. unfold gap. destruct (allones238 Q); cbn [bool_nat238]; lia.
      * rewrite site_start238_literal. cbn [phase_cells238].
        rewrite physical238_update by exact B. rewrite E. cbn [Nat.pred].
        rewrite <- app_assoc. reflexivity.
  - injection H as <-.
    pose proof (checked_site238_variant Q (EBreak level) false C ltac:(discriminate)) as C0.
    destruct (checked_variant238_round Q (EBreak level) false None (brk level Q)
      (allones238 (strip_path false level Q)) FilePlain238 gap (physical238 R ++ ext)
      C0 eq_refl (conj L I)) as [n Segment]. rewrite <- V in Segment.
    exists (boxed_denote238 gap (physical238 R ++ ext)
      (site_start238 (brk level Q) (bool_nat238 (allones238 (strip_path false level Q)))
        FilePlain238)), n.
    split; [|exact Segment].
    exists (brk level Q), R,
      (gap + (38 + bool_nat238 (allones238 (strip_path false level Q)) - length (brk level Q))), ext.
    split; [rewrite rm_run_snoc238, A, rm_step_concrete238, W; reflexivity|].
    split.
    + pose proof (brk_length238 level Q). unfold gap. rewrite <- LQ in D.
      destruct (allones238 (strip_path false level Q)); cbn [bool_nat238]; lia.
    + rewrite site_start238_literal. reflexivity.
  - injection H as <-.
    pose proof (checked_site238_variant Q (EContinue level) false C ltac:(discriminate)) as C0.
    destruct (checked_variant238_round Q (EContinue level) false None (cont level Q)
      false FilePlain238 gap (physical238 R ++ ext) C0 eq_refl (conj L I)) as [n Segment].
    rewrite <- V in Segment.
    exists (boxed_denote238 gap (physical238 R ++ ext)
      (site_start238 (cont level Q) (bool_nat238 false) FilePlain238)), n.
    split; [|exact Segment].
    exists (cont level Q), R, (gap + (38 - length (cont level Q))), ext.
    split; [rewrite rm_run_snoc238, A, rm_step_concrete238, W; reflexivity|].
    split.
    + pose proof (cont_length238 level Q). unfold gap. rewrite <- LQ in D. lia.
    + rewrite site_start238_literal. reflexivity.
Qed.

Lemma inv238_next N T : Inv238 N T ->
  (exists c, rm_run p238 N ([], R_boot238) = Some c /\ at_halt p238 c) \/
  (exists c', rm_run p238 (S N) ([], R_boot238) = Some c').
Proof.
  intros [P [R [k [ext [H [G V]]]]]].
  destruct (wf_walk p238 p238_wf P) as [e [d W]].
  change (walk p238 186 0 P 0 = Some (e,d)) in W.
  pose proof (walk_gt p238 186 0 P 0 e d W) as [D B].
  destruct e as [node|r|r|level|level|]; try discriminate.
  - right. rewrite rm_run_snoc238, H, rm_step_concrete238, W. eexists. reflexivity.
  - right. rewrite rm_run_snoc238, H, rm_step_concrete238, W. destruct (R r); eexists; reflexivity.
  - right. rewrite rm_run_snoc238, H, rm_step_concrete238, W. eexists. reflexivity.
  - right. rewrite rm_run_snoc238, H, rm_step_concrete238, W. eexists. reflexivity.
  - left. exists (P,R). split; [exact H|]. exists d. exact W.
Qed.

Lemma inv238_halt N T c : Inv238 N T ->
  rm_run p238 N ([], R_boot238) = Some c -> at_halt p238 c -> literal_halts238 T.
Proof.
  destruct c as [P R]. intros I H [d' Halt].
  destruct (inv238_view N T P R I H) as [e [d [k [ext [W [C [B [D [V G]]]]]]]]].
  change (walk p238 186 0 P 0 = Some (EHalt,d')) in Halt.
  rewrite W in Halt. injection Halt as -> _.
  rewrite V. apply checked_site238_halt; [exact C|apply physical238_length].
Qed.

Lemma inv238_reachable N c : rm_run p238 N ([], R_boot238) = Some c ->
  exists T n, exact_steps n (denote checkpoint238) T /\ Inv238 N T.
Proof.
  revert c. induction N as [|N IH]; intros c H.
  - exists (denote checkpoint238), 0. split; [apply exact_zero|apply inv238_boot].
  - pose proof H as H'. rewrite rm_run_snoc238 in H'.
    destruct (rm_run p238 N ([], R_boot238)) as [prior|] eqn:E; [|discriminate].
    destruct (IH prior eq_refl) as [T [n [R I]]].
    destruct (inv238_step N T c I H) as [T' [m [I' Segment]]].
    exists T', (n + S m). split; [eapply exact_append; eassumption|exact I'].
Qed.

Theorem rm238_literal_halts : rm_halts p238 ([], R_boot238) -> literal_halts238 (denote checkpoint238).
Proof.
  intros [N [c [R H]]]. destruct (inv238_reachable N c R) as [T [n [S I]]].
  apply (proj2 (exact_steps_halts_iff238 n (denote checkpoint238) T S)).
  eapply inv238_halt; eassumption.
Qed.
