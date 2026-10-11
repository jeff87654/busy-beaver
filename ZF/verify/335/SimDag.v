(** * SimDag: static facts about the decision DAG [zf2] (checked by [vm_compute]) and the
    IP-space bound along the RM run. *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith Lia.
From ZF Require Import RM ZF2Dag RMEquiv.
Import ListNotations.

(* the edge taken by node [n] on bit [b] (same as ZFTM.node_edge) *)
Definition dedge (n : nat) (b : bool) : edge := if b then snd (zf2_nodes n) else fst (zf2_nodes n).

(* boolean version of the edge-shape condition *)
Definition eck (b : bool) (e : edge) : bool :=
  match e with
  | ENode m => m <? 269
  | EInc r | EDecnz r => r <=? 10
  | EBreak k => b && (1 <=? k) && (k <=? 1)
  | EContinue k => b && (1 <=? k) && (k <=? 5)
  | EHalt => b
  end.

Lemma eck_all :
  forallb (fun n => eck false (dedge n false) && eck true (dedge n true)) (seq 0 269) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma in_seq269 n : n < 269 -> In n (seq 0 269).
Proof. intros H. apply in_seq. lia. Qed.

(** Shape of the edges: break / continue / halt leaves only in cdr position. *)
Lemma zf2_edges n b : n < 269 ->
  match dedge n b with
  | ENode m => m < 269
  | EInc r | EDecnz r => r <= 10
  | EBreak k => b = true /\ 1 <= k <= 1
  | EContinue k => b = true /\ 1 <= k <= 5
  | EHalt => b = true
  end.
Proof.
  intros Hn. pose proof eck_all as A. rewrite forallb_forall in A.
  specialize (A n (in_seq269 n Hn)).
  apply andb_prop in A as [A0 A1].
  assert (Hb : eck b (dedge n b) = true) by (destruct b; assumption). clear A0 A1.
  destruct (dedge n b); cbn [eck] in Hb;
    repeat match goal with
    | H : _ && _ = true |- _ => apply andb_prop in H; destruct H
    | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
    | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
    end; first [assumption | lia | split; [assumption | lia]].
Qed.

(** ** Generic walk facts for [zf2] *)

Lemma walk_S_zf2 f n P i :
  walk zf2 (S f) n P i =
  match dedge n (bit P i) with ENode m => walk zf2 f m P (S i) | e => Some (e, S i) end.
Proof. apply walk_S. Qed.

Lemma bits_cons P i k : map (bit P) (seq i (S k)) = bit P i :: map (bit P) (seq (S i) k).
Proof. reflexivity. Qed.

(* every leaf reached is an edge of some node *)
Lemma walk_leaf_edge f n P i e d :
  n < 269 -> walk zf2 f n P i = Some (e, d) -> exists n' b, n' < 269 /\ dedge n' b = e.
Proof.
  revert n i. induction f as [|f IH]; intros n i Hn W; [discriminate|].
  rewrite walk_S_zf2 in W. pose proof (zf2_edges n (bit P i) Hn) as Ed.
  destruct (dedge n (bit P i)) as [m| | | | |] eqn:E;
    try (injection W as <- _; eauto).
  eapply IH; eassumption.
Qed.

(** ** Depth, via the height table of RMEquiv *)
Definition tH : list nat := fix_tab zf2 h_step.

Definition depth_check : bool :=
  (lk tH 0 <=? 109) &&
  forallb (fun n => (hE (lk tH) (dedge n false) <? lk tH n) && (hE (lk tH) (dedge n true) <? lk tH n))
    (seq 0 269).

Lemma depth_check_ok : depth_check = true.
Proof. vm_compute. reflexivity. Qed.

Section Depth.
Variable H : nat -> nat.
Hypothesis HH : forall n b, n < 269 -> hE H (dedge n b) < H n.

Lemma walk_depth_gen f n P i e d : n < 269 -> walk zf2 f n P i = Some (e, d) -> d <= i + H n.
Proof.
  revert n i. induction f as [|f IH]; intros n i Hn W; [discriminate|].
  rewrite walk_S_zf2 in W. pose proof (zf2_edges n (bit P i) Hn) as Ed.
  pose proof (HH n (bit P i) Hn) as Hh.
  destruct (dedge n (bit P i)) as [m| | | | |] eqn:E;
    try (injection W as _ <-; simpl in Hh; lia).
  simpl in Hh. specialize (IH m (S i) Ed W). lia.
Qed.
End Depth.

(** Zero runs: as in SimBase.nz (duplicated here to keep this file independent of busycoq). *)
Fixpoint nzd (c : nat) (U : list bool) : bool :=
  match U with
  | [] => true
  | true :: U => nzd 0 U
  | false :: U => andb (Nat.ltb c 7) (nzd (S c) U)
  end.

(* the zero count after reading [U] *)
Fixpoint nzr (c : nat) (U : list bool) : nat :=
  match U with
  | [] => c
  | true :: U => nzr 0 U
  | false :: U => nzr (S c) U
  end.

Lemma nzd_app c U V : nzd c (U ++ V) = andb (nzd c U) (nzd (nzr c U) V).
Proof.
  revert c. induction U as [|[|] U IH]; intro c; simpl; [reflexivity | apply IH |].
  rewrite IH. apply andb_assoc.
Qed.

Lemma nzr_app c U V : nzr c (U ++ V) = nzr (nzr c U) V.
Proof. revert c. induction U as [|[|] U IH]; intro c; simpl; auto. Qed.

(* car-chain lengths *)
Definition cz_step (p : prog) (t : list nat) : list nat :=
  table p (fun n => match fst (nodes p n) with ENode m => S (lk t m) | _ => 1 end).
Definition tZ : list nat := fix_tab zf2 cz_step.

Definition cz_check : bool :=
  forallb (fun n => (1 <=? lk tZ n) && (lk tZ n <=? 7) &&
     match dedge n false with ENode m => S (lk tZ m) <=? lk tZ n | _ => true end)
    (seq 0 269).

Lemma cz_check_ok : cz_check = true.
Proof. vm_compute. reflexivity. Qed.

Section Zeros.
Variable Z : nat -> nat.
Hypothesis HZ : forall n, n < 269 ->
  1 <= Z n /\ Z n <= 7 /\ (forall m, dedge n false = ENode m -> S (Z m) <= Z n).

Lemma walk_nz_gen f n P i e d : n < 269 -> walk zf2 f n P i = Some (e, d) ->
  nzd 0 (rev (map (bit P) (seq i (d - i)))) = true /\
  nzr 0 (rev (map (bit P) (seq i (d - i)))) <= Z n.
Proof.
  revert n i. induction f as [|f IH]; intros n i Hn W; [discriminate|].
  pose proof (walk_gt _ _ _ _ _ _ _ W) as [Hd _].
  replace (d - i) with (S (d - S i)) by lia. rewrite bits_cons. simpl rev.
  rewrite nzd_app, nzr_app.
  rewrite walk_S_zf2 in W. pose proof (zf2_edges n (bit P i) Hn) as Ed.
  destruct (HZ n Hn) as (Z1 & Z9 & Zc).
  destruct (bit P i) eqn:Eb; destruct (dedge n _) as [m| | | | |] eqn:E;
    try (injection W as _ <-; rewrite Nat.sub_diag; simpl; split; [reflexivity | lia]).
  - destruct (IH m (S i) Ed W) as [I1 I2]. rewrite I1. simpl. split; [reflexivity | lia].
  - destruct (IH m (S i) Ed W) as [I1 I2]. rewrite I1. specialize (Zc m eq_refl).
    simpl. rewrite andb_true_r. split; [apply Nat.ltb_lt; lia | lia].
Qed.
End Zeros.

(** The bits read by a walk from the root have no 8 consecutive zeros (max car chain = 7). *)
Lemma walk_nz P e d :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) ->
  nzd 0 (rev (firstn d (P ++ repeat false d))) = true.
Proof.
  intros W. rewrite pad_bits. rewrite <- (Nat.sub_0_r d).
  refine (proj1 (walk_nz_gen (lk tZ) _ (nnodes zf2 + 1) 0 P 0 e d _ W)); [| simpl; lia].
  intros n Hn. pose proof cz_check_ok as A. unfold cz_check in A. rewrite forallb_forall in A.
  specialize (A n (in_seq269 n Hn)).
  apply andb_prop in A as [A Am]. apply andb_prop in A as [A1 A9].
  apply Nat.leb_le in A1, A9. split; [exact A1|]. split; [exact A9|].
  intros m Em. rewrite Em in Am. apply Nat.leb_le, Am.
Qed.

(** ** Continue levels, via the table [C] of the well-formedness proof *)
Section Cont.
Variable C : nat -> nat.
Hypothesis HC : forall n, n < 269 ->
  cE C (dedge n false) <= C n /\ cE C (dedge n true) <= S (C n).

Lemma walk_cont_gen f n P i k d : n < 269 -> walk zf2 f n P i = Some (EContinue k, d) ->
  k <= C n + count_occ bool_dec (map (bit P) (seq i (d - i))) true.
Proof.
  revert n i. induction f as [|f IH]; intros n i Hn W; [discriminate|].
  pose proof (walk_gt _ _ _ _ _ _ _ W) as [Hd _].
  replace (d - i) with (S (d - S i)) by lia. rewrite bits_cons.
  rewrite walk_S_zf2 in W. pose proof (zf2_edges n (bit P i) Hn) as Ed.
  destruct (HC n Hn) as [C0 C1].
  destruct (bit P i) eqn:Eb; destruct (dedge n _) as [m| | | | |] eqn:E;
    try discriminate; simpl count_occ;
    try (injection W as -> <-; simpl in C0, C1; lia).
  - specialize (IH m (S i) Ed W). simpl in C1. lia.
  - specialize (IH m (S i) Ed W). simpl in C0. lia.
Qed.
End Cont.

(** A continue leaf is reached only after enough cdr edges (ones) on the path. *)
Lemma walk_cont P k d :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (EContinue k, d) ->
  k <= count_occ bool_dec (firstn d (P ++ repeat false d)) true.
Proof.
  intros W. destruct (wf_escape zf2 zf2_wf) as (B & C & _ & C0 & HBC).
  rewrite pad_bits. rewrite <- (Nat.sub_0_r d).
  enough (k <= C 0 + count_occ bool_dec (map (bit P) (seq 0 (d - 0))) true) by (simpl in C0; lia).
  apply (walk_cont_gen C) with (f := nnodes zf2 + 1); [| simpl; lia | exact W].
  intros n Hn. destruct (HBC n Hn) as (_ & _ & H0 & H1). split; assumption.
Qed.

(** Depth bound. *)
Lemma walk_depth P e d :
  walk zf2 (nnodes zf2 + 1) (root zf2) P 0 = Some (e, d) -> d <= 109.
Proof.
  intros W. pose proof depth_check_ok as A. unfold depth_check in A.
  apply andb_prop in A as [A0 A]. apply Nat.leb_le in A0. rewrite forallb_forall in A.
  enough (d <= 0 + lk tH 0) by lia.
  apply (walk_depth_gen (lk tH)) with (f := nnodes zf2 + 1) (P := P) (e := e); [| simpl; lia | exact W].
  intros n b Hn. specialize (A n (in_seq269 n Hn)).
  apply andb_prop in A as [A1 A2]. destruct b; apply Nat.ltb_lt; assumption.
Qed.

(** ** IP space along the run.  [need c] = cells right of the IP marker needed by the next
    operation; [ndec n c] = number of decnz operations among the first [n] steps from [c]. *)
Definition is_dec (c : conf) : nat :=
  match walk zf2 (nnodes zf2 + 1) (root zf2) (fst c) 0 with
  | Some (EDecnz _, _) => 1
  | _ => 0
  end.

Fixpoint ndec (n : nat) (c : conf) : nat :=
  match n with
  | 0 => 0
  | S n => match rm_step zf2 c with None => 0 | Some c' => is_dec c + ndec n c' end
  end.

Definition need (c : conf) : nat :=
  match walk zf2 (nnodes zf2 + 1) (root zf2) (fst c) 0 with
  | Some (EInc r, d) | Some (EDecnz r, d) => d + r + 3
  | Some (_, d) => d
  | None => 0
  end.

Lemma need_le c : need c <= 122.
Proof.
  unfold need. destruct (walk zf2 (nnodes zf2 + 1) (root zf2) (fst c) 0) as [[e d]|] eqn:W;
    [|lia].
  pose proof (walk_depth _ _ _ W) as Hd.
  assert (Hr : root zf2 < 269) by (simpl; lia).
  destruct (walk_leaf_edge _ _ _ _ _ _ Hr W) as (n' & b & Hn' & E).
  pose proof (zf2_edges n' b Hn') as Ed. rewrite E in Ed.
  destruct e; lia.
Qed.

Lemma ndec_S n c :
  ndec (S n) c = match rm_step zf2 c with None => 0 | Some c' => is_dec c + ndec n c' end.
Proof. reflexivity. Qed.

Lemma ndec_mono a b c c' : rm_run zf2 (a + b) c = Some c' -> ndec a c <= ndec (a + b) c.
Proof.
  revert c. induction a as [|a IH]; intros c Hr; [simpl; lia|].
  replace (S a + b) with (S (a + b)) in * by lia.
  rewrite rm_run_S in Hr. rewrite !ndec_S.
  destruct (rm_step zf2 c) as [c1|]; [|discriminate].
  specialize (IH c1 Hr). lia.
Qed.

(* the first steps of the run, checked by computation *)
Fixpoint chk (N : nat) (c : conf) (nd : nat) : bool :=
  (need c <=? 18 + nd) &&
  match N with
  | 0 => true
  | S N => match rm_step zf2 c with None => true | Some c' => chk N c' (nd + is_dec c) end
  end.

Lemma chk_sound N : forall c nd n c', chk N c nd = true -> n <= N ->
  rm_run zf2 n c = Some c' -> need c' <= 18 + nd + ndec n c.
Proof.
  induction N as [|N IH]; intros c nd n c' Hc Hn Hr;
    cbn [chk] in Hc; apply andb_prop in Hc as [H0 Hc]; apply Nat.leb_le in H0.
  - assert (n = 0) as -> by lia. cbn [rm_run] in Hr. injection Hr as <-. cbn [ndec]. lia.
  - destruct n as [|n].
    + cbn [rm_run] in Hr. injection Hr as <-. cbn [ndec]. lia.
    + rewrite rm_run_S in Hr. rewrite ndec_S.
      destruct (rm_step zf2 c) as [c1|]; [|discriminate].
      assert (Hn' : n <= N) by lia.
      specialize (IH c1 (nd + is_dec c) n c' Hc Hn' Hr). lia.
Qed.

Definition N0 := 240.

Lemma chk_ok : chk N0 ([], regs0) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ndec_N0 : (104 <=? ndec N0 ([], regs0)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem ip_space n c :
  rm_run zf2 n ([], regs0) = Some c -> need c <= 18 + ndec n ([], regs0).
Proof.
  intros Hr. destruct (le_lt_dec n N0) as [Hn|Hn].
  - pose proof (chk_sound N0 _ 0 n c chk_ok Hn Hr). lia.
  - replace n with (N0 + (n - N0)) in Hr |- * by lia.
    pose proof (ndec_mono _ _ _ _ Hr). pose proof ndec_N0 as A. apply Nat.leb_le in A.
    pose proof (need_le c). lia.
Qed.
