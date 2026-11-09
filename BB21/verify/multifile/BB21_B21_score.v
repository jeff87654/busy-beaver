(** B21: the halting tape and a first lower bound on the score: sigma > 4^^341. *)
From BB8 Require Import Individual212.
From BB8 Require Import BB21_B21_absdef BB21_B21_tm BB21_B21_sim BB21_B21_grow BB21_B21_steps BB21_B21_inv
  BB21_B21_proc BB21_B21_phase BB21_B21_run.
From Coq Require Import Lia PeanoNat List Bool.
Import ListNotations.
Set Default Goal Selector "!".

(** ** counting ones (repository convention, as in BB20_JZ20.v) *)
Definition sym_val (s : Sym) : nat := match s with S0 => 0%nat | S1 => 1%nat end.
Fixpoint count1 (xs : list Sym) : nat := match xs with [] => 0%nat | x :: t => (sym_val x + count1 t)%nat end.
Definition onesN (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = (count1 L + sym_val s + count1 R)%nat.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl. - reflexivity. - rewrite IHxs. lia. Qed.
Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl. - reflexivity. - rewrite count1_app, IHn. lia. Qed.

Fixpoint LPl (ms : list nat) : list Sym :=
  match ms with
  | [] => []
  | m :: t => [0;1]^^m ++ [0] ++ LPl t
  end.

Lemma LP_LPl : forall ms, LP ms = LPl ms *> const 0.
Proof. induction ms as [| m ms IH]; [reflexivity |]. cbn [LP LPl]. rewrite IH. rewrite !Str_app_assoc. reflexivity. Qed.

Lemma count_LPl : forall ms, count1 (LPl ms) = fold_right Nat.add 0%nat ms.
Proof. induction ms as [| m ms IH]; [reflexivity |]. cbn [LPl fold_right]. rewrite !count1_app, count1_pow, IH. cbn [count1 sym_val]. lia. Qed.

Lemma ones_halt : forall ms q,
  onesN (Halt_cfg (0 >> LP ms) ([1;1;0;0]^^(S q) *> 1 >> 1 >> const 0)) (fold_right Nat.add 0%nat ms + 2 * S q + 2)%nat.
Proof.
  intros ms q. exists RR, (LPl ms), ([1;1;0;0]^^(S q) ++ [1;1]), S0. split.
  - unfold Halt_cfg. rewrite LP_LPl. rewrite Str_app_assoc. reflexivity.
  - rewrite count_LPl, count1_app, count1_pow. simpl. lia.
Qed.

(** ** from a phase end with J-acc = 2 mod 4 to the halting configuration *)
Lemma end_to_halt : forall s, PhaseEnd s -> jacc s mod 4 = 2 ->
  exists c N, AT (enc s) -->* c /\ halted tm c /\ onesN c N /\ (jacc s <= 2 * N)%nat.
Proof.
  intros s [I [Hf [Hu Hd]]] Hm.
  destruct (b0ok_of s I) as [x [d [ds [Hb Hnz]]]].
  assert (He : AT (enc s) -->* JC (jacc s) (map pred (es s) ++ [length (b0 s) - 1]) (rb [[1%nat]] (const 0))).
  { unfold enc. rewrite Hf, Hu, Hb.
    follow (B_engine x d ds (rev (map ones (es s)) ++ [[1%nat]]) Hnz).
    rewrite <- map_rev. unfold ones.
    pose proof (i_es s I) as Hes. unfold esok in Hes.
    replace (engf 0 (d :: ds) x + 3)%nat with (S (engf 0 (d :: ds) x + 2)) by lia.
    set (x' := (engf 0 (d :: ds) x + 2)%nat).
    replace (length (d :: ds)) with (S (length ds)) by reflexivity.
    follow (B_Es (rev (es s)) x' (length ds) [] [[1%nat]] (Forall_rev Hes)).
    unfold jacc. rewrite Hb. rewrite rev_length, map_rev, rev_involutive.
    apply evstep_refl'. unfold x'. replace (length (x :: d :: ds) - 1)%nat with (S (length ds)) by (simpl; lia). unfold eng. replace (S (engf 0 (d :: ds) x + 2) + 2 * length (es s))%nat with (engf 0 (d :: ds) x + 3 + 2 * length (es s))%nat by lia. reflexivity. }
  pose proof (Nat.div_mod (jacc s) 4 ltac:(lia)) as D. rewrite Hm in D.
  remember (jacc s / 4) as q. clear Heqq.
  assert (Hnz' : Forall (fun m => m <> 0%nat) (map pred (es s) ++ [length (b0 s) - 1])).
  { apply Forall_app. split.
    - rewrite Forall_map. eapply Forall_impl; [| exact (i_es s I)]. intros a Ha. destruct a; simpl in *; lia.
    - constructor; [| constructor]. rewrite Hb. simpl. lia. }
  exists (Halt_cfg (0 >> LP (map pred (es s) ++ [length (b0 s) - 1])) ([1;1;0;0]^^(S q) *> 1 >> 1 >> const 0)).
  exists (fold_right Nat.add 0%nat (map pred (es s) ++ [length (b0 s) - 1]) + 2 * S q + 2)%nat.
  split; [| split; [reflexivity | split; [apply ones_halt | lia]]].
  follow He. rewrite D. apply B_haltc. exact Hnz'.
Qed.

(** ** 4^^341 *)
Local Open Scope nat_scope.
Fixpoint tet (n : nat) : nat := match n with Datatypes.O => 1 | S n' => 4 ^ tet n' end.

Lemma h2_ge : forall z, 64 * 4 ^ z <= h 2 z.
Proof.
  intros z. change (h 2 z) with (iter (z + 3) (h 1) 1). pose proof (h1_iter (z + 3)) as E.
  rewrite Nat.pow_add_r in E. change (4 ^ 3) with 64 in E.
  assert (1 <= 4 ^ z) by (pose proof (Nat.pow_le_mono_r 4 0 z ltac:(lia) ltac:(lia)) as P; simpl in P; lia).
  nia.
Qed.

Lemma h2_iter : forall n, 64 * tet (S (S (S n))) <= iter (S (S n)) (h 2) 1.
Proof.
  induction n as [| n IH].
  - cbn [iter]. pose proof (h2_ge (h 2 1)) as A. pose proof (h2_ge 1) as B.
    change (4 ^ 1) with 4 in B.
    assert (C : tet 2 = 256) by reflexivity.
    assert (D : 4 ^ tet 2 <= 4 ^ h 2 1) by (apply Nat.pow_le_mono_r; [lia | rewrite C; lia]).
    change (tet 3) with (4 ^ tet 2). clear C. lia.
  - change (iter (S (S (S n))) (h 2) 1) with (h 2 (iter (S (S n)) (h 2) 1)).
    pose proof (h2_ge (iter (S (S n)) (h 2) 1)) as A.
    change (tet (S (S (S (S n))))) with (4 ^ tet (S (S (S n)))).
    assert (4 ^ tet (S (S (S n))) <= 4 ^ iter (S (S n)) (h 2) 1) by (apply Nat.pow_le_mono_r; lia). lia.
Qed.

Lemma J3_tet : 64 * tet 341 <= J3.
Proof.
  rewrite J3_eq, jacc_s3.
  assert (E : iter 3 (h 1) 1 = 337) by (cbn [iter]; rewrite !h1; reflexivity).
  rewrite E. change (h 3 337) with (iter (337 + 3) (h 2) 1).
  pose proof (h2_iter 338) as H. replace (337 + 3) with (S (S 338)) by lia. lia.
Qed.

Lemma tet_pos : forall n, 1 <= tet n.
Proof. induction n; [simpl; lia |]. change (tet (S n)) with (4 ^ tet n). pose proof (Nat.pow_le_mono_r 4 0 (tet n) ltac:(lia) ltac:(lia)). simpl in H. lia. Qed.

Close Scope nat_scope.
Lemma star_conv' : forall a b, BB21_B21_proc.star refill21 a b -> BB21_B21_sim.star a b.
Proof.
  intros a b H. induction H.
  - apply BB21_B21_sim.star_refl.
  - eapply BB21_B21_sim.star_step; [rewrite astep_G; exact H | exact IHstar].
Qed.

(** the score: sigma = N + 1 (the halting transition R0 = 1RZ writes one more 1) *)
Theorem sigma_lower_bound_tet : exists c N, c0 -[ tm ]->* c /\ halted tm c /\ onesN c N /\ (tet 341 < N)%nat.
Proof.
  destruct abstract_final as [s [Hs [E [Hm HJ]]]].
  destruct (end_to_halt s E Hm) as [c [N [Hc [Hh [Ho HN]]]]].
  exists c, N. split; [| split; [exact Hh | split; [exact Ho |]]].
  - follow boot. follow (star_sim _ _ (star_conv' _ _ Hs)). exact Hc.
  - pose proof J3_tet. destruct (jacc_end_form s E) as [q Hq].
    pose proof (tet_pos 341). lia.
Qed.
