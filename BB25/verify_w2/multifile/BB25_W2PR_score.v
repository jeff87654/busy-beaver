(** W2PR: the halting tape and the score bound. *)
From BB8 Require Import Individual252.
From BB8 Require Import BB21_B21_absdef BB25_W2PR_tm BB25_W2PR_sim BB21_B21_grow BB21_B21_steps BB21_B21_inv
  BB21_B21_proc BB21_B21_phase BB25_W2PR_run.
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
  onesN (Halt_cfg (0 >> LP ms) ([1;1;0;0;1;1;0;0]^^(S q) *> 1 >> 1 >> const 0)) (fold_right Nat.add 0%nat ms + 4 * S q + 2)%nat.
Proof.
  intros ms q. exists RR, (LPl ms), ([1;1;0;0;1;1;0;0]^^(S q) ++ [1;1]), S0. split.
  - unfold Halt_cfg. rewrite LP_LPl. rewrite Str_app_assoc. reflexivity.
  - rewrite count_LPl, count1_app, count1_pow. simpl. lia.
Qed.

(** ** from a phase end with J-acc = 2 mod 4 to the halting configuration *)
Lemma end_to_halt : forall s, PhaseEnd s -> jacc s mod 8 = 6 ->
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
  pose proof (Nat.div_mod (jacc s) 8 ltac:(lia)) as D. rewrite Hm in D.
  remember (jacc s / 8) as q. clear Heqq.
  assert (Hnz' : Forall (fun m => m <> 0%nat) (map pred (es s) ++ [length (b0 s) - 1])).
  { apply Forall_app. split.
    - rewrite Forall_map. eapply Forall_impl; [| exact (i_es s I)]. intros a Ha. destruct a; simpl in *; lia.
    - constructor; [| constructor]. rewrite Hb. simpl. lia. }
  exists (Halt_cfg (0 >> LP (map pred (es s) ++ [length (b0 s) - 1])) ([1;1;0;0;1;1;0;0]^^(S q) *> 1 >> 1 >> const 0)).
  exists (fold_right Nat.add 0%nat (map pred (es s) ++ [length (b0 s) - 1]) + 4 * S q + 2)%nat.
  split; [| split; [reflexivity | split; [apply ones_halt | lia]]].
  follow He. rewrite D. apply B_haltc. exact Hnz'.
Qed.


Lemma star_convW : forall a b, BB21_B21_proc.star refillW a b -> BB25_W2PR_sim.star a b.
Proof.
  intros a b H. induction H.
  - apply BB25_W2PR_sim.star_refl.
  - eapply BB25_W2PR_sim.star_step; [exact H | exact IHstar].
Qed.

(** sigma = N + 1 (the halting transition R0 = 1RZ writes one more 1) *)
Theorem sigma_lower_boundW : exists c N, c0 -[ tm ]->* c /\ halted tm c /\ onesN c N /\
  (iter 5 Fh (tet 341) < N)%nat.
Proof.
  destruct abstract_finalW as [s [Hs [E [Hm HG]]]].
  destruct (end_to_halt s E Hm) as [c [N [Hc [Hh [Ho HN]]]]].
  exists c, N. split; [| split; [exact Hh | split; [exact Ho |]]].
  - follow boot. follow (star_sim _ _ (star_convW _ _ Hs)). exact Hc.
  - pose proof (jacc_end_lb s E) as B. pose proof (h_S0 (length (es s) + 1) ltac:(lia)) as HS.
    replace (Datatypes.S (length (es s) + 1)) with (length (es s) + 2)%nat in HS by lia. lia.
Qed.

Theorem haltW : halts tm c0.
Proof.
  destruct abstract_finalW as [s [Hs [E [Hm _]]]].
  exact (BB25_W2PR_sim.halts_from (enc s) (star_convW _ _ Hs) (halt_endW s E Hm)).
Qed.
