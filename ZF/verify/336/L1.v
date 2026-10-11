(** * L1: the abstract enumerator halts iff [v_0 e. v_0] is provable  (R3s336 version).

    Soundness: every entry of the (infinite, zero-padded) stack, read through the total decoder
    [D] (L1_Arith), is provable; the moot wff 0 decodes to [v_0 = v_0], derived in [prov_eq_refl].
    Completeness: a derivation compiles to a list of proof steps, which the enumerator executes
    when [nextproof] reaches the step list's code.
    R3s336 pushes machine texts of EXT, REP, INF (L1_R3s): soundness uses [prov_EXT_M] etc.;
    completeness derives the original axioms from the variants by compiled pure-logic ([lprov])
    derivations of [A. v2 EXT_M -> EXT], [REP_M ph -> REP ph], [INF_M -> INF]. *)
From Coq Require Import Arith.Arith Lia Lists.List Bool.Bool.
From ZF Require Import Logic Enum L1_Arith L1_Prop L1_LDef L1_LProp L1_LMeta L1_R3s.
Import ListNotations.

Section Iter.
Context {A : Type} (f : A -> A).
Lemma iter_succ_r n x : Nat.iter (S n) f x = Nat.iter n f (f x).
Proof. induction n; [reflexivity|]. change (f (Nat.iter (S n) f x) = f (Nat.iter n f (f x))). now rewrite IHn. Qed.
Lemma iter_add n m x : Nat.iter (n + m) f x = Nat.iter n f (Nat.iter m f x).
Proof. induction n; [reflexivity|]. simpl. now rewrite IHn. Qed.
End Iter.

(** ** Some derived rules and [x = x] *)
Lemma syl a b c : prov (Wim a b) -> prov (Wim b c) -> prov (Wim a c).
Proof. intros H1 H2. exact (DET _ _ (DET _ _ (B1 a b c) H1) H2). Qed.

Lemma contra a b : prov (Wim a b) -> prov (Wim (Wn b) (Wn a)).
Proof. intro H. exact (DET _ _ (pc_contra a b) H). Qed.

Lemma ex_mono x a b : prov (Wim a b) -> prov (Wim (Wex x a) (Wex x b)).
Proof.
  intro H. unfold Wex. apply contra.
  exact (DET _ _ (B4 x (Wn b) (Wn a)) (GEN x _ (contra _ _ H))).
Qed.

Lemma prov_eq_refl x : prov (Weq x x).
Proof.
  set (z := S x).
  assert (h3 : prov (Wim (Weq z x) (Weq x x))) by exact (DET _ _ (pc_W _ _) (B8a z x x)).
  assert (h5 : prov (Wim (Weq x x) (Wal z (Weq x x)))).
  { exact (DET _ _ (pc_andl _ _) (B6a x x z ltac:(lia) ltac:(lia))). }
  pose proof (ex_mono z _ _ (syl _ _ _ h3 h5)) as h7.
  exact (DET _ _ (B6c z (Weq x x)) (DET _ _ h7 (B7 z x))).
Qed.

(** From here on, never unfold the pairing function (codes of closed wffs are huge). *)
Opaque pair.

(** ** Soundness *)
Definition popn (k ws : nat) : nat := Nat.iter k (fun w => snd (unpair w)) ws.
Definition goodstack (ws : nat) : Prop := forall k, prov (D (fst (unpair (popn k ws)))).

Lemma good_pop w : goodstack w -> prov (D (fst (unpair w))) /\ goodstack (snd (unpair w)).
Proof.
  intro H. split; [exact (H 0)|]. intro k. specialize (H (S k)).
  unfold popn in *. now rewrite iter_succ_r in H.
Qed.

Lemma good_push x w : prov (D x) -> goodstack w -> goodstack (push x w).
Proof.
  intros Hx Hw [|k]; unfold popn, push.
  - simpl. now rewrite unpair_pair.
  - rewrite iter_succ_r, unpair_pair. apply Hw.
Qed.

Lemma good_0 : goodstack 0.
Proof.
  assert (E : forall k, popn k 0 = 0).
  { induction k; [reflexivity|]. unfold popn in *. rewrite iter_succ_r. exact IHk. }
  intro k. rewrite E. change (prov (Weq 0 0)). apply prov_eq_refl.
Qed.

Lemma prov_D0 : prov (D 0).
Proof. rewrite D_0. apply prov_eq_refl. Qed.

Ltac Dsimp := repeat first [rewrite D_wim | rewrite D_wn | rewrite D_wal | rewrite D_weq
                           | rewrite D_wel | rewrite D_wex | rewrite D_wa].

Lemma apply_clause_good c p1 p2 p3 w : goodstack w ->
  prov (D (fst (apply_clause c p1 p2 p3 w))) /\ goodstack (snd (apply_clause c p1 p2 p3 w)).
Proof.
  intro Hw.
  destruct c as [|c].
  { (* DET *)
    cbn [apply_clause]. unfold pop.
    destruct (good_pop w Hw) as [Hph Hw1].
    destruct (unpair w) as [ph w1] eqn:E1. simpl in Hph, Hw1.
    destruct (good_pop w1 Hw1) as [Hmaj Hw2].
    destruct (unpair w1) as [maj w2] eqn:E2. simpl in Hmaj, Hw2.
    split; [|exact Hw2]. simpl fst.
    destruct (Nat.eqb_spec (wim ph p1) maj) as [<-|_]; [|exact prov_D0].
    rewrite D_wim in Hmaj. exact (DET _ _ Hmaj Hph). }
  destruct c as [|c].
  { (* GEN *)
    cbn [apply_clause]. unfold pop.
    destruct (good_pop w Hw) as [Hph Hw1].
    destruct (unpair w) as [ph w1]. simpl in *. split; [|exact Hw1].
    rewrite D_wal. now apply GEN. }
  do 6 (destruct c as [|c];
    [ cbn [apply_clause clause fst snd]; split; [|exact Hw];
      unfold clause_2, clause_3, clause_4, clause_5, clause_6, clause_7; Dsimp; constructor | ]).
  destruct c as [|c].
  { (* B6a, roles x y z = p3 p1 p2 *)
    cbn [apply_clause fst snd]. split; [|exact Hw].
    destruct (Nat.eqb_spec p2 p3); [exact prov_D0|].
    destruct (Nat.eqb_spec p2 p1); [exact prov_D0|]. simpl.
    unfold clause_8. Dsimp. now apply B6a. }
  do 4 (destruct c as [|c];
    [ cbn [apply_clause clause fst snd]; split; [|exact Hw];
      unfold clause_9, clause_10, clause_11, clause_12; Dsimp; constructor | ]).
  destruct c as [|c].
  { cbn [apply_clause clause fst snd]. split; [|exact Hw].
    replace (clause_13 p1 p2 p3) with (code EXT_M) by reflexivity. rewrite D_code. exact prov_EXT_M. }
  destruct c as [|c].
  { cbn [apply_clause clause fst snd]. split; [|exact Hw].
    unfold clause_14. Dsimp. exact (prov_REP_M (D p2)). }
  { cbn [apply_clause clause fst snd]. split; [|exact Hw].
    replace (clause_15 p1 p2 p3) with (code INF_M) by reflexivity. rewrite D_code. exact prov_INF_M. }
Qed.

(** ** One enumerator step, given the decoded proof step *)
Definition step : Type := (nat * nat * nat * nat)%type.

Definition scode (a : step) (r : nat) : nat :=
  let '(ac, p1, p2, p3) := a in pair ac (pair p1 (pair p2 (pair p3 r))).

Definition xstep (a : step) (st : nat * nat) : nat * nat :=
  let '(ac, p1, p2, p3) := a in
  let '(t, w) := st in
  let ws1 := push t w in
  if Nat.eqb ac 0 then (0, ws1)
  else apply_clause (nth (Nat.min ac 16 - 1) axiomorder 15) p1 p2 p3 ws1.

Definition pl1_of (s : state) : nat := if Nat.eqb (pl s) 0 then np s else pred (pl s).
Definition np1_of (s : state) : nat := if Nat.eqb (pl s) 0 then S (np s) else np s.

Lemma step_dec s a r : pl1_of s = scode a r ->
  enum_step s = mkState r (np1_of s) (fst (xstep a (tw s, ws s))) (snd (xstep a (tw s, ws s))).
Proof.
  destruct s as [pl np tw ws]. destruct a as [[[ac p1] p2] p3].
  unfold pl1_of, np1_of, enum_step. cbn [Enum.pl Enum.np Enum.tw Enum.ws].
  intro H. destruct (Nat.eqb pl 0); rewrite H; unfold scode; rewrite !unpair_pair;
    unfold xstep; destruct (if Nat.eqb ac 0 then _ else _); reflexivity.
Qed.

Lemma decomp z : exists a r, z = scode a r /\ r <= z.
Proof.
  destruct (unpair z) as [ac z1] eqn:E1.
  destruct (unpair z1) as [p1 z2] eqn:E2.
  destruct (unpair z2) as [p2 z3] eqn:E3.
  destruct (unpair z3) as [p3 r] eqn:E4.
  pose proof (pair_unpair z) as F1. pose proof (pair_unpair z1) as F2.
  pose proof (pair_unpair z2) as F3. pose proof (pair_unpair z3) as F4.
  rewrite E1 in F1. rewrite E2 in F2. rewrite E3 in F3. rewrite E4 in F4. simpl in *.
  exists (ac, p1, p2, p3), r. unfold scode. split; [congruence|].
  pose proof (pair_ge_r p3 r). pose proof (pair_ge_r p2 z3).
  pose proof (pair_ge_r p1 z2). pose proof (pair_ge_r ac z1). lia.
Qed.

Lemma step_shape s : exists a r, r <= pl1_of s /\
  enum_step s = mkState r (np1_of s) (fst (xstep a (tw s, ws s))) (snd (xstep a (tw s, ws s))).
Proof.
  destruct (decomp (pl1_of s)) as (a & r & E & Hr). exists a, r. split; [exact Hr|].
  now apply step_dec.
Qed.

(** ** Soundness *)
Definition Inv (s : state) : Prop := prov (D (tw s)) /\ goodstack (ws s).

Lemma xstep_good a t w : prov (D t) -> goodstack w ->
  prov (D (fst (xstep a (t, w)))) /\ goodstack (snd (xstep a (t, w))).
Proof.
  intros Ht Hw. destruct a as [[[ac p1] p2] p3]. unfold xstep.
  pose proof (good_push t w Ht Hw) as Hw1.
  destruct (Nat.eqb ac 0); [split; [exact prov_D0 | exact Hw1]|].
  now apply apply_clause_good.
Qed.

Lemma Inv_step s : Inv s -> Inv (enum_step s).
Proof.
  intros [Ht Hw]. destruct (step_shape s) as (a & r & _ & ->).
  exact (xstep_good a _ _ Ht Hw).
Qed.

Lemma Inv_iter n : Inv (Nat.iter n enum_step s0).
Proof.
  induction n.
  - split; [exact prov_D0 | exact good_0].
  - exact (Inv_step _ IHn).
Qed.

Theorem enum_sound : enum_halts -> prov (Wel v0 v0).
Proof.
  intros [n Hn]. destruct (Inv_iter (S n)) as [Ht _]. rewrite Hn in Ht.
  rewrite <- code_Wel_v0_v0, D_code in Ht. exact Ht.
Qed.

(** ** Completeness: every value of nextproof is loaded *)
Lemma drain k : forall s, pl s <= k ->
  exists n, pl (Nat.iter n enum_step s) = 0 /\ np (Nat.iter n enum_step s) = np s.
Proof.
  induction k as [|k IH]; intros s Hs.
  - exists 0. split; [simpl; lia | reflexivity].
  - destruct (Nat.eqb_spec (pl s) 0) as [E|E].
    + exists 0. split; [exact E | reflexivity].
    + destruct (step_shape s) as (a & r & Hr & Es).
      unfold pl1_of, np1_of in *. apply Nat.eqb_neq in E. rewrite E in *.
      destruct (IH (enum_step s)) as (n & H1 & H2); [rewrite Es; simpl; lia|].
      exists (S n). rewrite iter_succ_r. split; [exact H1|]. rewrite H2, Es. reflexivity.
Qed.

Lemma reach m : exists n, pl (Nat.iter n enum_step s0) = 0 /\ np (Nat.iter n enum_step s0) = m.
Proof.
  induction m as [|m (n & H1 & H2)].
  - exists 0. split; reflexivity.
  - set (s := Nat.iter n enum_step s0) in *.
    destruct (step_shape s) as (a & r & Hr & Es).
    unfold pl1_of, np1_of in *. rewrite H1 in *. simpl in Hr, Es.
    destruct (drain m (enum_step s)) as (n' & G1 & G2); [rewrite Es; simpl; lia|].
    exists (n' + S n). rewrite iter_add.
    change (Nat.iter (S n) enum_step s0) with (enum_step s). split; [exact G1|].
    rewrite G2, Es. simpl. now rewrite H2.
Qed.

(** ** Executing a step list *)
Fixpoint exec (L : list step) (st : nat * nat) : nat * nat :=
  match L with [] => st | a :: L => exec L (xstep a st) end.

Fixpoint enc_tail (L : list step) : nat :=
  match L with [] => 0 | a :: L => S (scode a (enc_tail L)) end.

Lemma run_tail L : forall s, pl s = enc_tail L ->
  Nat.iter (length L) enum_step s
  = mkState 0 (np s) (fst (exec L (tw s, ws s))) (snd (exec L (tw s, ws s))).
Proof.
  induction L as [|a L IH]; intros s Hs.
  - destruct s; simpl in *. now subst.
  - simpl length. rewrite iter_succ_r.
    rewrite (step_dec s a (enc_tail L)).
    + rewrite IH by reflexivity. unfold np1_of. rewrite Hs. simpl.
      destruct (xstep a (tw s, ws s)). reflexivity.
    + unfold pl1_of. rewrite Hs. reflexivity.
Qed.

Lemma run_proof a L s : pl s = 0 -> np s = scode a (enc_tail L) ->
  tw (Nat.iter (S (length L)) enum_step s) = fst (exec (a :: L) (tw s, ws s)).
Proof.
  intros H1 H2. rewrite iter_succ_r, (step_dec s a (enc_tail L)).
  - rewrite run_tail by reflexivity. simpl. destruct (xstep a (tw s, ws s)). reflexivity.
  - unfold pl1_of. rewrite H1. exact H2.
Qed.

Lemma exec_app L1 L2 st : exec (L1 ++ L2) st = exec L2 (exec L1 st).
Proof. revert st; induction L1; intro st; simpl; auto. Qed.

(** ** Compiling a derivation *)
Definition pushes (L : list step) (c : nat) : Prop :=
  L <> [] /\ forall t w, exec L (t, w) = (c, push t w).

Lemma pushes_one a c : (forall t w, xstep a (t, w) = (c, push t w)) -> pushes [a] c.
Proof. intro H. split; [discriminate|]. intros t w. apply H. Qed.

Lemma pushes_det L1 L2 a b : pushes L1 (code (Wim a b)) -> pushes L2 (code a) ->
  pushes (L1 ++ L2 ++ [(3, code b, 0, 0)]) (code b).
Proof.
  intros [N1 H1] [N2 H2]. split; [destruct L1; [contradiction | discriminate]|]. intros t w.
  rewrite !exec_app, H1, H2. simpl. unfold pop, push.
  rewrite !unpair_pair. change (code (Wim a b)) with (wim (code a) (code b)).
  now rewrite Nat.eqb_refl.
Qed.

Lemma pushes_gen L x a : pushes L (code a) -> pushes (L ++ [(5, 0, 0, x)]) (code (Wal x a)).
Proof.
  intros [N H]. split; [destruct L; [contradiction | discriminate]|]. intros t w.
  rewrite exec_app, H. simpl. unfold pop, push. now rewrite unpair_pair.
Qed.

(* step = (ac, p1, p2, p3); ac = 1-based position of the clause in axiomorder,
   parameters placed according to the clause's role permutation *)
Lemma lcompile a : lprov a -> exists L, pushes L (code a).
Proof.
  induction 1 as [a b _ [L1 H1] _ [L2 H2] | x a _ [L H]
    | a b c | a | a b | x a b | x y z Hxz Hyz | x y a | x a | x y | x y z | x y z | x y z].
  - eexists. exact (pushes_det _ _ _ _ H1 H2).
  - eexists. exact (pushes_gen _ _ _ H).
  - exists [(9, code c, code b, code a)]; apply pushes_one; reflexivity.
  - exists [(13, code a, 0, 0)]; apply pushes_one; reflexivity.
  - exists [(12, code b, code a, 0)]; apply pushes_one; reflexivity.
  - exists [(10, code b, code a, x)]; apply pushes_one; reflexivity.
  - exists [(15, y, z, x)]; apply pushes_one; intros t w. simpl.
    rewrite Nat.eq_sym_iff in Hxz, Hyz.
    apply Nat.eqb_neq in Hxz, Hyz. now rewrite Hxz, Hyz.
  - exists [(2, y, code a, x)]; apply pushes_one; reflexivity.
  - exists [(11, code a, 0, x)]; apply pushes_one; reflexivity.
  - exists [(14, y, x, 0)]; apply pushes_one; reflexivity.
  - exists [(8, z, y, x)]; apply pushes_one; reflexivity.
  - exists [(7, z, y, x)]; apply pushes_one; reflexivity.
  - exists [(6, y, z, x)]; apply pushes_one; reflexivity.
Qed.

Lemma compile a : prov a -> exists L, pushes L (code a).
Proof.
  induction 1 as [a b _ [L1 H1] _ [L2 H2] | x a _ [L H]
    | a b c | a | a b | x a b | x y z Hxz Hyz | x y a | x a | x y | x y z | x y z | x y z
    | | a | ];
    try (apply lcompile; constructor; assumption).
  - eexists. exact (pushes_det _ _ _ _ H1 H2).
  - eexists. exact (pushes_gen _ _ _ H).
  - (* EXT from A. v2 EXT_M *)
    destruct (lcompile _ (proj2 R3s_EXT)) as [L HL].
    eexists. refine (pushes_det _ _ _ _ HL (pushes_gen _ v2 _ (pushes_one (16, 0, 0, 0) _ _))).
    reflexivity.
  - (* REP a from REP_M a *)
    destruct (lcompile _ (proj2 (R3s_REP a))) as [L HL].
    eexists. refine (pushes_det _ _ _ _ HL (pushes_one (4, 0, code a, 0) _ _)). reflexivity.
  - (* INF from INF_M *)
    destruct (lcompile _ (proj2 R3s_INF)) as [L HL].
    eexists. refine (pushes_det _ _ _ _ HL (pushes_one (1, 0, 0, 0) _ _)). reflexivity.
Qed.

Theorem enum_complete : prov (Wel v0 v0) -> enum_halts.
Proof.
  intro H. destruct (compile _ H) as [[|a L] [N HL]]; [contradiction|].
  destruct (reach (scode a (enc_tail L))) as (n & H1 & H2).
  exists (length L + n). rewrite <- Nat.add_succ_l, iter_add.
  rewrite (run_proof a L) by assumption. rewrite HL. apply code_Wel_v0_v0.
Qed.

Theorem enum_halts_iff : enum_halts <-> prov (Wel v0 v0).
Proof. split; [exact enum_sound | exact enum_complete]. Qed.

Print Assumptions enum_halts_iff.
