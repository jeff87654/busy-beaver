(* machine: 1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI *)
From BB8 Require Import Individual162.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* J16_w2 (core-named, start state A):
   1LG1LA_0LI1RC_0LD1LG_0RE1LD_0RM1RL_1RB1RF_1LH0LA_1RF0RN_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LG0RN_0RP1RO_1RZ1RM_1LB1LI
   Isomorphic canonical Tree Normal Form (TNF):
   1LB1LA_1LC0LA_1RD0RL_1RE1RD_0LF1RO_1LG1LF_0LH1LF_1RI1RJ_0RI0RD_0RK1RI_0LB0RL_0RN1RM_1RZ1RK_1LE1LF_0LP1LB_0RJ1LP *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.L, G)   | A, 1 => Some (1, TM.L, A)
  | B, 0 => Some (0, TM.L, I)   | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)   | C, 1 => Some (1, TM.L, G)
  | D, 0 => Some (0, TM.R, E)   | D, 1 => Some (1, TM.L, D)
  | E, 0 => Some (0, TM.R, M)   | E, 1 => Some (1, TM.R, L)
  | F, 0 => Some (1, TM.R, B)   | F, 1 => Some (1, TM.R, F)
  | G, 0 => Some (1, TM.L, H)   | G, 1 => Some (0, TM.L, A)
  | H, 0 => Some (1, TM.R, F)   | H, 1 => Some (0, TM.R, N)
  | I, 0 => Some (1, TM.L, J)   | I, 1 => Some (1, TM.L, I)
  | J, 0 => Some (0, TM.L, K)   | J, 1 => Some (1, TM.L, I)
  | K, 0 => Some (1, TM.R, L)   | K, 1 => Some (1, TM.R, E)
  | L, 0 => Some (0, TM.R, L)   | L, 1 => Some (0, TM.R, F)
  | M, 0 => Some (0, TM.L, G)   | M, 1 => Some (0, TM.R, N)
  | N, 0 => Some (0, TM.R, P)   | N, 1 => Some (1, TM.R, O)
  | O, 0 => None                | O, 1 => Some (1, TM.R, M)
  | P, 0 => Some (1, TM.L, B)   | P, 1 => Some (1, TM.L, I)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n.
  - reflexivity.
  - simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : Sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof. intros. rewrite const_unfold at 1. apply align_lpow. Qed.

Ltac align_tape := repeat ((rewrite align_lpow || rewrite align_lpow_const); simpl app).
Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
Ltac finish_norm := apply evstep_refl'; norm_nat; align_tape; try reflexivity; lia_refl.

Lemma one_shift : forall n (ys : side), [1]^^n *> 1 >> ys = 1 >> [1]^^n *> ys.
Proof. intros. apply (align_lpow 1 [] ys n). Qed.

Lemma ones_add : forall n m (ys : side), [1]^^n *> [1]^^m *> ys = [1]^^(n + m) *> ys.
Proof. intros. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

(** ** Walks *)
Lemma walkF : forall n l r, l {{F}}> [1]^^n *> r -->* [1]^^n *> l {{F}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkA : forall n l r, [1]^^n *> l <{{A}} r -->* l <{{A}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkD : forall n l r, [1]^^n *> l <{{D}} r -->* l <{{D}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkI : forall n l r, [1]^^n *> l <{{I}} r -->* l <{{I}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma zigAG : forall n l r, [0;1]^^n *> l <{{A}} r -->* l <{{A}} [0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma zigIJ : forall n l r, [0;1]^^n *> l <{{I}} r -->* l <{{I}} [1;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triNOM : forall n l r, l {{N}}> [1;1;1]^^n *> r -->* [0;1;1]^^n *> l {{N}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triAGA : forall n l r, [0;1;1]^^n *> l <{{A}} r -->* l <{{A}} [1;0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triIJI : forall n l r, [0;1;1]^^n *> l <{{I}} r -->* l <{{I}} [1;1;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.


(** ** Digit lists on the tape *)
Fixpoint rl (ds : list nat) (r : side) : side :=
  match ds with
  | [] => r
  | d :: t => [1]^^d *> 0 >> rl t r
  end.

Lemma rl_app : forall a b r, rl (a ++ b) r = rl a (rl b r).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

Lemma rl_rep1 : forall n r, rl (repeat 1%nat n) r = [1;0]^^n *> r.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Lemma rl_rep2 : forall n r, rl (repeat 2%nat n) r = [1;1;0]^^n *> r.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Lemma pow11 : forall j, @lpow Sym [1;1] j = [1]^^(2 * j).
Proof.
  induction j; [reflexivity |].
  replace (2 * S j) with (S (S (2 * j))) by lia. simpl. rewrite IHj. reflexivity.
Qed.

Lemma pow111 : forall j, @lpow Sym [1;1;1] j = [1]^^(3 * j).
Proof.
  induction j; [reflexivity |].
  replace (3 * S j) with (S (S (S (3 * j)))) by lia. simpl. rewrite IHj. reflexivity.
Qed.

Lemma rep_snoc : forall m (x : nat) ds, repeat x m ++ x :: ds = repeat x (S m) ++ ds.
Proof. induction m; intros; simpl. - reflexivity. - rewrite IHm. reflexivity. Qed.

Lemma rep_add : forall m n (x : nat), repeat x (m + n) = repeat x m ++ repeat x n.
Proof. induction m; intros; simpl. - reflexivity. - rewrite IHm. reflexivity. Qed.

(** Sweep configuration: F at the right end of the accumulator block (y cells right of the last 0),
    j passed 1-digits parked on the left as (1 0) pairs, then the context [0 >> l]. *)
Definition SW (l : side) (j y : nat) (ds : list nat) (R : side) : Q * tape :=
  ([1]^^y *> [0;1]^^j *> 0 >> l) {{F}}> (0 >> rl ds R).

(** inner boundary: H at the blank left of the inner list *)
Definition CI (x : nat) (ds : list nat) (R : side) : Q * tape :=
  const 0 <{{H}} ([1]^^x *> 0 >> rl ds R).

(** outer boundary (marker mode): far-left marker 1, two zeros, F at the outer accumulator *)
Definition CO (a : nat) (Rr : side) : Q * tape :=
  (0 >> 0 >> 1 >> const 0) {{F}}> ([1]^^a *> 0 >> Rr).

(** outer exit configuration: E facing 0 followed by B ones *)
Definition EX (B : nat) : Q * tape :=
  (1 >> const 0) {{E}}> (0 >> [1]^^B *> const 0).

Lemma SW_pass : forall l j y ds R, SW l j y (1%nat :: ds) R -->* SW l (S j) y ds R.
Proof.
  intros. unfold SW. cbn [rl lpow app Str_app].
  execute.
  follow walkD.
  rewrite align_lpow. simpl app.
  execute.
  rewrite !one_shift. execute.
  follow walkF. finish_norm.
Qed.

Lemma SW_pass_iter : forall n l j y ds R, SW l j y (repeat 1%nat n ++ ds) R -->* SW l (j + n) y ds R.
Proof.
  induction n; intros; simpl.
  - replace (j + 0) with j by lia. finish.
  - follow SW_pass. follow IHn. replace (S j + n) with (j + S n) by lia. finish.
Qed.

Lemma SW_E : forall l j y e ds R,
  SW l j y (S (S e) :: ds) R -->* l <{{G}} (1 >> [0;1]^^j *> [1]^^(S y) *> 0 >> rl (S e :: ds) R).
Proof.
  intros. unfold SW. cbn [rl lpow app Str_app].
  execute.
  follow walkA.
  follow zigAG.
  execute.
  finish_norm.
Qed.

Lemma pairs_ones : forall j y (X : side), [1;1]^^j *> [1]^^y *> 1 >> X = [1]^^(y + 2 * j + 1) *> X.
Proof.
  intros. rewrite pow11, ones_add, one_shift.
  replace (y + 2 * j + 1) with (S (2 * j + y)) by lia. reflexivity.
Qed.

(** inner exit: the exhausted inner list merges into the new outer accumulator *)
Lemma SW_exit_in : forall j y R, SW (const 0) j y [] (0 >> R) -->* CO (y + 2 * j + 1) R.
Proof.
  intros. unfold SW. cbn [rl].
  execute.
  follow walkI.
  follow zigIJ.
  execute.
  rewrite pairs_ones. unfold CO. finish.
Qed.

(** outer exit: the exhausted outer list merges into EX N *)
Lemma SW_exit_out : forall j y N, N = y + 2 * j + 2 ->
  SW (0 >> 1 >> const 0) j y [] (const 0) -->* EX N.
Proof.
  intros j y N HN. unfold SW. cbn [rl].
  execute.
  follow walkI.
  follow zigIJ.
  do 3 (eapply evstep_step; [prove_step |]).
  rewrite pairs_ones.
  unfold EX. replace N with (S (y + 2 * j + 1)) by lia.
  apply evstep_refl.
Qed.

Lemma CI_SW : forall x ds R, CI x ds R -->* SW (const 0) 0 (S x) ds R.
Proof.
  intros. unfold CI, SW.
  execute. follow walkF. finish_norm.
Qed.

Lemma SW_G_in : forall j y e ds R,
  SW (const 0) j y (S (S e) :: ds) R -->*
  const 0 <{{H}} (1 >> 1 >> [0;1]^^j *> [1]^^(S y) *> 0 >> rl (S e :: ds) R).
Proof.
  intros. follow SW_E. execute.
Qed.

Lemma CI_E0 : forall x e ds R, CI x (S (S e) :: ds) R -->* CI (x + 4) (S e :: ds) R.
Proof.
  intros. follow CI_SW. follow SW_G_in. unfold CI.
  replace (x + 4) with (S (S (S (S x)))) by lia. finish.
Qed.

Lemma CI_E1 : forall x j e ds R,
  CI x (repeat 1%nat (S j) ++ S (S e) :: ds) R -->* CI 2 (repeat 1%nat j ++ (x + 3) :: S e :: ds) R.
Proof.
  intros. follow CI_SW. follow SW_pass_iter. follow SW_G_in. unfold CI.
  rewrite rl_app, rl_rep1. cbn [rl lpow app Str_app].
  replace (0 + S j) with (S j) by lia.
  replace (x + 3) with (S (S (S x))) by lia. cbn [lpow app Str_app].
  rewrite (align_lpow 1 [0]). simpl app. finish.
Qed.

Lemma CI_exit : forall x n R, CI x (repeat 1%nat n) (0 >> R) -->* CO (x + 2 * n + 2) R.
Proof.
  intros. follow CI_SW.
  rewrite <- (app_nil_r (repeat 1%nat n)).
  follow SW_pass_iter. follow SW_exit_in.
  replace (x + 2 * n + 2) with (S x + 2 * (0 + n) + 1) by lia. finish.
Qed.

(** ** Refill & Halting from EX *)
Definition Hc (j : nat) : Q * tape :=
  (1 >> 0 >> [0;1;1]^^(S j) *> 0 >> 0 >> 1 >> const 0) {{O}}> (const 0).

Lemma Hc_halted : forall j, halted tm (Hc j).
Proof. intros. reflexivity. Qed.

Lemma RF_halt : forall j, EX (3 * S j + 1) -->* Hc j.
Proof.
  intros j. unfold EX, Hc.
  replace (3 * S j + 1) with (1 + (3 * j + 3)) by lia.
  do 2 rewrite <- ones_add. rewrite <- pow111.
  execute.
  follow triNOM.
  execute.
  follow triIJI.
  execute.
  follow triNOM.
  execute; repeat rewrite <- const_unfold; finish_norm.
Qed.

Lemma RF_0 : forall k, EX (3 * (k + 3)) -->* CO 5 (rl (3%nat :: repeat 2%nat k) (const 0)).
Proof.
  intros k. unfold EX, CO. cbn [rl]. rewrite rl_rep2.
  replace (3 * (k + 3)) with (1 + (3 * k + 8)) by lia.
  do 2 rewrite <- ones_add. rewrite <- pow111.
  execute.
  follow triNOM.
  execute.
  follow triAGA.
  align_tape.
  execute; repeat rewrite <- const_unfold; finish_norm.
Qed.

(** ** Outer rounds *)
Lemma CO_SW : forall a ds R, CO a (rl ds R) -->* SW (0 >> 1 >> const 0) 0 a ds R.
Proof. intros. unfold CO, SW. follow walkF. finish. Qed.

Lemma OEX : forall a n N, N = a + 2 * n + 2 -> CO a (rl (repeat 1%nat n) (const 0)) -->* EX N.
Proof.
  intros a n N HN. rewrite <- (app_nil_r (repeat 1%nat n)).
  follow CO_SW. follow SW_pass_iter. apply (SW_exit_out (0 + n) a N). lia.
Qed.

Lemma R1_raw : forall a p e os,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) (const 0)) -->*
  CO 5 (1 >> [0;1]^^p *> [1]^^(S a) *> 0 >> rl (S e :: os) (const 0)).
Proof.
  intros. follow CO_SW. follow SW_pass_iter. follow SW_E.
  replace (0 + S p) with (S p) by lia. cbn [lpow app Str_app].
  execute; unfold CO; finish_norm.
Qed.

Lemma R1 : forall a p e os,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) (const 0)) -->*
  CO 5 (rl (repeat 1%nat p ++ (a + 2) :: S e :: os) (const 0)).
Proof.
  intros. follow R1_raw. rewrite rl_app, rl_rep1.
  replace (a + 2) with (S (S a)) by lia. cbn [rl lpow app Str_app].
  rewrite (align_lpow 1 [0]). simpl app. finish.
Qed.

(** ** Exact hierarchy functions *)
Local Open Scope nat_scope.

Fixpoint iter {X : Type} (n : nat) (g : X -> X) (x : X) : X :=
  match n with
  | 0 => x
  | S n' => g (iter n' g x)
  end.

Lemma iter_S' : forall {X : Type} n (g : X -> X) x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

Lemma iter_add : forall {X : Type} a b (g : X -> X) x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

(** inner level maps: h 0 = position 2 (x -> x+4), h (S m) x = h m iterated x+2 times from 2 *)
Fixpoint h (m x : nat) : nat :=
  match m with
  | 0 => x + 4
  | S m' => iter (x + 2) (h m') 2
  end.

(** process n digits 2 at levels m, m+1, ... *)
Fixpoint hc (m n x : nat) : nat :=
  match n with
  | 0 => x
  | S n' => hc (S m) n' (h m x)
  end.

Definition Gk (k : nat) : nat := hc 0 (S k) 3 + 2 * S k + 2.
Definition G (a : nat) : nat := Gk (a / 3).

(** outer level maps *)
Fixpoint ho (m a : nat) : nat :=
  match m with
  | 0 => G a
  | S m' => iter (a + 1) (ho m') 5
  end.

Fixpoint hoc (m n a : nat) : nat :=
  match n with
  | 0 => a
  | S n' => hoc (S m) n' (ho m a)
  end.

Close Scope nat_scope.

(** ** Inner levels *)
Lemma LV_in : forall m e x ds R,
  CI x (repeat 1%nat m ++ S e :: ds) R -->* CI (iter e (h m) x) (repeat 1%nat (S m) ++ ds) R.
Proof.
  induction m as [| m IHm]; intros e; induction e as [| e IHe]; intros x ds R.
  - simpl. finish.
  - simpl app. follow CI_E0. follow IHe. rewrite iter_S'. finish.
  - rewrite rep_snoc. finish.
  - follow CI_E1. follow (IHm (x + 2)%nat 2%nat (S e :: ds) R).
    follow IHe. rewrite iter_S'. finish.
Qed.

Lemma Chain_in : forall n m x R,
  CI x (repeat 1%nat m ++ repeat 2%nat n) R -->* CI (hc m n x) (repeat 1%nat (m + n)) R.
Proof.
  induction n as [| n IHn]; intros m x R.
  - rewrite app_nil_r, Nat.add_0_r. finish.
  - simpl repeat. follow (LV_in m 1%nat x (repeat 2%nat n) R).
    follow IHn. replace (S m + n)%nat with (m + S n)%nat by lia. finish.
Qed.

Lemma R0_CI : forall k R,
  (0 >> 1 >> const 0) <{{G}} (1 >> [1]^^(S (3 * k + 2)) *> 0 >> R) -->*
  CI 3%nat (repeat 2%nat (S k)) (0 >> R).
Proof.
  intros k R. unfold CI. rewrite rl_rep2. cbn [rl lpow app Str_app].
  rewrite <- ones_add, <- pow111.
  execute.
  follow triNOM.
  execute.
  follow triAGA.
  align_tape.
  execute; repeat rewrite <- const_unfold; finish_norm.
Qed.

Lemma R0_k : forall k e os,
  CO (3 * k + 2)%nat (rl (S (S e) :: os) (const 0)) -->* CO (Gk k) (rl (S e :: os) (const 0)).
Proof.
  intros k e os.
  follow CO_SW. follow SW_E. cbn [lpow app Str_app].
  follow R0_CI.
  follow (Chain_in (S k) 0%nat 3%nat (0 >> rl (S e :: os) (const 0))).
  follow CI_exit.
  unfold Gk. finish.
Qed.

Lemma R0 : forall a e os, (exists k, a = (3 * k + 2)%nat) ->
  CO a (rl (S (S e) :: os) (const 0)) -->* CO (G a) (rl (S e :: os) (const 0)).
Proof.
  intros a e os [k Hk]. subst a.
  unfold G. replace ((3 * k + 2) / 3)%nat with k by (apply Nat.div_unique with 2%nat; lia).
  apply R0_k.
Qed.

Local Open Scope nat_scope.

(** ** The mod-3 invariant *)
Definition P1 (g : nat -> nat) : Prop := forall x, exists q, g x = x + 1 + 3 * q.

Lemma iter_P1 : forall g, P1 g -> forall n z, exists q, iter n g z = z + n + 3 * q.
Proof.
  intros g Hg. induction n; intros z.
  - exists 0. simpl. lia.
  - destruct (IHn z) as [q Hq]. destruct (Hg (iter n g z)) as [q' Hq'].
    exists (q + q'). simpl. rewrite Hq', Hq. lia.
Qed.

Lemma h_P1 : forall m, P1 (h m).
Proof.
  induction m as [| m IHm]; intros x.
  - exists 1. simpl. lia.
  - destruct (iter_P1 (h m) IHm (x + 2) 2) as [q Hq]. exists (q + 1). simpl h. rewrite Hq. lia.
Qed.

Lemma hc_mod : forall n m x, exists q, hc m n x = x + n + 3 * q.
Proof.
  induction n as [| n IHn]; intros m x.
  - exists 0. simpl. lia.
  - destruct (h_P1 m x) as [q Hq]. destruct (IHn (S m) (h m x)) as [q' Hq'].
    exists (q + q'). simpl hc. rewrite Hq', Hq. lia.
Qed.

Lemma Gk_mod3 : forall k, exists q, Gk k = 3 * q + 2.
Proof.
  intros k. unfold Gk. destruct (hc_mod (S k) 0 3) as [q Hq].
  exists (q + S k + 1). lia.
Qed.

Lemma G_mod3 : forall a, exists q, G a = 3 * q + 2.
Proof. intros a. apply Gk_mod3. Qed.

Lemma ho_mod3 : forall m a, exists q, ho m a = 3 * q + 2.
Proof.
  induction m as [| m IHm]; intros a.
  - apply G_mod3.
  - simpl. replace (a + 1) with (S a) by lia. simpl. apply IHm.
Qed.

Lemma hoc_mod3 : forall n m a, (exists q, a = 3 * q + 2) -> exists q, hoc m n a = 3 * q + 2.
Proof.
  induction n as [| n IHn]; intros m a Ha; simpl.
  - exact Ha.
  - apply IHn, ho_mod3.
Qed.

Close Scope nat_scope.

(** ** Outer levels *)
Lemma LV_out : forall m e a os, (exists k, a = (3 * k + 2)%nat) ->
  CO a (rl (repeat 1%nat m ++ S e :: os) (const 0)) -->* CO (iter e (ho m) a) (rl (repeat 1%nat (S m) ++ os) (const 0)).
Proof.
  induction m as [| m IHm]; intros e; induction e as [| e IHe]; intros a os Ha.
  - simpl. finish.
  - simpl app. follow (R0 a e os Ha).
    follow (IHe (G a) os (G_mod3 a)). rewrite iter_S'. finish.
  - rewrite rep_snoc. finish.
  - follow R1.
    assert (H5 : exists k, 5%nat = (3 * k + 2)%nat) by (exists 1%nat; lia).
    follow (IHm (a + 1)%nat 5%nat (S e :: os) H5).
    follow (IHe (ho (S m) a) os (ho_mod3 (S m) a)).
    rewrite iter_S'. finish.
Qed.

Lemma Chain_out : forall n m a os, (exists k, a = (3 * k + 2)%nat) ->
  CO a (rl (repeat 1%nat m ++ repeat 2%nat n ++ os) (const 0)) -->* CO (hoc m n a) (rl (repeat 1%nat (m + n) ++ os) (const 0)).
Proof.
  induction n as [| n IHn]; intros m a os Ha.
  - rewrite Nat.add_0_r. finish.
  - simpl repeat. cbn [app]. follow (LV_out m 1%nat a (repeat 2%nat n ++ os) Ha).
    follow (IHn (S m) (ho m a) os (ho_mod3 m a)).
    replace (S m + n)%nat with (m + S n)%nat by lia. finish.
Qed.

Local Open Scope nat_scope.

(** ** Exact Mod-9 / Mod-18 Periodicity of the Inner Hierarchy *)
Lemma h_0 : forall x, h 0 x = x + 4.  Proof. reflexivity. Qed.
Lemma h_S : forall m x, h (S m) x = iter (x + 2) (h m) 2.  Proof. reflexivity. Qed.
Lemma hc_0 : forall m x, hc m 0 x = x.  Proof. reflexivity. Qed.
Lemma hc_S : forall m n x, hc m (S n) x = hc (S m) n (h m x).  Proof. reflexivity. Qed.
Lemma G_eq : forall a, G a = hc 0 (S (a / 3)) 3 + 2 * S (a / 3) + 2.  Proof. reflexivity. Qed.
Lemma ho_0 : forall a, ho 0 a = G a.  Proof. reflexivity. Qed.
Lemma ho_S : forall m a, ho (S m) a = iter (a + 1) (ho m) 5.  Proof. reflexivity. Qed.
Lemma hoc_0 : forall m a, hoc m 0 a = a.  Proof. reflexivity. Qed.
Lemma hoc_S : forall m n a, hoc m (S n) a = hoc (S m) n (ho m a).  Proof. reflexivity. Qed.

Ltac Zify.zify_pre_hook ::= idtac.
Strategy opaque [h hc Gk G ho hoc].

Lemma iter_h0 : forall n y, iter n (h 0) y = y + 4 * n.
Proof. induction n; intros; cbn [iter]. - lia. - rewrite IHn, h_0. lia. Qed.

Lemma h1_eq : forall x, h 1 x = 4 * x + 10.
Proof. intros. rewrite h_S, iter_h0. lia. Qed.

Lemma h_even : forall m x, exists q, h (S m) x = 2 * q.
Proof.
  induction m as [| m IHm]; intros x.
  - rewrite h1_eq. exists (2 * x + 5). lia.
  - rewrite h_S. replace (x + 2) with (S (x + 1)) by lia. simpl iter. apply IHm.
Qed.

Lemma mod2_cases : forall n, (exists k, n = 2 * k) \/ (exists k, n = 2 * k + 1).
Proof.
  induction n as [| n [[k Hk] | [k Hk]]].
  - left. exists 0. lia.
  - right. exists k. lia.
  - left. exists (S k). lia.
Qed.

Lemma mod3_cases : forall n, (exists k, n = 3 * k) \/ (exists k, n = 3 * k + 1) \/ (exists k, n = 3 * k + 2).
Proof.
  induction n as [| n [[k Hk] | [[k Hk] | [k Hk]]]].
  - left. exists 0. lia.
  - right. left. exists k. lia.
  - right. right. exists k. lia.
  - left. exists (S k). lia.
Qed.

Lemma iter3_h1 : forall z, exists q, iter 3 (h 1) z = z + 3 + 9 * q.
Proof. intros z. cbn [iter]. rewrite !h1_eq. exists (7 * z + 23). lia. Qed.

Lemma h2_step3 : forall x, exists q, h 2 (x + 3) = h 2 x + 3 + 9 * q.
Proof.
  intros x. rewrite !h_S. replace (x + 3 + 2) with (3 + (x + 2)) by lia.
  rewrite iter_add. apply iter3_h1.
Qed.

Lemma h2_step3k : forall k r, exists q, h 2 (3 * k + r) = h 2 r + 3 * k + 9 * q.
Proof.
  induction k as [| k IHk]; intros r.
  - exists 0. replace (3 * 0 + r) with r by lia. lia.
  - replace (3 * S k + r) with ((3 * k + r) + 3) by lia.
    destruct (h2_step3 (3 * k + r)) as [q1 H1]. destruct (IHk r) as [q2 H2].
    exists (q1 + q2). lia.
Qed.

Lemma h2_012 : h 2 0 = 82 /\ h 2 1 = 338 /\ h 2 2 = 1362.
Proof. rewrite !h_S. cbn [Nat.add iter]. rewrite !h1_eq. lia. Qed.

Lemma h2_mod9_0 : forall k, exists q, h 2 (3 * k) = 3 * k + 1 + 9 * q.
Proof.
  intros k. destruct (h2_step3k k 0) as [q Hq]. destruct h2_012 as (H0 & _).
  exists (q + 9). replace (3 * k + 0) with (3 * k) in Hq by lia. lia.
Qed.

Lemma h2_mod9_1 : forall k, exists q, h 2 (3 * k + 1) = 3 * k + 5 + 9 * q.
Proof.
  intros k. destruct (h2_step3k k 1) as [q Hq]. destruct h2_012 as (_ & H1 & _).
  exists (q + 37). lia.
Qed.

Lemma h2_mod9_2 : forall k, exists q, h 2 (3 * k + 2) = 3 * k + 3 + 9 * q.
Proof.
  intros k. destruct (h2_step3k k 2) as [q Hq]. destruct h2_012 as (_ & _ & H2).
  exists (q + 151). lia.
Qed.

Lemma iter3_h2 : forall z, exists q, iter 3 (h 2) z = z + 6 + 9 * q.
Proof.
  intros z. cbn [iter]. destruct (mod3_cases z) as [[k Hk] | [[k Hk] | [k Hk]]]; subst z.
  - destruct (h2_mod9_0 k) as [q1 H1].
    replace (3 * k + 1 + 9 * q1) with (3 * (k + 3 * q1) + 1) in H1 by lia. rewrite H1.
    destruct (h2_mod9_1 (k + 3 * q1)) as [q2 H2].
    replace (3 * (k + 3 * q1) + 5 + 9 * q2) with (3 * (k + 3 * q1 + 3 * q2 + 1) + 2) in H2 by lia. rewrite H2.
    destruct (h2_mod9_2 (k + 3 * q1 + 3 * q2 + 1)) as [q3 H3].
    exists (q1 + q2 + q3). lia.
  - destruct (h2_mod9_1 k) as [q1 H1].
    replace (3 * k + 5 + 9 * q1) with (3 * (k + 3 * q1 + 1) + 2) in H1 by lia. rewrite H1.
    destruct (h2_mod9_2 (k + 3 * q1 + 1)) as [q2 H2].
    replace (3 * (k + 3 * q1 + 1) + 3 + 9 * q2) with (3 * (k + 3 * q1 + 3 * q2 + 2)) in H2 by lia. rewrite H2.
    destruct (h2_mod9_0 (k + 3 * q1 + 3 * q2 + 2)) as [q3 H3].
    exists (q1 + q2 + q3). lia.
  - destruct (h2_mod9_2 k) as [q1 H1].
    replace (3 * k + 3 + 9 * q1) with (3 * (k + 3 * q1 + 1)) in H1 by lia. rewrite H1.
    destruct (h2_mod9_0 (k + 3 * q1 + 1)) as [q2 H2].
    replace (3 * (k + 3 * q1 + 1) + 1 + 9 * q2) with (3 * (k + 3 * q1 + 3 * q2 + 1) + 1) in H2 by lia. rewrite H2.
    destruct (h2_mod9_1 (k + 3 * q1 + 3 * q2 + 1)) as [q3 H3].
    exists (q1 + q2 + q3). lia.
Qed.

Lemma h3_step3 : forall x, exists q, h 3 (x + 3) = h 3 x + 6 + 9 * q.
Proof.
  intros x. rewrite !h_S. replace (x + 3 + 2) with (3 + (x + 2)) by lia.
  rewrite iter_add. apply iter3_h2.
Qed.

Lemma h3_step3k : forall k r, exists q, h 3 (3 * k + r) = h 3 r + 6 * k + 9 * q.
Proof.
  induction k as [| k IHk]; intros r.
  - exists 0. replace (3 * 0 + r) with r by lia. lia.
  - replace (3 * S k + r) with ((3 * k + r) + 3) by lia.
    destruct (h3_step3 (3 * k + r)) as [q1 H1]. destruct (IHk r) as [q2 H2].
    exists (q1 + q2). lia.
Qed.

Lemma h_S_step : forall m x, h (S m) (S x) = h m (h (S m) x).
Proof. intros m x. rewrite !h_S. reflexivity. Qed.

Lemma h3_012 :
  (exists q, h 3 0 = 4 + 9 * q) /\
  (exists q, h 3 1 = 8 + 9 * q) /\
  (exists q, h 3 2 = 9 * q).
Proof.
  destruct h2_012 as (_ & _ & H22).
  assert (H30 : exists q, h 3 0 = 4 + 9 * q).
  { rewrite h_S. cbn [Nat.add iter]. rewrite H22.
    replace 1362 with (3 * 454) by lia.
    destruct (h2_mod9_0 454) as [q Hq]. exists (q + 151). lia. }
  destruct H30 as [q0 Hq0].
  assert (H31 : exists q, h 3 1 = 8 + 9 * q).
  { rewrite (h_S_step 2 0), Hq0.
    replace (4 + 9 * q0) with (3 * (3 * q0 + 1) + 1) by lia.
    destruct (h2_mod9_1 (3 * q0 + 1)) as [q1 Hq1]. exists (q0 + q1). lia. }
  destruct H31 as [q1 Hq1].
  assert (H32 : exists q, h 3 2 = 9 * q).
  { rewrite (h_S_step 2 1), Hq1.
    replace (8 + 9 * q1) with (3 * (3 * q1 + 2) + 2) by lia.
    destruct (h2_mod9_2 (3 * q1 + 2)) as [q2 Hq2]. exists (q1 + q2 + 1). lia. }
  split; [exists q0; exact Hq0 | split; [exists q1; exact Hq1 | exact H32]].
Qed.

Lemma h3_mod9_0 : forall k, exists q, h 3 (3 * k) = 6 * k + 4 + 9 * q.
Proof.
  intros k. destruct (h3_step3k k 0) as [q Hq]. destruct h3_012 as ([q0 H0] & _).
  exists (q + q0). replace (3 * k + 0) with (3 * k) in Hq by lia. lia.
Qed.

Lemma h3_mod9_1 : forall k, exists q, h 3 (3 * k + 1) = 6 * k + 8 + 9 * q.
Proof.
  intros k. destruct (h3_step3k k 1) as [q Hq]. destruct h3_012 as (_ & [q1 H1] & _).
  exists (q + q1). lia.
Qed.

Lemma h3_mod9_2 : forall k, exists q, h 3 (3 * k + 2) = 6 * k + 9 * q.
Proof.
  intros k. destruct (h3_step3k k 2) as [q Hq]. destruct h3_012 as (_ & _ & [q2 H2]).
  exists (q + q2). lia.
Qed.

Lemma h3_18_2 : forall k, exists k', h 3 (18 * k + 2) = 18 * k'.
Proof.
  intros k. replace (18 * k + 2) with (3 * (6 * k) + 2) by lia.
  destruct (h3_mod9_2 (6 * k)) as [q Hq].
  destruct (h_even 2 (3 * (6 * k) + 2)) as [w Hw].
  destruct (mod2_cases q) as [[m Hm] | [m Hm]]; [exists (2 * k + m) | exfalso]; lia.
Qed.

Lemma h3_18_0 : forall k, exists k', h 3 (18 * k) = 18 * k' + 4.
Proof.
  intros k. replace (18 * k) with (3 * (6 * k)) by lia.
  destruct (h3_mod9_0 (6 * k)) as [q Hq].
  destruct (h_even 2 (3 * (6 * k))) as [w Hw].
  destruct (mod2_cases q) as [[m Hm] | [m Hm]]; [exists (2 * k + m) | exfalso]; lia.
Qed.

Lemma h3_18_4 : forall k, exists k', h 3 (18 * k + 4) = 18 * k' + 14.
Proof.
  intros k. replace (18 * k + 4) with (3 * (6 * k + 1) + 1) by lia.
  destruct (h3_mod9_1 (6 * k + 1)) as [q Hq].
  destruct (h_even 2 (3 * (6 * k + 1) + 1)) as [w Hw].
  destruct (mod2_cases q) as [[m Hm] | [m Hm]]; [exists (2 * k + m) | exfalso]; lia.
Qed.

Lemma h3_18_14 : forall k, exists k', h 3 (18 * k + 14) = 18 * k' + 6.
Proof.
  intros k. replace (18 * k + 14) with (3 * (6 * k + 4) + 2) by lia.
  destruct (h3_mod9_2 (6 * k + 4)) as [q Hq].
  destruct (h_even 2 (3 * (6 * k + 4) + 2)) as [w Hw].
  destruct (mod2_cases q) as [[m Hm] | [m Hm]]; [exists (2 * k + m + 1) | exfalso]; lia.
Qed.

Lemma h3_18_6 : forall k, exists k', h 3 (18 * k + 6) = 18 * k' + 16.
Proof.
  intros k. replace (18 * k + 6) with (3 * (6 * k + 2)) by lia.
  destruct (h3_mod9_0 (6 * k + 2)) as [q Hq].
  destruct (h_even 2 (3 * (6 * k + 2))) as [w Hw].
  destruct (mod2_cases q) as [[m Hm] | [m Hm]]; [exists (2 * k + m) | exfalso]; lia.
Qed.

Lemma h3_18_16 : forall k, exists k', h 3 (18 * k + 16) = 18 * k' + 2.
Proof.
  intros k. replace (18 * k + 16) with (3 * (6 * k + 5) + 1) by lia.
  destruct (h3_mod9_1 (6 * k + 5)) as [q Hq].
  destruct (h_even 2 (3 * (6 * k + 5) + 1)) as [w Hw].
  destruct (mod2_cases q) as [[m Hm] | [m Hm]]; [exists (2 * k + m + 2) | exfalso]; lia.
Qed.

Lemma iter6_h3_18 : forall k, exists k', iter 6 (h 3) (18 * k + 2) = 18 * k' + 2.
Proof.
  intros k. cbn [iter].
  destruct (h3_18_2 k) as [k1 H1]; rewrite H1.
  destruct (h3_18_0 k1) as [k2 H2]; rewrite H2.
  destruct (h3_18_4 k2) as [k3 H3]; rewrite H3.
  destruct (h3_18_14 k3) as [k4 H4]; rewrite H4.
  destruct (h3_18_6 k4) as [k5 H5]; rewrite H5.
  apply h3_18_16.
Qed.

Lemma iter6w_h3_18 : forall w, exists k', iter (6 * w) (h 3) 2 = 18 * k' + 2.
Proof.
  induction w as [| w [k IH]].
  - exists 0. simpl. lia.
  - replace (6 * S w) with (6 + 6 * w) by lia.
    rewrite iter_add, IH. apply iter6_h3_18.
Qed.

Definition Cyc18 (g : nat -> nat) : Prop :=
  (forall k, exists k', g (18 * k + 2) = 18 * k' + 6) /\
  (forall k, exists k', g (18 * k + 6) = 18 * k' + 4) /\
  (forall k, exists k', g (18 * k + 4) = 18 * k' + 2).

Lemma h4_Cyc18 : Cyc18 (h 4).
Proof.
  split; [| split]; intros k; rewrite h_S.
  - replace (18 * k + 2 + 2) with (4 + 6 * (3 * k)) by lia.
    rewrite iter_add. destruct (iter6w_h3_18 (3 * k)) as [k0 H0]; rewrite H0.
    cbn [iter].
    destruct (h3_18_2 k0) as [k1 H1]; rewrite H1.
    destruct (h3_18_0 k1) as [k2 H2]; rewrite H2.
    destruct (h3_18_4 k2) as [k3 H3]; rewrite H3.
    apply h3_18_14.
  - replace (18 * k + 6 + 2) with (2 + 6 * (3 * k + 1)) by lia.
    rewrite iter_add. destruct (iter6w_h3_18 (3 * k + 1)) as [k0 H0]; rewrite H0.
    cbn [iter].
    destruct (h3_18_2 k0) as [k1 H1]; rewrite H1.
    apply h3_18_0.
  - replace (18 * k + 4 + 2) with (6 * (3 * k + 1)) by lia.
    apply iter6w_h3_18.
Qed.

Lemma Cyc18_iter3w : forall g, Cyc18 g -> forall w, exists k', iter (3 * w) g 2 = 18 * k' + 2.
Proof.
  intros g (H2 & H6 & H4). induction w as [| w [k IH]].
  - exists 0. simpl. lia.
  - replace (3 * S w) with (3 + 3 * w) by lia.
    rewrite iter_add, IH. cbn [iter].
    destruct (H2 k) as [k1 Hk1]; rewrite Hk1.
    destruct (H6 k1) as [k2 Hk2]; rewrite Hk2.
    apply H4.
Qed.

Lemma Cyc18_step : forall m, Cyc18 (h m) -> Cyc18 (h (S m)).
Proof.
  intros m Hg. pose proof (Cyc18_iter3w (h m) Hg) as Hw.
  destruct Hg as (H2 & H6 & H4).
  split; [| split]; intros k; rewrite h_S.
  - replace (18 * k + 2 + 2) with (1 + 3 * (6 * k + 1)) by lia.
    rewrite iter_add. destruct (Hw (6 * k + 1)) as [k0 H0]; rewrite H0.
    cbn [iter]. apply H2.
  - replace (18 * k + 6 + 2) with (2 + 3 * (6 * k + 2)) by lia.
    rewrite iter_add. destruct (Hw (6 * k + 2)) as [k0 H0]; rewrite H0.
    cbn [iter]. destruct (H2 k0) as [k1 H1]; rewrite H1. apply H6.
  - replace (18 * k + 4 + 2) with (3 * (6 * k + 2)) by lia.
    apply Hw.
Qed.

Lemma h_Cyc18 : forall d, Cyc18 (h (4 + d)).
Proof.
  induction d as [| d IH].
  - exact h4_Cyc18.
  - replace (4 + S d) with (S (4 + d)) by lia.
    apply Cyc18_step, IH.
Qed.

Lemma hc5_18 : exists k, hc 0 5 3 = 18 * k + 2.
Proof.
  do 5 rewrite hc_S. rewrite hc_0, h_0, h1_eq.
  replace (4 * (3 + 4) + 10) with (3 * 12 + 2) by lia.
  destruct (h2_mod9_2 12) as [q1 H1].
  replace (3 * 12 + 3 + 9 * q1) with (3 * (3 * q1 + 13)) in H1 by lia. rewrite H1.
  destruct (h3_mod9_0 (3 * q1 + 13)) as [q2 H2].
  destruct (h_even 2 (3 * (3 * q1 + 13))) as [w Hw].
  assert (H10 : exists k0, h 3 (3 * (3 * q1 + 13)) = 18 * k0 + 10).
  { destruct (mod2_cases q2) as [[m Hm] | [m Hm]]; [exists (q1 + m + 4) | exfalso]; lia. }
  destruct H10 as [k0 Hk0]; rewrite Hk0.
  rewrite h_S. replace (18 * k0 + 10 + 2) with (6 * (3 * k0 + 2)) by lia.
  apply iter6w_h3_18.
Qed.

Lemma hc_Cyc18_3 : forall d k,
  exists k', hc (4 + d) 3 (18 * k + 2) = 18 * k' + 2.
Proof.
  intros d k. do 3 rewrite hc_S. rewrite hc_0.
  destruct (h_Cyc18 d) as (H2 & _ & _).
  destruct (H2 k) as [k1 Hk1]; rewrite Hk1.
  destruct (h_Cyc18 (S d)) as (_ & H6 & _).
  replace (S (4 + d)) with (4 + S d) by lia.
  destruct (H6 k1) as [k2 Hk2]; rewrite Hk2.
  destruct (h_Cyc18 (S (S d))) as (_ & _ & H4).
  replace (S (4 + S d)) with (4 + S (S d)) by lia.
  apply H4.
Qed.

Lemma hc_split : forall m a b x, hc m (a + b) x = hc (m + a) b (hc m a x).
Proof.
  intros m a. generalize dependent m.
  induction a as [| a IHa]; intros m b x; cbn [Nat.add].
  - rewrite hc_0. replace (m + 0) with m by lia. reflexivity.
  - rewrite !hc_S, IHa. replace (S m + a) with (m + S a) by lia. reflexivity.
Qed.

Lemma hc15_18 : exists k, hc 0 15 3 = 18 * k + 6.
Proof.
  change 15 with (5 + (3 + (3 + (3 + 1)))).
  rewrite (hc_split 0 5 _ 3). destruct hc5_18 as [k0 H0]; rewrite H0.
  rewrite (hc_split 5 3 _ (18 * k0 + 2)).
  destruct (hc_Cyc18_3 1 k0) as [k1 H1]; cbn [Nat.add] in H1; rewrite H1.
  rewrite (hc_split 8 3 _ (18 * k1 + 2)).
  destruct (hc_Cyc18_3 4 k1) as [k2 H2]; cbn [Nat.add] in H2; rewrite H2.
  rewrite (hc_split 11 3 _ (18 * k2 + 2)).
  destruct (hc_Cyc18_3 7 k2) as [k3 H3]; cbn [Nat.add] in H3; rewrite H3.
  rewrite hc_S, hc_0. destruct (h_Cyc18 10) as (H2' & _).
  apply H2'.
Qed.

Lemma G_k : forall k, G (3 * k + 2) = hc 0 (S k) 3 + 2 * S k + 2.
Proof.
  intros k. rewrite G_eq.
  replace ((3 * k + 2) / 3) with k by (apply Nat.div_unique with 2; lia).
  reflexivity.
Qed.

Lemma G5_eq : G 5 = 44.
Proof.
  change (G 5) with (G (3 * 1 + 2)). rewrite (G_k 1).
  do 2 rewrite hc_S. rewrite hc_0, h_0, h1_eq. lia.
Qed.

Lemma G44_mod9 : exists k1 q1, G 44 + 4 = 3 * (k1 + 3) /\ k1 = 3 * q1 + 2.
Proof.
  destruct hc15_18 as [k Hk].
  exists (6 * k + 11), (2 * k + 3).
  change (G 44) with (G (3 * 14 + 2)). rewrite (G_k 14).
  rewrite Hk. lia.
Qed.

(** ** The run from the blank tape *)
Lemma boot1 : c0 -->* CO 5 (rl [1%nat] (const S0)).
Proof.
  unfold CO. cbn [rl lpow app Str_app].
  do 80 step. repeat rewrite <- const_unfold. finish.
Qed.

Lemma boot : c0 -->* CO 5 (rl [3%nat] (const S0)).
Proof.
  follow boot1.
  follow (OEX 5 1 9 eq_refl).
  apply (RF_0 0).
Qed.

Lemma LV_out_eq : forall m e a os b, (exists k, a = 3 * k + 2) -> b = iter e (ho m) a ->
  CO a (rl (repeat 1 m ++ S e :: os) (const S0)) -->* CO b (rl (repeat 1 (S m) ++ os) (const S0)).
Proof. intros. subst b. apply LV_out. assumption. Qed.

Lemma Chain_out_eq : forall n m a os b, (exists k, a = 3 * k + 2) -> b = hoc m n a ->
  CO a (rl (repeat 1 m ++ repeat 2 n ++ os) (const S0)) -->* CO b (rl (repeat 1 (m + n) ++ os) (const S0)).
Proof. intros. subst b. apply Chain_out. assumption. Qed.

Lemma run_gen : forall a1 k1 a2 j,
  a1 = iter 2 (ho 0) 5 -> (exists k, a1 = 3 * k + 2) ->
  a1 + 4 = 3 * (k1 + 3) -> a2 = hoc 1 k1 a1 ->
  a2 + 2 * S k1 + 2 = 3 * S j + 1 ->
  c0 -->* Hc j.
Proof.
  intros a1 k1 a2 j Ha1 Ha1m Hk1 Ha2 Hj.
  assert (H5 : exists k, 5 = 3 * k + 2) by (exists 1; lia).
  follow boot.
  follow (LV_out_eq 0 2 5 [] a1 H5 Ha1).
  follow (OEX a1 1 (3 * (k1 + 3)) ltac:(lia)).
  follow (RF_0 k1).
  follow (LV_out_eq 0 2 5 (repeat 2 k1) a1 H5 Ha1).
  rewrite <- (app_nil_r (repeat 2 k1)).
  follow (Chain_out_eq k1 1 a1 [] a2 Ha1m Ha2).
  rewrite app_nil_r.
  follow (OEX a2 (S k1) (3 * S j + 1) (eq_sym Hj)).
  apply RF_halt.
Qed.

Lemma Hiter5 : G 44 = iter 2 (ho 0) 5.
Proof. cbn [iter]. rewrite (ho_0 5), G5_eq, (ho_0 44). reflexivity. Qed.

Lemma J_gen : forall a1 k1 q1 a2,
  (exists k, a1 = 3 * k + 2) -> k1 = 3 * q1 + 2 -> a2 = hoc 1 k1 a1 ->
  exists j, a2 + 2 * S k1 + 2 = 3 * S j + 1.
Proof.
  intros a1 k1 q1 a2 Ha1 Hk1 Ha2.
  destruct (hoc_mod3 k1 1 a1 Ha1) as [q2 Hq2].
  exists (q2 + 2 * q1 + 2). subst. lia.
Qed.

Lemma run : exists k1 q1 a2 j,
  G 44 + 4 = 3 * (k1 + 3) /\ k1 = 3 * q1 + 2 /\
  a2 = hoc 1 k1 (G 44) /\ a2 + 2 * S k1 + 2 = 3 * S j + 1 /\
  c0 -->* Hc j.
Proof.
  destruct G44_mod9 as (k1 & q1 & Hk1 & Hq1).
  destruct (J_gen (G 44) k1 q1 (hoc 1 k1 (G 44)) (G_mod3 44) Hq1 eq_refl) as [j Hj].
  exists k1, q1, (hoc 1 k1 (G 44)), j.
  split; [exact Hk1 |]. split; [exact Hq1 |]. split; [reflexivity |]. split; [exact Hj |].
  exact (run_gen (G 44) k1 (hoc 1 k1 (G 44)) j Hiter5 (G_mod3 44) Hk1 eq_refl Hj).
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct run as (k1 & q1 & a2 & j & _ & _ & _ & _ & Hrun).
  destruct (with_counter Hrun) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts, Hc_halted.
Qed.

(** ** Score in the repository's standard form *)
Definition sym_val (s : Sym) : nat :=
  match s with
  | S0 => 0
  | S1 => 1
  end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with
  | [] => 0
  | x :: t => sym_val x + count1 t
  end.

(** [ones c N]: the tape of c is a finite word padded with 0s and holds exactly N ones. *)
Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl. - reflexivity. - rewrite IHxs. lia. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl. - reflexivity. - rewrite count1_app, IHn. lia. Qed.

Lemma ones_Hc : forall j, ones (Hc j) (2 * j + 4).
Proof.
  intros j. exists O, ([S1; S0] ++ [S0; S1; S1]^^(S j) ++ [S0; S0; S1]), (@nil Sym), S0.
  split.
  - unfold Hc. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, count1_pow. cbn [count1 sym_val]. lia.
Qed.

(** ** Fast-growing hierarchy up to f_(omega*2) *)
Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | 0 => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.

(** f_wk k = f_(omega+k);  f_w2 = f_(omega*2), f_(omega*2)(n) = f_(omega+n)(n) *)
Fixpoint f_wk (k : nat) : nat -> nat :=
  match k with
  | 0 => f_omega
  | S k' => fun n => iter n (f_wk k') n
  end.

Definition f_w2 (n : nat) : nat := f_wk n n.

Lemma iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

Lemma iter_ge : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_n : forall g, (forall a, a <= g a) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge. exact Hg.
Qed.

Lemma iter_linK : forall g K, (forall y, y + K <= g y) -> forall j c, c + j * K <= iter j g c.
Proof.
  intros g K Hg. induction j; intros c; simpl. - lia.
  - specialize (IHj c). specialize (Hg (iter j g c)). lia.
Qed.

Lemma iter_dom : forall K g h, (forall n z, K * n <= z -> K * g n <= h z) ->
  forall m n z, K * n <= z -> K * iter m g n <= iter m h z.
Proof. intros K g h Hd. induction m; intros n z Hz; simpl; auto. Qed.

(** generic transfer: a hierarchy iterated from a constant with >= z+1 iterations dominates the FGH-style one *)
Lemma transfer : forall (K c : nat) (F H : nat -> nat -> nat), 2 <= K ->
  (forall m n, F (S m) n = iter n (F m) n) ->
  (forall m z, iter (S z) (H m) c <= H (S m) z) ->
  (forall m y, y + K <= H m y) ->
  (forall n z, K * n <= z -> K * F 0 n <= H 0 z) ->
  forall m n z, K * n <= z -> K * F m n <= H m z.
Proof.
  intros K c F H HK HF HH Hg H0. induction m as [| m IH]; intros n z Hz.
  - auto.
  - rewrite HF.
    pose proof (HH m z) as Hm.
    replace (S z) with (n + (S z - n)) in Hm by nia.
    rewrite iter_add in Hm.
    assert (Hbig : K * n <= iter (S z - n) (H m) c).
    { pose proof (iter_linK (H m) K (Hg m) (S z - n) c). nia. }
    pose proof (iter_dom K (F m) (H m) IH n n (iter (S z - n) (H m) c) Hbig). lia.
Qed.

Lemma f_S : forall k n, f (S k) n = iter n (f k) n.
Proof. reflexivity. Qed.

Lemma f_props : forall k, (forall n, n <= f k n) /\ (forall a b, a <= b -> f k a <= f k b).
Proof.
  induction k as [| k [Hid Hmono]].
  - split; intros; simpl; lia.
  - split.
    + intros n. rewrite f_S. apply iter_ge. exact Hid.
    + intros a b Hab. rewrite !f_S. transitivity (iter a (f k) b).
      * apply iter_mono_x; assumption.
      * apply iter_mono_n; assumption.
Qed.

Lemma f_id : forall k n, n <= f k n.
Proof. intros. apply f_props. Qed.

Lemma f_mono : forall k a b, a <= b -> f k a <= f k b.
Proof. intros. apply f_props. assumption. Qed.

Lemma f_gt : forall k n, 1 <= n -> n < f k n.
Proof.
  induction k; intros n Hn.
  - simpl. lia.
  - rewrite f_S. destruct n as [| n']; [lia |].
    simpl. pose proof (iter_ge (f k) (f_id k) n' (S n')).
    specialize (IHk (iter n' (f k) (S n')) ltac:(lia)). lia.
Qed.

Lemma f_level : forall k n, 1 <= n -> f k n <= f (S k) n.
Proof.
  intros k n Hn. rewrite f_S. destruct n as [| n']; [lia |].
  rewrite iter_S'. apply iter_ge. apply f_id.
Qed.

Lemma f_level_mono : forall d k n, 1 <= n -> f k n <= f (d + k) n.
Proof.
  induction d; intros k n Hn. - reflexivity.
  - specialize (IHd k n Hn). pose proof (f_level (d + k) n Hn). change (S d + k) with (S (d + k)). lia.
Qed.

Lemma iter_succ_add : forall n x, iter n S x = n + x.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Lemma f1 : forall n, f 1 n = 2 * n.
Proof. intros. rewrite f_S. rewrite iter_succ_add. lia. Qed.

Lemma f_dbl : forall k n, 1 <= k -> 2 * n <= f k n.
Proof.
  intros k n Hk. destruct n as [| n']. - lia.
  - rewrite <- f1. replace k with ((k - 1) + 1) by lia. apply f_level_mono. lia.
Qed.

Lemma iter_f1 : forall n x, iter n (f 1) x = x * 2 ^ n.
Proof. induction n; intros; cbn [iter]. - simpl. lia. - rewrite IHn, f1. simpl. lia. Qed.

Lemma f2_eq : forall n, f 2 n = n * 2 ^ n.
Proof. intros. rewrite f_S. apply iter_f1. Qed.

(** f k (w+1) >= 2 f k w for k >= 2 *)
Lemma f_succ_dbl : forall k w, 2 <= k -> 2 * f k w <= f k (S w).
Proof.
  intros k w Hk. destruct k as [| k']; [lia |].
  rewrite !f_S. cbn [iter].
  pose proof (f_dbl k' (iter w (f k') (S w)) ltac:(lia)).
  pose proof (iter_mono_x (f k') (f_mono k') w w (S w) ltac:(lia)). lia.
Qed.

Lemma f_plus2 : forall k w, 2 <= k -> 4 * f k w <= f k (w + 2).
Proof.
  intros k w Hk. replace (w + 2) with (S (S w)) by lia.
  pose proof (f_succ_dbl k w Hk). pose proof (f_succ_dbl k (S w) Hk). lia.
Qed.

Lemma f_S_2 : forall k, f (S k) 2 = f k (f k 2).
Proof. reflexivity. Qed.

Lemma f_omega_eq : forall n, f_omega n = f n n.
Proof. reflexivity. Qed.

Lemma f_omega_id : forall n, n <= f_omega n.
Proof. intros n. apply f_id. Qed.

Lemma f_omega_mono : forall a b, a <= b -> f_omega a <= f_omega b.
Proof.
  intros [| a'] b Hab.
  - destruct b as [| b']. + reflexivity.
    + change (f_omega 0) with 1. pose proof (f_omega_id (S b')). lia.
  - rewrite !f_omega_eq.
    pose proof (f_level_mono (b - S a') (S a') (S a') ltac:(lia)) as L1.
    replace (b - S a' + S a') with b in L1 by lia.
    pose proof (f_mono b (S a') b Hab). lia.
Qed.

Lemma f_wk_S : forall k n, f_wk (S k) n = iter n (f_wk k) n.
Proof. reflexivity. Qed.

Lemma f_wk_props : forall k, (forall n, n <= f_wk k n) /\ (forall a b, a <= b -> f_wk k a <= f_wk k b).
Proof.
  induction k as [| k [Hid Hmono]].
  - split. + apply f_omega_id. + apply f_omega_mono.
  - split.
    + intros n. rewrite f_wk_S. apply iter_ge. exact Hid.
    + intros a b Hab. rewrite !f_wk_S. transitivity (iter a (f_wk k) b).
      * apply iter_mono_x; assumption.
      * apply iter_mono_n; assumption.
Qed.

Lemma f_wk_id : forall k n, n <= f_wk k n.
Proof. intros. apply f_wk_props. Qed.

Lemma f_wk_mono : forall k a b, a <= b -> f_wk k a <= f_wk k b.
Proof. intros. apply f_wk_props. assumption. Qed.

Lemma f_wk_level : forall k n, 1 <= n -> f_wk k n <= f_wk (S k) n.
Proof.
  intros k n Hn. rewrite f_wk_S. destruct n as [| n']; [lia |].
  rewrite iter_S'. apply iter_ge. apply f_wk_id.
Qed.

Lemma f_wk_level_mono : forall d k n, 1 <= n -> f_wk k n <= f_wk (d + k) n.
Proof.
  induction d; intros k n Hn. - reflexivity.
  - specialize (IHd k n Hn). pose proof (f_wk_level (d + k) n Hn). change (S d + k) with (S (d + k)). lia.
Qed.

Lemma f_w2_mono : forall a b, a <= b -> f_w2 a <= f_w2 b.
Proof.
  intros [| a'] b Hab; unfold f_w2.
  - destruct b as [| b']. + reflexivity.
    + pose proof (f_wk_id 0 0). pose proof (f_wk_level_mono (S b') 0 (S b') ltac:(lia)).
      pose proof (f_wk_mono 0 0 (S b') ltac:(lia)). rewrite Nat.add_0_r in *. lia.
  - pose proof (f_wk_level_mono (b - S a') (S a') (S a') ltac:(lia)) as L1.
    replace (b - S a' + S a') with b in L1 by lia.
    pose proof (f_wk_mono b (S a') b Hab). lia.
Qed.

(** ** Lower bounds for the machine's hierarchy *)
Lemma h_ge : forall m y, y + 2 <= h m y.
Proof.
  induction m as [| m IHm]; intros y.
  - rewrite h_0. lia.
  - rewrite h_S. pose proof (iter_linK (h m) 2 IHm (y + 2) 2). lia.
Qed.

Lemma h_dom : forall m n z, 2 * n <= z -> 2 * f m n <= h m z.
Proof.
  apply (transfer 2 2 f h ltac:(lia) f_S).
  - intros m z. rewrite h_S. apply iter_mono_n; [| lia].
    intros a. pose proof (h_ge m a). lia.
  - exact h_ge.
  - intros n z Hz. simpl f. rewrite h_0. lia.
Qed.

Lemma hc_ge : forall n m x, x + 2 * n <= hc m n x.
Proof.
  induction n as [| n IHn]; intros m x.
  - rewrite hc_0. lia.
  - rewrite hc_S. pose proof (IHn (S m) (h m x)). pose proof (h_ge m x). lia.
Qed.

Lemma hc_last : forall n m x, hc m (S n) x = h (m + n) (hc m n x).
Proof.
  induction n as [| n IHn]; intros m x.
  - rewrite hc_S, !hc_0, Nat.add_0_r. reflexivity.
  - rewrite hc_S, IHn, hc_S. f_equal. lia.
Qed.

Lemma G_ge : forall a, a + 6 <= G a.
Proof.
  intros a. rewrite G_eq.
  pose proof (hc_ge (S (a / 3)) 0 3).
  pose proof (Nat.div_mod a 3 ltac:(lia)).
  pose proof (Nat.mod_upper_bound a 3 ltac:(lia)).
  lia.
Qed.

Lemma G_dom : forall n z, 6 * n <= z -> 6 * f_omega n <= G z.
Proof.
  intros n z Hz. pose proof (G_ge z) as Hg.
  destruct n as [| [| n']].
  - change (f_omega 0) with 1. lia.
  - change (f_omega 1) with 2. lia.
  - set (n := S (S n')) in *.
    pose proof (Nat.div_mod z 3 ltac:(lia)) as Hdm.
    pose proof (Nat.mod_upper_bound z 3 ltac:(lia)) as Hmb.
    rewrite G_eq.
    set (c := z / 3) in *.
    assert (Hc : 2 * n <= c) by lia.
    destruct c as [| c'] eqn:Ec; [lia |].
    rewrite (hc_S 0 (S c') 3), h_0, hc_last. change (3 + 4) with 7.
    replace (1 + c') with (S c') by lia.
    pose proof (hc_ge c' 1 7) as HX.
    pose proof (h_dom (S c') (2 * n) (hc 1 c' 7) ltac:(lia)) as Hh.
    assert (H3 : 3 * f n n <= f (S c') (2 * n)).
    { pose proof (f_level_mono (S c' - S n) (S n) (2 * n) ltac:(lia)) as L1.
      replace (S c' - S n + S n) with (S c') in L1 by lia.
      rewrite f_S in L1.
      pose proof (iter_mono_n (f n) (f_id n) 3 (2 * n) (2 * n) ltac:(lia)) as L2.
      pose proof (iter_mono_x (f n) (f_mono n) 3 n (2 * n) ltac:(lia)) as L3.
      cbn [iter] in L2, L3.
      pose proof (f_dbl n (f n n) ltac:(lia)).
      pose proof (f_dbl n (f n (f n n)) ltac:(lia)). lia. }
    rewrite f_omega_eq. lia.
Qed.

Lemma ho_ge : forall m y, y + 6 <= ho m y.
Proof.
  induction m as [| m IHm]; intros y.
  - rewrite ho_0. pose proof (G_ge y). lia.
  - rewrite ho_S. pose proof (iter_linK (ho m) 6 IHm (y + 1) 5). lia.
Qed.

Lemma ho_dom : forall m n z, 6 * n <= z -> 6 * f_wk m n <= ho m z.
Proof.
  apply (transfer 6 5 f_wk ho ltac:(lia) f_wk_S).
  - intros m z. rewrite ho_S. replace (z + 1) with (S z) by lia. lia.
  - exact ho_ge.
  - exact G_dom.
Qed.

Lemma hoc_ge : forall n m a, a + 6 * n <= hoc m n a.
Proof.
  induction n as [| n IHn]; intros m a.
  - rewrite hoc_0. lia.
  - rewrite hoc_S. pose proof (IHn (S m) (ho m a)). pose proof (ho_ge m a). lia.
Qed.

Lemma hoc_last : forall n m a, hoc m (S n) a = ho (m + n) (hoc m n a).
Proof.
  induction n as [| n IHn]; intros m a.
  - rewrite hoc_S, !hoc_0, Nat.add_0_r. reflexivity.
  - rewrite hoc_S, IHn, hoc_S. f_equal. lia.
Qed.

(** ** The inner value G 44 = hc 0 15 3 + 32 exceeds 8 * f_15(2) *)
Lemma hc_tower_base : 2 * f 3 2 + 4 <= hc 1 2 7.
Proof.
  rewrite hc_last, hc_S, hc_0, h1_eq.
  replace (1 + 1) with 2 by reflexivity. replace (4 * 7 + 10) with 38 by reflexivity.
  pose proof (h_dom 2 9 38 ltac:(lia)) as Hh. rewrite f2_eq in Hh.
  assert (Hf3 : f 3 2 = 2048).
  { rewrite f_S_2, !f2_eq. reflexivity. }
  assert (H9 : 9 * 2 ^ 9 = 4608) by reflexivity.
  rewrite Hf3. rewrite H9 in Hh. lia.
Qed.

Lemma hc_tower_step : forall n, 2 <= n -> 2 * f (S n) 2 + 4 <= hc 1 n 7 ->
  8 * f (S (S n)) 2 <= hc 1 (S n) 7.
Proof.
  intros n Hn IHn. rewrite hc_last. replace (1 + n) with (S n) by lia.
  pose proof (h_dom (S n) (f (S n) 2 + 2) (hc 1 n 7) ltac:(lia)) as Hh.
  pose proof (f_plus2 (S n) (f (S n) 2) ltac:(lia)) as Hp.
  assert (E : f (S n) (f (S n) 2) = f (S (S n)) 2) by reflexivity.
  lia.
Qed.

Lemma hc_tower : forall n, 2 <= n -> 2 * f (S n) 2 + 4 <= hc 1 n 7.
Proof.
  intros n Hn. induction Hn as [| m Hm IH].
  - exact hc_tower_base.
  - pose proof (hc_tower_step m Hm IH). pose proof (f_gt (S (S m)) 2 ltac:(lia)). lia.
Qed.

Lemma f_w2_eq : forall n, f_w2 n = f_wk n n.
Proof. reflexivity. Qed.

Strategy opaque [f f_omega f_wk f_w2].

Lemma G44_bound : 8 * f 15 2 <= G 44.
Proof.
  change (G 44) with (G (3 * 14 + 2)). rewrite (G_k 14).
  rewrite hc_S, h_0. change (3 + 4) with 7.
  pose proof (hc_tower_step 13 ltac:(lia) (hc_tower 13 ltac:(lia))). lia.
Qed.

(** ** Final bound: sigma > f_(omega*2)(f_15(2)) > f_(omega*2)(f_13(2)) *)
Lemma bound_gen : forall Y0 a1 k1 a2 j,
  2 <= Y0 -> 8 * Y0 <= a1 -> a1 + 4 = 3 * (k1 + 3) ->
  a2 = hoc 1 k1 a1 -> a2 + 2 * S k1 + 2 = 3 * S j + 1 ->
  f_w2 Y0 < 2 * j + 4.
Proof.
  intros Y0 a1 k1 a2 j HY0 HG Hk1 Ha2 Hj.
  assert (HkY : Y0 <= k1) by lia.
  destruct k1 as [| k1']; [lia |].
  rewrite hoc_last in Ha2. replace (1 + k1') with (S k1') in Ha2 by lia.
  pose proof (hoc_ge k1' 1 a1) as Hb1.
  pose proof (ho_dom (S k1') (S k1') (hoc 1 k1' a1) ltac:(lia)) as Hdom.
  pose proof (f_w2_mono Y0 (S k1') HkY) as Hmono.
  pose proof (f_w2_eq (S k1')) as Hw2.
  lia.
Qed.

Theorem score_exact : exists k1 q1 a2 j c,
  G 44 + 4 = 3 * (k1 + 3) /\ k1 = 3 * q1 + 2 /\
  a2 = hoc 1 k1 (G 44) /\ a2 + 2 * S k1 + 2 = 3 * S j + 1 /\
  c0 -->* c /\ halted tm c /\ ones c (2 * j + 4).
Proof.
  destruct run as (k1 & q1 & a2 & j & Hk1 & Hq1 & Ha2 & Hj & Hrun).
  exists k1, q1, a2, j, (Hc j).
  split; [exact Hk1 |]. split; [exact Hq1 |]. split; [exact Ha2 |]. split; [exact Hj |].
  split; [exact Hrun |]. split; [apply Hc_halted | apply ones_Hc].
Qed.

Lemma f15_ge2 : 2 <= f 15 2.
Proof. pose proof (f_gt 15 2 ltac:(lia)). lia. Qed.

Lemma fw2_13_15 : f_w2 (f 13 2) <= f_w2 (f 15 2).
Proof. apply f_w2_mono, (f_level_mono 2 13 2). lia. Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_w2 (f 13 2) < N /\ f_w2 (f 15 2) < N.
Proof.
  destruct run as (k1 & q1 & a2 & j & Hk1 & Hq1 & Ha2 & Hj & Hrun).
  exists (Hc j), (2 * j + 4).
  split; [exact Hrun |]. split; [apply Hc_halted |]. split; [apply ones_Hc |].
  pose proof (bound_gen (f 15 2) (G 44) k1 a2 j f15_ge2 G44_bound Hk1 Ha2 Hj) as HB15.
  pose proof fw2_13_15 as Hw13_15.
  clear Hk1 Hq1 Ha2 Hj Hrun.
  split; lia.
Qed.

Print Assumptions halt.
Print Assumptions score_exact.
Print Assumptions sigma_lower_bound.
