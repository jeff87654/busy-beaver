(* machine: 1LG1RH_0LI1RC_0LD1LQ_0RE1LD_0RP1RL_1RB1RF_1LQ1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LQ0RN_0LQ1RO_1RZ1RM_0LQ0RA_1LH0LG *)
(** * Standalone 17-State BB(17) Champion J17_w2_champ: halts with sigma > f_(omega*2)(f_omega^3(f_14(2))) > f_(omega*2)(f_15(2))

    Core-named (A-start):
      1LG1RH_0LI1RC_0LD1LQ_0RE1LD_0RP1RL_1RB1RF_1LQ1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LQ0RN_0LQ1RO_1RZ1RM_0LQ0RA_1LH0LG
    Unmirrored Tree Normal Form (TNF):
      1LB1RD_1LC1LB_1LD0LB_1RE0RM_1RF1RE_0LG1RP_1LH1LG_0LI1LG_1RJ1RK_0RJ0RE_0RL1RJ_0LC0RA_1RZ1RN_0LC0RO_0LC1RM_0LQ1LC_0RK1LQ
    1RB L/R-Mirrored Canonical TNF:
      1RB1LD_1RC1RB_1RD0RB_1LE0LM_1LF1LE_0RG1LP_1RH1RG_0RI1RG_1LJ1LK_0LJ0LE_0LL1LJ_0RC0LA_1RZ1LN_0RC0LO_0RC1LM_0RQ1RC_0LK1RQ

    Anatomy:
      - 15-state inner/outer sweep + residue-1 expansion engine (B..O, QQ) completely disjoint from the 2-state refill module (A, P):
        CI, R0, R1, and OEX never touch states A or P.
      - Blank-tape boot (135 steps, visiting all 17/17 states):
        c0 -->* CO 5 [] -->* EX 7 -->* CO 4 [1; 2] -->* CO 4 [6; 1].
      - Outer Run 1: CO 4 [6; 1] -->* CO (iter 5 G 4) [1; 1] -->* EX B1 with B1 = iter 5 G 4 + 6.
      - Exact Mod-486 -> Mod-9 periodicity (verified constructively via linear table scan):
        iter 5 G 4 == 4 (mod 9), hence B1 = 9 * S q1 + 1 = 3 * S (S (3 * q1 + 1)) + 1.
      - Refill 1 (RF_1): EX (3 * S (S k1) + 1) -->* CO 4 (1 :: repeat 2 (S k1)), with 1 + S k1 = 3 * S q1.
      - Outer Run 2: CO 4 (1 :: repeat 2 (S k1)) -->* CO a2 (repeat 1 (3 * S q1)) -->* EX B2,
        where a2 = hoc 1 (S k1) 4 == 1 (mod 3), so B2 = a2 + 2 * (3 * S q1) + 2 == 0 (mod 3),
        entering RF_halt: EX (3 * S (S j)) -->* Hc j (DETERMINISTIC HALT).
      - FGH Lower Bound:
        N = 2 * j + 4 > f_(omega*2)(iter 3 f_omega (f 14 2)) > f_(omega*2)(f 15 2),
        establishing the first standalone 17-state Busy Beaver champion beating BB(16) (J16_w2). *)

From BB8 Require Import Individual172.
From Coq Require Import Lia PeanoNat List Bool.
Import ListNotations.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0  => Some (1, TM.L, G)   | A, 1  => Some (1, TM.R, H)
  | B, 0  => Some (0, TM.L, I)   | B, 1  => Some (1, TM.R, C)
  | C, 0  => Some (0, TM.L, D)   | C, 1  => Some (1, TM.L, QQ)
  | D, 0  => Some (0, TM.R, E)   | D, 1  => Some (1, TM.L, D)
  | E, 0  => Some (0, TM.R, P)   | E, 1  => Some (1, TM.R, L)
  | F, 0  => Some (1, TM.R, B)   | F, 1  => Some (1, TM.R, F)
  | G, 0  => Some (1, TM.L, QQ)  | G, 1  => Some (1, TM.L, G)
  | H, 0  => Some (1, TM.R, F)   | H, 1  => Some (0, TM.R, O)
  | I, 0  => Some (1, TM.L, J)   | I, 1  => Some (1, TM.L, I)
  | J, 0  => Some (0, TM.L, K)   | J, 1  => Some (1, TM.L, I)
  | K, 0  => Some (1, TM.R, L)   | K, 1  => Some (1, TM.R, E)
  | L, 0  => Some (0, TM.R, L)   | L, 1  => Some (0, TM.R, F)
  | M, 0  => Some (0, TM.L, QQ)  | M, 1  => Some (0, TM.R, N)
  | N, 0  => Some (0, TM.L, QQ)  | N, 1  => Some (1, TM.R, O)
  | O, 0  => None                | O, 1  => Some (1, TM.R, M)
  | P, 0  => Some (0, TM.L, QQ)  | P, 1  => Some (0, TM.R, A)
  | QQ, 0 => Some (1, TM.L, H)   | QQ, 1 => Some (0, TM.L, G)
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
Lemma walkG : forall n l r, [1]^^n *> l <{{G}} r -->* l <{{G}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkD : forall n l r, [1]^^n *> l <{{D}} r -->* l <{{D}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkI : forall n l r, [1]^^n *> l <{{I}} r -->* l <{{I}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma zigGQ : forall n l r, [0;1]^^n *> l <{{G}} r -->* l <{{G}} [0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma zigIJ : forall n l r, [0;1]^^n *> l <{{I}} r -->* l <{{I}} [1;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triOMN : forall n l r, l {{O}}> [1;1;1]^^n *> r -->* [1;0;1]^^n *> l {{O}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triGGQ : forall n l r, [1;0;1]^^n *> l <{{G}} r -->* l <{{G}} [0;1;1]^^n *> r.
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

Definition SW (l : side) (j y : nat) (ds : list nat) (R : side) : Q * tape :=
  ([1]^^y *> [0;1]^^j *> 0 >> l) {{F}}> (0 >> rl ds R).

Definition CI (x : nat) (ds : list nat) (R : side) : Q * tape :=
  const 0 <{{H}} ([1]^^x *> 0 >> rl ds R).

Definition CO (a : nat) (Rr : side) : Q * tape :=
  (0 >> 0 >> 1 >> const 0) {{F}}> ([1]^^a *> 0 >> Rr).

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
  SW l j y (S (S e) :: ds) R -->* l <{{QQ}} (1 >> [0;1]^^j *> [1]^^(S y) *> 0 >> rl (S e :: ds) R).
Proof.
  intros. unfold SW. cbn [rl lpow app Str_app].
  execute.
  follow walkG.
  follow zigGQ.
  execute.
  finish_norm.
Qed.

Lemma pairs_ones : forall j y (X : side), [1;1]^^j *> [1]^^y *> 1 >> X = [1]^^(y + 2 * j + 1) *> X.
Proof.
  intros. rewrite pow11, ones_add, one_shift.
  replace (y + 2 * j + 1) with (S (2 * j + y)) by lia. reflexivity.
Qed.

Lemma SW_exit_in : forall j y R, SW (const 0) j y [] (0 >> R) -->* CO (y + 2 * j + 1) R.
Proof.
  intros. unfold SW. cbn [rl].
  execute.
  follow walkI.
  follow zigIJ.
  execute.
  rewrite pairs_ones. unfold CO. finish.
Qed.

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

Lemma SW_Q_in : forall j y e ds R,
  SW (const 0) j y (S (S e) :: ds) R -->*
  const 0 <{{H}} (1 >> 1 >> [0;1]^^j *> [1]^^(S y) *> 0 >> rl (S e :: ds) R).
Proof.
  intros. follow SW_E. execute.
Qed.

Lemma CI_E0 : forall x e ds R, CI x (S (S e) :: ds) R -->* CI (x + 4) (S e :: ds) R.
Proof.
  intros. follow CI_SW. follow SW_Q_in. unfold CI.
  replace (x + 4) with (S (S (S (S x)))) by lia. finish.
Qed.

Lemma CI_E1 : forall x j e ds R,
  CI x (repeat 1%nat (S j) ++ S (S e) :: ds) R -->* CI 2 (repeat 1%nat j ++ (x + 3) :: S e :: ds) R.
Proof.
  intros. follow CI_SW. follow SW_pass_iter. follow SW_Q_in. unfold CI.
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

(** ** Disjoint 2-State Refill & Halting from EX (States P, A) *)
Definition Hc (j : nat) : Q * tape :=
  ([1;0;1]^^j *> 1 >> 0 >> 1 >> 0 >> 1 >> 0 >> 0 >> 1 >> const 0) {{O}}> (const 0).

Lemma Hc_halted : forall j, halted tm (Hc j).
Proof. intros. reflexivity. Qed.

Lemma RF_halt : forall j, EX (3 * S (S j)) -->* Hc j.
Proof.
  intros j. unfold EX, Hc.
  replace (3 * S (S j)) with (6 + 3 * j) by lia.
  rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  execute. follow triOMN. finish.
Qed.

Lemma shift_101 : forall n (X : side), 1 >> [1;0;1]^^n *> X = [1;1;0]^^n *> 1 >> X.
Proof.
  intros. symmetry. apply (align_lpow 1 [1;0] X n).
Qed.

Lemma RF_1 : forall k, EX (3 * S (S k) + 1) -->* CO 4 (rl (1%nat :: repeat 2%nat (S k)) (const 0)).
Proof.
  intros k. unfold EX, CO. cbn [repeat rl]. rewrite rl_rep2. cbn [lpow app Str_app].
  replace (3 * S (S k) + 1) with (6 + (3 * k + 1)) by lia.
  do 2 rewrite <- ones_add. rewrite <- pow111. cbn [lpow app Str_app].
  execute.
  follow triOMN.
  execute.
  follow triGGQ.
  rewrite align_lpow_const. simpl app.
  execute.
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
  CO 4 (1 >> [0;1]^^p *> [1]^^(S a) *> 0 >> rl (S e :: os) (const 0)).
Proof.
  intros. follow CO_SW. follow SW_pass_iter. follow SW_E.
  replace (0 + S p) with (S p) by lia. cbn [lpow app Str_app].
  execute; unfold CO; finish_norm.
Qed.

Lemma R1 : forall a p e os,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) (const 0)) -->*
  CO 4 (rl (repeat 1%nat p ++ (a + 2) :: S e :: os) (const 0)).
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

Fixpoint h (m x : nat) : nat :=
  match m with
  | 0 => x + 4
  | S m' => iter (x + 2) (h m') 2
  end.

Fixpoint hc (m n x : nat) : nat :=
  match n with
  | 0 => x
  | S n' => hc (S m) n' (h m x)
  end.

Definition Gk (k : nat) : nat := hc 0 (S k) 2 + 2 * S k + 2.
Definition G (a : nat) : nat := Gk (a / 3).

Fixpoint ho (m a : nat) : nat :=
  match m with
  | 0 => G a
  | S m' => iter (a + 1) (ho m') 4
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
  (0 >> 1 >> const 0) <{{QQ}} (1 >> [1]^^(S (3 * k + 1)) *> 0 >> R) -->*
  CI 2%nat (repeat 2%nat (S k)) (0 >> R).
Proof.
  intros k R. unfold CI. cbn [repeat rl]. rewrite rl_rep2. cbn [lpow app Str_app].
  rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  execute.
  follow triOMN.
  execute.
  follow triGGQ.
  rewrite (align_lpow 0 [1;1]). simpl app.
  execute.
Qed.

Lemma R0_k : forall k e os,
  CO (3 * k + 1)%nat (rl (S (S e) :: os) (const 0)) -->* CO (Gk k) (rl (S e :: os) (const 0)).
Proof.
  intros k e os.
  follow CO_SW. follow SW_E. cbn [lpow app Str_app].
  follow R0_CI.
  follow (Chain_in (S k) 0%nat 2%nat (0 >> rl (S e :: os) (const 0))).
  follow CI_exit.
  unfold Gk. finish.
Qed.

Lemma R0 : forall a e os, (exists k, a = (3 * k + 1)%nat) ->
  CO a (rl (S (S e) :: os) (const 0)) -->* CO (G a) (rl (S e :: os) (const 0)).
Proof.
  intros a e os [k Hk]. subst a.
  unfold G. replace ((3 * k + 1) / 3)%nat with k by (apply Nat.div_unique with 1%nat; lia).
  apply R0_k.
Qed.

Local Open Scope nat_scope.

(** ** Mod-3 invariant *)
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

Lemma Gk_mod3 : forall k, exists q, Gk k = 3 * q + 1.
Proof.
  intros k. unfold Gk. destruct (hc_mod (S k) 0 2) as [q Hq].
  exists (q + S k + 1). lia.
Qed.

Lemma G_mod3 : forall a, exists q, G a = 3 * q + 1.
Proof. intros a. apply Gk_mod3. Qed.

Lemma ho_mod3 : forall m a, exists q, ho m a = 3 * q + 1.
Proof.
  induction m as [| m IHm]; intros a.
  - apply G_mod3.
  - simpl. replace (a + 1) with (S a) by lia. simpl. apply IHm.
Qed.

Lemma hoc_mod3 : forall n m a, (exists q, a = 3 * q + 1) -> exists q, hoc m n a = 3 * q + 1.
Proof.
  induction n as [| n IHn]; intros m a Ha; simpl.
  - exact Ha.
  - apply IHn, ho_mod3.
Qed.

Close Scope nat_scope.

(** ** Outer levels *)
Lemma LV_out : forall m e a os, (exists k, a = (3 * k + 1)%nat) ->
  CO a (rl (repeat 1%nat m ++ S e :: os) (const 0)) -->* CO (iter e (ho m) a) (rl (repeat 1%nat (S m) ++ os) (const 0)).
Proof.
  induction m as [| m IHm]; intros e; induction e as [| e IHe]; intros a os Ha.
  - simpl. finish.
  - simpl app. follow (R0 a e os Ha).
    follow (IHe (G a) os (G_mod3 a)). rewrite iter_S'. finish.
  - rewrite rep_snoc. finish.
  - follow R1.
    assert (H4 : exists k, 4%nat = (3 * k + 1)%nat) by (exists 1%nat; lia).
    follow (IHm (a + 1)%nat 4%nat (S e :: os) H4).
    follow (IHe (ho (S m) a) os (ho_mod3 (S m) a)).
    rewrite iter_S'. finish.
Qed.

Lemma Chain_out : forall n m a os, (exists k, a = (3 * k + 1)%nat) ->
  CO a (rl (repeat 1%nat m ++ repeat 2%nat n ++ os) (const 0)) -->* CO (hoc m n a) (rl (repeat 1%nat (m + n) ++ os) (const 0)).
Proof.
  induction n as [| n IHn]; intros m a os Ha.
  - rewrite Nat.add_0_r. finish.
  - simpl repeat. cbn [app]. follow (LV_out m 1%nat a (repeat 2%nat n ++ os) Ha).
    follow (IHn (S m) (ho m a) os (ho_mod3 m a)).
    replace (S m + n)%nat with (m + S n)%nat by lia. finish.
Qed.

Local Open Scope nat_scope.

(** ** Constructive Mod-486 -> Mod-9 Periodicity of the Inner Hierarchy *)
Lemma h_0 : forall x, h 0 x = x + 4.  Proof. reflexivity. Qed.
Lemma h_S : forall m x, h (S m) x = iter (x + 2) (h m) 2.  Proof. reflexivity. Qed.
Lemma hc_0 : forall m x, hc m 0 x = x.  Proof. reflexivity. Qed.
Lemma hc_S : forall m n x, hc m (S n) x = hc (S m) n (h m x).  Proof. reflexivity. Qed.
Lemma G_eq : forall a, G a = hc 0 (S (a / 3)) 2 + 2 * S (a / 3) + 2.  Proof. reflexivity. Qed.
Lemma ho_0 : forall a, ho 0 a = G a.  Proof. reflexivity. Qed.
Lemma ho_S : forall m a, ho (S m) a = iter (a + 1) (ho m) 4.  Proof. reflexivity. Qed.
Lemma hoc_0 : forall m a, hoc m 0 a = a.  Proof. reflexivity. Qed.
Lemma hoc_S : forall m n a, hoc m (S n) a = hoc (S m) n (ho m a).  Proof. reflexivity. Qed.

Ltac Zify.zify_pre_hook ::= idtac.
Strategy opaque [h hc Gk G ho hoc].

Lemma G_k : forall k, G (3 * k + 1) = hc 0 (S k) 2 + 2 * S k + 2.
Proof.
  intros k. rewrite G_eq.
  replace ((3 * k + 1) / 3) with k by (apply Nat.div_unique with 1; lia).
  reflexivity.
Qed.

Lemma iter_h0 : forall n y, iter n (h 0) y = y + 4 * n.
Proof. induction n; intros; cbn [iter]. - lia. - rewrite IHn, h_0. lia. Qed.

Lemma h1_eq : forall x, h 1 x = 4 * x + 10.
Proof. intros. rewrite h_S, iter_h0. lia. Qed.

Lemma h_ge2 : forall m x, 2 <= h m x.
Proof.
  induction m as [| m IHm]; intros x.
  - rewrite h_0. lia.
  - rewrite h_S. replace (x + 2) with (S (x + 1)) by lia. simpl iter. apply IHm.
Qed.

(** Shifted residue mod 486 in [2 .. 487] *)
Definition sh486 (z : nat) : nat := 2 + (z - 2) mod 486.

Lemma sh486_eq : forall z, 2 <= z -> exists u, z = 486 * u + sh486 z.
Proof.
  intros z Hz. unfold sh486.
  exists ((z - 2) / 486).
  pose proof (Nat.div_mod (z - 2) 486 ltac:(lia)) as Hdm.
  lia.
Qed.

Lemma sh486_shift : forall q y, 2 <= y -> sh486 (486 * q + y) = sh486 y.
Proof.
  intros q y Hy. unfold sh486.
  replace (486 * q + y - 2) with ((y - 2) + q * 486) by lia.
  rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma sh486_bound : forall z, 2 <= sh486 z /\ sh486 z < 488.
Proof.
  intros z. unfold sh486.
  pose proof (Nat.mod_upper_bound (z - 2) 486 ltac:(lia)). lia.
Qed.

Lemma sh486_small : forall z, 2 <= z -> z < 488 -> sh486 z = z.
Proof.
  intros z H1 H2. unfold sh486.
  rewrite Nat.mod_small by lia. lia.
Qed.

Fixpoint scan_iter (k : nat) (g : nat -> nat) (y : nat) : list nat :=
  match k with
  | 0 => []
  | S k' => y :: scan_iter k' g (g y)
  end.

Lemma nth_scan_iter : forall k i g y d, i < k -> nth i (scan_iter k g y) d = iter i g y.
Proof.
  induction k as [| k IH]; intros [| i] g y d Hi; try lia; cbn [scan_iter nth].
  - reflexivity.
  - rewrite IH by lia. rewrite iter_S'. reflexivity.
Qed.

Definition lkp (t : list nat) (z : nat) : nat := nth (z - 2) t 2.
Definition mk_tab (g : nat -> nat) : list nat := scan_iter 486 g (iter 4 g 2).

Definition t0 : list nat := map (fun r => sh486 (r + 6)) (seq 0 486).
Definition t1 : list nat := mk_tab (lkp t0).
Definition t2 : list nat := mk_tab (lkp t1).
Definition t3 : list nat := mk_tab (lkp t2).
Definition t4 : list nat := mk_tab (lkp t3).
Definition t5 : list nat := mk_tab (lkp t4).

Lemma h0_rep486 : forall x, 2 <= x -> sh486 (h 0 x) = lkp t0 (sh486 x).
Proof.
  intros x Hx. rewrite h_0.
  destruct (sh486_eq x Hx) as [u Hu].
  pose proof (sh486_bound x) as [Hb1 Hb2].
  replace (x + 4) with (486 * u + ((sh486 x - 2) + 6)) by lia.
  rewrite sh486_shift by lia.
  unfold lkp, t0.
  symmetry.
  transitivity (nth (sh486 x - 2) (map (fun r => sh486 (r + 6)) (seq 0 486)) (sh486 (482 + 6))); [reflexivity |].
  rewrite (map_nth (fun r => sh486 (r + 6))), seq_nth by lia.
  reflexivity.
Qed.

Lemma iter_period486 : forall g,
  iter 486 g (iter 4 g 2) = iter 4 g 2 ->
  forall q n, 4 <= n -> iter (486 * q + n) g 2 = iter n g 2.
Proof.
  intros g Hper. induction q as [| q IHq]; intros n Hn.
  - simpl. reflexivity.
  - replace (486 * S q + n) with (486 * q + (486 + n)) by lia.
    rewrite IHq by lia.
    replace (486 + n) with ((n - 4) + (486 + 4)) by lia.
    rewrite !iter_add, Hper, <- iter_add.
    replace (n - 4 + 4) with n by lia. reflexivity.
Qed.

Lemma rep486_step : forall m tg,
  (forall x, 2 <= x -> sh486 (h m x) = lkp tg (sh486 x)) ->
  iter 486 (lkp tg) (iter 4 (lkp tg) 2) = iter 4 (lkp tg) 2 ->
  forall x, 2 <= x -> sh486 (h (S m) x) = lkp (mk_tab (lkp tg)) (sh486 x).
Proof.
  intros m tg Hrep Hper x Hx. rewrite h_S.
  assert (Hit : forall k, sh486 (iter k (h m) 2) = iter k (lkp tg) 2).
  { induction k as [| k IHk]; simpl.
    - apply sh486_small; lia.
    - assert (Hge : 2 <= iter k (h m) 2).
      { destruct k; simpl; [lia | apply h_ge2]. }
      rewrite Hrep by exact Hge. rewrite IHk. reflexivity. }
  rewrite Hit.
  destruct (sh486_eq x Hx) as [u Hu].
  pose proof (sh486_bound x) as [Hb1 Hb2].
  replace (x + 2) with (486 * u + ((sh486 x - 2) + 4)) by lia.
  rewrite (iter_period486 (lkp tg) Hper u ((sh486 x - 2) + 4)) by lia.
  unfold lkp, mk_tab.
  rewrite nth_scan_iter by lia.
  rewrite <- iter_add. reflexivity.
Qed.

Lemma per_t0 : iter 486 (lkp t0) (iter 4 (lkp t0) 2) = iter 4 (lkp t0) 2.
Proof. vm_compute. reflexivity. Qed.
Lemma per_t1 : iter 486 (lkp t1) (iter 4 (lkp t1) 2) = iter 4 (lkp t1) 2.
Proof. vm_compute. reflexivity. Qed.
Lemma per_t2 : iter 486 (lkp t2) (iter 4 (lkp t2) 2) = iter 4 (lkp t2) 2.
Proof. vm_compute. reflexivity. Qed.
Lemma per_t3 : iter 486 (lkp t3) (iter 4 (lkp t3) 2) = iter 4 (lkp t3) 2.
Proof. vm_compute. reflexivity. Qed.
Lemma per_t4 : iter 486 (lkp t4) (iter 4 (lkp t4) 2) = iter 4 (lkp t4) 2.
Proof. vm_compute. reflexivity. Qed.
Lemma per_t5 : iter 486 (lkp t5) (iter 4 (lkp t5) 2) = iter 4 (lkp t5) 2.
Proof. vm_compute. reflexivity. Qed.
Lemma stab_t5 : mk_tab (lkp t5) = t5.
Proof. vm_compute. reflexivity. Qed.

Lemma h1_rep486 : forall x, 2 <= x -> sh486 (h 1 x) = lkp t1 (sh486 x).
Proof. exact (rep486_step 0 t0 h0_rep486 per_t0). Qed.
Lemma h2_rep486 : forall x, 2 <= x -> sh486 (h 2 x) = lkp t2 (sh486 x).
Proof. exact (rep486_step 1 t1 h1_rep486 per_t1). Qed.
Lemma h3_rep486 : forall x, 2 <= x -> sh486 (h 3 x) = lkp t3 (sh486 x).
Proof. exact (rep486_step 2 t2 h2_rep486 per_t2). Qed.
Lemma h4_rep486 : forall x, 2 <= x -> sh486 (h 4 x) = lkp t4 (sh486 x).
Proof. exact (rep486_step 3 t3 h3_rep486 per_t3). Qed.
Lemma h5_rep486 : forall x, 2 <= x -> sh486 (h 5 x) = lkp t5 (sh486 x).
Proof. exact (rep486_step 4 t4 h4_rep486 per_t4). Qed.

Lemma h5d_rep486 : forall d x, 2 <= x -> sh486 (h (5 + d) x) = lkp t5 (sh486 x).
Proof.
  induction d as [| d IH]; intros x Hx.
  - replace (5 + 0) with 5 by lia. apply h5_rep486; exact Hx.
  - replace (5 + S d) with (S (5 + d)) by lia.
    pose proof (rep486_step (5 + d) t5 IH per_t5 x Hx) as Hs.
    rewrite stab_t5 in Hs. exact Hs.
Qed.

Lemma hc_ge2 : forall n m x, 2 <= x -> 2 <= hc m n x.
Proof.
  induction n as [| n IH]; intros m x Hx.
  - rewrite hc_0. exact Hx.
  - rewrite hc_S. apply IH, h_ge2.
Qed.

Lemma hc_split : forall m a b x, hc m (a + b) x = hc (m + a) b (hc m a x).
Proof.
  intros m a. generalize dependent m.
  induction a as [| a IHa]; intros m b x; cbn [Nat.add].
  - rewrite hc_0. replace (m + 0) with m by lia. reflexivity.
  - rewrite !hc_S, IHa. replace (S m + a) with (m + S a) by lia. reflexivity.
Qed.

Lemma hc6_sh486 : sh486 (hc 0 6 2) = 182.
Proof.
  do 6 rewrite hc_S. rewrite hc_0.
  rewrite h5_rep486 by apply h_ge2.
  rewrite h4_rep486 by apply h_ge2.
  rewrite h3_rep486 by apply h_ge2.
  rewrite h2_rep486 by apply h_ge2.
  rewrite h1_rep486 by apply h_ge2.
  rewrite h0_rep486 by lia.
  replace (sh486 2) with 2 by (symmetry; apply sh486_small; lia).
  vm_compute. reflexivity.
Qed.

Lemma t5_cyc3 : lkp t5 182 = 150 /\ lkp t5 150 = 4 /\ lkp t5 4 = 182.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma hc_t5_step3 : forall d x, 2 <= x -> sh486 x = 182 -> sh486 (hc (5 + d) 3 x) = 182.
Proof.
  intros d x Hx Hsh. destruct t5_cyc3 as (C1 & C2 & C3).
  do 3 rewrite hc_S. rewrite hc_0.
  replace (S (S (5 + d))) with (5 + S (S d)) by lia.
  replace (S (5 + d)) with (5 + S d) by lia.
  rewrite (h5d_rep486 (S (S d))) by apply h_ge2.
  rewrite (h5d_rep486 (S d)) by apply h_ge2.
  rewrite (h5d_rep486 d) by exact Hx.
  rewrite Hsh, C1, C2, C3. reflexivity.
Qed.

Lemma hc_period3_486 : forall q,
  sh486 (hc 0 (6 + 3 * q) 2) = 182 /\
  sh486 (hc 0 (6 + 3 * q + 1) 2) = 150 /\
  sh486 (hc 0 (6 + 3 * q + 2) 2) = 4.
Proof.
  induction q as [| q (IH0 & _ & _)].
  - destruct t5_cyc3 as (C1 & C2 & _).
    replace (6 + 3 * 0) with 6 by lia.
    split; [exact hc6_sh486 |].
    split.
    + rewrite (hc_split 0 6 1 2), hc_S, hc_0. cbn [Nat.add].
      change (h 6) with (h (5 + 1)). rewrite (h5d_rep486 1) by (apply hc_ge2; lia).
      rewrite hc6_sh486, C1. reflexivity.
    + rewrite (hc_split 0 6 2 2). do 2 rewrite hc_S. rewrite hc_0. cbn [Nat.add].
      change (h 7) with (h (5 + 2)). change (h 6) with (h (5 + 1)).
      rewrite (h5d_rep486 2) by apply h_ge2.
      rewrite (h5d_rep486 1) by (apply hc_ge2; lia).
      rewrite hc6_sh486, C1, C2. reflexivity.
  - destruct t5_cyc3 as (C1 & C2 & _).
    assert (Hbase : sh486 (hc 0 (6 + 3 * S q) 2) = 182).
    { replace (6 + 3 * S q) with ((6 + 3 * q) + 3) by lia.
      rewrite (hc_split 0 (6 + 3 * q) 3 2).
      replace (0 + (6 + 3 * q)) with (5 + (1 + 3 * q)) by lia.
      apply hc_t5_step3; [apply hc_ge2; lia | exact IH0]. }
    split; [exact Hbase |].
    split.
    + rewrite (hc_split 0 (6 + 3 * S q) 1 2), hc_S, hc_0.
      replace (0 + (6 + 3 * S q)) with (5 + (1 + 3 * S q)) by lia.
      rewrite (h5d_rep486 (1 + 3 * S q)) by (apply hc_ge2; lia).
      rewrite Hbase, C1. reflexivity.
    + rewrite (hc_split 0 (6 + 3 * S q) 2 2). do 2 rewrite hc_S. rewrite hc_0.
      replace (S (0 + (6 + 3 * S q))) with (5 + S (1 + 3 * S q)) by lia.
      replace (0 + (6 + 3 * S q)) with (5 + (1 + 3 * S q)) by lia.
      rewrite (h5d_rep486 (S (1 + 3 * S q))) by apply h_ge2.
      rewrite (h5d_rep486 (1 + 3 * S q)) by (apply hc_ge2; lia).
      rewrite Hbase, C1, C2. reflexivity.
Qed.

Lemma G4_eq : G 4 = 40.
Proof.
  change (G 4) with (G (3 * 1 + 1)). rewrite (G_k 1).
  do 2 rewrite hc_S. rewrite hc_0, h_0, h1_eq. lia.
Qed.

Lemma G5_4_mod9 : exists q1, iter 5 G 4 + 6 = 9 * S q1 + 1.
Proof.
  cbn [iter]. rewrite G4_eq.
  (* Step 2: G 40 == 34 (mod 243) *)
  assert (HG2 : exists q2, G 40 = 243 * q2 + 34).
  { change (G 40) with (G (3 * 13 + 1)). rewrite (G_k 13).
    destruct (hc_period3_486 2) as (_ & _ & H14).
    replace (6 + 3 * 2 + 2) with 14 in H14 by lia.
    destruct (sh486_eq (hc 0 14 2) (hc_ge2 14 0 2 ltac:(lia))) as [u1 Hu1].
    rewrite H14 in Hu1. exists (2 * u1). lia. }
  destruct HG2 as [q2 Hq2]. rewrite Hq2.
  (* Step 3: G (243*q2 + 34) == 46 (mod 81) *)
  assert (HG3 : exists q3, G (243 * q2 + 34) = 81 * q3 + 46).
  { replace (243 * q2 + 34) with (3 * (81 * q2 + 11) + 1) by lia.
    rewrite (G_k (81 * q2 + 11)).
    destruct (hc_period3_486 (27 * q2 + 2)) as (H0 & _ & _).
    replace (6 + 3 * (27 * q2 + 2)) with (S (81 * q2 + 11)) in H0 by lia.
    destruct (sh486_eq (hc 0 (S (81 * q2 + 11)) 2) (hc_ge2 _ 0 2 ltac:(lia))) as [u2 Hu2].
    rewrite H0 in Hu2. exists (6 * u2 + 2 * q2 + 2). lia. }
  destruct HG3 as [q3 Hq3]. rewrite Hq3.
  (* Step 4: G (81*q3 + 46) == 22 (mod 27) *)
  assert (HG4 : exists q4, G (81 * q3 + 46) = 27 * q4 + 22).
  { replace (81 * q3 + 46) with (3 * (27 * q3 + 15) + 1) by lia.
    rewrite (G_k (27 * q3 + 15)).
    destruct (hc_period3_486 (9 * q3 + 3)) as (_ & H1 & _).
    replace (6 + 3 * (9 * q3 + 3) + 1) with (S (27 * q3 + 15)) in H1 by lia.
    destruct (sh486_eq (hc 0 (S (27 * q3 + 15)) 2) (hc_ge2 _ 0 2 ltac:(lia))) as [u3 Hu3].
    rewrite H1 in Hu3. exists (18 * u3 + 2 * q3 + 6). lia. }
  destruct HG4 as [q4 Hq4]. rewrite Hq4.
  (* Step 5: G (27*q4 + 22) == 4 (mod 9) *)
  replace (27 * q4 + 22) with (3 * (9 * q4 + 7) + 1) by lia.
  rewrite (G_k (9 * q4 + 7)).
  destruct (hc_period3_486 (3 * q4)) as (_ & _ & H2).
  replace (6 + 3 * (3 * q4) + 2) with (S (9 * q4 + 7)) in H2 by lia.
  destruct (sh486_eq (hc 0 (S (9 * q4 + 7)) 2) (hc_ge2 _ 0 2 ltac:(lia))) as [u4 Hu4].
  rewrite H2 in Hu4.
  exists (54 * u4 + 2 * q4 + 2). lia.
Qed.

(** ** The run from the blank tape *)
Lemma boot1 : c0 -->* CO 5 (rl [] (const S0)).
Proof.
  unfold CO. cbn [rl lpow app Str_app].
  do 19 step. repeat rewrite <- const_unfold. finish.
Qed.

Lemma boot : c0 -->* CO 4 (rl [6%nat; 1%nat] (const S0)).
Proof.
  follow boot1.
  follow (OEX 5 0 7 eq_refl).
  follow (RF_1 0).
  exact (R1 4 0 0 []).
Qed.

Lemma LV_out_eq : forall m e a os b, (exists k, a = 3 * k + 1) -> b = iter e (ho m) a ->
  CO a (rl (repeat 1 m ++ S e :: os) (const S0)) -->* CO b (rl (repeat 1 (S m) ++ os) (const S0)).
Proof. intros. subst b. apply LV_out. assumption. Qed.

Lemma Chain_out_eq : forall n m a os b, (exists k, a = 3 * k + 1) -> b = hoc m n a ->
  CO a (rl (repeat 1 m ++ repeat 2 n ++ os) (const S0)) -->* CO b (rl (repeat 1 (m + n) ++ os) (const S0)).
Proof. intros. subst b. apply Chain_out. assumption. Qed.

Lemma run_gen : forall a1 q1 k1 a2 j,
  a1 = iter 5 (ho 0) 4 ->
  a1 + 6 = 9 * S q1 + 1 ->
  k1 = 3 * q1 + 1 ->
  a2 = hoc 1 (S k1) 4 ->
  a2 + 2 * (3 * S q1) + 2 = 3 * S (S j) ->
  c0 -->* Hc j.
Proof.
  intros a1 q1 k1 a2 j Ha1 Hq1 Hk1 Ha2 Hj.
  assert (H4 : exists k, 4 = 3 * k + 1) by (exists 1; lia).
  follow boot.
  follow (LV_out_eq 0 5 4 [1] a1 H4 Ha1).
  cbn [repeat app].
  follow (OEX a1 2 (3 * S (S k1) + 1) ltac:(lia)).
  follow (RF_1 k1).
  rewrite <- (app_nil_r (repeat 2 (S k1))).
  change (1 :: repeat 2 (S k1) ++ []) with (repeat 1 1 ++ repeat 2 (S k1) ++ []).
  follow (Chain_out_eq (S k1) 1 4 [] a2 H4 Ha2).
  rewrite app_nil_r.
  replace (1 + S k1) with (3 * S q1) by lia.
  follow (OEX a2 (3 * S q1) (3 * S (S j)) (eq_sym Hj)).
  apply RF_halt.
Qed.

Lemma iter_ho0_G : forall n a, iter n (ho 0) a = iter n G a.
Proof.
  induction n as [| n IH]; intros a; cbn [iter].
  - reflexivity.
  - rewrite IH, ho_0. reflexivity.
Qed.

Lemma J_gen : forall q1 k1 a2,
  k1 = 3 * q1 + 1 -> a2 = hoc 1 (S k1) 4 ->
  exists j, a2 + 2 * (3 * S q1) + 2 = 3 * S (S j).
Proof.
  intros q1 k1 a2 Hk1 Ha2.
  assert (H4 : exists k, 4 = 3 * k + 1) by (exists 1; lia).
  destruct (hoc_mod3 (S k1) 1 4 H4) as [qa Hqa].
  exists (qa + 2 * q1 + 1). subst. lia.
Qed.

Lemma run : exists q1 k1 a2 j,
  iter 5 G 4 + 6 = 9 * S q1 + 1 /\
  k1 = 3 * q1 + 1 /\
  a2 = hoc 1 (S k1) 4 /\
  a2 + 2 * (3 * S q1) + 2 = 3 * S (S j) /\
  c0 -->* Hc j.
Proof.
  destruct G5_4_mod9 as [q1 Hq1].
  set (k1 := 3 * q1 + 1).
  set (a2 := hoc 1 (S k1) 4).
  destruct (J_gen q1 k1 a2 eq_refl eq_refl) as [j Hj].
  exists q1, k1, a2, j.
  split; [exact Hq1 |]. split; [reflexivity |]. split; [reflexivity |]. split; [exact Hj |].
  apply (run_gen (iter 5 G 4) q1 k1 a2 j); [symmetry; apply iter_ho0_G | exact Hq1 | reflexivity | reflexivity | exact Hj].
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct run as (q1 & k1 & a2 & j & _ & _ & _ & _ & Hrun).
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

Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl. - reflexivity. - rewrite IHxs. lia. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl. - reflexivity. - rewrite count1_app, IHn. lia. Qed.

Lemma ones_Hc : forall j, ones (Hc j) (2 * j + 4).
Proof.
  intros j. exists O, ([S1; S0; S1]^^j ++ [S1; S0; S1; S0; S1; S0; S0; S1]), (@nil Sym), S0.
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

Fixpoint f_wk (k : nat) : nat -> nat :=
  match k with
  | 0 => f_omega
  | S k' => fun n => iter n (f_wk k') n
  end.

Definition f_w2 (n : nat) : nat := f_wk n n.

Opaque h hc Gk G ho hoc.
Strategy opaque [h hc Gk G ho hoc].

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

Lemma iter_dom : forall K g h0, (forall n z, K * n <= z -> K * g n <= h0 z) ->
  forall m n z, K * n <= z -> K * iter m g n <= iter m h0 z.
Proof. intros K g h0 Hd. induction m; intros n z Hz; simpl; auto. Qed.

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

Lemma f_0 : forall n, f 0 n = S n.  Proof. reflexivity. Qed.
Lemma f_S : forall k n, f (S k) n = iter n (f k) n.  Proof. reflexivity. Qed.

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

Lemma f2_2 : f 2 2 = 8.
Proof. rewrite f2_eq. reflexivity. Qed.

Lemma f2_4 : f 2 4 = 64.
Proof. rewrite f2_eq. reflexivity. Qed.

Lemma f3_2_eq : f 3 2 = f 2 8.
Proof. rewrite (f_S_2 2), f2_2. reflexivity. Qed.

Lemma f14_2_ge : 64 <= f 14 2.
Proof.
  pose proof (f_mono 2 4 8 ltac:(lia)) as H1.
  rewrite f2_4, <- f3_2_eq in H1.
  pose proof (f_level_mono 11 3 2 ltac:(lia)) as H2.
  change (11 + 3) with 14 in H2. lia.
Qed.

Lemma f_omega_eq : forall n, f_omega n = f n n.  Proof. reflexivity. Qed.
Lemma f_omega_0 : f_omega 0 = 1.  Proof. reflexivity. Qed.
Lemma f_omega_1 : f_omega 1 = 2.  Proof. reflexivity. Qed.

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

Lemma f_wk_0 : forall n, f_wk 0 n = f_omega n.  Proof. reflexivity. Qed.
Lemma f_wk_S : forall k n, f_wk (S k) n = iter n (f_wk k) n.  Proof. reflexivity. Qed.

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

Lemma f_w2_eq : forall n, f_w2 n = f_wk n n.  Proof. reflexivity. Qed.

Lemma f_w2_id : forall n, n <= f_w2 n.
Proof. intros n. unfold f_w2. apply f_wk_id. Qed.

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

(** ** Dominance of h, hc, G, ho, hoc *)
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

Opaque f f_omega f_wk f_w2.

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
  pose proof (hc_ge (S (a / 3)) 0 2).
  pose proof (Nat.div_mod a 3 ltac:(lia)).
  pose proof (Nat.mod_upper_bound a 3 ltac:(lia)).
  lia.
Qed.

Lemma G_dom : forall n z, 6 * n <= z -> 6 * f_omega n <= G z.
Proof.
  intros n z Hz. pose proof (G_ge z) as Hg.
  destruct n as [| [| n']].
  - rewrite f_omega_0. lia.
  - rewrite f_omega_1. lia.
  - set (n := S (S n')) in *.
    pose proof (Nat.div_mod z 3 ltac:(lia)) as Hdm.
    pose proof (Nat.mod_upper_bound z 3 ltac:(lia)) as Hmb.
    rewrite G_eq.
    set (c := z / 3) in *.
    assert (Hc : 2 * n <= c) by lia.
    destruct c as [| c'] eqn:Ec; [lia |].
    rewrite (hc_S 0 (S c') 2), (h_0 2), hc_last. change (2 + 4) with 6.
    replace (1 + c') with (S c') by lia.
    pose proof (hc_ge c' 1 6) as HX.
    pose proof (h_dom (S c') (2 * n) (hc 1 c' 6) ltac:(lia)) as Hh.
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
  - rewrite ho_S. pose proof (iter_linK (ho m) 6 IHm (y + 1) 4). lia.
Qed.

Lemma ho_dom : forall m n z, 6 * n <= z -> 6 * f_wk m n <= ho m z.
Proof.
  apply (transfer 6 4 f_wk ho ltac:(lia) f_wk_S).
  - intros m z. rewrite ho_S. replace (z + 1) with (S z) by lia. lia.
  - exact ho_ge.
  - intros n z Hz. rewrite f_wk_0, ho_0. apply G_dom; exact Hz.
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

(** ** Concrete Seed Lower Bound: iter 5 G 4 >= 6 * iter 3 f_omega (f 14 2) *)
Lemma hc_tower_base : 2 * f 3 2 + 4 <= hc 1 2 6.
Proof.
  rewrite (hc_last 1 1 6), (hc_S 1 0 6), (hc_0 2 (h 1 6)), (h1_eq 6).
  change (1 + 1) with 2; change (4 * 6 + 10) with 34.
  pose proof (h_dom 2 17 34 ltac:(lia)) as Hh.
  pose proof (f_plus2 2 8 ltac:(lia)) as Hp.
  change (8 + 2) with 10 in Hp.
  pose proof (f_mono 2 10 17 ltac:(lia)) as Hm.
  pose proof (f_id 3 2).
  rewrite <- f3_2_eq in Hp. lia.
Qed.

Lemma hc_tower_step : forall n, 2 <= n -> 2 * f (S n) 2 + 4 <= hc 1 n 6 ->
  8 * f (S (S n)) 2 <= hc 1 (S n) 6.
Proof.
  intros n Hn IHn. rewrite (hc_last n 1 6). replace (1 + n) with (S n) by lia.
  pose proof (h_dom (S n) (f (S n) 2 + 2) (hc 1 n 6) ltac:(lia)) as Hh.
  pose proof (f_plus2 (S n) (f (S n) 2) ltac:(lia)) as Hp.
  rewrite <- (f_S_2 (S n)) in Hp. lia.
Qed.

Lemma hc_tower : forall n, 2 <= n -> 2 * f (S n) 2 + 4 <= hc 1 n 6.
Proof.
  intros n Hn. induction Hn as [| m Hm IH].
  - exact hc_tower_base.
  - pose proof (hc_tower_step m Hm IH). pose proof (f_id (S (S m)) 2). lia.
Qed.

Lemma G40_bound : 6 * f 14 2 <= G 40.
Proof.
  change (G 40) with (G (3 * 13 + 1)). rewrite (G_k 13).
  rewrite (hc_S 0 13 2), (h_0 2). change (2 + 4) with 6.
  pose proof (hc_tower_step 12 ltac:(lia) (hc_tower 12 ltac:(lia))). lia.
Qed.

Lemma G5_4_bound : 6 * iter 3 f_omega (f 14 2) <= iter 5 G 4.
Proof.
  cbn [iter]. rewrite G4_eq.
  pose proof G40_bound as H2.
  pose proof (G_dom (f 14 2) (G 40) H2) as H3.
  pose proof (G_dom (f_omega (f 14 2)) (G (G 40)) H3) as H4.
  exact (G_dom (f_omega (f_omega (f 14 2))) (G (G (G 40))) H4).
Qed.

Lemma hoc1_dom_w2 : forall k, 1 <= k -> 6 * f_w2 (S k) <= hoc 1 (S k) 4.
Proof.
  intros [| k'] Hk; [lia |].
  rewrite (hoc_last (S k') 1 4). change (1 + S k') with (S (S k')).
  assert (Hb : 6 * S (S k') <= hoc 1 (S k') 4).
  { rewrite (hoc_S 1 k' 4).
    pose proof (hoc_ge k' 2 (ho 1 4)).
    assert (Hho1 : 34 <= ho 1 4)
      by (rewrite (ho_S 0 4); pose proof (iter_linK (ho 0) 6 (ho_ge 0) (4 + 1) 4); lia).
    lia. }
  pose proof (ho_dom (S (S k')) (S (S k')) (hoc 1 (S k') 4) Hb) as Hd.
  rewrite <- (f_w2_eq (S (S k'))) in Hd. exact Hd.
Qed.

Lemma bound_gen : forall Y0 a1 q1 k1 a2 j,
  2 <= Y0 -> 6 * Y0 <= a1 ->
  a1 + 6 = 9 * S q1 + 1 ->
  k1 = 3 * q1 + 1 ->
  a2 = hoc 1 (S k1) 4 ->
  a2 + 2 * (3 * S q1) + 2 = 3 * S (S j) ->
  f_w2 Y0 < 2 * j + 4.
Proof.
  intros Y0 a1 q1 k1 a2 j HY0 Ha1 Hq1 Hk1 Ha2 Hj.
  assert (Hk1_ge : 1 <= k1) by lia.
  assert (HSk1_ge : Y0 <= S k1) by lia.
  pose proof (hoc1_dom_w2 k1 Hk1_ge) as Hd.
  pose proof (f_w2_mono Y0 (S k1) HSk1_ge) as Hm.
  lia.
Qed.

Lemma Y0_ge2 : 2 <= iter 3 f_omega (f 14 2).
Proof.
  pose proof f14_2_ge.
  pose proof (iter_ge f_omega f_omega_id 3 (f 14 2)).
  lia.
Qed.

Lemma beat_J16_inner : f 15 2 <= iter 3 f_omega (f 14 2).
Proof.
  pose proof f14_2_ge as Hf14.
  pose proof (f_mono 15 2 15 ltac:(lia)) as H1.
  rewrite <- (f_omega_eq 15) in H1.
  pose proof (f_omega_mono 15 (f 14 2) ltac:(lia)) as H2.
  pose proof (f_omega_id (f_omega (f 14 2))) as H3.
  pose proof (f_omega_id (f_omega (f_omega (f 14 2)))) as H4.
  cbn [iter]. lia.
Qed.

Lemma beat_J16_w2 : f_w2 (f 15 2) <= f_w2 (iter 3 f_omega (f 14 2)).
Proof. apply f_w2_mono, beat_J16_inner. Qed.

Theorem score_exact : exists q1 k1 a2 j c,
  iter 5 G 4 + 6 = 9 * S q1 + 1 /\
  k1 = 3 * q1 + 1 /\
  a2 = hoc 1 (S k1) 4 /\
  a2 + 2 * (3 * S q1) + 2 = 3 * S (S j) /\
  c0 -->* c /\ halted tm c /\ ones c (2 * j + 4).
Proof.
  destruct run as (q1 & k1 & a2 & j & Hq1 & Hk1 & Ha2 & Hj & Hrun).
  exists q1, k1, a2, j, (Hc j).
  split; [exact Hq1 |]. split; [exact Hk1 |]. split; [exact Ha2 |]. split; [exact Hj |].
  split; [exact Hrun |]. split; [apply Hc_halted | apply ones_Hc].
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
    f_w2 (f 15 2) < N /\ f_w2 (iter 3 f_omega (f 14 2)) < N.
Proof.
  destruct run as (q1 & k1 & a2 & j & Hq1 & Hk1 & Ha2 & Hj & Hrun).
  exists (Hc j), (2 * j + 4).
  split; [exact Hrun |]. split; [apply Hc_halted |]. split; [apply ones_Hc |].
  pose proof (bound_gen (iter 3 f_omega (f 14 2)) (iter 5 G 4) q1 k1 a2 j
                Y0_ge2 G5_4_bound Hq1 Hk1 Ha2 Hj) as HB17.
  split; [exact (Nat.le_lt_trans _ _ _ beat_J16_w2 HB17) | exact HB17].
Qed.

(** ** Exact Isomorphism to Unmirrored Tree Normal Form (TNF) *)
Definition tm_tnf : TM := fun '(q, s) =>
  match q, s with
  | A,  S0 => Some (S1, TM.L, B)  | A,  S1 => Some (S1, TM.R, D)
  | B,  S0 => Some (S1, TM.L, C)  | B,  S1 => Some (S1, TM.L, B)
  | C,  S0 => Some (S1, TM.L, D)  | C,  S1 => Some (S0, TM.L, B)
  | D,  S0 => Some (S1, TM.R, E)  | D,  S1 => Some (S0, TM.R, M)
  | E,  S0 => Some (S1, TM.R, F)  | E,  S1 => Some (S1, TM.R, E)
  | F,  S0 => Some (S0, TM.L, BB172.G)  | F,  S1 => Some (S1, TM.R, P)
  | BB172.G, S0 => Some (S1, TM.L, H)   | BB172.G, S1 => Some (S1, TM.L, BB172.G)
  | H,  S0 => Some (S0, TM.L, I)        | H,  S1 => Some (S1, TM.L, BB172.G)
  | I,  S0 => Some (S1, TM.R, J)  | I,  S1 => Some (S1, TM.R, K)
  | J,  S0 => Some (S0, TM.R, J)  | J,  S1 => Some (S0, TM.R, E)
  | K,  S0 => Some (S0, TM.R, L)  | K,  S1 => Some (S1, TM.R, J)
  | L,  S0 => Some (S0, TM.L, C)  | L,  S1 => Some (S0, TM.R, A)
  | M,  S0 => None                | M,  S1 => Some (S1, TM.R, N)
  | N,  S0 => Some (S0, TM.L, C)  | N,  S1 => Some (S0, TM.R, O)
  | O,  S0 => Some (S0, TM.L, C)  | O,  S1 => Some (S1, TM.R, M)
  | P,  S0 => Some (S0, TM.L, QQ) | P,  S1 => Some (S1, TM.L, C)
  | QQ, S0 => Some (S0, TM.R, K)  | QQ, S1 => Some (S1, TM.L, QQ)
  end.

Definition perm_tnf (q : Q) : Q :=
  match q with
  | A => A | B => F | C => P | D => QQ | E => K | F => E | BB172.G => B | H => D
  | I => BB172.G | J => H | K => I | L => J | M => N | N => O | O => M | P => L | QQ => C
  end.

Lemma perm_tnf_trans : forall q s,
  tm_tnf (perm_tnf q, s) =
  match tm (q, s) with
  | None => None
  | Some (s', d, q') => Some (s', d, perm_tnf q')
  end.
Proof. intros [] []; reflexivity. Qed.

Lemma perm_step_tnf : forall c1 c2, c1 -[ tm ]-> c2 ->
  (perm_tnf (fst c1), snd c1) -[ tm_tnf ]-> (perm_tnf (fst c2), snd c2).
Proof.
  intros c1 c2 H. destruct H as [q q' s s' l r Htr | q q' s s' l r Htr]; cbn [fst snd].
  - apply step_left. rewrite perm_tnf_trans, Htr. reflexivity.
  - apply step_right. rewrite perm_tnf_trans, Htr. reflexivity.
Qed.

Lemma perm_evstep_tnf : forall c1 c2, c1 -[ tm ]->* c2 ->
  (perm_tnf (fst c1), snd c1) -[ tm_tnf ]->* (perm_tnf (fst c2), snd c2).
Proof.
  intros c1 c2 H. induction H as [c | c1 c2 c3 H1 _ IH].
  - apply evstep_refl.
  - eapply evstep_step; [exact (perm_step_tnf c1 c2 H1) | exact IH].
Qed.

Lemma perm_halted_tnf : forall q t, halted tm (q, t) -> halted tm_tnf (perm_tnf q, t).
Proof.
  intros q [[l s] r] H. unfold halted in *. rewrite perm_tnf_trans, H. reflexivity.
Qed.

Theorem sigma_lower_bound_tnf :
  exists c N, c0 -[ tm_tnf ]->* c /\ halted tm_tnf c /\ ones c N /\
    f_w2 (f 15 2) < N /\ f_w2 (iter 3 f_omega (f 14 2)) < N.
Proof.
  destruct sigma_lower_bound as ([q t] & N & Hrun & Hhalt & Hones & HB15 & HB17).
  exists (perm_tnf q, t), N.
  split; [exact (perm_evstep_tnf c0 (q, t) Hrun) |].
  split; [exact (perm_halted_tnf q t Hhalt) |].
  split; [| split; [exact HB15 | exact HB17]].
  destruct Hones as (q0 & L & R & s & Heq & HN).
  injection Heq as Hq Ht; subst q0 t.
  exists (perm_tnf q), L, R, s. split; [reflexivity | exact HN].
Qed.

Theorem halt_tnf : halts tm_tnf c0.
Proof.
  destruct sigma_lower_bound_tnf as (c & _ & Hrun & Hhalt & _).
  exact (halted_evstep_halts tm_tnf c0 c Hrun Hhalt).
Qed.

Print Assumptions halt.
Print Assumptions halt_tnf.
Print Assumptions score_exact.
Print Assumptions sigma_lower_bound.
Print Assumptions sigma_lower_bound_tnf.


