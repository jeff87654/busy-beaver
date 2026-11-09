(** * 15-state BB(15) champion J15_fw13 halts, with sigma > f_(omega+13)(20)

    J15_fw13 = 1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM

    Anatomy:
    - 12-state core sweep engine (A..L): identical to J20 on A, B, C, D, E1, F, G, H0, I, J, K, L.
      Inner level maps: h 0 x = x + 4, h (S m) x = iter (x + 2) (h m) 2, hc m n x.
    - Non-shifting period-3 expansion & refill (M, N, O with H1 = 0RO, E0 = 0RH, O0 = 1RZ):
      - Outer R0 on a = 3c + 1 expands to CI 2 (repeat 2 (c+1)) and evaluates to
        G(3c + 1) = hc 0 (c + 1) 2 + 2(c + 1) + 2 == 1 (mod 3).
      - Outer R1 resets the accumulator to 4 == 1 (mod 3) and promotes a + 2.
      - Outer exhaustion OEX on CO(a, 1^n) reaches RQ(a + 2n + 1) (corresponding to EX(B) with B = a + 2n + 2):
        * RQ(3k + 1) (B = 3k + 2 == 2 mod 3) refills to CO(4, 2^k).
        * RQ(3j)     (B = 3j + 1 == 1 mod 3) halts at O0 = 1RZ in configuration Hc(j) with 2j + 1 ones on tape.
    - Trajectory:
      c0 ->* CO(3, []) ->* RQ(4) ->* CO(4, [2]) ->* CO(40, [1]) ->* RQ(43)
         ->* CO(4, 2^14) (at step 1012)
         ->* CO(hoc 0 14 4, 1^14) ->* RQ(hoc 0 14 4 + 29) ->* Hc(j) (HALT).

    Main results (zero axioms):
      [step_1012]         : c0 -->* CO 4 (rl (repeat 2 14) (const S0))
      [halt]              : halts tm c0
      [score_exact]       : exists j c, hoc 0 14 4 + 29 = 3 * j /\ c0 -->* c /\ halted tm c /\ ones c (2 * j + 1)
      [sigma_lower_bound] : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_wk 13 20 < N. *)

From BB8 Require Import Individual152.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF0RO_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LA1RO_1RZ1RM *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.L, H)   | A, 1 => Some (0, TM.L, G)
  | B, 0 => Some (0, TM.L, I)   | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)   | C, 1 => Some (1, TM.L, A)
  | D, 0 => Some (0, TM.R, E)   | D, 1 => Some (1, TM.L, D)
  | E, 0 => Some (0, TM.R, H)   | E, 1 => Some (1, TM.R, L)
  | F, 0 => Some (1, TM.R, B)   | F, 1 => Some (1, TM.R, F)
  | G, 0 => Some (1, TM.L, A)   | G, 1 => Some (1, TM.L, G)
  | H, 0 => Some (1, TM.R, F)   | H, 1 => Some (0, TM.R, O)
  | I, 0 => Some (1, TM.L, J)   | I, 1 => Some (1, TM.L, I)
  | J, 0 => Some (0, TM.L, K)   | J, 1 => Some (1, TM.L, I)
  | K, 0 => Some (1, TM.R, L)   | K, 1 => Some (1, TM.R, E)
  | L, 0 => Some (0, TM.R, L)   | L, 1 => Some (0, TM.R, F)
  | M, 0 => Some (0, TM.L, A)   | M, 1 => Some (0, TM.R, N)
  | N, 0 => Some (0, TM.L, A)   | N, 1 => Some (1, TM.R, O)
  | O, 0 => None                | O, 1 => Some (1, TM.R, M)
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
Lemma zigGA : forall n l r, [0;1]^^n *> l <{{G}} r -->* l <{{G}} [0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma zigIJ : forall n l r, [0;1]^^n *> l <{{I}} r -->* l <{{I}} [1;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triOMN : forall n l r, l {{O}}> [1;1;1]^^n *> r -->* [1;0;1]^^n *> l {{O}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triGA : forall n l r, [1;0;1]^^n *> l <{{G}} r -->* l <{{G}} [0;1;1]^^n *> r.
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
  SW l j y (S (S e) :: ds) R -->* l <{{A}} (1 >> [0;1]^^j *> [1]^^(S y) *> 0 >> rl (S e :: ds) R).
Proof.
  intros. unfold SW. cbn [rl lpow app Str_app].
  execute.
  follow walkG.
  follow zigGA.
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

(** outer exhaustion state after E0 = 0RH, H1 = 0RO on EX(N + 1) *)
Definition RQ (N : nat) : Q * tape := (0 >> 0 >> 1 >> const 0) {{O}}> ([1]^^N *> const 0).

(** outer exit: the exhausted outer list is merged and enters O> on the remaining N ones *)
Lemma SW_exit_out : forall j y N, N = y + 2 * j + 1 ->
  SW (0 >> 1 >> const 0) j y [] (const 0) -->* RQ N.
Proof.
  intros j y N HN. unfold SW. cbn [rl].
  execute.
  follow walkI.
  follow zigIJ.
  execute.
  rewrite pairs_ones.
  unfold RQ. subst N. finish.
Qed.

Lemma CI_SW : forall x ds R, CI x ds R -->* SW (const 0) 0 (S x) ds R.
Proof.
  intros. unfold CI, SW.
  execute. follow walkF. finish_norm.
Qed.

Lemma SW_A_in : forall j y e ds R,
  SW (const 0) j y (S (S e) :: ds) R -->*
  const 0 <{{H}} (1 >> 1 >> [0;1]^^j *> [1]^^(S y) *> 0 >> rl (S e :: ds) R).
Proof.
  intros. follow SW_E. execute.
Qed.

Lemma CI_E0 : forall x e ds R, CI x (S (S e) :: ds) R -->* CI (x + 4) (S e :: ds) R.
Proof.
  intros. follow CI_SW. follow SW_A_in. unfold CI.
  replace (x + 4) with (S (S (S (S x)))) by lia. finish.
Qed.

Lemma CI_E1 : forall x j e ds R,
  CI x (repeat 1%nat (S j) ++ S (S e) :: ds) R -->* CI 2 (repeat 1%nat j ++ (x + 3) :: S e :: ds) R.
Proof.
  intros. follow CI_SW. follow SW_pass_iter. follow SW_A_in. unfold CI.
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

(** ** Expansion & Refill via O, M, N and G, A *)

Lemma EXP_c : forall c X,
  (0 >> 1 >> const 0) <{{A}} (1 >> [1]^^(S (3 * c + 1)) *> 0 >> X) -->*
  CI 2 (repeat 2%nat (S c)) (0 >> X).
Proof.
  intros c X. unfold CI. rewrite rl_rep2.
  change (1 >> [1]^^(S (3 * c + 1)) *> 0 >> X) with (1 >> 1 >> [1]^^(3 * c + 1) *> 0 >> X).
  rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  execute.
  follow triOMN.
  execute.
  follow triGA.
  rewrite (align_lpow 0 [1;1]). simpl app.
  execute.
Qed.

(** Halting configuration & Refill rules *)
Definition Hc (k : nat) : Q * tape := ([1;0;1]^^k *> 0 >> 0 >> 1 >> const 0) {{O}}> (const 0).

Lemma Hc_halted : forall k, halted tm (Hc k).
Proof. intros. reflexivity. Qed.

Lemma RF_halt : forall k, RQ (3 * k) -->* Hc k.
Proof. intros. unfold RQ, Hc. rewrite <- pow111. follow triOMN. finish. Qed.

Lemma RF_1 : forall k, RQ (3 * k + 1) -->* CO 4 (rl (repeat 2%nat k) (const 0)).
Proof.
  intros k. unfold RQ, CO. rewrite rl_rep2.
  rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  follow triOMN.
  execute.
  follow triGA.
  align_tape.
  execute.
Qed.

(** ** Outer rounds *)
Lemma CO_SW : forall a ds R, CO a (rl ds R) -->* SW (0 >> 1 >> const 0) 0 a ds R.
Proof. intros. unfold CO, SW. follow walkF. finish. Qed.

Lemma OEX : forall a n N, N = a + 2 * n + 1 -> CO a (rl (repeat 1%nat n) (const 0)) -->* RQ N.
Proof.
  intros a n N HN. rewrite <- (app_nil_r (repeat 1%nat n)).
  follow CO_SW. follow SW_pass_iter. apply (SW_exit_out (0 + n) a N). lia.
Qed.

Lemma R1_raw : forall a p e os,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) (const 0)) -->*
  CO 4 (1 >> [0;1]^^p *> [1]^^(S a) *> 0 >> rl (S e :: os) (const 0)).
Proof.
  intros. follow CO_SW. follow SW_pass_iter. follow SW_E. execute.
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

Definition Gc (c : nat) : nat := hc 0 (S c) 2 + 2 * S c + 2.
Definition G (a : nat) : nat := Gc (a / 3).

(** outer level maps (R1 resets accumulator to 4) *)
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

Lemma R0_c : forall c e os,
  CO (3 * c + 1) (rl (S (S e) :: os) (const 0)) -->* CO (Gc c) (rl (S e :: os) (const 0)).
Proof.
  intros c e os.
  follow CO_SW. follow SW_E.
  follow EXP_c.
  follow (Chain_in (S c) 0%nat 2%nat (0 >> rl (S e :: os) (const 0))).
  simpl Nat.add.
  apply CI_exit.
Qed.

Local Open Scope nat_scope.

(** ** Mod-3 invariants: h m is x -> x + 1 (mod 3), and G / ho / hoc preserve == 1 (mod 3) *)
Definition P1 (g : nat -> nat) : Prop := forall x, exists q, g x = (x + 1 + 3 * q)%nat.

Lemma iter_P1 : forall g, P1 g -> forall n z, exists q, iter n g z = (z + n + 3 * q)%nat.
Proof.
  intros g Hg. induction n; intros z.
  - exists 0%nat. simpl. lia.
  - destruct (IHn z) as [q Hq]. destruct (Hg (iter n g z)) as [q' Hq'].
    exists (q + q')%nat. simpl. rewrite Hq', Hq. lia.
Qed.

Lemma h_P1 : forall m, P1 (h m).
Proof.
  induction m as [| m IHm]; intros x.
  - exists 1%nat. simpl. lia.
  - destruct (iter_P1 (h m) IHm (x + 2) 2) as [q Hq]. exists (q + 1)%nat. simpl h. rewrite Hq. lia.
Qed.

Lemma hc_mod : forall n m x, exists q, hc m n x = (x + n + 3 * q)%nat.
Proof.
  induction n as [| n IHn]; intros m x.
  - exists 0%nat. simpl. lia.
  - destruct (h_P1 m x) as [q Hq]. destruct (IHn (S m) (h m x)) as [q' Hq'].
    exists (q + q')%nat. simpl hc. rewrite Hq', Hq. lia.
Qed.

Definition mod3_1 (x : nat) : Prop := exists k, x = 3 * k + 1.

Lemma mod3_1_4 : mod3_1 4.
Proof. exists 1. reflexivity. Qed.

Lemma Gc_mod3_1 : forall c, mod3_1 (Gc c).
Proof.
  intros c. unfold Gc.
  destruct (hc_mod (S c) 0 2) as [q Hq].
  exists (q + S c + 1). lia.
Qed.

Lemma G_mod3_1 : forall a, mod3_1 (G a).
Proof. intros a. apply Gc_mod3_1. Qed.

Lemma ho_mod3_1 : forall m a, mod3_1 (ho m a).
Proof.
  induction m as [| m IHm]; intros a.
  - apply G_mod3_1.
  - simpl ho. replace (a + 1) with (S a) by lia. simpl iter. apply IHm.
Qed.

Lemma hoc_mod3_1 : forall n m a, mod3_1 a -> mod3_1 (hoc m n a).
Proof.
  induction n as [| n IHn]; intros m a Ha.
  - exact Ha.
  - simpl hoc. apply IHn, ho_mod3_1.
Qed.

Close Scope nat_scope.

Lemma R0 : forall a e os, mod3_1 a ->
  CO a (rl (S (S e) :: os) (const 0)) -->* CO (G a) (rl (S e :: os) (const 0)).
Proof.
  intros a e os [c ->].
  replace (G (3 * c + 1)) with (Gc c).
  - apply R0_c.
  - unfold G. f_equal. apply (Nat.div_unique (3 * c + 1) 3 c 1); lia.
Qed.

(** ** Outer levels (under the a == 1 mod 3 invariant) *)
Lemma LV_out : forall m e a os, mod3_1 a ->
  CO a (rl (repeat 1%nat m ++ S e :: os) (const 0)) -->* CO (iter e (ho m) a) (rl (repeat 1%nat (S m) ++ os) (const 0)).
Proof.
  induction m as [| m IHm]; intros e; induction e as [| e IHe]; intros a os Ha.
  - simpl. finish.
  - simpl app. follow (R0 a e os Ha). follow (IHe (G a) os (G_mod3_1 a)). rewrite iter_S'. finish.
  - rewrite rep_snoc. finish.
  - follow R1. follow (IHm (a + 1)%nat 4%nat (S e :: os) mod3_1_4).
    follow (IHe (ho (S m) a) os (ho_mod3_1 (S m) a)). rewrite iter_S'. finish.
Qed.

Lemma Chain_out : forall n m a os, mod3_1 a ->
  CO a (rl (repeat 1%nat m ++ repeat 2%nat n ++ os) (const 0)) -->* CO (hoc m n a) (rl (repeat 1%nat (m + n) ++ os) (const 0)).
Proof.
  induction n as [| n IHn]; intros m a os Ha.
  - rewrite Nat.add_0_r. finish.
  - simpl repeat. cbn [app]. follow (LV_out m 1%nat a (repeat 2%nat n ++ os) Ha).
    follow (IHn (S m) (ho m a) os (ho_mod3_1 m a)). replace (S m + n)%nat with (m + S n)%nat by lia. finish.
Qed.

Local Open Scope nat_scope.

(** ** The run from the blank tape *)
Lemma boot : c0 -->* CO 3 (rl [] (const S0)).
Proof. unfold CO. cbn [rl]. execute. Qed.

Lemma h_0 : forall x, h 0 x = x + 4.  Proof. reflexivity. Qed.
Lemma h_S : forall m x, h (S m) x = iter (x + 2) (h m) 2.  Proof. reflexivity. Qed.
Lemma hc_0 : forall m x, hc m 0 x = x.  Proof. reflexivity. Qed.
Lemma hc_S : forall m n x, hc m (S n) x = hc (S m) n (h m x).  Proof. reflexivity. Qed.
Lemma ho_0 : forall a, ho 0 a = G a.  Proof. reflexivity. Qed.
Lemma ho_S : forall m a, ho (S m) a = iter (a + 1) (ho m) 4.  Proof. reflexivity. Qed.
Lemma hoc_0 : forall m a, hoc m 0 a = a.  Proof. reflexivity. Qed.
Lemma hoc_S : forall m n a, hoc m (S n) a = hoc (S m) n (ho m a).  Proof. reflexivity. Qed.
Lemma G_4 : G 4 = 40.  Proof. reflexivity. Qed.
Lemma G_eq : forall a, G a = hc 1 (a / 3) 6 + 2 * (a / 3) + 4.
Proof. intros a. unfold G, Gc. simpl. lia. Qed.

Opaque h hc G ho hoc.

(** Explicit trajectory to step 1012: c0 -->* CO([4, 2^14]) via 2 outer refills *)
Theorem step_1012 : c0 -->* CO 4 (rl (repeat 2 14) (const S0)).
Proof.
  follow boot.
  follow (OEX 3 0 4 eq_refl).
  follow (RF_1 1).
  simpl repeat.
  follow (R0 4 0 [] mod3_1_4).
  rewrite G_4.
  follow (OEX 40 1 43 eq_refl).
  exact (RF_1 14).
Qed.

Lemma J_gen : forall a2, a2 = hoc 0 14 4 -> exists j, a2 + 29 = 3 * j.
Proof.
  intros a2 ->.
  destruct (hoc_mod3_1 14 0 4 mod3_1_4) as [k Hk].
  exists (k + 10). lia.
Qed.

Lemma run_gen : forall a2 j,
  a2 = hoc 0 14 4 -> a2 + 29 = 3 * j -> c0 -->* Hc j.
Proof.
  intros a2 j Ha2 Hj.
  follow step_1012.
  pose proof (Chain_out 14 0 4 [] mod3_1_4) as Hc14.
  rewrite app_nil_r in Hc14. simpl repeat in Hc14 at 1. simpl app in Hc14.
  rewrite <- Ha2 in Hc14.
  follow Hc14.
  follow (OEX a2 14 (3 * j) ltac:(lia)).
  apply RF_halt.
Qed.

Lemma run : exists j, hoc 0 14 4 + 29 = 3 * j /\ c0 -->* Hc j.
Proof.
  destruct (J_gen (hoc 0 14 4) eq_refl) as [j Hj].
  exists j. split; [exact Hj |].
  exact (run_gen (hoc 0 14 4) j eq_refl Hj).
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct run as (j & _ & Hrun).
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

Lemma ones_Hc : forall j, ones (Hc j) (2 * j + 1).
Proof.
  intros j. exists O, ([S1; S0; S1]^^j ++ [S0; S0; S1]), (@nil Sym), S0.
  split.
  - unfold Hc. rewrite Str_app_assoc. reflexivity.
  - rewrite count1_app, count1_pow. cbn [count1 sym_val]. lia.
Qed.

(** ** Fast-growing hierarchy up to f_(omega+k) *)
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

Lemma f_omega_eq : forall n, f_omega n = f n n.
Proof. reflexivity. Qed.

Lemma f_wk_S : forall k n, f_wk (S k) n = iter n (f_wk k) n.
Proof. reflexivity. Qed.

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

Lemma G_ge : forall a, a + 8 <= G a.
Proof.
  intros a. rewrite (Nat.div_mod a 3) at 1 by lia.
  pose proof (Nat.mod_upper_bound a 3 ltac:(lia)).
  rewrite G_eq. pose proof (hc_ge (a / 3) 1 6). lia.
Qed.

Lemma G_dom : forall n z, 6 * n <= z -> 6 * f_omega n <= G z.
Proof.
  intros n z Hz. pose proof (G_ge z) as Hg.
  destruct n as [| [| n']].
  - change (f_omega 0) with 1. lia.
  - change (f_omega 1) with 2. lia.
  - set (n := S (S n')) in *.
    pose proof (Nat.div_mod z 3 ltac:(lia)) as Hdm. pose proof (Nat.mod_upper_bound z 3 ltac:(lia)) as Hmb.
    rewrite G_eq.
    set (c := z / 3) in *.
    assert (Hc : 2 * n <= c) by lia.
    destruct c as [| c'] eqn:Ec; [lia |].
    rewrite hc_last.
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

Lemma ho_ge : forall m y, y + 8 <= ho m y.
Proof.
  induction m as [| m IHm]; intros y.
  - rewrite ho_0. pose proof (G_ge y). lia.
  - rewrite ho_S. pose proof (iter_linK (ho m) 8 IHm (y + 1) 4). lia.
Qed.

Lemma ho_dom : forall m n z, 6 * n <= z -> 6 * f_wk m n <= ho m z.
Proof.
  apply (transfer 6 4 f_wk ho ltac:(lia) f_wk_S).
  - intros m z. rewrite ho_S. replace (z + 1) with (S z) by lia. lia.
  - intros m y. pose proof (ho_ge m y). lia.
  - exact G_dom.
Qed.

Lemma hoc_ge : forall n m a, a + 8 * n <= hoc m n a.
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

Lemma hoc14_dom : 6 * f_wk 13 20 <= hoc 0 14 4.
Proof.
  change 14 with (S 13).
  rewrite hoc_last. simpl Nat.add.
  apply ho_dom.
  rewrite hoc_S, ho_0, G_4.
  pose proof (hoc_ge 12 1 40). lia.
Qed.

Theorem score_exact : exists j c,
  hoc 0 14 4 + 29 = 3 * j /\ c0 -->* c /\ halted tm c /\ ones c (2 * j + 1).
Proof.
  destruct run as (j & Hj & Hrun).
  exists j, (Hc j).
  split; [exact Hj |]. split; [exact Hrun |].
  split; [apply Hc_halted | apply ones_Hc].
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_wk 13 20 < N.
Proof.
  destruct run as (j & Hj & Hrun).
  exists (Hc j), (2 * j + 1).
  split; [exact Hrun |]. split; [apply Hc_halted |]. split; [apply ones_Hc |].
  pose proof hoc14_dom. lia.
Qed.

Print Assumptions step_1012.
Print Assumptions halt.
Print Assumptions score_exact.
Print Assumptions sigma_lower_bound.
