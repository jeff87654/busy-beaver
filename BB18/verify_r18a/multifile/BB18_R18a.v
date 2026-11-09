(** * R18a: an 18-state halter with sigma > f_(omega*2)(f_omega(f_omega(f_10(2))))

    R18a = 1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0LQ0LO_1LR1LP_0LQ1LN_0RO1LB_0LL1RZ

    Credit: R18a is derived from Jacobzheng's 20-state BB(20) champion J20
    (1LH0LG_..._0LF0LR, proved in BB20_JZ20.v, whose proof this file adapts).  J20's 4-state refill
    (Q R S T) is deleted: the refill reuses J20's expansion walker M and rewriter N O P, and two new
    dispatch states Q, R read the cell left of the rewriter exit (blank in an expansion, the far-left
    marker in a refill).  Rows A-P equal J20's except E0 (0RH), N0 (0LQ), O0 (1LR), P0 (0LQ).

    Anatomy (J20's coordinates, outer boundary CO a ds = 0^inf 1 0 0 F> 1^a 0 ds):
      expansion, inner engine, the outer rules R0 [a,e,..] -> [G a, e-1, ..] and
      R1 [a,1^(p+1),e,..] -> [3,1^p,a+2,e-1,..] are J20's exactly (same G, ho, hoc).
      Outer exhaustion CO a [1^n] merges a block of T = a+2n+2 cells, rewritten from the right in period 3:
        T = 3c+1 -> HALT (O0 writes the gap, R reads the marker; R1 = 1RZ writes 1 on a 1), 2c+2 ones;
        T = 3k+2 -> CO 0 [1,1,2^k];   T = 3k -> CO 0 [1,2^k].
    Run: CO 3 [] -> T=5 -> CO 0 [1,1,2] -> CO 3 [5,1,1] -> CO a1 [1,1,1], a1 = iter 3 G 28 (G 3 = 28)
      -> T1 = a1+8 = 3(k+1) -> CO 0 [1,2^(k+1)] -> CO 28 [1,1,2^k] -> CO a2 [1^(k+2)], a2 = hoc 2 k 28
      -> T2 = a2+2(k+2)+2 = 3c+1 -> HALT.
    Halting is DETERMINISTIC by J20's mod-3 invariant (G and every ho m are x -> x+1 mod 3).

    Main results (no axioms):
      [halt]              : halts tm c0
      [score_exact]       : the halting tape holds exactly 2c+2 ones (= sigma: the halting transition writes 1 on a 1),
                            iter 3 G 28 + 8 = 3(k+1),  a2 = hoc 2 k 28,  a2 + 2(k+2) + 2 = 3c+1
      [sigma_lower_bound] : f_w2 (f_omega (f_omega (f 10 2))) < N   (f_w2 = f_(omega*2))
      [beats_J19]         : f_wk 7 (f_wk 7 5) < N             (J19's BB(19) bound, f_(omega+7)^2(5))
      [beats_M18_229]     : iter 229 (f_wk 3) 9 < N           (M18_229round's BB(18) bound, f_(omega+3)^229(9)) *)

From BB8 Require Import Individual182.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_0LQ0LO_1LR1LP_0LQ1LN_0RO1LB_0LL1RZ *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.L, H)   | A, 1 => Some (0, TM.L, G)
  | B, 0 => Some (0, TM.L, I)   | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)   | C, 1 => Some (1, TM.L, A)
  | D, 0 => Some (0, TM.R, E)   | D, 1 => Some (1, TM.L, D)
  | E, 0 => Some (0, TM.R, H)   | E, 1 => Some (1, TM.R, L)
  | F, 0 => Some (1, TM.R, B)   | F, 1 => Some (1, TM.R, F)
  | G, 0 => Some (1, TM.L, A)   | G, 1 => Some (1, TM.L, G)
  | H, 0 => Some (1, TM.R, F)   | H, 1 => Some (1, TM.R, M)
  | I, 0 => Some (1, TM.L, J)   | I, 1 => Some (1, TM.L, I)
  | J, 0 => Some (0, TM.L, K)   | J, 1 => Some (1, TM.L, I)
  | K, 0 => Some (1, TM.R, L)   | K, 1 => Some (1, TM.R, E)
  | L, 0 => Some (0, TM.R, L)   | L, 1 => Some (0, TM.R, F)
  | M, 0 => Some (0, TM.L, N)   | M, 1 => Some (1, TM.R, M)
  | N, 0 => Some (0, TM.L, QQ)  | N, 1 => Some (0, TM.L, O)
  | O, 0 => Some (1, TM.L, RR)  | O, 1 => Some (1, TM.L, P)
  | P, 0 => Some (0, TM.L, QQ)  | P, 1 => Some (1, TM.L, N)
  | QQ, 0 => Some (0, TM.R, O)  | QQ, 1 => Some (1, TM.L, B)
  | RR, 0 => Some (0, TM.L, L)  | RR, 1 => None
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
Lemma walkM : forall n l r, l {{M}}> [1]^^n *> r -->* [1]^^n *> l {{M}}> r.
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
Lemma triNOP : forall n l r, [1;1;1]^^n *> l <{{N}} r -->* l <{{N}} [1;1;0]^^n *> r.
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

Lemma ones3 : forall n (X : side), [1]^^n *> 1 >> 1 >> 1 >> X = [1]^^(n + 3) *> X.
Proof. intros. rewrite <- ones_add. reflexivity. Qed.

(** refill start: N at the right end of the merged block, gap 0 and marker 1 on its left *)
Definition RN (T : nat) : Q * tape := ([1]^^T *> 0 >> 1 >> const 0) <{{N}} (0 >> const 0).

Lemma ones_snoc : forall n (X : side), [1]^^n *> 1 >> X = [1]^^(S n) *> X.
Proof. intros. rewrite one_shift. reflexivity. Qed.

(** outer exit: the exhausted outer list is merged (marker and gap kept) and M walks to the right end *)
Lemma SW_exit_out : forall j y T, T = (y + 2 * j + 2)%nat ->
  SW (0 >> 1 >> const 0) j y [] (const 0) -->* RN T.
Proof.
  intros j y T HT. unfold SW. cbn [rl].
  execute.
  follow walkI.
  follow zigIJ.
  execute.
  rewrite pairs_ones.
  follow walkM.
  rewrite ones_snoc.
  eapply evstep_step; [prove_step |].
  unfold RN. subst T. replace (y + 2 * j + 2)%nat with (S (y + 2 * j + 1)) by lia.
  apply evstep_refl.
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

(** expansion of the marker+accumulator block: T = 3c+1+y cells.  The rewriter exit (N0/P0 -> Q0, or O0 -> R0)
    reads the blank left of the block and returns to F exactly where J20's 0RF exits do. *)
Lemma EXP : forall c y X, y < 3 ->
  ([1]^^(3 * c + 1 + y) *> const 0) <{{N}} (0 >> X) -->* SW (const 0) 0 y (repeat 2%nat c) (0 >> X).
Proof.
  intros c y X Hy. unfold SW. rewrite rl_rep2.
  destruct y as [| [| [| y]]]; try lia.
  - replace (3 * c + 1 + 0) with (3 * c + 1) by lia.
    rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
    follow triNOP. execute.
  - replace (3 * c + 1 + 1) with (3 * c + 2) by lia.
    rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
    follow triNOP. execute.
  - replace (3 * c + 1 + 2) with (3 * S c) by lia.
    rewrite <- pow111.
    follow triNOP. execute.
Qed.

(** ** Refill (N O P rewrite the merged block from the right, period 3; Q R dispatch at the left end) *)
Definition Hh (c : nat) : Q * tape := (1 >> const 0) <{{RR}} (1 >> 0 >> [1;1;0]^^c *> const 0).

Lemma Hh_halted : forall c, halted tm (Hh c).
Proof. intros. reflexivity. Qed.

Lemma RF_halt : forall c, RN (3 * c + 1) -->* Hh c.
Proof.
  intros. unfold RN, Hh. rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  follow triNOP. execute.
Qed.

Lemma RF_A : forall k, RN (3 * k + 2) -->* CO 0 (1 >> 0 >> 1 >> 0 >> [1;1;0]^^k *> const 0).
Proof.
  intros. unfold RN. rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  follow triNOP. execute.
Qed.

Lemma RF_B : forall k, RN (3 * k) -->* CO 0 (1 >> 0 >> [1;1;0]^^k *> const 0).
Proof.
  intros. unfold RN. rewrite <- pow111.
  follow triNOP. execute.
Qed.

Lemma rfA_rl : forall k, 1 >> 0 >> 1 >> 0 >> [1;1;0]^^k *> const 0 = rl (1%nat :: 1%nat :: repeat 2%nat k) (const 0).
Proof. intros. cbn [rl]. rewrite rl_rep2. reflexivity. Qed.

Lemma rfB_rl : forall k, 1 >> 0 >> [1;1;0]^^k *> const 0 = rl (1%nat :: repeat 2%nat k) (const 0).
Proof. intros. cbn [rl]. rewrite rl_rep2. reflexivity. Qed.

(** ** Outer rounds *)
Lemma CO_SW : forall a ds R, CO a (rl ds R) -->* SW (0 >> 1 >> const 0) 0 a ds R.
Proof. intros. unfold CO, SW. follow walkF. finish. Qed.

Lemma OEX : forall a n T, T = (a + 2 * n + 2)%nat -> CO a (rl (repeat 1%nat n) (const 0)) -->* RN T.
Proof.
  intros a n T HT. rewrite <- (app_nil_r (repeat 1%nat n)).
  follow CO_SW. follow SW_pass_iter. apply (SW_exit_out (0 + n) a T). lia.
Qed.
Lemma ones4 : forall n (X : side), [1]^^n *> 1 >> 1 >> 1 >> 1 >> X = [1]^^(n + 4) *> X.
Proof. intros. rewrite <- ones_add. reflexivity. Qed.

Lemma R1_raw : forall a p e os,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) (const 0)) -->*
  CO 3 (1 >> [0;1]^^p *> [1]^^(S a) *> 0 >> rl (S e :: os) (const 0)).
Proof.
  intros. follow CO_SW. follow SW_pass_iter. follow SW_E. execute.
Qed.

Lemma R1 : forall a p e os,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) (const 0)) -->*
  CO 3 (rl (repeat 1%nat p ++ (a + 2) :: S e :: os) (const 0)).
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

Definition Gcy (c y : nat) : nat := hc 1 c (y + 3) + 2 * c + 4.
Definition G (a : nat) : nat := Gcy (a / 3) (a mod 3).

(** outer level maps *)
Fixpoint ho (m a : nat) : nat :=
  match m with
  | 0 => G a
  | S m' => iter (a + 1) (ho m') 3
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

Lemma SW_E0_in : forall y e ds R, SW (const 0) 0 y (S (S e) :: ds) R -->* CI (y + 3) (S e :: ds) R.
Proof.
  intros. follow SW_A_in. unfold CI.
  replace (y + 3)%nat with (S (S (S y))) by lia. finish.
Qed.

Lemma Inner_run : forall c y X, SW (const 0) 0 y (repeat 2%nat (S c)) (0 >> X) -->* CO (Gcy c y) X.
Proof.
  intros. simpl repeat. follow SW_E0_in.
  follow (Chain_in c 1%nat (y + 3)%nat (0 >> X)).
  follow CI_exit. unfold Gcy. replace (hc 1 c (y + 3) + 2 * (1 + c) + 2)%nat with (hc 1 c (y + 3) + 2 * c + 4)%nat by lia.
  finish.
Qed.

Lemma R0_aux : forall a c y e os, (y < 3)%nat -> a = (3 * c + y)%nat ->
  CO a (rl (S (S e) :: os) (const 0)) -->* CO (Gcy c y) (rl (S e :: os) (const 0)).
Proof.
  intros a c y e os Hy Ha. follow CO_SW. follow SW_E. execute.
  follow walkM. execute.
  rewrite ones4.
  replace (a + 4)%nat with (3 * S c + 1 + y)%nat by lia.
  follow EXP. apply Inner_run.
Qed.

Lemma R0 : forall a e os,
  CO a (rl (S (S e) :: os) (const 0)) -->* CO (G a) (rl (S e :: os) (const 0)).
Proof.
  intros. apply (R0_aux a (a / 3) (a mod 3) e os (Nat.mod_upper_bound a 3 ltac:(lia))).
  pose proof (Nat.div_mod a 3); lia.
Qed.

(** ** Outer levels *)
Lemma LV_out : forall m e a os,
  CO a (rl (repeat 1%nat m ++ S e :: os) (const 0)) -->* CO (iter e (ho m) a) (rl (repeat 1%nat (S m) ++ os) (const 0)).
Proof.
  induction m as [| m IHm]; intros e; induction e as [| e IHe]; intros a os.
  - simpl. finish.
  - simpl app. follow R0. follow IHe. rewrite iter_S'. finish.
  - rewrite rep_snoc. finish.
  - follow R1. follow (IHm (a + 1)%nat 3%nat (S e :: os)).
    follow IHe. rewrite iter_S'. finish.
Qed.

Lemma Chain_out : forall n m a os,
  CO a (rl (repeat 1%nat m ++ repeat 2%nat n ++ os) (const 0)) -->* CO (hoc m n a) (rl (repeat 1%nat (m + n) ++ os) (const 0)).
Proof.
  induction n as [| n IHn]; intros m a os.
  - rewrite Nat.add_0_r. finish.
  - simpl repeat. cbn [app]. follow (LV_out m 1%nat a (repeat 2%nat n ++ os)).
    follow IHn. replace (S m + n)%nat with (m + S n)%nat by lia. finish.
Qed.

Local Open Scope nat_scope.

(** ** The mod-3 invariant: every level map is x -> x + 1 (mod 3) *)
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

Lemma G_eq : forall a, G a = (hc 1 (a / 3) (a mod 3 + 3) + 2 * (a / 3) + 4)%nat.
Proof. reflexivity. Qed.

Lemma G_P1 : P1 G.
Proof.
  intros a. rewrite G_eq. destruct (hc_mod (a / 3) 1 (a mod 3 + 3)) as [q Hq].
  exists (q + 2)%nat. rewrite Hq. pose proof (Nat.div_mod a 3). lia.
Qed.

Lemma ho_P1 : forall m, P1 (ho m).
Proof.
  induction m as [| m IHm]; intros x.
  - apply G_P1.
  - destruct (iter_P1 (ho m) IHm (x + 1) 3) as [q Hq]. exists (q + 1)%nat. simpl ho. rewrite Hq. lia.
Qed.

Lemma hoc_mod : forall n m a, exists q, hoc m n a = (a + n + 3 * q)%nat.
Proof.
  induction n as [| n IHn]; intros m a.
  - exists 0%nat. simpl. lia.
  - destruct (ho_P1 m a) as [q Hq]. destruct (IHn (S m) (ho m a)) as [q' Hq'].
    exists (q + q')%nat. simpl hoc. rewrite Hq', Hq. lia.
Qed.

(** ** Boot *)
Lemma boot : c0 -->* CO 3 (rl [] (const S0)).
Proof. unfold CO. cbn [rl]. execute. Qed.

Lemma h_0 : forall x, h 0 x = x + 4.  Proof. reflexivity. Qed.
Lemma h_S : forall m x, h (S m) x = iter (x + 2) (h m) 2.  Proof. reflexivity. Qed.
Lemma hc_0 : forall m x, hc m 0 x = x.  Proof. reflexivity. Qed.
Lemma hc_S : forall m n x, hc m (S n) x = hc (S m) n (h m x).  Proof. reflexivity. Qed.
Lemma ho_0 : forall a, ho 0 a = G a.  Proof. reflexivity. Qed.
Lemma ho_S : forall m a, ho (S m) a = iter (a + 1) (ho m) 3.  Proof. reflexivity. Qed.
Lemma hoc_0 : forall m a, hoc m 0 a = a.  Proof. reflexivity. Qed.
Lemma hoc_S : forall m n a, hoc m (S n) a = hoc (S m) n (ho m a).  Proof. reflexivity. Qed.
Lemma iter_ho0 : forall n x, iter n (ho 0) x = iter n G x.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Opaque h hc G ho hoc.

Lemma LV_out_eq : forall m e a os b, b = iter e (ho m) a ->
  CO a (rl (repeat 1 m ++ S e :: os) (const S0)) -->* CO b (rl (repeat 1 (S m) ++ os) (const S0)).
Proof. intros. subst b. apply LV_out. Qed.

Lemma Chain_out_eq : forall n m a os b, b = hoc m n a ->
  CO a (rl (repeat 1 m ++ repeat 2 n ++ os) (const S0)) -->* CO b (rl (repeat 1 (m + n) ++ os) (const S0)).
Proof. intros. subst b. apply Chain_out. Qed.



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
Lemma iter_h0 : forall n y, iter n (h 0) y = y + 4 * n.
Proof. induction n; intros; simpl. - lia. - rewrite IHn, h_0. lia. Qed.

Lemma h1_eq : forall x, h 1 x = 4 * x + 10.
Proof. intros. rewrite h_S, iter_h0. lia. Qed.

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

Lemma G_cy : forall c y, y < 3 -> G (3 * c + y) = hc 1 c (y + 3) + 2 * c + 4.
Proof.
  intros c y Hy. rewrite G_eq.
  replace ((3 * c + y) / 3) with c by (apply Nat.div_unique with y; lia).
  replace ((3 * c + y) mod 3) with y by (apply Nat.mod_unique with c; lia).
  reflexivity.
Qed.

Lemma G_ge : forall a, a + 7 <= G a.
Proof.
  intros a. rewrite (Nat.div_mod a 3) at 1 by lia. rewrite G_eq.
  pose proof (hc_ge (a / 3) 1 (a mod 3 + 3)). lia.
Qed.

Lemma G_dom : forall n z, 6 * n <= z -> 6 * f_omega n <= G z.
Proof.
  intros n z Hz. pose proof (G_ge z) as Hg.
  destruct n as [| [| n']].
  - change (f_omega 0) with 1. lia.
  - change (f_omega 1) with 2. lia.
  - set (n := S (S n')) in *.
    pose proof (Nat.div_mod z 3 ltac:(lia)) as Hdm. pose proof (Nat.mod_upper_bound z 3 ltac:(lia)) as Hmb.
    set (c := z / 3) in *. set (y := z mod 3) in *.
    assert (Hc : 2 * n <= c) by lia.
    destruct c as [| c'] eqn:Ec; [lia |].
    rewrite Hdm, (G_cy (S c') y Hmb), hc_last.
    replace (1 + c') with (S c') by lia.
    pose proof (hc_ge c' 1 (y + 3)) as HX.
    pose proof (h_dom (S c') (2 * n) (hc 1 c' (y + 3)) ltac:(lia)) as Hh.
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
  - rewrite ho_S. pose proof (iter_linK (ho m) 6 IHm (y + 1) 3). lia.
Qed.

Lemma ho_dom : forall m n z, 6 * n <= z -> 6 * f_wk m n <= ho m z.
Proof.
  apply (transfer 6 3 f_wk ho ltac:(lia) f_wk_S).
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

(** the inner value G 28 = hc 1 9 4 + 22 already exceeds 8 f_10(2) *)
Lemma hc_tower_base : 2 * f 3 2 + 4 <= hc 1 2 4.
Proof.
  rewrite hc_last, hc_S, hc_0, h1_eq.
  replace (1 + 1) with 2 by reflexivity. replace (4 * 4 + 10) with 26 by reflexivity.
  pose proof (h_dom 2 9 26 ltac:(lia)) as Hh. rewrite f2_eq in Hh.
  assert (Hf3 : f 3 2 = 2048).
  { rewrite f_S_2, !f2_eq. reflexivity. }
  assert (H9 : 9 * 2 ^ 9 = 4608) by reflexivity.
  rewrite Hf3. rewrite H9 in Hh. lia.
Qed.

Lemma hc_tower_step : forall n, 2 <= n -> 2 * f (S n) 2 + 4 <= hc 1 n 4 ->
  8 * f (S (S n)) 2 <= hc 1 (S n) 4.
Proof.
  intros n Hn IHn. rewrite hc_last. replace (1 + n) with (S n) by lia.
  pose proof (h_dom (S n) (f (S n) 2 + 2) (hc 1 n 4) ltac:(lia)) as Hh.
  pose proof (f_plus2 (S n) (f (S n) 2) ltac:(lia)) as Hp.
  assert (E : f (S n) (f (S n) 2) = f (S (S n)) 2) by reflexivity.
  lia.
Qed.

Lemma hc_tower : forall n, 2 <= n -> 2 * f (S n) 2 + 4 <= hc 1 n 4.
Proof.
  intros n Hn. induction Hn as [| m Hm IH].
  - exact hc_tower_base.
  - pose proof (hc_tower_step m Hm IH). pose proof (f_gt (S (S m)) 2 ltac:(lia)). lia.
Qed.

Lemma hc9 : 8 * f 10 2 <= hc 1 9 4.
Proof.
  exact (hc_tower_step 8 ltac:(lia) (hc_tower 8 ltac:(lia))).
Qed.

Lemma G3 : G 3 = 28.
Proof.
  change (G 3) with (G (3 * 1 + 0)). rewrite (G_cy 1 0 ltac:(lia)).
  rewrite hc_S, hc_0, h1_eq. reflexivity.
Qed.

Lemma G28 : 8 * f 10 2 <= G 28.
Proof.
  change (G 28) with (G (3 * 9 + 1)). rewrite (G_cy 9 1 ltac:(lia)). change (1 + 3) with 4. pose proof hc9. lia.
Qed.

Lemma hoc_last : forall n m x, hoc m (S n) x = ho (m + n) (hoc m n x).
Proof.
  induction n as [| n IHn]; intros m x.
  - rewrite hoc_S, !hoc_0, Nat.add_0_r. reflexivity.
  - rewrite hoc_S, IHn, hoc_S. f_equal. lia.
Qed.

(** ** The run from the blank tape *)
Lemma a1_eq : iter 4 (ho 0) 3 = iter 3 G 28.
Proof. rewrite iter_ho0, iter_S', G3. reflexivity. Qed.

Lemma K_gen : exists k, iter 3 G 28 + 8 = 3 * S k.
Proof.
  destruct (iter_P1 G G_P1 3 28) as [q Hq]. exists (12 + q). rewrite Hq. lia.
Qed.

Lemma C_gen : forall k, exists c, hoc 2 k 28 + 2 * (k + 2) + 2 = 3 * c + 1.
Proof.
  intros k. destruct (hoc_mod k 2 28) as [q Hq]. exists (k + 11 + q). rewrite Hq. lia.
Qed.

Lemma run_gen : forall a1 k a2 c,
  a1 = iter 3 G 28 -> a1 + 8 = 3 * S k -> a2 = hoc 2 k 28 -> a2 + 2 * (k + 2) + 2 = 3 * c + 1 ->
  c0 -->* Hh c.
Proof.
  intros a1 k a2 c Ha1 Hk Ha2 Hc.
  assert (Ha1' : a1 = iter 4 (ho 0) 3) by (rewrite a1_eq; exact Ha1).
  follow boot.
  follow (OEX 3 0 5 eq_refl).
  follow (RF_A 1). rewrite rfA_rl.
  follow (R1 0 1 0 []).
  follow (R1 3 0 0 [1]).
  follow (LV_out_eq 0 4 3 [1;1] a1 Ha1').
  follow (OEX a1 3 (3 * S k) ltac:(lia)).
  follow (RF_B (S k)). rewrite rfB_rl.
  follow (R1 0 0 0 (repeat 2 k)).
  follow (R0 3 0 (1 :: repeat 2 k)).
  rewrite G3.
  replace (1 :: 1 :: repeat 2 k) with (repeat 1 2 ++ repeat 2 k ++ []) by (rewrite app_nil_r; reflexivity).
  follow (Chain_out_eq k 2 28 [] a2 Ha2).
  rewrite app_nil_r.
  follow (OEX a2 (2 + k) (3 * c + 1) ltac:(lia)).
  apply RF_halt.
Qed.

Lemma run : exists k a2 c,
  iter 3 G 28 + 8 = 3 * S k /\ a2 = hoc 2 k 28 /\ a2 + 2 * (k + 2) + 2 = 3 * c + 1 /\ c0 -->* Hh c.
Proof.
  destruct K_gen as [k Hk]. destruct (C_gen k) as [c Hc].
  exists k, (hoc 2 k 28), c.
  split; [exact Hk |]. split; [reflexivity |]. split; [exact Hc |].
  exact (run_gen (iter 3 G 28) k (hoc 2 k 28) c eq_refl Hk eq_refl Hc).
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct run as (k & a2 & c & _ & _ & _ & Hrun).
  destruct (with_counter Hrun) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts, Hh_halted.
Qed.

Lemma ones_Hh : forall c, ones (Hh c) (2 * c + 2).
Proof.
  intros c. exists RR, (@nil Sym), ([S1; S0] ++ [S1; S1; S0]^^c), S1.
  split.
  - unfold Hh. rewrite Str_app_assoc. reflexivity.
  - rewrite count1_app, count1_pow. cbn [count1 sym_val]. lia.
Qed.

(** ** Final bound: sigma > f_(omega*2)(f_omega(f_omega(f_10(2)))) *)
Lemma iter3 : forall (g : nat -> nat) x, iter 3 g x = g (g (g x)).
Proof. reflexivity. Qed.

Lemma iter2 : forall (g : nat -> nat) x, iter 2 g x = g (g x).
Proof. reflexivity. Qed.

Lemma bound_gen : forall a1 k a2 c,
  a1 = iter 3 G 28 -> a1 + 8 = 3 * S k -> a2 = hoc 2 k 28 -> a2 + 2 * (k + 2) + 2 = 3 * c + 1 ->
  f_w2 (f_omega (f_omega (f 10 2))) < 2 * c + 2.
Proof.
  intros a1 k a2 c Ha1 Hk Ha2 Hc.
  rewrite iter3 in Ha1.
  pose proof G28 as H0.
  pose proof (G_dom (f 10 2) (G 28) ltac:(lia)) as H1.
  pose proof (G_dom (f_omega (f 10 2)) (G (G 28)) ltac:(lia)) as H2.
  assert (HY : 2 * f_omega (f_omega (f 10 2)) <= S k) by lia.
  destruct k as [| k'].
  - pose proof (f_omega_id (f_omega (f 10 2))). pose proof (f_omega_id (f 10 2)).
    pose proof (f_gt 10 2 ltac:(lia)). lia.
  - rewrite hoc_last in Ha2.
    pose proof (hoc_ge k' 2 28) as Hb.
    pose proof (ho_dom (2 + k') (2 + k') (hoc 2 k' 28) ltac:(lia)) as H3.
    assert (H4 : f_w2 (2 + k') = f_wk (2 + k') (2 + k')) by reflexivity.
    pose proof (f_w2_mono (f_omega (f_omega (f 10 2))) (2 + k') ltac:(lia)) as H5.
    lia.
Qed.

Theorem score_exact : exists k a2 c cfg,
  iter 3 G 28 + 8 = 3 * S k /\ a2 = hoc 2 k 28 /\ a2 + 2 * (k + 2) + 2 = 3 * c + 1 /\
  c0 -->* cfg /\ halted tm cfg /\ ones cfg (2 * c + 2).
Proof.
  destruct run as (k & a2 & c & Hk & Ha2 & Hc & Hrun).
  exists k, a2, c, (Hh c).
  split; [exact Hk |]. split; [exact Ha2 |]. split; [exact Hc |]. split; [exact Hrun |].
  split; [apply Hh_halted | apply ones_Hh].
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_w2 (f_omega (f_omega (f 10 2))) < N.
Proof.
  destruct run as (k & a2 & c & Hk & Ha2 & Hc & Hrun).
  exists (Hh c), (2 * c + 2).
  split; [exact Hrun |]. split; [apply Hh_halted |]. split; [apply ones_Hh |].
  exact (bound_gen (iter 3 G 28) k a2 c eq_refl Hk Ha2 Hc).
Qed.

(** ** Comparison with the other bars (same FGH definitions as BB19_JZ19.v and BB18_229round_fw3.v) *)
Lemma Y_big : 2048 <= f_omega (f_omega (f 10 2)).
Proof.
  pose proof (f_omega_id (f_omega (f 10 2))). pose proof (f_omega_id (f 10 2)).
  pose proof (f_level_mono 7 3 2 ltac:(lia)) as L. replace (7 + 3) with 10 in L by reflexivity.
  assert (Hf3 : f 3 2 = 2048) by (rewrite f_S_2, !f2_eq; reflexivity).
  lia.
Qed.

Lemma J19_dom : forall Y, 8 <= Y -> f_wk 7 (f_wk 7 5) <= f_w2 Y.
Proof.
  intros Y HY. unfold f_w2.
  pose proof (f_wk_level_mono (Y - 8) 8 Y ltac:(lia)) as L1. replace (Y - 8 + 8) with Y in L1 by lia.
  rewrite (f_wk_S 7 Y) in L1.
  pose proof (iter_mono_n (f_wk 7) (f_wk_id 7) 2 Y Y ltac:(lia)) as L2.
  pose proof (iter_mono_x (f_wk 7) (f_wk_mono 7) 2 5 Y ltac:(lia)) as L3.
  rewrite (iter2 (f_wk 7) Y) in L2, L3. rewrite (iter2 (f_wk 7) 5) in L3. lia.
Qed.

Lemma M18_dom : forall Y, 229 <= Y -> iter 229 (f_wk 3) 9 <= f_w2 Y.
Proof.
  intros Y HY. unfold f_w2.
  pose proof (f_wk_level_mono (Y - 4) 4 Y ltac:(lia)) as L1. replace (Y - 4 + 4) with Y in L1 by lia.
  rewrite (f_wk_S 3 Y) in L1.
  pose proof (iter_mono_n (f_wk 3) (f_wk_id 3) 229 Y Y ltac:(lia)) as L2.
  pose proof (iter_mono_x (f_wk 3) (f_wk_mono 3) 229 9 Y ltac:(lia)) as L3.
  lia.
Qed.

Theorem beats_J19 : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_wk 7 (f_wk 7 5) < N.
Proof.
  destruct sigma_lower_bound as (c & N & H1 & H2 & H3 & H4).
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof (J19_dom (f_omega (f_omega (f 10 2))) ltac:(pose proof Y_big; lia)). lia.
Qed.

Theorem beats_M18_229 : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ iter 229 (f_wk 3) 9 < N.
Proof.
  destruct sigma_lower_bound as (c & N & H1 & H2 & H3 & H4).
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof (M18_dom (f_omega (f_omega (f 10 2))) ltac:(pose proof Y_big; lia)). lia.
Qed.

Print Assumptions halt.
Print Assumptions score_exact.
Print Assumptions sigma_lower_bound.
Print Assumptions beats_J19.
Print Assumptions beats_M18_229.
