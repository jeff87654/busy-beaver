(** * 18-state BB(18) champion J18_w2_C_tnf (A-started TNF of C-booted machine) halts,
      with sigma > f_(omega*2)(2 * f_omega^9(35)) > f_(omega*2)(2 * f_omega^8(f_3(17))).

    J18_w2_C_tnf = 0LB1LF_0RC1LB_0RD1RM_1LE0RN_1LF1LE_1LG0LE_1RH1RP_1RI1RH_0LJ1RA_1LK1LJ_0LL1LJ_1RM1RC_0RM0RH_1LE1RO_1RZ1RD_0LF0RQ_0LH1RR_0LF1RP

    Main results (no axioms):
      [halt]              : halts tm c0
      [score_exact]       : exact halting configuration and recurrence equations
      [sigma_lower_bound] : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
                            f_w2 (2 * iter 9 f_omega 35) < N /\ f_w2 (2 * iter 8 f_omega (f 3 17)) < N *)

From BB8 Require Import Individual182.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 0LB1LF_0RC1LB_0RD1RM_1LE0RN_1LF1LE_1LG0LE_1RH1RP_1RI1RH_0LJ1RA_1LK1LJ_0LL1LJ_1RM1RC_0RM0RH_1LE1RO_1RZ1RD_0LF0RQ_0LH1RR_0LF1RP *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (0, TM.L, B)   | A, 1 => Some (1, TM.L, F)
  | B, 0 => Some (0, TM.R, C)   | B, 1 => Some (1, TM.L, B)
  | C, 0 => Some (0, TM.R, D)   | C, 1 => Some (1, TM.R, M)
  | D, 0 => Some (1, TM.L, E)   | D, 1 => Some (0, TM.R, N)
  | E, 0 => Some (1, TM.L, F)   | E, 1 => Some (1, TM.L, E)
  | F, 0 => Some (1, TM.L, G)   | F, 1 => Some (0, TM.L, E)
  | G, 0 => Some (1, TM.R, H)   | G, 1 => Some (1, TM.R, P)
  | H, 0 => Some (1, TM.R, I)   | H, 1 => Some (1, TM.R, H)
  | I, 0 => Some (0, TM.L, J)   | I, 1 => Some (1, TM.R, A)
  | J, 0 => Some (1, TM.L, K)   | J, 1 => Some (1, TM.L, J)
  | K, 0 => Some (0, TM.L, L)   | K, 1 => Some (1, TM.L, J)
  | L, 0 => Some (1, TM.R, M)   | L, 1 => Some (1, TM.R, C)
  | M, 0 => Some (0, TM.R, M)   | M, 1 => Some (0, TM.R, H)
  | N, 0 => Some (1, TM.L, E)   | N, 1 => Some (1, TM.R, O)
  | O, 0 => None                | O, 1 => Some (1, TM.R, D)
  | P, 0 => Some (0, TM.L, F)   | P, 1 => Some (0, TM.R, QQ)
  | QQ, 0 => Some (0, TM.L, H)  | QQ, 1 => Some (1, TM.R, RR)
  | RR, 0 => Some (0, TM.L, F)  | RR, 1 => Some (1, TM.R, P)
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

(** ** Walks (in TNF state labeling: H=F, E=G, B=D, J=I, F=A, G=H, P=M, D=R) *)
Lemma walkF : forall n l r, l {{H}}> [1]^^n *> r -->* [1]^^n *> l {{H}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkG : forall n l r, [1]^^n *> l <{{E}} r -->* l <{{E}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkD : forall n l r, [1]^^n *> l <{{B}} r -->* l <{{B}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkI : forall n l r, [1]^^n *> l <{{J}} r -->* l <{{J}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma zigGA : forall n l r, [0;1]^^n *> l <{{E}} r -->* l <{{E}} [0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma zigIJ : forall n l r, [0;1]^^n *> l <{{J}} r -->* l <{{J}} [1;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triMNO : forall n l r, l {{P}}> [1;1;1]^^n *> r -->* [1;1;0]^^n *> l {{P}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triRPQ : forall n l r, l {{D}}> [1;1;1]^^n *> r -->* [1;1;0]^^n *> l {{D}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triAG : forall n l r, [1;1;0]^^n *> l <{{F}} r -->* l <{{F}} [1;1;0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triIJI : forall n l r, [1;0;1]^^n *> l <{{J}} r -->* l <{{J}} [1;1;1]^^n *> r.
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

(** Sweep configuration *)
Definition SW (l : side) (j y : nat) (ds : list nat) (R : side) : Q * tape :=
  ([1]^^y *> [0;1]^^j *> 0 >> l) {{H}}> (0 >> rl ds R).

(** inner boundary *)
Definition CI (x : nat) (ds : list nat) (R : side) : Q * tape :=
  const 0 <{{G}} ([1]^^x *> 0 >> rl ds R).

(** outer boundary *)
Definition CO (a : nat) (Rr : side) : Q * tape :=
  (0 >> 0 >> 1 >> const 0) {{H}}> ([1]^^a *> 0 >> Rr).

(** outer exhaustion *)
Definition EX (B : nat) : Q * tape :=
  (0 >> 1 >> const 0) {{D}}> ([1]^^B *> const 0).

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
  SW l j y (S (S e) :: ds) R -->* l <{{F}} (1 >> [0;1]^^j *> [1]^^(S y) *> 0 >> rl (S e :: ds) R).
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

Lemma SW_exit_in : forall j y R, SW (const 0) j y [] (0 >> R) -->* CO (y + 2 * j + 1) R.
Proof.
  intros. unfold SW. cbn [rl].
  execute.
  follow walkI.
  follow zigIJ.
  execute.
  rewrite pairs_ones. unfold CO. finish.
Qed.

Lemma SW_exit_out : forall j y B, B = y + 2 * j + 2 ->
  SW (0 >> 1 >> const 0) j y [] (const 0) -->* EX B.
Proof.
  intros j y B HB. unfold SW, EX. cbn [rl].
  replace B with (S (y + 2 * j + 1)) by lia.
  execute.
  follow walkI.
  follow zigIJ.
  rewrite pairs_ones.
  execute.
Qed.

Lemma CI_SW : forall x ds R, CI x ds R -->* SW (const 0) 0 (S x) ds R.
Proof.
  intros. unfold CI, SW.
  execute. follow walkF. finish_norm.
Qed.

Lemma SW_A_in : forall j y e ds R,
  SW (const 0) j y (S (S e) :: ds) R -->*
  const 0 <{{G}} (1 >> 1 >> [0;1]^^j *> [1]^^(S y) *> 0 >> rl (S e :: ds) R).
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

(** ** 3-State Boundary-Shifting Expansion (P, QQ, RR) *)
Lemma EXP_0 : forall c X,
  (1 >> 1 >> 0 >> 1 >> const 0) {{P}}> ([1]^^(3 * c) *> 0 >> X) -->* CI 2 (repeat 2%nat (S c)) (0 >> X).
Proof.
  intros c X. unfold CI. rewrite rl_rep2, <- pow111.
  follow triMNO. execute. follow triAG. execute.
Qed.

Lemma EXP_1 : forall c X,
  (1 >> 1 >> 0 >> 1 >> const 0) {{P}}> ([1]^^(3 * c + 1) *> 0 >> X) -->* CO (3 * c + 5) X.
Proof.
  intros c X. unfold CO.
  replace (3 * c + 5)%nat with (S (S (S (S (S (3 * c)))))) by lia.
  rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  follow triMNO. execute.
  rewrite (align_lpow 1 [1;0]). simpl app.
  execute. follow triIJI.
  rewrite pow111, !one_shift.
  execute.
Qed.

Lemma EXP_2 : forall c X,
  (1 >> 1 >> 0 >> 1 >> const 0) {{P}}> ([1]^^(3 * c + 2) *> 0 >> X) -->* CI 2 (repeat 2%nat (S c) ++ [1%nat]) (0 >> X).
Proof.
  intros c X. unfold CI. rewrite rl_app, rl_rep2, <- ones_add, <- pow111. cbn [rl lpow app Str_app].
  follow triMNO. execute. follow triAG. execute.
Qed.

(** ** 3-State Left-to-Right Refill (N, O, D) *)
Definition Hc (k : nat) : Q * tape := (1 >> 0 >> [1;1;0]^^k *> 0 >> 1 >> const 0) {{O}}> (const 0).

Lemma Hc_halted : forall k, halted tm (Hc k).
Proof. intros. reflexivity. Qed.

Lemma RF_halt : forall k, EX (3 * k + 2) -->* Hc k.
Proof.
  intros k. unfold EX, Hc. rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  follow triRPQ. execute.
Qed.

Lemma tail2 : forall k, [1;1;0]^^k *> 1 >> 1 >> const 0 = [1;1;0]^^(S k) *> const 0.
Proof.
  induction k; simpl. - rewrite <- const_unfold. reflexivity. - rewrite IHk. reflexivity.
Qed.

Lemma RF_1 : forall k, EX (3 * S k + 1) -->* CO 10 (rl (repeat 2%nat (S k)) (const 0)).
Proof.
  intros k. unfold EX, CO. rewrite rl_rep2, <- tail2.
  replace (3 * S k + 1)%nat with (3 + (3 * k + 1))%nat by lia.
  rewrite <- !ones_add, <- pow111. cbn [lpow app Str_app].
  execute. follow triRPQ. execute. follow triAG.
  execute.
Qed.

Lemma RF_0 : forall k, EX (3 * S (S k)) -->* CO 10 (rl (repeat 2%nat k ++ [4%nat]) (const 0)).
Proof.
  intros k. unfold EX, CO. rewrite rl_app, rl_rep2.
  replace (3 * S (S k))%nat with (3 + (3 * k + 3))%nat by lia.
  rewrite <- !ones_add, <- pow111. cbn [rl lpow app Str_app].
  execute. follow triRPQ. execute. follow triAG.
  execute.
Qed.

(** ** Outer rounds *)
Lemma CO_SW : forall a ds R, CO a (rl ds R) -->* SW (0 >> 1 >> const 0) 0 a ds R.
Proof. intros. unfold CO, SW. follow walkF. finish. Qed.

Lemma OEX : forall a n B, B = a + 2 * n + 2 -> CO a (rl (repeat 1%nat n) (const 0)) -->* EX B.
Proof.
  intros a n B HB. rewrite <- (app_nil_r (repeat 1%nat n)).
  follow CO_SW. follow SW_pass_iter. apply (SW_exit_out (0 + n) a B). lia.
Qed.

Lemma R1_raw : forall a p e os,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) (const 0)) -->*
  CO 6 (1 >> [0;1]^^p *> [1]^^(S a) *> 0 >> rl (S e :: os) (const 0)).
Proof.
  intros. follow CO_SW. follow SW_pass_iter. follow SW_E. execute.
Qed.

Lemma R1 : forall a p e os,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) (const 0)) -->*
  CO 6 (rl (repeat 1%nat p ++ (a + 2) :: S e :: os) (const 0)).
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

Definition G0 (c : nat) : nat := hc 1 c 6 + 2 * c + 4.
Definition Gcy (c y : nat) : nat :=
  match y with
  | 0 => G0 c
  | 1 => 3 * c + 5
  | _ => G0 c + 2
  end.
Definition G (a : nat) : nat := Gcy (a / 3) (a mod 3).

Fixpoint ho (m a : nat) : nat :=
  match m with
  | 0 => G a
  | S m' => iter (a + 1) (ho m') 6
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

Lemma Inner_run_0 : forall c X,
  CI 2 (repeat 2%nat (S c)) (0 >> X) -->* CO (G0 c) X.
Proof.
  intros c X. simpl repeat.
  follow CI_E0.
  change (1%nat :: repeat 2%nat c) with (repeat 1%nat 1 ++ repeat 2%nat c).
  follow (Chain_in c 1%nat 6%nat (0 >> X)).
  follow CI_exit. unfold G0.
  replace (hc 1 c 6 + 2 * (1 + c) + 2)%nat with (hc 1 c 6 + 2 * c + 4)%nat by lia.
  finish.
Qed.

Lemma CI_app : forall x a b R, CI x (a ++ b) R = CI x a (rl b R).
Proof. intros. unfold CI. rewrite rl_app. reflexivity. Qed.

Lemma Inner_run_2 : forall c X,
  CI 2 (repeat 2%nat (S c) ++ [1%nat]) (0 >> X) -->* CO (G0 c + 2) X.
Proof.
  intros c X. rewrite CI_app. simpl repeat.
  follow CI_E0.
  change (1%nat :: repeat 2%nat c) with (repeat 1%nat 1 ++ repeat 2%nat c).
  follow (Chain_in c 1%nat 6%nat (rl [1%nat] (0 >> X))).
  rewrite <- CI_app, rep_snoc, app_nil_r.
  follow CI_exit. unfold G0.
  replace (hc 1 c 6 + 2 * S (1 + c) + 2)%nat with (hc 1 c 6 + 2 * c + 4 + 2)%nat by lia.
  finish.
Qed.

Lemma R0_aux : forall a c y e os, (y < 3)%nat -> a = (3 * c + y)%nat ->
  CO a (rl (S (S e) :: os) (const 0)) -->* CO (Gcy c y) (rl (S e :: os) (const 0)).
Proof.
  intros a c y e os Hy Ha. follow CO_SW. follow SW_E.
  cbn [lpow app Str_app].
  step. step. step. step. step.
  subst a.
  destruct y as [| [| [| y]]]; try lia; cbn [Gcy].
  - replace (3 * c + 0)%nat with (3 * c)%nat by lia.
    follow EXP_0. apply Inner_run_0.
  - follow EXP_1. finish.
  - follow EXP_2. apply Inner_run_2.
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
  - follow R1. follow (IHm (a + 1)%nat 6%nat (S e :: os)).
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

Lemma G0_mod : forall c, exists q, G0 c = (3 * c + 1 + 3 * q)%nat.
Proof.
  intros c. unfold G0. destruct (hc_mod c 1 6) as [q Hq].
  exists (q + 3)%nat. lia.
Qed.

Lemma G0_mod1 : forall c, exists c1, G0 c = 3 * c1 + 1.
Proof.
  intros c. destruct (G0_mod c) as [q Hq]. exists (c + q). lia.
Qed.

Lemma Gcy_mod : forall c y, y < 3 -> exists q, Gcy c y = (3 * c + y + 1 + 3 * q)%nat.
Proof.
  intros c y Hy. destruct (G0_mod c) as [q Hq].
  destruct y as [| [| [| y]]]; try lia; cbn [Gcy].
  - exists q. lia.
  - exists 1%nat. lia.
  - exists q. lia.
Qed.

Lemma G_P1 : P1 G.
Proof.
  intros a. unfold G.
  destruct (Gcy_mod (a / 3) (a mod 3) (Nat.mod_upper_bound a 3 ltac:(lia))) as [q Hq].
  exists q. pose proof (Nat.div_mod a 3 ltac:(lia)). lia.
Qed.

Lemma ho_P1 : forall m, P1 (ho m).
Proof.
  induction m as [| m IHm]; intros x.
  - apply G_P1.
  - destruct (iter_P1 (ho m) IHm (x + 1) 6) as [q Hq]. exists (q + 2)%nat. simpl ho. rewrite Hq. lia.
Qed.

Lemma hoc_mod : forall n m a, exists q, hoc m n a = (a + n + 3 * q)%nat.
Proof.
  induction n as [| n IHn]; intros m a.
  - exists 0%nat. simpl. lia.
  - destruct (ho_P1 m a) as [q Hq]. destruct (IHn (S m) (ho m a)) as [q' Hq'].
    exists (q + q')%nat. simpl hoc. rewrite Hq', Hq. lia.
Qed.

(** ** The run from the blank tape *)
Lemma boot : c0 -->* CO 5 (rl [] (const S0)).
Proof. unfold CO. cbn [rl]. execute. Qed.

Lemma h_0 : forall x, h 0 x = x + 4.  Proof. reflexivity. Qed.
Lemma h_S : forall m x, h (S m) x = iter (x + 2) (h m) 2.  Proof. reflexivity. Qed.
Lemma hc_0 : forall m x, hc m 0 x = x.  Proof. reflexivity. Qed.
Lemma hc_S : forall m n x, hc m (S n) x = hc (S m) n (h m x).  Proof. reflexivity. Qed.
Lemma G0_eq : forall c, G0 c = hc 1 c 6 + 2 * c + 4.  Proof. reflexivity. Qed.
Lemma G_eq : forall a, G a = Gcy (a / 3) (a mod 3).  Proof. reflexivity. Qed.
Lemma ho_0 : forall a, ho 0 a = G a.  Proof. reflexivity. Qed.
Lemma ho_S : forall m a, ho (S m) a = iter (a + 1) (ho m) 6.  Proof. reflexivity. Qed.
Lemma hoc_0 : forall m a, hoc m 0 a = a.  Proof. reflexivity. Qed.
Lemma hoc_S : forall m n a, hoc m (S n) a = hoc (S m) n (ho m a).  Proof. reflexivity. Qed.

Opaque h hc G0 G ho hoc.
Strategy opaque [h hc G0 G ho hoc].

Lemma K_gen : forall a1, a1 = hoc 0 2 10 -> exists k, a1 + 6 = 3 * S (S k).
Proof.
  intros a1 Ha. destruct (hoc_mod 2 0 10) as [q Hq].
  exists (q + 4). subst. lia.
Qed.

Lemma J_gen : forall k b a2, b = hoc 0 k 10 -> a2 = iter 3 (ho k) b -> exists j, a2 + 2 * S k + 2 = 3 * j + 2.
Proof.
  intros k b a2 Hb Ha2.
  destruct (hoc_mod k 0 10) as [q1 H1].
  destruct (iter_P1 (ho k) (ho_P1 k) 3 b) as [q2 H2].
  exists (k + q1 + q2 + 5). subst. lia.
Qed.

Lemma LV_out_eq : forall m e a os b, b = iter e (ho m) a ->
  CO a (rl (repeat 1 m ++ S e :: os) (const S0)) -->* CO b (rl (repeat 1 (S m) ++ os) (const S0)).
Proof. intros. subst b. apply LV_out. Qed.

Lemma Chain_out_eq : forall n m a os b, b = hoc m n a ->
  CO a (rl (repeat 1 m ++ repeat 2 n ++ os) (const S0)) -->* CO b (rl (repeat 1 (m + n) ++ os) (const S0)).
Proof. intros. subst b. apply Chain_out. Qed.

Lemma run_gen : forall a1 k b a2 j,
  a1 = hoc 0 2 10 -> a1 + 6 = 3 * S (S k) ->
  b = hoc 0 k 10 -> a2 = iter 3 (ho k) b -> a2 + 2 * S k + 2 = 3 * j + 2 ->
  c0 -->* Hc j.
Proof.
  intros a1 k b a2 j Ha1 Hk Hb Ha2 Hj.
  follow boot.
  follow (OEX 5 0 7 eq_refl).
  follow (RF_1 1).
  rewrite <- (app_nil_r (repeat 2 2)).
  follow (Chain_out_eq 2 0 10 [] a1 Ha1).
  rewrite app_nil_r.
  follow (OEX a1 2 (3 * S (S k)) ltac:(lia)).
  follow (RF_0 k).
  follow (Chain_out_eq k 0 10 [4] b Hb).
  follow (LV_out_eq k 3 b [] a2 Ha2).
  rewrite app_nil_r.
  follow (OEX a2 (S k) (3 * j + 2) ltac:(lia)).
  apply RF_halt.
Qed.

Lemma run : exists k a2 j,
  hoc 0 2 10 + 6 = 3 * S (S k) /\ a2 = iter 3 (ho k) (hoc 0 k 10) /\
  a2 + 2 * S k + 2 = 3 * j + 2 /\ c0 -->* Hc j.
Proof.
  destruct (K_gen (hoc 0 2 10) eq_refl) as [k Hk].
  destruct (J_gen k (hoc 0 k 10) (iter 3 (ho k) (hoc 0 k 10)) eq_refl eq_refl) as [j Hj].
  exists k, (iter 3 (ho k) (hoc 0 k 10)), j.
  split; [exact Hk |]. split; [reflexivity |]. split; [exact Hj |].
  exact (run_gen (hoc 0 2 10) k (hoc 0 k 10) (iter 3 (ho k) (hoc 0 k 10)) j
           eq_refl Hk eq_refl eq_refl Hj).
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct run as (k & a2 & j & _ & _ & _ & Hrun).
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

Lemma ones_Hc : forall j, ones (Hc j) (2 * j + 2).
Proof.
  intros j. exists O, ([S1; S0] ++ [S1; S1; S0]^^j ++ [S0; S1]), (@nil Sym), S0.
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

Lemma G_cy : forall c y, y < 3 -> G (3 * c + y) = Gcy c y.
Proof.
  intros c y Hy. rewrite G_eq.
  replace ((3 * c + y) / 3) with c by (apply Nat.div_unique with y; lia).
  replace ((3 * c + y) mod 3) with y by (apply Nat.mod_unique with c; lia).
  reflexivity.
Qed.

Lemma G0_ge : forall c, 3 * c + 10 <= G0 c.
Proof.
  intros c. rewrite G0_eq. pose proof (hc_ge c 1 6). lia.
Qed.

Lemma G_ge : forall a, a + 4 <= G a.
Proof.
  intros a. rewrite (Nat.div_mod a 3) at 1 by lia. rewrite G_eq.
  pose proof (Nat.mod_upper_bound a 3 ltac:(lia)) as Hy.
  set (c := a / 3). set (y := a mod 3) in *.
  pose proof (G0_ge c).
  destruct y as [| [| [| y']]]; try lia; cbn [Gcy]; lia.
Qed.

Lemma G0_dom : forall n c, 2 * n <= c -> 6 * f_omega n <= G0 c.
Proof.
  intros n c Hc. pose proof (G0_ge c) as Hg0.
  destruct n as [| [| n']].
  - change (f_omega 0) with 1. lia.
  - change (f_omega 1) with 2. lia.
  - set (n := S (S n')) in *.
    destruct c as [| c'] eqn:Ec; [lia |].
    rewrite G0_eq, hc_last.
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

Lemma GG_dom : forall n z, 6 * n <= z -> 6 * f_omega n <= G (G z).
Proof.
  intros n z Hz.
  pose proof (Nat.div_mod z 3 ltac:(lia)) as Hdm.
  pose proof (Nat.mod_upper_bound z 3 ltac:(lia)) as Hy.
  set (c := z / 3) in *. set (y := z mod 3) in *.
  assert (Hc : 2 * n <= c) by lia.
  rewrite Hdm, (G_cy c y Hy).
  destruct y as [| [| [| y']]]; try lia; cbn [Gcy].
  - pose proof (G0_dom n c Hc). pose proof (G_ge (G0 c)). lia.
  - replace (3 * c + 5) with (3 * S c + 2) by lia.
    rewrite (G_cy (S c) 2 ltac:(lia)). cbn [Gcy].
    pose proof (G0_dom n (S c) ltac:(lia)). lia.
  - pose proof (G0_dom n c Hc). pose proof (G_ge (G0 c + 2)). lia.
Qed.

Lemma iter_2n : forall n (g : nat -> nat) x, iter (2 * n) g x = iter n (fun y => g (g y)) x.
Proof.
  induction n as [| n IHn]; intros g x.
  - reflexivity.
  - replace (2 * S n) with (S (S (2 * n))) by lia.
    cbn [iter]. rewrite IHn. reflexivity.
Qed.

Lemma ho0_ge : forall y, y + 4 <= ho 0 y.
Proof. intros y. rewrite ho_0. apply G_ge. Qed.

Lemma ho_ge : forall m y, y + 4 <= ho m y.
Proof.
  induction m as [| m IHm]; intros y.
  - apply ho0_ge.
  - rewrite ho_S. pose proof (iter_linK (ho m) 4 IHm (y + 1) 6). lia.
Qed.

Lemma ho_S_ge : forall m y, y + 6 <= ho (S m) y.
Proof.
  intros m y. rewrite ho_S. pose proof (iter_linK (ho m) 4 (ho_ge m) (y + 1) 6). lia.
Qed.

Lemma ho1_dom : forall n z, 6 * n <= z -> 6 * f_wk 1 n <= ho 1 z.
Proof.
  intros n z Hz. rewrite f_wk_S, ho_S.
  replace (z + 1) with (2 * n + (z + 1 - 2 * n)) by lia.
  rewrite iter_add, iter_2n.
  set (w0 := iter (z + 1 - 2 * n) (ho 0) 6).
  assert (Hw0 : 6 * n <= w0).
  { subst w0. pose proof (iter_linK (ho 0) 4 ho0_ge (z + 1 - 2 * n) 6). lia. }
  assert (HGG : forall m w, 6 * m <= w -> 6 * f_omega m <= ho 0 (ho 0 w)).
  { intros m w Hw. rewrite !ho_0. apply GG_dom. exact Hw. }
  exact (iter_dom 6 f_omega (fun y => ho 0 (ho 0 y)) HGG n n w0 Hw0).
Qed.

Lemma ho_S_dom : forall d n z, 6 * n <= z -> 6 * f_wk (S d) n <= ho (S d) z.
Proof.
  apply (transfer 6 6 (fun d => f_wk (S d)) (fun d => ho (S d)) ltac:(lia)).
  - intros d n. reflexivity.
  - intros d z. rewrite ho_S. replace (z + 1) with (S z) by lia. lia.
  - intros d y. apply ho_S_ge.
  - exact ho1_dom.
Qed.

Lemma hoc_ge : forall n m a, a + 4 * n <= hoc m n a.
Proof.
  induction n as [| n IHn]; intros m a.
  - rewrite hoc_0. lia.
  - rewrite hoc_S. pose proof (IHn (S m) (ho m a)). pose proof (ho_ge m a). lia.
Qed.

Lemma hoc_S_ge : forall n m a, a + 6 * n <= hoc (S m) n a.
Proof.
  induction n as [| n IHn]; intros m a.
  - rewrite hoc_0. lia.
  - rewrite hoc_S. pose proof (IHn (S m) (ho (S m) a)). pose proof (ho_S_ge m a). lia.
Qed.

(** ** Lower bound on hoc 0 2 10 = ho 1 14 = iter 15 (ho 0) 6 *)
Lemma G02_ge : 210 <= G0 2.
Proof.
  rewrite (G0_eq 2), hc_last, hc_S, hc_0, h1_eq.
  replace (1 + 1) with 2 by reflexivity. replace (4 * 6 + 10) with 34 by reflexivity.
  pose proof (h_dom 2 9 34 ltac:(lia)) as Hh. rewrite f2_eq in Hh.
  assert (H9 : 9 * 2 ^ 9 = 4608) by reflexivity.
  rewrite H9 in Hh. lia.
Qed.

Lemma G10_eq : G 10 = 14.
Proof.
  change (G 10) with (G (3 * 3 + 1)). rewrite (G_cy 3 1 ltac:(lia)). reflexivity.
Qed.

Lemma G6_eq : G 6 = G0 2.
Proof.
  change (G 6) with (G (3 * 2 + 0)). rewrite (G_cy 2 0 ltac:(lia)). reflexivity.
Qed.

Lemma f_w2_eq : forall n, f_w2 n = f_wk n n.
Proof. reflexivity. Qed.

Opaque f f_omega f_wk f_w2.
Strategy opaque [f f_omega f_wk f_w2].

Lemma G_cy0 : forall c, G (3 * c) = G0 c.
Proof.
  intros c. replace (3 * c) with (3 * c + 0) by lia.
  rewrite (G_cy c 0 ltac:(lia)). reflexivity.
Qed.

Lemma G_cy1 : forall c, G (3 * c + 1) = 3 * c + 5.
Proof.
  intros c. rewrite (G_cy c 1 ltac:(lia)). reflexivity.
Qed.

Lemma G_cy2 : forall c, G (3 * c + 2) = G0 c + 2.
Proof.
  intros c. rewrite (G_cy c 2 ltac:(lia)). reflexivity.
Qed.

Lemma iter3_ho0 : forall x, iter 3 (ho 0) x = G (G (G x)).
Proof.
  intros x. cbn [iter]. rewrite (ho_0 x), (ho_0 (G x)), (ho_0 (G (G x))). reflexivity.
Qed.

Lemma G3_dom_G0 : forall n c, 6 * n <= G0 c ->
  (exists c', iter 3 (ho 0) (3 * c) = 3 * c') /\ 6 * f_omega n <= iter 3 (ho 0) (3 * c).
Proof.
  intros n c H1.
  destruct (G0_mod1 c) as [c1 Hc1].
  destruct (G0_mod1 (S c1)) as [c2 Hc2].
  pose proof (G0_dom n (S c1) ltac:(lia)) as H2.
  assert (Hiter : iter 3 (ho 0) (3 * c) = G0 (S c1) + 2).
  { rewrite (iter3_ho0 (3 * c)), (G_cy0 c), Hc1, (G_cy1 c1).
    replace (3 * c1 + 5) with (3 * S c1 + 2) by lia.
    apply G_cy2. }
  split; [exists (S c2); lia | lia].
Qed.

Lemma G3_dom : forall n z, (exists c, z = 3 * c) -> 6 * n <= z ->
  (exists c', iter 3 (ho 0) z = 3 * c') /\ 6 * iter 2 f_omega n <= iter 3 (ho 0) z.
Proof.
  intros n z [c Hc] Hz. subst z.
  pose proof (G0_dom n c ltac:(lia)) as H1.
  assert (Hf2 : iter 2 f_omega n = f_omega (f_omega n)) by reflexivity.
  rewrite Hf2.
  exact (G3_dom_G0 (f_omega n) c H1).
Qed.

Lemma G3_iter : forall r n z, (exists c, z = 3 * c) -> 6 * n <= z ->
  (exists c', iter (3 * r) (ho 0) z = 3 * c') /\ 6 * iter (2 * r) f_omega n <= iter (3 * r) (ho 0) z.
Proof.
  induction r as [| r IHr]; intros n z Hmod Hz.
  - cbn [Nat.mul iter]. split; [exact Hmod | exact Hz].
  - replace (3 * S r) with (3 + 3 * r) by lia.
    replace (2 * S r) with (2 + 2 * r) by lia.
    rewrite (iter_add 3 (3 * r) (ho 0) z), (iter_add 2 (2 * r) f_omega n).
    destruct (IHr n z Hmod Hz) as [Hmod' Hz'].
    exact (G3_dom (iter (2 * r) f_omega n) (iter (3 * r) (ho 0) z) Hmod' Hz').
Qed.

Lemma G3_base : (exists c', iter 3 (ho 0) 6 = 3 * c') /\ 6 * f_omega 35 <= iter 3 (ho 0) 6.
Proof.
  exact (G3_dom_G0 35 2 G02_ge).
Qed.

Lemma f3_17_le_f_omega_35 : f 3 17 <= f_omega 35.
Proof.
  rewrite (f_omega_eq 35).
  pose proof (f_level_mono 32 3 35 ltac:(lia)) as L1.
  change (32 + 3) with 35 in L1.
  pose proof (f_mono 3 17 35 ltac:(lia)). lia.
Qed.

Lemma a1_bound_35 : 6 * iter 9 f_omega 35 <= hoc 0 2 10.
Proof.
  rewrite (hoc_S 0 1 10), (hoc_S 1 0 (ho 0 10)), (hoc_0 2 (ho 1 (ho 0 10))), (ho_0 10), G10_eq, (ho_S 0 14).
  change (14 + 1) with (3 * 4 + 3).
  rewrite (iter_add (3 * 4) 3 (ho 0) 6).
  rewrite (iter_S' 8 f_omega 35).
  destruct G3_base as [Hmod Hz].
  destruct (G3_iter 4 (f_omega 35) (iter 3 (ho 0) 6) Hmod Hz) as [_ H9].
  exact H9.
Qed.

Lemma pos_S : forall n, 1 <= S n.
Proof. intros n. apply le_n_S, Nat.le_0_l. Qed.

Lemma iter_f_omega_pos : forall r n, 1 <= n -> 1 <= iter r f_omega n.
Proof. intros r n Hn. exact (Nat.le_trans 1 n (iter r f_omega n) Hn (iter_ge f_omega f_omega_id r n)). Qed.

Lemma f_pos : forall k n, 1 <= n -> 1 <= f k n.
Proof. intros k n Hn. exact (Nat.le_trans 1 n (f k n) Hn (f_id k n)). Qed.

Lemma Hpos1 : 1 <= iter 9 f_omega 35.
Proof. exact (iter_f_omega_pos 9 35 (pos_S 34)). Qed.

Lemma Hpos2 : 1 <= iter 8 f_omega (f 3 17).
Proof. exact (iter_f_omega_pos 8 (f 3 17) (f_pos 3 17 (pos_S 16))). Qed.

Lemma a1_bound_f3_17 : 6 * iter 8 f_omega (f 3 17) <= hoc 0 2 10.
Proof.
  pose proof a1_bound_35 as H1.
  rewrite (iter_S' 8 f_omega 35) in H1.
  pose proof (iter_mono_x f_omega f_omega_mono 8 (f 3 17) (f_omega 35) f3_17_le_f_omega_35).
  lia.
Qed.

Lemma bound_gen : forall Y0 A1 k b a2 j,
  1 <= Y0 -> 6 * Y0 <= A1 -> A1 + 6 = 3 * S (S k) ->
  b = hoc 0 k 10 -> a2 = iter 3 (ho k) b -> a2 + 2 * S k + 2 = 3 * j + 2 ->
  f_w2 (2 * Y0) < 2 * j + 2.
Proof.
  intros Y0 A1 k b a2 j HY0 HA1 Hk Hb Ha2 Hj.
  assert (HkY : 2 * Y0 <= k) by lia.
  destruct k as [| k'] eqn:Ek; [lia |].
  assert (Hb1 : 6 * S k' <= b).
  { subst b. rewrite hoc_S.
    pose proof (hoc_S_ge k' 0 (ho 0 10)).
    pose proof (ho0_ge 10). lia. }
  pose proof (ho_S_dom k' (S k') b Hb1) as H1.
  pose proof (ho_S_ge k' (ho (S k') b)) as H2.
  pose proof (ho_S_ge k' (ho (S k') (ho (S k') b))) as H3.
  assert (HA2 : iter 3 (ho (S k')) b = ho (S k') (ho (S k') (ho (S k') b))) by reflexivity.
  pose proof (f_w2_mono (2 * Y0) (S k') HkY) as Hmono.
  rewrite (f_w2_eq (S k')) in Hmono. rewrite HA2 in Ha2. lia.
Qed.

Theorem score_exact : exists k a2 j c,
  hoc 0 2 10 + 6 = 3 * S (S k) /\ a2 = iter 3 (ho k) (hoc 0 k 10) /\
  a2 + 2 * S k + 2 = 3 * j + 2 /\ c0 -->* c /\ halted tm c /\ ones c (2 * j + 2).
Proof.
  destruct run as (k & a2 & j & Hk & Ha2 & Hj & Hrun).
  exists k, a2, j, (Hc j).
  split; [exact Hk |]. split; [exact Ha2 |]. split; [exact Hj |]. split; [exact Hrun |].
  split; [apply Hc_halted | apply ones_Hc].
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
    f_w2 (2 * iter 9 f_omega 35) < N /\ f_w2 (2 * iter 8 f_omega (f 3 17)) < N.
Proof.
  destruct run as (k & a2 & j & Hk & Ha2 & Hj & Hrun).
  exists (Hc j), (2 * j + 2).
  split; [exact Hrun |]. split; [apply Hc_halted |]. split; [apply ones_Hc |].
  split.
  - exact (bound_gen (iter 9 f_omega 35) (hoc 0 2 10) k (hoc 0 k 10) a2 j Hpos1 a1_bound_35 Hk eq_refl Ha2 Hj).
  - exact (bound_gen (iter 8 f_omega (f 3 17)) (hoc 0 2 10) k (hoc 0 k 10) a2 j Hpos2 a1_bound_f3_17 Hk eq_refl Ha2 Hj).
Qed.

Print Assumptions halt.
Print Assumptions sigma_lower_bound.
