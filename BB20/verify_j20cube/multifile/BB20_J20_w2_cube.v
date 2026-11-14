(* machine: 1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RT0RK_1LS1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_0LA0LA_1RZ1LK *)
(** * 20-state BB(20) champion J20_w2_cube halts in 4 genuine data-driven refills,
      with sigma > f_(omega*2)^3(f_5(2)) >>> f_(omega*2)(f_(omega+2)^2(f_10(2))) [previous BB(20) champion J20].

    Unmirrored A-started TNF (proved below):
      1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RT0RK_1LS1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_0LA0LA_1RZ1LK
    1RB L/R-mirrored Canonical TNF (isomorphic step-for-step):
      1RB0RM_1LC1LN_1LD1LC_0RE1LQ_1RF1RE_0RG1RE_1LH1LI_0LH0LC_0LJ1LH_0LT0LK_1RS1LL_1RM1LJ_1RA1RM_0RA0LO_0RC1LP_0RA1LN_0RR1RA_0LI1RR_0RA0RA_1RZ1RK
    Core-named (A-start):
      1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RR1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LA0RN_0LF1RO_0LA1RM_1LT1RQ_1LG1RR_0RS0RP_1RZ1LP_0LA0LA

    Architecture (Two-Stage Right-End Sentinel Upgrade -> 4 Genuine Refills = f_(omega*2)^3):
      - Boot -> EX 5 (const 0)
      - Refill 1 (B0 = 5 == 2 mod 3): EX 5 (const 0) -> CO 10 (rl [3] (const 0))
      - Outer Run 1 -> EX B1 (const 0), with B1 = 3 * S (S k1) + 1 (== 1 mod 3)
      - Refill 2 (B1 == 1 mod 3, K0 = 1LSS -> SS0 = 0LA): parks 1-bit sentinel (0 >> 1 >> const 0),
        giving CO 10 (rl (repeat 2 (S k1)) (0 >> 1 >> const 0))
      - Outer Run 2 -> OEX shifts stream -> EX B2 (1 >> const 0), with B2 = 3 * S (S k2) (== 0 mod 3)
      - Refill 3 (B2 == 0 mod 3, J0 = 0RTT -> TT1 = 1LK -> K0 = 1LSS -> SS1 = 0LA):
        upgrades sentinel to 2-bit (0 >> 1 >> 1 >> const 0) and appends trailing [1],
        giving CO 10 (rl (repeat 2 k2 ++ [1]) (0 >> 1 >> 1 >> const 0))
      - Outer Run 3 -> OEX shifts stream -> EX B3 (1 >> 1 >> const 0), with B3 = 3 * S k3 + 2 (== 2 mod 3)
      - Refill 4 (B3 == 2 mod 3, L0 = 1LM): absorbs BOTH sentinel 1s into final digit 5
        on 100% clean blank right tape, giving CO 10 (rl (repeat 2 k3 ++ [5]) (const 0))
      - Outer Run 4 -> OEX -> EX B4 (const 0), with B4 = 3 * S j (== 0 mod 3)
      - Exhaustion 5 (B4 == 0 mod 3, J0 = 0RTT -> TT0 = None): deterministic halt at Hc (S j)!

    Main results (zero axioms):
      [halt]              : halts tm c0
      [score_exact]       : exact halting configuration and 4-refill recurrence equations
      [sigma_lower_bound] : exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
                            iter 3 f_w2 (f 5 2) < N /\
                            f_w2 (f_wk 2 (f_wk 2 (f 10 2))) < N *)

From BB8 Require Import Individual202.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* Unmirrored TNF: 1LB0LM_1RC1RN_1RD1RC_0LE1RQ_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RJ1RH_0RT0RK_1LS1RL_1LM1RJ_1LA1LM_0LA0RO_0LC1RP_0LA1RN_0LR1LA_0RI1LR_0LA0LA_1RZ1LK *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A,  0 => Some (1, TM.L, B)   | A,  1 => Some (0, TM.L, M)
  | B,  0 => Some (1, TM.R, C)   | B,  1 => Some (1, TM.R, N)
  | C,  0 => Some (1, TM.R, D)   | C,  1 => Some (1, TM.R, C)
  | D,  0 => Some (0, TM.L, E)   | D,  1 => Some (1, TM.R, QQ)
  | E,  0 => Some (1, TM.L, F)   | E,  1 => Some (1, TM.L, E)
  | F,  0 => Some (0, TM.L, G)   | F,  1 => Some (1, TM.L, E)
  | G,  0 => Some (1, TM.R, H)   | G,  1 => Some (1, TM.R, I)
  | H,  0 => Some (0, TM.R, H)   | H,  1 => Some (0, TM.R, C)
  | I,  0 => Some (0, TM.R, J)   | I,  1 => Some (1, TM.R, H)
  | J,  0 => Some (0, TM.R, TT)  | J,  1 => Some (0, TM.R, K)
  | K,  0 => Some (1, TM.L, SS)  | K,  1 => Some (1, TM.R, L)
  | L,  0 => Some (1, TM.L, M)   | L,  1 => Some (1, TM.R, J)
  | M,  0 => Some (1, TM.L, A)   | M,  1 => Some (1, TM.L, M)
  | N,  0 => Some (0, TM.L, A)   | N,  1 => Some (0, TM.R, O)
  | O,  0 => Some (0, TM.L, C)   | O,  1 => Some (1, TM.R, P)
  | P,  0 => Some (0, TM.L, A)   | P,  1 => Some (1, TM.R, N)
  | QQ, 0 => Some (0, TM.L, RR)  | QQ, 1 => Some (1, TM.L, A)
  | RR, 0 => Some (0, TM.R, I)   | RR, 1 => Some (1, TM.L, RR)
  | SS, 0 => Some (0, TM.L, A)   | SS, 1 => Some (0, TM.L, A)
  | TT, 0 => None                | TT, 1 => Some (1, TM.L, K)
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

(** ** Walks (TNF mapping: C=F, M=G, RR=D, E=I, A=A, B=H, N=M, J=R, SS=T, TT=S) *)
Lemma walkF : forall n l r, l {{C}}> [1]^^n *> r -->* [1]^^n *> l {{C}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkG : forall n l r, [1]^^n *> l <{{M}} r -->* l <{{M}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkD : forall n l r, [1]^^n *> l <{{RR}} r -->* l <{{RR}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkI : forall n l r, [1]^^n *> l <{{E}} r -->* l <{{E}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma zigGA : forall n l r, [0;1]^^n *> l <{{M}} r -->* l <{{M}} [0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma zigIJ : forall n l r, [0;1]^^n *> l <{{E}} r -->* l <{{E}} [1;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triMNO : forall n l r, l {{N}}> [1;1;1]^^n *> r -->* [1;1;0]^^n *> l {{N}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triRPQ : forall n l r, l {{J}}> [1;1;1]^^n *> r -->* [1;1;0]^^n *> l {{J}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triAG : forall n l r, [1;1;0]^^n *> l <{{A}} r -->* l <{{A}} [1;1;0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma triIJI : forall n l r, [1;0;1]^^n *> l <{{E}} r -->* l <{{E}} [1;1;1]^^n *> r.
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

(** ** Canonical Configurations (parameterized over right-anchor stream R) *)
Definition SW (l : side) (j y : nat) (ds : list nat) (R : side) : Q * tape :=
  ([1]^^y *> [0;1]^^j *> 0 >> l) {{C}}> (0 >> rl ds R).

Definition CI (x : nat) (ds : list nat) (R : side) : Q * tape :=
  const 0 <{{B}} ([1]^^x *> 0 >> rl ds R).

Definition CO (a : nat) (Rr : side) : Q * tape :=
  (0 >> 0 >> 1 >> const 0) {{C}}> ([1]^^a *> 0 >> Rr).

Definition EX (B : nat) (R : side) : Q * tape :=
  (0 >> 1 >> const 0) {{J}}> ([1]^^B *> 0 >> R).

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

Lemma SW_exit_in : forall j y R, SW (const 0) j y [] (0 >> R) -->* CO (y + 2 * j + 1) R.
Proof.
  intros. unfold SW. cbn [rl].
  execute.
  follow walkI.
  follow zigIJ.
  execute.
  rewrite pairs_ones. unfold CO. finish.
Qed.

Lemma SW_exit_out : forall j y B R, B = y + 2 * j + 2 ->
  SW (0 >> 1 >> const 0) j y [] (0 >> R) -->* EX B R.
Proof.
  intros j y B R HB. unfold SW, EX. cbn [rl].
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
  const 0 <{{B}} (1 >> 1 >> [0;1]^^j *> [1]^^(S y) *> 0 >> rl (S e :: ds) R).
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

(** ** 3-State Boundary-Shifting Expansion (N, O, P) *)
Lemma EXP_0 : forall c X,
  (1 >> 1 >> 0 >> 1 >> const 0) {{N}}> ([1]^^(3 * c) *> 0 >> X) -->* CI 2 (repeat 2%nat (S c)) (0 >> X).
Proof.
  intros c X. unfold CI. rewrite rl_rep2, <- pow111.
  follow triMNO. execute. follow triAG. execute.
Qed.

Lemma EXP_1 : forall c X,
  (1 >> 1 >> 0 >> 1 >> const 0) {{N}}> ([1]^^(3 * c + 1) *> 0 >> X) -->* CO (3 * c + 5) X.
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
  (1 >> 1 >> 0 >> 1 >> const 0) {{N}}> ([1]^^(3 * c + 2) *> 0 >> X) -->* CI 2 (repeat 2%nat (S c) ++ [1%nat]) (0 >> X).
Proof.
  intros c X. unfold CI. rewrite rl_app, rl_rep2, <- ones_add, <- pow111. cbn [rl lpow app Str_app].
  follow triMNO. execute. follow triAG. execute.
Qed.

(** ** 5-State Refill & Two-Stage Right-End Sentinel Transitions (J, K, L, SS, TT) *)
Definition Hc (k : nat) : Q * tape := (0 >> [1;1;0]^^k *> 0 >> 1 >> const 0) {{TT}}> (const 0).

Lemma Hc_halted : forall k, halted tm (Hc k).
Proof. intros. reflexivity. Qed.

Lemma RF_halt : forall k, EX (3 * k) (const 0) -->* Hc k.
Proof.
  intros k. unfold EX, Hc. rewrite <- pow111.
  follow triRPQ. execute.
Qed.

Lemma RF_1 : EX 5 (const 0) -->* CO 10 (rl [3%nat] (const 0)).
Proof.
  unfold EX, CO. cbn [rl lpow app Str_app].
  replace (0 >> const 0) with (const 0) by apply const_unfold.
  execute.
Qed.

Lemma RF_2 : forall k,
  EX (3 * S (S k) + 1) (const 0) -->* CO 10 (rl (repeat 2%nat (S k)) (0 >> 1 >> const 0)).
Proof.
  intros k. unfold EX, CO. rewrite rl_rep2.
  replace (3 * S (S k) + 1)%nat with (3 + (3 * S k + 1))%nat by lia.
  rewrite <- !ones_add, <- (pow111 (S k)). cbn [lpow app Str_app].
  execute. follow triRPQ. execute. follow triAG. execute.
Qed.

Lemma RF_3 : forall k,
  EX (3 * S (S k)) (1 >> const 0) -->* CO 10 (rl (repeat 2%nat k ++ [1%nat]) (0 >> 1 >> 1 >> const 0)).
Proof.
  intros k. unfold EX, CO. rewrite rl_app, rl_rep2.
  replace (3 * S (S k))%nat with (3 + (3 * k + 3))%nat by lia.
  rewrite <- !ones_add, <- (pow111 k). cbn [rl lpow app Str_app].
  execute. follow triRPQ. execute. follow triAG. execute.
Qed.

Lemma RF_4 : forall k,
  EX (3 * S k + 2) (1 >> 1 >> const 0) -->* CO 10 (rl (repeat 2%nat k ++ [5%nat]) (const 0)).
Proof.
  intros k. unfold EX, CO. rewrite rl_app, rl_rep2.
  replace (3 * S k + 2)%nat with (3 + (3 * k + 2))%nat by lia.
  rewrite <- !ones_add, <- (pow111 k). cbn [rl lpow app Str_app].
  replace (0 >> const 0) with (const 0) by apply const_unfold.
  execute. follow triRPQ. execute. follow triAG. execute.
Qed.

(** ** Outer rounds (arbitrary right-anchor stream R) *)
Lemma CO_SW : forall a ds R, CO a (rl ds R) -->* SW (0 >> 1 >> const 0) 0 a ds R.
Proof. intros. unfold CO, SW. follow walkF. finish. Qed.

Lemma OEX : forall a n B R, B = a + 2 * n + 2 ->
  CO a (rl (repeat 1%nat n) (0 >> R)) -->* EX B R.
Proof.
  intros a n B R HB. rewrite <- (app_nil_r (repeat 1%nat n)).
  follow CO_SW. follow SW_pass_iter. apply (SW_exit_out (0 + n) a B R). lia.
Qed.

Lemma OEX_0 : forall a n B, B = a + 2 * n + 2 ->
  CO a (rl (repeat 1%nat n) (const 0)) -->* EX B (const 0).
Proof.
  intros a n B HB.
  replace (rl (repeat 1%nat n) (const 0)) with (rl (repeat 1%nat n) (0 >> const 0))
    by (f_equal; symmetry; apply const_unfold).
  apply (OEX a n B (const 0) HB).
Qed.

Lemma R1_raw : forall a p e os R,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) R) -->*
  CO 6 (1 >> [0;1]^^p *> [1]^^(S a) *> 0 >> rl (S e :: os) R).
Proof.
  intros. follow CO_SW. follow SW_pass_iter. follow SW_E. execute.
Qed.

Lemma R1 : forall a p e os R,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) R) -->*
  CO 6 (rl (repeat 1%nat p ++ (a + 2) :: S e :: os) R).
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

Lemma R0_aux : forall a c y e os R, (y < 3)%nat -> a = (3 * c + y)%nat ->
  CO a (rl (S (S e) :: os) R) -->* CO (Gcy c y) (rl (S e :: os) R).
Proof.
  intros a c y e os R Hy Ha. follow CO_SW. follow SW_E.
  cbn [lpow app Str_app].
  step. step. step. step. step.
  subst a.
  destruct y as [| [| [| y]]]; try lia; cbn [Gcy].
  - replace (3 * c + 0)%nat with (3 * c)%nat by lia.
    follow EXP_0. apply Inner_run_0.
  - follow EXP_1. finish.
  - follow EXP_2. apply Inner_run_2.
Qed.

Lemma R0 : forall a e os R,
  CO a (rl (S (S e) :: os) R) -->* CO (G a) (rl (S e :: os) R).
Proof.
  intros. apply (R0_aux a (a / 3) (a mod 3) e os R (Nat.mod_upper_bound a 3 ltac:(lia))).
  pose proof (Nat.div_mod a 3); lia.
Qed.

(** ** Outer levels (arbitrary right-anchor stream R) *)
Lemma LV_out : forall m e a os R,
  CO a (rl (repeat 1%nat m ++ S e :: os) R) -->* CO (iter e (ho m) a) (rl (repeat 1%nat (S m) ++ os) R).
Proof.
  induction m as [| m IHm]; intros e; induction e as [| e IHe]; intros a os R.
  - simpl. finish.
  - simpl app. follow R0. follow IHe. rewrite iter_S'. finish.
  - rewrite rep_snoc. finish.
  - follow R1. follow (IHm (a + 1)%nat 6%nat (S e :: os) R).
    follow IHe. rewrite iter_S'. finish.
Qed.

Lemma Chain_out : forall n m a os R,
  CO a (rl (repeat 1%nat m ++ repeat 2%nat n ++ os) R) -->* CO (hoc m n a) (rl (repeat 1%nat (m + n) ++ os) R).
Proof.
  induction n as [| n IHn]; intros m a os R.
  - rewrite Nat.add_0_r. finish.
  - simpl repeat. cbn [app]. follow (LV_out m 1%nat a (repeat 2%nat n ++ os) R).
    follow IHn. replace (S m + n)%nat with (m + S n)%nat by lia. finish.
Qed.

Local Open Scope nat_scope.

(** ** Mod-3 invariant *)
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

(** ** Boot & Equation Unfoldings before Opacity *)
Lemma boot : c0 -->* CO 3 (rl [] (const S0)).
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

(** ** Parametric 4-Refill Trajectory & Halt Proof *)
Lemma K1_gen : forall a1, a1 = iter 2 (ho 0) 10 -> exists k1, a1 + 4 = 3 * S (S k1) + 1.
Proof.
  intros a1 Ha1.
  destruct (iter_P1 (ho 0) (ho_P1 0) 2 10) as [q Hq].
  exists (q + 3). subst. lia.
Qed.

Lemma K2_gen : forall k1 a2, a2 = hoc 0 (S k1) 10 -> exists k2, a2 + 2 * S k1 + 2 = 3 * S (S k2).
Proof.
  intros k1 a2 Ha2.
  destruct (hoc_mod (S k1) 0 10) as [q Hq].
  exists (k1 + q + 3). subst. lia.
Qed.

Lemma K3_gen : forall k2 a3, a3 = hoc 0 k2 10 -> exists k3, a3 + 2 * S k2 + 2 = 3 * S k3 + 2.
Proof.
  intros k2 a3 Ha3.
  destruct (hoc_mod k2 0 10) as [q Hq].
  exists (k2 + q + 3). subst. lia.
Qed.

Lemma J_gen : forall k3 b4 a4,
  b4 = hoc 0 k3 10 -> a4 = iter 4 (ho k3) b4 ->
  exists j, a4 + 2 * S k3 + 2 = 3 * S j.
Proof.
  intros k3 b4 a4 Hb4 Ha4.
  destruct (hoc_mod k3 0 10) as [q1 H1].
  destruct (iter_P1 (ho k3) (ho_P1 k3) 4 b4) as [q2 H2].
  exists (k3 + q1 + q2 + 5). subst. lia.
Qed.

Lemma LV_out_eq : forall m e a os R b, b = iter e (ho m) a ->
  CO a (rl (repeat 1 m ++ S e :: os) R) -->* CO b (rl (repeat 1 (S m) ++ os) R).
Proof. intros. subst b. apply LV_out. Qed.

Lemma Chain_out_eq : forall n m a os R b, b = hoc m n a ->
  CO a (rl (repeat 1 m ++ repeat 2 n ++ os) R) -->* CO b (rl (repeat 1 (m + n) ++ os) R).
Proof. intros. subst b. apply Chain_out. Qed.

Lemma run_gen : forall a1 k1 a2 k2 a3 k3 b4 a4 j,
  a1 = iter 2 (ho 0) 10 -> a1 + 4 = 3 * S (S k1) + 1 ->
  a2 = hoc 0 (S k1) 10 -> a2 + 2 * S k1 + 2 = 3 * S (S k2) ->
  a3 = hoc 0 k2 10 -> a3 + 2 * S k2 + 2 = 3 * S k3 + 2 ->
  b4 = hoc 0 k3 10 -> a4 = iter 4 (ho k3) b4 -> a4 + 2 * S k3 + 2 = 3 * S j ->
  c0 -->* Hc (S j).
Proof.
  intros a1 k1 a2 k2 a3 k3 b4 a4 j Ha1 Hk1 Ha2 Hk2 Ha3 Hk3 Hb4 Ha4 Hj.
  follow boot.
  follow (OEX_0 3 0 5 eq_refl).
  follow RF_1.
  change [3] with (repeat 1 0 ++ S 2 :: []).
  follow (LV_out_eq 0 2 10 [] (const S0) a1 Ha1).
  cbn [app].
  follow (OEX_0 a1 1 (3 * S (S k1) + 1) ltac:(lia)).
  follow (RF_2 k1).
  rewrite <- (app_nil_r (repeat 2 (S k1))).
  follow (Chain_out_eq (S k1) 0 10 [] (S0 >> S1 >> const S0) a2 Ha2).
  rewrite app_nil_r.
  follow (OEX a2 (S k1) (3 * S (S k2)) (S1 >> const S0) ltac:(lia)).
  follow (RF_3 k2).
  follow (Chain_out_eq k2 0 10 [1] (S0 >> S1 >> S1 >> const S0) a3 Ha3).
  change (0 + k2) with k2.
  rewrite (rep_snoc k2 1 []), app_nil_r.
  follow (OEX a3 (S k2) (3 * S k3 + 2) (S1 >> S1 >> const S0) ltac:(lia)).
  follow (RF_4 k3).
  follow (Chain_out_eq k3 0 10 [5] (const S0) b4 Hb4).
  follow (LV_out_eq k3 4 b4 [] (const S0) a4 Ha4).
  rewrite app_nil_r.
  follow (OEX_0 a4 (S k3) (3 * S j) ltac:(lia)).
  apply RF_halt.
Qed.

Lemma run : exists k1 a2 k2 a3 k3 a4 j,
  iter 2 (ho 0) 10 + 4 = 3 * S (S k1) + 1 /\
  a2 = hoc 0 (S k1) 10 /\ a2 + 2 * S k1 + 2 = 3 * S (S k2) /\
  a3 = hoc 0 k2 10 /\ a3 + 2 * S k2 + 2 = 3 * S k3 + 2 /\
  a4 = iter 4 (ho k3) (hoc 0 k3 10) /\ a4 + 2 * S k3 + 2 = 3 * S j /\
  c0 -->* Hc (S j).
Proof.
  set (a1 := iter 2 (ho 0) 10).
  destruct (K1_gen a1 eq_refl) as [k1 Hk1].
  set (a2 := hoc 0 (S k1) 10).
  destruct (K2_gen k1 a2 eq_refl) as [k2 Hk2].
  set (a3 := hoc 0 k2 10).
  destruct (K3_gen k2 a3 eq_refl) as [k3 Hk3].
  set (b4 := hoc 0 k3 10).
  set (a4 := iter 4 (ho k3) b4).
  destruct (J_gen k3 b4 a4 eq_refl eq_refl) as [j Hj].
  exists k1, a2, k2, a3; exists k3, a4, j.
  split; [exact Hk1 |]. split; [reflexivity |]. split; [exact Hk2 |].
  split; [reflexivity |]. split; [exact Hk3 |].
  split; [reflexivity |]. split; [exact Hj |].
  exact (run_gen a1 k1 a2 k2 a3 k3 b4 a4 j eq_refl Hk1 eq_refl Hk2 eq_refl Hk3 eq_refl eq_refl Hj).
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct run as (k1 & a2 & k2 & a3 & k3 & a4 & j & _ & _ & _ & _ & _ & _ & _ & Hrun).
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

Lemma ones_Hc : forall k, ones (Hc k) (2 * k + 1).
Proof.
  intros k. exists TT, ([S0] ++ [S1; S1; S0]^^k ++ [S0; S1]), (@nil Sym), S0.
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

Lemma f4_2_eq : f 4 2 = f 3 (f 3 2).
Proof. apply (f_S_2 3). Qed.

Lemma f5_2_eq : f 5 2 = f 4 (f 4 2).
Proof. apply (f_S_2 4). Qed.

Lemma f5_2_ge : 64 <= f 5 2.
Proof.
  pose proof (f_mono 2 4 8 ltac:(lia)) as H1.
  rewrite f2_4, <- f3_2_eq in H1.
  pose proof (f_level_mono 2 3 2 ltac:(lia)) as H2.
  change (2 + 3) with 5 in H2. lia.
Qed.

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

Lemma f_wk_0 : forall n, f_wk 0 n = f_omega n.
Proof. reflexivity. Qed.

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

Lemma f_w2_eq : forall n, f_w2 n = f_wk n n.
Proof. reflexivity. Qed.

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

(** ** Hierarchy Dominance Lemmas *)
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

Lemma ho_ge_id : forall m y, y <= ho m y.
Proof. intros m y. pose proof (ho_ge m y). lia. Qed.

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

Lemma hoc_S_ge : forall n m a, a + 6 * n <= hoc (S m) n a.
Proof.
  induction n as [| n IHn]; intros m a.
  - rewrite hoc_0. lia.
  - rewrite hoc_S. pose proof (IHn (S m) (ho (S m) a)). pose proof (ho_S_ge m a). lia.
Qed.

Lemma hoc_last : forall n m a, hoc m (S n) a = ho (m + n) (hoc m n a).
Proof.
  induction n as [| n IHn]; intros m a.
  - rewrite hoc_S, !hoc_0, Nat.add_0_r. reflexivity.
  - rewrite hoc_S, IHn, hoc_S. f_equal. lia.
Qed.

Lemma G10_eq : G 10 = 14.
Proof.
  change (G 10) with (G (3 * 3 + 1)). rewrite (G_cy 3 1 ltac:(lia)). reflexivity.
Qed.

Opaque f f_omega f_wk f_w2.
Strategy opaque [f f_omega f_wk f_w2].

(** ** Concrete Seed & 4-Refill Lower Bounds *)
Lemma G0_4_ge : 8 * f 5 2 <= G0 4.
Proof.
  rewrite (G0_eq 4), (hc_last 3 1 6), (hc_last 2 1 6), (hc_last 1 1 6), (hc_S 1 0 6), (hc_0 2 (h 1 6)).
  change (1 + 3) with 4; change (1 + 2) with 3; change (1 + 1) with 2.
  rewrite (h1_eq 6); change (4 * 6 + 10) with 34.
  pose proof (h_dom 2 17 34 ltac:(lia)) as Hh2.
  pose proof (f_plus2 2 8 ltac:(lia)) as Hfp2.
  change (8 + 2) with 10 in Hfp2.
  pose proof (f_mono 2 10 17 ltac:(lia)) as Hm2.
  rewrite <- f3_2_eq in Hfp2.
  pose proof (f_id 3 2) as Hf3id.
  pose proof (h_dom 3 (f 3 2 + 2) (h 2 34) ltac:(lia)) as Hh3.
  pose proof (f_plus2 3 (f 3 2) ltac:(lia)) as Hfp3.
  rewrite <- f4_2_eq in Hfp3.
  pose proof (f_id 4 2) as Hf4id.
  pose proof (h_dom 4 (f 4 2 + 2) (h 3 (h 2 34)) ltac:(lia)) as Hh4.
  pose proof (f_plus2 4 (f 4 2) ltac:(lia)) as Hfp4.
  rewrite <- f5_2_eq in Hfp4. lia.
Qed.

Lemma a1_bound : 8 * f 5 2 <= iter 2 (ho 0) 10.
Proof.
  cbn [iter]. rewrite (ho_0 10), G10_eq, (ho_0 14).
  change 14 with (3 * 4 + 2). rewrite (G_cy 4 2 ltac:(lia)). cbn [Gcy].
  pose proof G0_4_ge. lia.
Qed.

Lemma hoc_dom_w2 : forall k, 1 <= k -> 6 * f_w2 k <= hoc 0 (S k) 10.
Proof.
  intros [| k'] Hk; [lia |].
  rewrite (hoc_last (S k') 0 10). change (0 + S k') with (S k').
  assert (Hb : 6 * S k' <= hoc 0 (S k') 10).
  { rewrite (hoc_S 0 k' 10).
    pose proof (hoc_S_ge k' 0 (ho 0 10)).
    pose proof (ho0_ge 10). lia. }
  pose proof (ho_S_dom k' (S k') (hoc 0 (S k') 10) Hb) as Hd.
  rewrite <- (f_w2_eq (S k')) in Hd. exact Hd.
Qed.

Lemma bound_4refill : forall a1 k1 a2 k2 a3 k3 a4 j,
  8 * f 5 2 <= a1 -> a1 + 4 = 3 * S (S k1) + 1 ->
  a2 = hoc 0 (S k1) 10 -> a2 + 2 * S k1 + 2 = 3 * S (S k2) ->
  a3 = hoc 0 k2 10 -> a3 + 2 * S k2 + 2 = 3 * S k3 + 2 ->
  a4 = iter 4 (ho k3) (hoc 0 k3 10) -> a4 + 2 * S k3 + 2 = 3 * S j ->
  iter 3 f_w2 (f 5 2) < 2 * S j + 1.
Proof.
  intros a1 k1 a2 k2 a3 k3 a4 j Ha1 Hk1 Ha2 Hk2 Ha3 Hk3 Ha4 Hj.
  pose proof f5_2_ge as Hf5.
  assert (Hk1_ge : 2 * f 5 2 <= k1) by lia.
  pose proof (hoc_dom_w2 k1 ltac:(lia)) as Hd1.
  pose proof (f_w2_mono (f 5 2) k1 ltac:(lia)) as Hm1.
  assert (Ha2_ge : 6 * f_w2 (f 5 2) <= a2) by lia.
  pose proof (f_w2_id (f 5 2)) as Hw2_id1.
  assert (Hk2_ge : 2 * f_w2 (f 5 2) <= k2) by lia.
  destruct k2 as [| k2'] eqn:Ek2; [lia |].
  pose proof (hoc_dom_w2 k2' ltac:(lia)) as Hd2.
  pose proof (f_w2_mono (f_w2 (f 5 2)) k2' ltac:(lia)) as Hm2.
  change (f_w2 (f_w2 (f 5 2))) with (iter 2 f_w2 (f 5 2)) in Hm2.
  assert (Ha3_ge : 6 * iter 2 f_w2 (f 5 2) <= a3) by lia.
  pose proof (f_w2_id (f_w2 (f 5 2))) as Hw2_id2.
  change (f_w2 (f_w2 (f 5 2))) with (iter 2 f_w2 (f 5 2)) in Hw2_id2.
  assert (Hk3_ge : 2 * iter 2 f_w2 (f 5 2) <= k3) by lia.
  destruct k3 as [| k3'] eqn:Ek3; [lia |].
  assert (Ha4_step : hoc 0 (S (S k3')) 10 <= a4).
  { subst a4. rewrite (hoc_last (S k3') 0 10). change (0 + S k3') with (S k3').
    rewrite (iter_S' 3 (ho (S k3')) (hoc 0 (S k3') 10)).
    apply (iter_ge (ho (S k3')) (ho_ge_id (S k3')) 3). }
  pose proof (hoc_dom_w2 (S k3') ltac:(lia)) as Hd3.
  pose proof (f_w2_mono (iter 2 f_w2 (f 5 2)) (S k3') ltac:(lia)) as Hm3.
  change (f_w2 (iter 2 f_w2 (f 5 2))) with (iter 3 f_w2 (f 5 2)) in Hm3.
  lia.
Qed.

Lemma beat_J20_inner : f_wk 2 (f_wk 2 (f 10 2)) <= f_w2 (f 5 2).
Proof.
  assert (H1 : f 10 2 <= f_wk 3 16).
  { pose proof (f_mono 10 2 10 ltac:(lia)) as L1.
    rewrite <- (f_omega_eq 10), <- (f_wk_0 10) in L1.
    pose proof (f_wk_mono 0 10 16 ltac:(lia)) as L2.
    pose proof (f_wk_level_mono 3 0 16 ltac:(lia)) as L3.
    change (3 + 0) with 3 in L3. lia. }
  pose proof (f_wk_id 3 16) as Hid3.
  assert (H2 : f_wk 2 (f 10 2) <= f_wk 3 (f_wk 3 16)).
  { pose proof (f_wk_mono 2 (f 10 2) (f_wk 3 16) H1).
    pose proof (f_wk_level 2 (f_wk 3 16) ltac:(lia)). lia. }
  pose proof (f_wk_id 3 (f_wk 3 16)) as Hid33.
  assert (H3 : f_wk 2 (f_wk 2 (f 10 2)) <= iter 3 (f_wk 3) 16).
  { pose proof (f_wk_mono 2 (f_wk 2 (f 10 2)) (f_wk 3 (f_wk 3 16)) H2).
    pose proof (f_wk_level 2 (f_wk 3 (f_wk 3 16)) ltac:(lia)).
    cbn [iter]. lia. }
  assert (H4 : iter 3 (f_wk 3) 16 <= f_wk 4 16).
  { rewrite (f_wk_S 3 16).
    exact (iter_mono_n (f_wk 3) (f_wk_id 3) 3 16 16 ltac:(lia)). }
  pose proof (f_wk_level_mono 12 4 16 ltac:(lia)) as H5.
  change (12 + 4) with 16 in H5. rewrite <- (f_w2_eq 16) in H5.
  pose proof f5_2_ge.
  pose proof (f_w2_mono 16 (f 5 2) ltac:(lia)). lia.
Qed.

Theorem score_exact : exists k1 a2 k2 a3 k3 a4 j c,
  iter 2 (ho 0) 10 + 4 = 3 * S (S k1) + 1 /\
  a2 = hoc 0 (S k1) 10 /\ a2 + 2 * S k1 + 2 = 3 * S (S k2) /\
  a3 = hoc 0 k2 10 /\ a3 + 2 * S k2 + 2 = 3 * S k3 + 2 /\
  a4 = iter 4 (ho k3) (hoc 0 k3 10) /\ a4 + 2 * S k3 + 2 = 3 * S j /\
  c0 -->* c /\ halted tm c /\ ones c (2 * S j + 1).
Proof.
  destruct run as (k1 & a2 & k2 & a3 & k3 & a4 & j & Hk1 & Ha2 & Hk2 & Ha3 & Hk3 & Ha4 & Hj & Hrun).
  exists k1, a2, k2, a3; exists k3, a4, j, (Hc (S j)).
  split; [exact Hk1 |]. split; [exact Ha2 |]. split; [exact Hk2 |].
  split; [exact Ha3 |]. split; [exact Hk3 |]. split; [exact Ha4 |].
  split; [exact Hj |]. split; [exact Hrun |].
  split; [apply Hc_halted | apply ones_Hc].
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
    iter 3 f_w2 (f 5 2) < N /\
    f_w2 (f_wk 2 (f_wk 2 (f 10 2))) < N.
Proof.
  destruct run as (k1 & a2 & k2 & a3 & k3 & a4 & j & Hk1 & Ha2 & Hk2 & Ha3 & Hk3 & Ha4 & Hj & Hrun).
  exists (Hc (S j)), (2 * S j + 1).
  split; [exact Hrun |]. split; [apply Hc_halted |]. split; [apply ones_Hc |].
  pose proof (bound_4refill (iter 2 (ho 0) 10) k1 a2 k2 a3 k3 a4 j a1_bound Hk1 Ha2 Hk2 Ha3 Hk3 Ha4 Hj) as Hmain.
  pose proof (f_w2_mono (f_wk 2 (f_wk 2 (f 10 2))) (f_w2 (f 5 2)) beat_J20_inner) as Hb1.
  pose proof (f_w2_id (f_w2 (f_w2 (f 5 2)))) as Hid3.
  change (f_w2 (f_w2 (f_w2 (f 5 2)))) with (iter 3 f_w2 (f 5 2)) in Hid3.
  split; [exact Hmain | exact (Nat.le_lt_trans _ _ _ (Nat.le_trans _ _ _ Hb1 Hid3) Hmain)].
Qed.

Print Assumptions halt.
Print Assumptions sigma_lower_bound.
