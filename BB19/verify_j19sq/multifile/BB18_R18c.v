(* machine: 1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_1LQ0LO_0LR1LP_1LQ1LN_1LF0LM_0RC1RZ *)
(** * 18-state BB(18) champion R18c halts deterministically, with
      sigma(18) > f_(omega*2)(f_(omega+1)(f_4(2))) >> f_(omega*2)(2 * f_omega^9(35)) [J18_w2_C_tnf].

    Core-named (A-start):
      1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_1LQ0LO_0LR1LP_1LQ1LN_1LF0LM_0RC1RZ
    Unmirrored A-started TNF (proved isomorphic via [halt_tnf] and [sigma_lower_bound_tnf]):
      1LB0LP_1RC1RJ_1RD1RC_0LE1RO_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RB1RH_0LK1RJ_1LN0LL_0LR1LM_1LN1LK_1LC0LJ_0LQ1LA_1LA1LP_0RI1LQ_0RO1RZ
    1RB L/R-mirrored Canonical TNF:
      1RB0RP_1LC1LJ_1LD1LC_0RE1LO_1RF1RE_0RG1RE_1LH1LI_0LH0LC_0LB1LH_0RK1LJ_1RN0RL_0RR1RM_1RN1RK_1RC0RJ_0RQ1RA_1RA1RP_0LI1RQ_0LO1RZ

    Architecture (Unified 6-State Expansion + Multi-Digit Refill M, N, O, P, QQ, RR):
      - Both outer R0 (where H consumes the left marker 1) and outer exhaustion E0 = 0RH
        (where H preserves the left marker 1 behind a separating 0) enter the SAME
        mod-3 scanner N, O, P!
      - At the left end of the block, QQ1 = 0LM detects and erases the preserved marker 1
        during refill, converting EX B into a multi-digit outer list:
          * B = 3*j + 1        -> HALT at RR, 1 with 2*j + 1 ones
          * B = 3*(k+1) + 2    -> CO 7 (rl (repeat 2 (k+2)) (const 0))     (B0 = 5 -> CO 7 [2; 2])
          * B = 3*(k+2)        -> CO 7 (rl (3 :: repeat 2 (k+1)) (const 0))
      - Outer R0 satisfies P1 G (G a == a + 1 mod 3 for ALL a >= 0), and outer R1 resets
        the accumulator to 15 (== 0 mod 3), so P1 (ho m) holds for ALL m >= 0!
      - Blank-tape trajectory:
          c0 -->* CO 3 [] -->* EX 5 -->* CO 7 [2; 2]
             -->* CO a1 [1; 1]    (a1 = ho 1 (G 7) == 0 mod 3, B1 = a1 + 6 = 3*(k1 + 2))
             -->* EX B1 -->* CO 7 (3 :: repeat 2 (k1 + 1))
             -->* CO a2 (repeat 1 (k1 + 2))  (B2 = a2 + 2*(k1 + 2) + 2 == 1 mod 3)
             -->* EX (3*(j + 1) + 1) -->* Hc (j + 1) [HALT]!

    Main results (zero axioms):
      [halt], [halt_tnf]                           : halts tm c0, halts tm_tnf c0
      [score_exact]                                : exact halting tape and 2-refill equations
      [sigma_lower_bound], [sigma_lower_bound_tnf] : f_w2 (2 * iter 9 f_omega 35) < f_w2 (f_wk 1 (f 4 2)) < N *)

From BB8 Require Import Individual182.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* Core-named R18c:
   1LH0LG_0LI1RC_0LD1LA_0RE1LD_0RH1RL_1RB1RF_1LA1LG_1RF1RM_1LJ1LI_0LK1LI_1RL1RE_0RL0RF_0LN1RM_1LQ0LO_0LR1LP_1LQ1LN_1LF0LM_0RC1RZ *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A,  0 => Some (1, TM.L, H)   | A,  1 => Some (0, TM.L, G)
  | B,  0 => Some (0, TM.L, I)   | B,  1 => Some (1, TM.R, C)
  | C,  0 => Some (0, TM.L, D)   | C,  1 => Some (1, TM.L, A)
  | D,  0 => Some (0, TM.R, E)   | D,  1 => Some (1, TM.L, D)
  | E,  0 => Some (0, TM.R, H)   | E,  1 => Some (1, TM.R, L)
  | F,  0 => Some (1, TM.R, B)   | F,  1 => Some (1, TM.R, F)
  | G,  0 => Some (1, TM.L, A)   | G,  1 => Some (1, TM.L, G)
  | H,  0 => Some (1, TM.R, F)   | H,  1 => Some (1, TM.R, M)
  | I,  0 => Some (1, TM.L, J)   | I,  1 => Some (1, TM.L, I)
  | J,  0 => Some (0, TM.L, K)   | J,  1 => Some (1, TM.L, I)
  | K,  0 => Some (1, TM.R, L)   | K,  1 => Some (1, TM.R, E)
  | L,  0 => Some (0, TM.R, L)   | L,  1 => Some (0, TM.R, F)
  | M,  0 => Some (0, TM.L, N)   | M,  1 => Some (1, TM.R, M)
  | N,  0 => Some (1, TM.L, QQ)  | N,  1 => Some (0, TM.L, O)
  | O,  0 => Some (0, TM.L, RR)  | O,  1 => Some (1, TM.L, P)
  | P,  0 => Some (1, TM.L, QQ)  | P,  1 => Some (1, TM.L, N)
  | QQ, 0 => Some (1, TM.L, F)   | QQ, 1 => Some (0, TM.L, M)
  | RR, 0 => Some (0, TM.R, C)   | RR, 1 => None
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

(** ** Canonical Configurations *)
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

Lemma SW_exit_out : forall j y B, B = y + 2 * j + 2 ->
  SW (0 >> 1 >> const 0) j y [] (const 0) -->* EX B.
Proof.
  intros j y B HB. unfold SW, EX. cbn [rl].
  replace B with (S (y + 2 * j + 1)) by lia.
  execute.
  follow walkI.
  follow zigIJ.
  rewrite pairs_ones.
  replace (0 >> const 0) with (const 0) by apply const_unfold.
  execute.
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

(** ** Unified Refill & Expansion Scanner (M, N, O, P, QQ, RR) *)
Lemma EX_N : forall B,
  EX (S B) -->* ([1]^^(S B) *> 0 >> 1 >> const 0) <{{N}} (0 >> const 0).
Proof.
  intros B. unfold EX. cbn [lpow app Str_app].
  execute.
  follow walkM.
  rewrite one_shift.
  execute.
Qed.

Definition Hc (j : nat) : Q * tape :=
  (1 >> const 0) <{{RR}} (0 >> 0 >> [1;1;0]^^j *> const 0).

Lemma Hc_halted : forall j, halted tm (Hc j).
Proof. intros. reflexivity. Qed.

Lemma RF_halt : forall j, EX (3 * j + 1) -->* Hc j.
Proof.
  intros j. replace (3 * j + 1)%nat with (S (3 * j))%nat by lia.
  follow (EX_N (3 * j)).
  replace (S (3 * j))%nat with (3 * j + 1)%nat by lia.
  rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  follow triNOP.
  replace (0 >> const 0) with (const 0) by apply const_unfold.
  unfold Hc. execute.
Qed.

Lemma N00_CO7 : forall Y,
  const 0 <{{N}} (0 >> 0 >> Y) -->* CO 7 Y.
Proof.
  intros Y.
  assert (Hstep : const 0 <{{N}} (0 >> 0 >> Y) -->* SW (const 0) 0 4 [1%nat] (0 >> Y)).
  { unfold SW. cbn [rl lpow app Str_app]. execute. }
  follow Hstep.
  follow SW_pass.
  follow SW_exit_in.
  finish.
Qed.

Lemma RF_2 : forall k,
  EX (3 * S k + 2) -->* CO 7 (rl (repeat 2%nat (S (S k))) (const 0)).
Proof.
  intros k. replace (3 * S k + 2)%nat with (S (3 * k + 4))%nat by lia.
  follow (EX_N (3 * k + 4)).
  replace (S (3 * k + 4))%nat with (3 * k + 5)%nat by lia.
  rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  follow triNOP.
  replace (0 >> const 0) with (const 0) by apply const_unfold.
  assert (Hmid :
    (1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> const 0) <{{N}} ([1;1;0]^^k *> const 0) -->*
    const 0 <{{N}} (0 >> 0 >> rl (repeat 2%nat (S (S k))) (const 0))).
  { cbn [repeat rl]. rewrite rl_rep2. cbn [lpow app Str_app]. execute. }
  follow Hmid.
  apply N00_CO7.
Qed.

Lemma RF_0 : forall k,
  EX (3 * S (S k)) -->* CO 7 (rl (3%nat :: repeat 2%nat (S k)) (const 0)).
Proof.
  intros k. replace (3 * S (S k))%nat with (S (3 * k + 5))%nat by lia.
  follow (EX_N (3 * k + 5)).
  replace (S (3 * k + 5))%nat with (3 * k + 6)%nat by lia.
  rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  follow triNOP.
  replace (0 >> const 0) with (const 0) by apply const_unfold.
  assert (Hmid :
    (1 >> 1 >> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> const 0) <{{N}} ([1;1;0]^^k *> const 0) -->*
    const 0 <{{N}} (0 >> 0 >> rl (3%nat :: repeat 2%nat (S k)) (const 0))).
  { cbn [repeat rl]. rewrite rl_rep2. cbn [lpow app Str_app]. execute. }
  follow Hmid.
  apply N00_CO7.
Qed.

(** ** Expansion Branches for Outer R0 *)
Lemma EXP_zero : forall X,
  ([1]^^4 *> const 0) <{{N}} (0 >> X) -->* CO 4 X.
Proof.
  intros X.
  assert (Hstep : ([1]^^4 *> const 0) <{{N}} (0 >> X) -->* SW (const 0) 0 3 [] (0 >> X)).
  { unfold SW. cbn [rl lpow app Str_app]. execute. }
  follow Hstep.
  follow SW_exit_in.
  finish.
Qed.

Lemma EXP_0s : forall c' X,
  ([1]^^(3 * S c' + 4) *> const 0) <{{N}} (0 >> X) -->* CI 6 (1%nat :: repeat 2%nat c') (0 >> X).
Proof.
  intros c' X. unfold CI. cbn [rl]. rewrite rl_rep2.
  replace (3 * S c' + 4)%nat with (3 * c' + 7)%nat by lia.
  rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  follow triNOP.
  execute.
Qed.

Lemma EXP_1 : forall c X,
  ([1]^^(3 * c + 5) *> const 0) <{{N}} (0 >> X) -->* CI 3 (repeat 2%nat (S (S c))) (0 >> X).
Proof.
  intros c X. unfold CI. cbn [repeat rl]. rewrite rl_rep2.
  rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  follow triNOP.
  execute.
Qed.

Lemma EXP_2 : forall c X,
  ([1]^^(3 * c + 6) *> const 0) <{{N}} (0 >> X) -->* CI 3 (3%nat :: repeat 2%nat (S c)) (0 >> X).
Proof.
  intros c X. unfold CI. cbn [repeat rl]. rewrite rl_rep2.
  rewrite <- ones_add, <- pow111. cbn [lpow app Str_app].
  follow triNOP.
  execute.
Qed.

(** ** Outer Rounds *)
Lemma CO_SW : forall a ds, CO a (rl ds (const 0)) -->* SW (0 >> 1 >> const 0) 0 a ds (const 0).
Proof. intros. unfold CO, SW. follow walkF. finish. Qed.

Lemma OEX : forall a n B, B = a + 2 * n + 2 ->
  CO a (rl (repeat 1%nat n) (const 0)) -->* EX B.
Proof.
  intros a n B HB. rewrite <- (app_nil_r (repeat 1%nat n)).
  follow CO_SW. follow SW_pass_iter. apply (SW_exit_out (0 + n) a B). lia.
Qed.

Lemma R1_CI : forall Y,
  (0 >> 1 >> const 0) <{{A}} (1 >> 0 >> Y) -->* CI 3 [3%nat] (0 >> Y).
Proof.
  intros Y. unfold CI. cbn [rl lpow app Str_app]. execute.
Qed.

Lemma R1_raw : forall a p e os,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) (const 0)) -->*
  CO 15 (1 >> [0;1]^^p *> [1]^^(S a) *> 0 >> rl (S e :: os) (const 0)).
Proof.
  intros a p e os.
  follow CO_SW. follow SW_pass_iter. follow SW_E.
  replace (0 + S p)%nat with (S p) by lia.
  cbn [lpow app Str_app].
  follow R1_CI.
  follow CI_E0.
  follow CI_E0.
  follow (CI_exit 11 1 (1 >> [0;1]^^p *> [1]^^(S a) *> 0 >> rl (S e :: os) (const 0))).
  finish.
Qed.

Lemma R1 : forall a p e os,
  CO a (rl (repeat 1%nat (S p) ++ S (S e) :: os) (const 0)) -->*
  CO 15 (rl (repeat 1%nat p ++ (a + 2) :: S e :: os) (const 0)).
Proof.
  intros. follow R1_raw. rewrite rl_app, rl_rep1.
  replace (a + 2) with (S (S a)) by lia. cbn [rl lpow app Str_app].
  rewrite (align_lpow 1 [0]). simpl app. finish.
Qed.

(** ** Hierarchy Functions *)
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

Definition Gcy (c y : nat) : nat :=
  match y with
  | 0 => match c with
         | 0 => 4
         | S c' => hc 1 c' 6 + 2 * c' + 4
         end
  | 1 => hc 1 (S c) 7 + 2 * S c + 4
  | _ => hc 1 (S c) 11 + 2 * S c + 4
  end.

Definition G (a : nat) : nat := Gcy (a / 3) (a mod 3).

Fixpoint ho (m a : nat) : nat :=
  match m with
  | 0 => G a
  | S m' => iter (a + 1) (ho m') 15
  end.

Fixpoint hoc (m n a : nat) : nat :=
  match n with
  | 0 => a
  | S n' => hoc (S m) n' (ho m a)
  end.

Close Scope nat_scope.

(** ** Inner Levels *)
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

Lemma R0_N : forall a e os,
  CO a (rl (S (S e) :: os) (const 0)) -->*
  ([1]^^(a + 4) *> const 0) <{{N}} (0 >> rl (S e :: os) (const 0)).
Proof.
  intros a e os.
  rewrite <- ones_add. cbn [lpow app Str_app].
  follow CO_SW. follow SW_E. cbn [lpow app Str_app].
  execute.
  follow walkM.
  execute.
Qed.

Lemma R0_cy : forall c y e os, (y < 3)%nat ->
  CO (3 * c + y) (rl (S (S e) :: os) (const 0)) -->* CO (Gcy c y) (rl (S e :: os) (const 0)).
Proof.
  intros c y e os Hy.
  set (X := rl (S e :: os) (const 0)).
  follow R0_N.
  destruct y as [| [| [| y']]]; try lia.
  - destruct c as [| c']; cbn [Gcy].
    + simpl Nat.add. apply EXP_zero.
    + replace (3 * S c' + 0 + 4)%nat with (3 * S c' + 4)%nat by lia.
      follow EXP_0s.
      change (1%nat :: repeat 2%nat c') with (repeat 1%nat 1 ++ repeat 2%nat c').
      follow (Chain_in c' 1%nat 6%nat (0 >> X)).
      follow CI_exit.
      replace (hc 1 c' 6 + 2 * (1 + c') + 2)%nat with (hc 1 c' 6 + 2 * c' + 4)%nat by lia.
      finish.
  - cbn [Gcy].
    replace (3 * c + 1 + 4)%nat with (3 * c + 5)%nat by lia.
    follow EXP_1.
    cbn [repeat]. follow CI_E0.
    change (1%nat :: repeat 2%nat (S c)) with (repeat 1%nat 1 ++ repeat 2%nat (S c)).
    follow (Chain_in (S c) 1%nat 7%nat (0 >> X)).
    follow CI_exit.
    replace (hc 1 (S c) 7 + 2 * (1 + S c) + 2)%nat with (hc 1 (S c) 7 + 2 * S c + 4)%nat by lia.
    finish.
  - cbn [Gcy].
    replace (3 * c + 2 + 4)%nat with (3 * c + 6)%nat by lia.
    follow EXP_2.
    follow CI_E0. follow CI_E0.
    change (1%nat :: repeat 2%nat (S c)) with (repeat 1%nat 1 ++ repeat 2%nat (S c)).
    follow (Chain_in (S c) 1%nat 11%nat (0 >> X)).
    follow CI_exit.
    replace (hc 1 (S c) 11 + 2 * (1 + S c) + 2)%nat with (hc 1 (S c) 11 + 2 * S c + 4)%nat by lia.
    finish.
Qed.

Lemma R0 : forall a e os,
  CO a (rl (S (S e) :: os) (const 0)) -->* CO (G a) (rl (S e :: os) (const 0)).
Proof.
  intros a e os.
  rewrite (Nat.div_mod a 3) at 1 by lia. unfold G.
  apply R0_cy, Nat.mod_upper_bound. lia.
Qed.

(** ** Outer Levels *)
Lemma LV_out : forall m e a os,
  CO a (rl (repeat 1%nat m ++ S e :: os) (const 0)) -->* CO (iter e (ho m) a) (rl (repeat 1%nat (S m) ++ os) (const 0)).
Proof.
  induction m as [| m IHm]; intros e; induction e as [| e IHe]; intros a os.
  - simpl. finish.
  - simpl app. follow R0. follow IHe. rewrite iter_S'. finish.
  - rewrite rep_snoc. finish.
  - follow R1. follow (IHm (a + 1)%nat 15%nat (S e :: os)).
    follow IHe. rewrite iter_S'. finish.
Qed.

Lemma Chain_out : forall n m a os,
  CO a (rl (repeat 1%nat m ++ repeat 2%nat n ++ os) (const 0)) -->* CO (hoc m n a) (rl (repeat 1%nat (m + n) ++ os) (const 0)).
Proof.
  induction n as [| n IHn]; intros m a os.
  - simpl. rewrite Nat.add_0_r. finish.
  - cbn [repeat app].
    follow (LV_out m 1%nat a (repeat 2%nat n ++ os)).
    follow IHn. replace (S m + n)%nat with (m + S n)%nat by lia. finish.
Qed.

Local Open Scope nat_scope.

(** ** Equations Before Opacity *)
Lemma h_0 : forall x, h 0 x = x + 4.  Proof. reflexivity. Qed.
Lemma h_S : forall m x, h (S m) x = iter (x + 2) (h m) 2.  Proof. reflexivity. Qed.
Lemma hc_0 : forall m x, hc m 0 x = x.  Proof. reflexivity. Qed.
Lemma hc_S : forall m n x, hc m (S n) x = hc (S m) n (h m x).  Proof. reflexivity. Qed.
Lemma G_eq : forall a, G a = Gcy (a / 3) (a mod 3).  Proof. reflexivity. Qed.
Lemma ho_0 : forall a, ho 0 a = G a.  Proof. reflexivity. Qed.
Lemma ho_S : forall m a, ho (S m) a = iter (a + 1) (ho m) 15.  Proof. reflexivity. Qed.
Lemma hoc_0 : forall m a, hoc m 0 a = a.  Proof. reflexivity. Qed.
Lemma hoc_S : forall m n a, hoc m (S n) a = hoc (S m) n (ho m a).  Proof. reflexivity. Qed.

Lemma G_cy : forall c y, y < 3 -> G (3 * c + y) = Gcy c y.
Proof.
  intros c y Hy. rewrite G_eq.
  replace ((3 * c + y) / 3) with c by (apply Nat.div_unique with y; lia).
  replace ((3 * c + y) mod 3) with y by (apply Nat.mod_unique with c; lia).
  reflexivity.
Qed.

(** ** Mod-3 Invariant (Deterministic Termination Proof) *)
Definition P1 (g : nat -> nat) : Prop := forall x, exists q, g x = x + 1 + 3 * q.

Lemma iter_P1 : forall g, P1 g -> forall n x, exists q, iter n g x = x + n + 3 * q.
Proof.
  intros g Hg. induction n as [| n IH]; intros x; simpl.
  - exists 0; lia.
  - destruct (IH x) as [q1 H1]. destruct (Hg (iter n g x)) as [q2 H2].
    exists (q1 + q2). lia.
Qed.

Lemma h_P1 : forall m, P1 (h m).
Proof.
  induction m as [| m IHm]; intros x.
  - rewrite h_0. exists 1; lia.
  - rewrite h_S. destruct (iter_P1 (h m) IHm (x + 2) 2) as [q Hq].
    exists (q + 1). lia.
Qed.

Lemma hc_P1 : forall n m x, exists q, hc m n x = x + n + 3 * q.
Proof.
  induction n as [| n IH]; intros m x.
  - rewrite hc_0. exists 0; lia.
  - rewrite hc_S. destruct (h_P1 m x) as [q1 H1].
    destruct (IH (S m) (h m x)) as [q2 H2].
    exists (q1 + q2). lia.
Qed.

Lemma G_P1 : P1 G.
Proof.
  intros a.
  pose proof (Nat.div_mod a 3 ltac:(lia)) as Hdm.
  pose proof (Nat.mod_upper_bound a 3 ltac:(lia)) as Hy.
  set (c := a / 3) in *. set (y := a mod 3) in *.
  rewrite Hdm, (G_cy c y Hy).
  destruct y as [| [| [| y']]]; try lia; cbn [Gcy].
  - destruct c as [| c'].
    + exists 1; lia.
    + destruct (hc_P1 c' 1 6) as [q Hq]. exists (q + 2); lia.
  - destruct (hc_P1 (S c) 1 7) as [q Hq]. exists (q + 4); lia.
  - destruct (hc_P1 (S c) 1 11) as [q Hq]. exists (q + 5); lia.
Qed.

Lemma ho_P1 : forall m, P1 (ho m).
Proof.
  induction m as [| m IHm]; intros a.
  - rewrite ho_0. apply G_P1.
  - rewrite ho_S. destruct (iter_P1 (ho m) IHm (a + 1) 15) as [q Hq].
    exists (q + 5). lia.
Qed.

Lemma hoc_P1 : forall n m a, exists q, hoc m n a = a + n + 3 * q.
Proof.
  induction n as [| n IH]; intros m a.
  - rewrite hoc_0. exists 0; lia.
  - rewrite hoc_S. destruct (ho_P1 m a) as [q1 H1].
    destruct (IH (S m) (ho m a)) as [q2 H2].
    exists (q1 + q2). lia.
Qed.

(** ** Hierarchy Positivity (for S (S k1) and S j witnesses) *)
Lemma iter_ge_base : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl; [lia |].
  specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma h_ge_base : forall m y, y + 2 <= h m y.
Proof.
  induction m as [| m IHm]; intros y.
  - rewrite h_0; lia.
  - rewrite h_S.
    assert (Hlin : forall j c, c + 2 * j <= iter j (h m) c).
    { induction j; intros c; simpl; [lia | specialize (IHj c); specialize (IHm (iter j (h m) c)); lia]. }
    pose proof (Hlin (y + 2) 2). lia.
Qed.

Lemma hc_ge_base : forall n m x, x + 2 * n <= hc m n x.
Proof.
  induction n as [| n IH]; intros m x.
  - rewrite hc_0; lia.
  - rewrite hc_S. pose proof (IH (S m) (h m x)). pose proof (h_ge_base m x). lia.
Qed.

Lemma G_ge4 : forall a, a + 4 <= G a.
Proof.
  intros a.
  pose proof (Nat.div_mod a 3 ltac:(lia)) as Hdm.
  pose proof (Nat.mod_upper_bound a 3 ltac:(lia)) as Hy.
  set (c := a / 3) in *. set (y := a mod 3) in *.
  rewrite Hdm, (G_cy c y Hy).
  destruct y as [| [| [| y']]]; try lia; cbn [Gcy].
  - destruct c as [| c']; [lia | pose proof (hc_ge_base c' 1 6); lia].
  - pose proof (hc_ge_base (S c) 1 7); lia.
  - pose proof (hc_ge_base (S c) 1 11); lia.
Qed.

Lemma ho_ge4 : forall m a, a + 4 <= ho m a.
Proof.
  induction m as [| m IHm]; intros a.
  - rewrite ho_0. apply G_ge4.
  - rewrite ho_S.
    assert (Hlin : forall j c, c + 4 * j <= iter j (ho m) c).
    { induction j; intros c; simpl; [lia | specialize (IHj c); specialize (IHm (iter j (ho m) c)); lia]. }
    pose proof (Hlin (a + 1) 15). lia.
Qed.

Lemma hoc_ge4 : forall n m a, a + 4 * n <= hoc m n a.
Proof.
  induction n as [| n IH]; intros m a.
  - rewrite hoc_0; lia.
  - rewrite hoc_S. pose proof (IH (S m) (ho m a)). pose proof (ho_ge4 m a). lia.
Qed.

(** ** The Run from the Blank Tape *)
Lemma boot1 : c0 -->* CO 3 (rl [] (const S0)).
Proof.
  unfold CO. cbn [rl lpow app Str_app].
  do 13 step. repeat rewrite <- const_unfold. finish.
Qed.

Lemma boot : c0 -->* CO 7 (rl [2%nat; 2%nat] (const S0)).
Proof.
  follow boot1.
  follow (OEX 3 0 5 eq_refl).
  exact (RF_2 0).
Qed.

Lemma LV_out_eq : forall m e a os b, b = iter e (ho m) a ->
  CO a (rl (repeat 1 m ++ S e :: os) (const S0)) -->* CO b (rl (repeat 1 (S m) ++ os) (const S0)).
Proof. intros. subst b. apply LV_out. Qed.

Lemma Chain_out_eq : forall n m a os b, b = hoc m n a ->
  CO a (rl (repeat 1 m ++ repeat 2 n ++ os) (const S0)) -->* CO b (rl (repeat 1 (m + n) ++ os) (const S0)).
Proof. intros. subst b. apply Chain_out. Qed.

Lemma run_gen : forall a1 k1 b0 a2 j,
  a1 = hoc 0 2 7 ->
  a1 + 6 = 3 * S (S k1) ->
  b0 = iter 2 (ho 0) 7 ->
  a2 = hoc 1 (S k1) b0 ->
  a2 + 2 * (1 + S k1) + 2 = 3 * S j + 1 ->
  c0 -->* Hc (S j).
Proof.
  intros a1 k1 b0 a2 j Ha1 Hk1 Hb0 Ha2 Hj.
  follow boot.
  change [2%nat; 2%nat] with (repeat 1 0 ++ repeat 2 2 ++ []).
  follow (Chain_out_eq 2 0 7 [] a1 Ha1).
  rewrite app_nil_r. simpl Nat.add.
  follow (OEX a1 2 (3 * S (S k1)) ltac:(lia)).
  follow (RF_0 k1).
  change (3 :: repeat 2 (S k1)) with (repeat 1 0 ++ S 2 :: repeat 2 (S k1)).
  follow (LV_out_eq 0 2 7 (repeat 2 (S k1)) b0 Hb0).
  rewrite <- (app_nil_r (repeat 2 (S k1))).
  follow (Chain_out_eq (S k1) 1 b0 [] a2 Ha2).
  rewrite app_nil_r.
  follow (OEX a2 (1 + S k1) (3 * S j + 1) (eq_sym Hj)).
  apply RF_halt.
Qed.

Lemma run : exists a1 k1 b0 a2 j,
  a1 = hoc 0 2 7 /\
  a1 + 6 = 3 * S (S k1) /\
  b0 = iter 2 (ho 0) 7 /\
  a2 = hoc 1 (S k1) b0 /\
  a2 + 2 * (1 + S k1) + 2 = 3 * S j + 1 /\
  c0 -->* Hc (S j).
Proof.
  set (a1 := hoc 0 2 7).
  assert (Hk1_ex : exists k1, a1 + 6 = 3 * S (S k1)).
  { unfold a1. destruct (hoc_P1 2 0 7) as [q1 Hq1].
    pose proof (hoc_ge4 2 0 7).
    exists (q1 + 3). lia. }
  destruct Hk1_ex as [k1 Hk1].
  set (b0 := iter 2 (ho 0) 7).
  set (a2 := hoc 1 (S k1) b0).
  assert (Hj_ex : exists j, a2 + 2 * (1 + S k1) + 2 = 3 * S j + 1).
  { unfold a2, b0.
    destruct (iter_P1 (ho 0) (ho_P1 0) 2 7) as [qb Hqb].
    destruct (hoc_P1 (S k1) 1 (iter 2 (ho 0) 7)) as [q2 Hq2].
    exists (qb + q2 + S k1 + 3). lia. }
  destruct Hj_ex as [j Hj].
  exists a1, k1, b0, a2, j.
  split; [reflexivity |]. split; [exact Hk1 |]. split; [reflexivity |].
  split; [reflexivity |]. split; [exact Hj |].
  exact (run_gen a1 k1 b0 a2 j eq_refl Hk1 eq_refl eq_refl Hj).
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct run as (_ & _ & _ & _ & j & _ & _ & _ & _ & _ & Hrun).
  exact (halted_evstep_halts tm c0 (Hc (S j)) Hrun (Hc_halted (S j))).
Qed.

(** ** Score in Standard Form *)
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

Lemma ones_Hc : forall j, ones (Hc j) (2 * j + 1).
Proof.
  intros j. exists RR, (@nil Sym), (S0 :: S0 :: [S1; S1; S0]^^j), S1.
  split.
  - unfold Hc. reflexivity.
  - cbn [count1 sym_val]. rewrite count1_pow. cbn [count1 sym_val]. lia.
Qed.

(** ** Fast-Growing Hierarchy up to f_(omega*2) *)
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

Opaque h hc G ho hoc.
Strategy opaque [h hc G ho hoc].

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

Lemma f_id : forall k n, n <= f k n.  Proof. intros. apply f_props. Qed.
Lemma f_mono : forall k a b, a <= b -> f k a <= f k b.  Proof. intros. apply f_props. assumption. Qed.

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

Lemma f_S_2 : forall k, f (S k) 2 = f k (f k 2).  Proof. reflexivity. Qed.
Lemma f2_2 : f 2 2 = 8.  Proof. rewrite f2_eq. reflexivity. Qed.
Lemma f2_4 : f 2 4 = 64.  Proof. rewrite f2_eq. reflexivity. Qed.
Lemma f3_2_eq : f 3 2 = f 2 8.  Proof. rewrite (f_S_2 2), f2_2. reflexivity. Qed.

Lemma f4_2_ge : 64 <= f 4 2.
Proof.
  pose proof (f_mono 2 4 8 ltac:(lia)) as H1.
  rewrite f2_4, <- f3_2_eq in H1.
  pose proof (f_level_mono 1 3 2 ltac:(lia)) as H2.
  change (1 + 3) with 4 in H2. lia.
Qed.

Lemma f_omega_eq : forall n, f_omega n = f n n.  Proof. reflexivity. Qed.
Lemma f_omega_0 : f_omega 0 = 1.  Proof. reflexivity. Qed.
Lemma f_omega_1 : f_omega 1 = 2.  Proof. reflexivity. Qed.
Lemma f_omega_id : forall n, n <= f_omega n.  Proof. intros n. apply f_id. Qed.

Lemma f_omega_dbl : forall n, 1 <= n -> 2 * n <= f_omega n.
Proof. intros n Hn. rewrite f_omega_eq. apply f_dbl; exact Hn. Qed.

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
Lemma f_wk_1 : forall n, f_wk 1 n = iter n f_omega n.  Proof. reflexivity. Qed.
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

Lemma f_wk_id : forall k n, n <= f_wk k n.  Proof. intros. apply f_wk_props. Qed.
Lemma f_wk_mono : forall k a b, a <= b -> f_wk k a <= f_wk k b.  Proof. intros. apply f_wk_props. assumption. Qed.

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
Lemma f_w2_id : forall n, n <= f_w2 n.  Proof. intros n. unfold f_w2. apply f_wk_id. Qed.

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

Lemma G_ge6_pos : forall a, 1 <= a -> a + 6 <= G a.
Proof.
  intros a Ha.
  pose proof (Nat.div_mod a 3 ltac:(lia)) as Hdm.
  pose proof (Nat.mod_upper_bound a 3 ltac:(lia)) as Hy.
  set (c := a / 3) in *. set (y := a mod 3) in *.
  rewrite Hdm, (G_cy c y Hy).
  destruct y as [| [| [| y']]]; try lia; cbn [Gcy].
  - destruct c as [| c']; [lia | pose proof (hc_ge c' 1 6); lia].
  - pose proof (hc_ge (S c) 1 7); lia.
  - pose proof (hc_ge (S c) 1 11); lia.
Qed.

Lemma G_dom : forall n z, 1 <= z -> 6 * n <= z -> 6 * f_omega n <= G z.
Proof.
  intros n z Hz1 Hz.
  destruct n as [| [| n']].
  - rewrite f_omega_0. pose proof (G_ge6_pos z Hz1). lia.
  - rewrite f_omega_1. pose proof (G_ge6_pos z Hz1). lia.
  - set (n := S (S n')) in *.
    pose proof (Nat.div_mod z 3 ltac:(lia)) as Hdm.
    pose proof (Nat.mod_upper_bound z 3 ltac:(lia)) as Hy.
    set (c := z / 3) in *. set (y := z mod 3) in *.
    assert (Hc : 2 * n <= c) by lia.
    rewrite Hdm, (G_cy c y Hy).
    assert (Hfn : forall k, S n <= k -> 3 * f n n <= f k (2 * n)).
    { intros k Hk.
      pose proof (f_level_mono (k - S n) (S n) (2 * n) ltac:(lia)) as L1.
      replace (k - S n + S n) with k in L1 by lia.
      rewrite f_S in L1.
      pose proof (iter_mono_n (f n) (f_id n) 3 (2 * n) (2 * n) ltac:(lia)) as L2.
      pose proof (iter_mono_x (f n) (f_mono n) 3 n (2 * n) ltac:(lia)) as L3.
      cbn [iter] in L2, L3.
      pose proof (f_dbl n (f n n) ltac:(lia)).
      pose proof (f_dbl n (f n (f n n)) ltac:(lia)). lia. }
    destruct y as [| [| [| y']]]; try lia; cbn [Gcy].
    + destruct c as [| [| c'']]; [lia | lia |].
      rewrite (hc_last c'' 1 6). replace (1 + c'') with (S c'') by lia.
      pose proof (hc_ge c'' 1 6).
      pose proof (h_dom (S c'') (2 * n) (hc 1 c'' 6) ltac:(lia)).
      pose proof (Hfn (S c'') ltac:(lia)).
      rewrite f_omega_eq. lia.
    + rewrite (hc_last c 1 7). replace (1 + c) with (S c) by lia.
      pose proof (hc_ge c 1 7).
      pose proof (h_dom (S c) (2 * n) (hc 1 c 7) ltac:(lia)).
      pose proof (Hfn (S c) ltac:(lia)).
      rewrite f_omega_eq. lia.
    + rewrite (hc_last c 1 11). replace (1 + c) with (S c) by lia.
      pose proof (hc_ge c 1 11).
      pose proof (h_dom (S c) (2 * n) (hc 1 c 11) ltac:(lia)).
      pose proof (Hfn (S c) ltac:(lia)).
      rewrite f_omega_eq. lia.
Qed.

Lemma iter_lin6_pos : forall g, (forall u, 1 <= u -> u + 6 <= g u) ->
  forall j c, 1 <= c -> c + 6 * j <= iter j g c.
Proof.
  intros g Hg. induction j as [| j IHj]; intros c Hc; cbn [iter].
  - lia.
  - specialize (IHj c Hc). specialize (Hg (iter j g c) ltac:(lia)). lia.
Qed.

Lemma ho_ge_pos : forall m y, 1 <= y -> y + 6 <= ho m y.
Proof.
  induction m as [| m IHm]; intros y Hy.
  - rewrite ho_0. apply G_ge6_pos; exact Hy.
  - rewrite ho_S. pose proof (iter_lin6_pos (ho m) IHm (y + 1) 15 ltac:(lia)). lia.
Qed.

Lemma iter_dom_pos : forall K g h0,
  (forall n z, 1 <= z -> K * n <= z -> K * g n <= h0 z) ->
  (forall u, 1 <= u -> u + 6 <= h0 u) ->
  forall k n z, 1 <= z -> K * n <= z -> K * iter k g n <= iter k h0 z.
Proof.
  intros K g h0 Hd Hpos. induction k as [| k IHk]; intros n z Hz1 Hz; cbn [iter].
  - exact Hz.
  - assert (Hzk : 1 <= iter k h0 z).
    { pose proof (iter_lin6_pos h0 Hpos k z Hz1). lia. }
    apply Hd; [exact Hzk | apply IHk; assumption].
Qed.

Lemma ho_dom : forall m n z, 1 <= z -> 6 * n <= z -> 6 * f_wk m n <= ho m z.
Proof.
  induction m as [| m IHm]; intros n z Hz1 Hz.
  - rewrite f_wk_0, ho_0. apply G_dom; assumption.
  - rewrite f_wk_S, ho_S.
    replace (z + 1) with (n + (z + 1 - n)) by nia.
    rewrite iter_add.
    assert (Hlin : 15 + 6 * (z + 1 - n) <= iter (z + 1 - n) (ho m) 15)
      by exact (iter_lin6_pos (ho m) (ho_ge_pos m) (z + 1 - n) 15 ltac:(lia)).
    exact (iter_dom_pos 6 (f_wk m) (ho m) IHm (ho_ge_pos m) n n
             (iter (z + 1 - n) (ho m) 15) ltac:(lia) ltac:(nia)).
Qed.

Lemma hoc_ge_pos : forall n m a, 1 <= a -> a + 6 * n <= hoc m n a.
Proof.
  induction n as [| n IHn]; intros m a Ha.
  - rewrite hoc_0. lia.
  - rewrite hoc_S.
    pose proof (ho_ge_pos m a Ha) as H1.
    pose proof (IHn (S m) (ho m a) ltac:(lia)). lia.
Qed.

Lemma hoc_last : forall n m a, hoc m (S n) a = ho (m + n) (hoc m n a).
Proof.
  induction n as [| n IHn]; intros m a.
  - rewrite hoc_S, !hoc_0, Nat.add_0_r. reflexivity.
  - rewrite hoc_S, IHn, hoc_S. f_equal. lia.
Qed.

(** ** Concrete Seed Lower Bound: G 7 >= 8 * f 4 2 and hoc 0 2 7 >= 6 * f_wk 1 (f 4 2) *)
Lemma hc_tower_base7 : 2 * f 3 2 + 4 <= hc 1 2 7.
Proof.
  rewrite (hc_last 1 1 7), (hc_S 1 0 7), (hc_0 2 (h 1 7)), (h1_eq 7).
  change (1 + 1) with 2; change (4 * 7 + 10) with 38.
  pose proof (h_dom 2 19 38 ltac:(lia)) as Hh.
  pose proof (f_plus2 2 8 ltac:(lia)) as Hp.
  change (8 + 2) with 10 in Hp.
  pose proof (f_mono 2 10 19 ltac:(lia)) as Hm.
  pose proof (f_id 3 2).
  rewrite <- f3_2_eq in Hp. lia.
Qed.

Lemma hc_tower_step7 : forall n, 2 <= n -> 2 * f (S n) 2 + 4 <= hc 1 n 7 ->
  8 * f (S (S n)) 2 <= hc 1 (S n) 7.
Proof.
  intros n Hn IHn. rewrite (hc_last n 1 7). replace (1 + n) with (S n) by lia.
  pose proof (h_dom (S n) (f (S n) 2 + 2) (hc 1 n 7) ltac:(lia)) as Hh.
  pose proof (f_plus2 (S n) (f (S n) 2) ltac:(lia)) as Hp.
  rewrite <- (f_S_2 (S n)) in Hp. lia.
Qed.

Lemma G7_bound : 6 * f 4 2 <= G 7.
Proof.
  change (G 7) with (G (3 * 2 + 1)).
  rewrite (G_cy 2 1 ltac:(lia)). cbn [Gcy].
  pose proof (hc_tower_step7 2 ltac:(lia) hc_tower_base7). lia.
Qed.

Lemma a1_bound : 6 * f_wk 1 (f 4 2) <= hoc 0 2 7.
Proof.
  rewrite (hoc_S 0 1 7), (hoc_S 1 0 (ho 0 7)), (hoc_0 2 (ho 1 (ho 0 7))), (ho_0 7).
  pose proof f4_2_ge. pose proof G7_bound.
  exact (ho_dom 1 (f 4 2) (G 7) ltac:(lia) G7_bound).
Qed.

Lemma hoc1_dom_w2 : forall b0 k, 1 <= b0 -> 1 <= k -> 6 * f_w2 (S k) <= hoc 1 (S k) b0.
Proof.
  intros b0 [| k'] Hb0 Hk; [lia |].
  rewrite (hoc_last (S k') 1 b0). change (1 + S k') with (S (S k')).
  assert (Hb : 6 * S (S k') <= hoc 1 (S k') b0).
  { rewrite (hoc_S 1 k' b0).
    assert (Hho1 : 21 <= ho 1 b0).
    { rewrite (ho_S 0 b0). pose proof (iter_lin6_pos (ho 0) (ho_ge_pos 0) (b0 + 1) 15 ltac:(lia)). lia. }
    pose proof (hoc_ge_pos k' 2 (ho 1 b0) ltac:(lia)). lia. }
  pose proof (ho_dom (S (S k')) (S (S k')) (hoc 1 (S k') b0) ltac:(lia) Hb) as Hd.
  rewrite <- (f_w2_eq (S (S k'))) in Hd. exact Hd.
Qed.

Lemma bound_gen : forall Y0 a1 k1 b0 a2 j,
  2 <= Y0 -> 6 * Y0 <= a1 ->
  a1 + 6 = 3 * S (S k1) ->
  1 <= b0 ->
  a2 = hoc 1 (S k1) b0 ->
  a2 + 2 * (1 + S k1) + 2 = 3 * S j + 1 ->
  f_w2 Y0 < 2 * S j + 1.
Proof.
  intros Y0 a1 k1 b0 a2 j HY0 Ha1 Hk1 Hb0 Ha2 Hj.
  assert (Hk1_ge : 1 <= k1) by lia.
  assert (HSk1_ge : Y0 <= S k1) by lia.
  pose proof (hoc1_dom_w2 b0 k1 Hb0 Hk1_ge) as Hd.
  pose proof (f_w2_mono Y0 (S k1) HSk1_ge) as Hm.
  lia.
Qed.

Lemma Y0_ge2 : 2 <= f_wk 1 (f 4 2).
Proof.
  pose proof f4_2_ge.
  pose proof (f_wk_id 1 (f 4 2)).
  lia.
Qed.

Lemma b0_ge1 : 1 <= iter 2 (ho 0) 7.
Proof.
  cbn [iter]. pose proof (ho_ge_pos 0 7 ltac:(lia)).
  pose proof (ho_ge_pos 0 (ho 0 7) ltac:(lia)). lia.
Qed.

Lemma beat_J18_inner : 2 * iter 9 f_omega 35 <= f_wk 1 (f 4 2).
Proof.
  set (W := iter 9 f_omega 35).
  assert (HW35 : 35 <= W) by (unfold W; apply iter_ge, f_omega_id).
  pose proof (f_omega_dbl W ltac:(lia)) as Hdbl.
  change (f_omega W) with (iter 10 f_omega 35) in Hdbl.
  pose proof f4_2_ge as Hf4.
  pose proof (iter_mono_x f_omega f_omega_mono 10 35 (f 4 2) ltac:(lia)) as Hx.
  pose proof (iter_mono_n f_omega f_omega_id 10 (f 4 2) (f 4 2) ltac:(lia)) as Hn.
  rewrite <- (f_wk_1 (f 4 2)) in Hn.
  lia.
Qed.

Lemma beat_J18_w2 : f_w2 (2 * iter 9 f_omega 35) <= f_w2 (f_wk 1 (f 4 2)).
Proof. apply f_w2_mono, beat_J18_inner. Qed.

Theorem score_exact : exists a1 k1 b0 a2 j c,
  a1 = hoc 0 2 7 /\
  a1 + 6 = 3 * S (S k1) /\
  b0 = iter 2 (ho 0) 7 /\
  a2 = hoc 1 (S k1) b0 /\
  a2 + 2 * (1 + S k1) + 2 = 3 * S j + 1 /\
  c0 -->* c /\ halted tm c /\ ones c (2 * S j + 1).
Proof.
  destruct run as (a1 & k1 & b0 & a2 & j & Ha1 & Hk1 & Hb0 & Ha2 & Hj & Hrun).
  exists a1, k1, b0, a2, j, (Hc (S j)).
  split; [exact Ha1 |]. split; [exact Hk1 |]. split; [exact Hb0 |].
  split; [exact Ha2 |]. split; [exact Hj |]. split; [exact Hrun |].
  split; [apply Hc_halted | apply ones_Hc].
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\
    f_w2 (2 * iter 9 f_omega 35) < N /\ f_w2 (f_wk 1 (f 4 2)) < N.
Proof.
  destruct run as (a1 & k1 & b0 & a2 & j & Ha1 & Hk1 & Hb0 & Ha2 & Hj & Hrun).
  exists (Hc (S j)), (2 * S j + 1).
  split; [exact Hrun |]. split; [apply Hc_halted |]. split; [apply ones_Hc |].
  assert (Ha1_bd : 6 * f_wk 1 (f 4 2) <= a1) by (rewrite Ha1; exact a1_bound).
  assert (Hb0_bd : 1 <= b0) by (rewrite Hb0; exact b0_ge1).
  pose proof (bound_gen (f_wk 1 (f 4 2)) a1 k1 b0 a2 j Y0_ge2 Ha1_bd Hk1 Hb0_bd Ha2 Hj) as HB18.
  split; [exact (Nat.le_lt_trans _ _ _ beat_J18_w2 HB18) | exact HB18].
Qed.

(** ** Exact Isomorphism to Unmirrored Tree Normal Form (TNF) *)
(* Unmirrored TNF:
   1LB0LP_1RC1RJ_1RD1RC_0LE1RO_1LF1LE_0LG1LE_1RH1RI_0RH0RC_0RB1RH_0LK1RJ_1LN0LL_0LR1LM_1LN1LK_1LC0LJ_0LQ1LA_1LA1LP_0RI1LQ_0RO1RZ *)
Definition tm_tnf : TM := fun '(q, s) =>
  match q, s with
  | A,       S0 => Some (S1, TM.L, B)       | A,       S1 => Some (S0, TM.L, P)
  | B,       S0 => Some (S1, TM.R, C)       | B,       S1 => Some (S1, TM.R, J)
  | C,       S0 => Some (S1, TM.R, D)       | C,       S1 => Some (S1, TM.R, C)
  | D,       S0 => Some (S0, TM.L, E)       | D,       S1 => Some (S1, TM.R, O)
  | E,       S0 => Some (S1, TM.L, F)       | E,       S1 => Some (S1, TM.L, E)
  | F,       S0 => Some (S0, TM.L, BB182.G) | F,       S1 => Some (S1, TM.L, E)
  | BB182.G, S0 => Some (S1, TM.R, H)       | BB182.G, S1 => Some (S1, TM.R, I)
  | H,       S0 => Some (S0, TM.R, H)       | H,       S1 => Some (S0, TM.R, C)
  | I,       S0 => Some (S0, TM.R, B)       | I,       S1 => Some (S1, TM.R, H)
  | J,       S0 => Some (S0, TM.L, K)       | J,       S1 => Some (S1, TM.R, J)
  | K,       S0 => Some (S1, TM.L, N)       | K,       S1 => Some (S0, TM.L, L)
  | L,       S0 => Some (S0, TM.L, RR)      | L,       S1 => Some (S1, TM.L, M)
  | M,       S0 => Some (S1, TM.L, N)       | M,       S1 => Some (S1, TM.L, K)
  | N,       S0 => Some (S1, TM.L, C)       | N,       S1 => Some (S0, TM.L, J)
  | O,       S0 => Some (S0, TM.L, QQ)      | O,       S1 => Some (S1, TM.L, A)
  | P,       S0 => Some (S1, TM.L, A)       | P,       S1 => Some (S1, TM.L, P)
  | QQ,      S0 => Some (S0, TM.R, I)       | QQ,      S1 => Some (S1, TM.L, QQ)
  | RR,      S0 => Some (S0, TM.R, O)       | RR,      S1 => None
  end.

Definition perm_tnf (q : Q) : Q :=
  match q with
  | A => A | B => D | C => O | D => QQ | E => I | F => C | BB182.G => P | H => B | I => E
  | J => F | K => BB182.G | L => H | M => J | N => K | O => L | P => M | QQ => N | RR => RR
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
    f_w2 (2 * iter 9 f_omega 35) < N /\ f_w2 (f_wk 1 (f 4 2)) < N.
Proof.
  destruct sigma_lower_bound as ([q t] & N & Hrun & Hhalt & Hones & HB18_old & HB18_new).
  exists (perm_tnf q, t), N.
  split; [exact (perm_evstep_tnf c0 (q, t) Hrun) |].
  split; [exact (perm_halted_tnf q t Hhalt) |].
  split; [| split; [exact HB18_old | exact HB18_new]].
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

