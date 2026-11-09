(** W2PR (25 states: Racheline's B21 with a mod-8 refill test): TM-level macro lemmas.  Copy of BB21_B21_tm.v with
    the table changed and the refill gadgets (R..Y) redone. *)
From BB8 Require Import Individual252.
From BB8 Require Import BB21_B21_absdef.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 0LI0LF_0RJ1RG_0RD1LC_1RH1RE_1LO0RH_1LA1LF_0LC1LA_1RB1RH_1RD0LF_1LP0RK_0LM1LL_0LL1LM_1LE1LN_0RQ0LM_0RP1LO_1LR0RH_1LF1RQ_1RZ0LS_1LH0LT_1LH1LU_0LE1LV_0LH0LW_1LH0LX_1LH1LY_0LE1LR *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (0, TM.L, I)       | A, 1 => Some (0, TM.L, F)
  | B, 0 => Some (0, TM.R, J)       | B, 1 => Some (1, TM.R, G)
  | C, 0 => Some (0, TM.R, D)       | C, 1 => Some (1, TM.L, C)
  | D, 0 => Some (1, TM.R, H)       | D, 1 => Some (1, TM.R, E)
  | E, 0 => Some (1, TM.L, O)       | E, 1 => Some (0, TM.R, H)
  | F, 0 => Some (1, TM.L, A)       | F, 1 => Some (1, TM.L, F)
  | G, 0 => Some (0, TM.L, C)       | G, 1 => Some (1, TM.L, A)
  | H, 0 => Some (1, TM.R, B)       | H, 1 => Some (1, TM.R, H)
  | I, 0 => Some (1, TM.R, D)       | I, 1 => Some (0, TM.L, F)
  | J, 0 => Some (1, TM.L, P)       | J, 1 => Some (0, TM.R, K)
  | K, 0 => Some (0, TM.L, M)       | K, 1 => Some (1, TM.L, L)
  | L, 0 => Some (0, TM.L, L)       | L, 1 => Some (1, TM.L, M)
  | M, 0 => Some (1, TM.L, E)       | M, 1 => Some (1, TM.L, N)
  | N, 0 => Some (0, TM.R, QQ)      | N, 1 => Some (0, TM.L, M)
  | O, 0 => Some (0, TM.R, P)       | O, 1 => Some (1, TM.L, O)
  | P, 0 => Some (1, TM.L, RR)      | P, 1 => Some (0, TM.R, H)
  | QQ, 0 => Some (1, TM.L, F)      | QQ, 1 => Some (1, TM.R, QQ)
  | RR, 0 => None                   | RR, 1 => Some (0, TM.L, SS)
  | SS, 0 => Some (1, TM.L, H)      | SS, 1 => Some (0, TM.L, TT)
  | TT, 0 => Some (1, TM.L, H)      | TT, 1 => Some (1, TM.L, UU)
  | UU, 0 => Some (0, TM.L, E)      | UU, 1 => Some (1, TM.L, VV)
  | VV, 0 => Some (0, TM.L, H)      | VV, 1 => Some (0, TM.L, WW)
  | WW, 0 => Some (1, TM.L, H)      | WW, 1 => Some (0, TM.L, XX)
  | XX, 0 => Some (1, TM.L, H)      | XX, 1 => Some (1, TM.L, YY)
  | YY, 0 => Some (0, TM.L, E)      | YY, 1 => Some (1, TM.L, RR)
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

Lemma one_shift : forall n (ys : side), [1]^^n *> 1 >> ys = 1 >> [1]^^n *> ys.
Proof. intros. apply (align_lpow 1 [] ys n). Qed.

Lemma ones_add : forall n m (ys : side), [1]^^n *> [1]^^m *> ys = [1]^^(n + m) *> ys.
Proof. intros. rewrite lpow_add, Str_app_assoc. reflexivity. Qed.

Lemma pair_shift : forall (a b : Sym) n (r : side), [a;b]^^n *> a >> b >> r = a >> b >> [a;b]^^n *> r.
Proof. induction n; intros. - reflexivity. - simpl. rewrite IHn. reflexivity. Qed.

Lemma quad_shift : forall (a b c d : Sym) n (r : side),
  [a;b;c;d]^^n *> a >> b >> c >> d >> r = a >> b >> c >> d >> [a;b;c;d]^^n *> r.
Proof. induction n; intros. - reflexivity. - simpl. rewrite IHn. reflexivity. Qed.

Lemma oct_shift : forall (a b c d e f g h : Sym) n (r : side),
  [a;b;c;d;e;f;g;h]^^n *> a >> b >> c >> d >> e >> f >> g >> h >> r = a >> b >> c >> d >> e >> f >> g >> h >> [a;b;c;d;e;f;g;h]^^n *> r.
Proof. induction n; intros. - reflexivity. - simpl. rewrite IHn. reflexivity. Qed.

Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
Lemma ones_snoc : forall n (r : side), [1]^^n *> 1 >> r = [1]^^(S n) *> r.
Proof. intros. rewrite one_shift. reflexivity. Qed.

Lemma pair10 : forall n (r : side), [1;0]^^n *> 1 >> r = 1 >> [0;1]^^n *> r.
Proof. intros. apply (align_lpow 1 [0] r n). Qed.
Ltac canon := repeat (rewrite ?one_shift, ?pair_shift, ?quad_shift, ?oct_shift, ?pair10).
Ltac finish_norm := apply evstep_refl'; canon; first [reflexivity | norm_nat; canon; first [reflexivity | lia_refl]].

(** ** Walks *)
Lemma walkH : forall n l r, l {{H}}> [1]^^n *> r -->* [1]^^n *> l {{H}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkQ : forall n l r, l {{QQ}}> [1]^^n *> r -->* [1]^^n *> l {{QQ}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkF : forall n l r, [1]^^n *> l <{{F}} r -->* l <{{F}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkC : forall n l r, [1]^^n *> l <{{C}} r -->* l <{{C}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.
Lemma walkO : forall n l r, [1]^^n *> l <{{O}} r -->* l <{{O}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Ltac st := eapply evstep_step; [prove_step |]; simpl_tape.
Ltac shw := match goal with |- ?g => idtac g end.

(** ** Engine *)
Lemma E0 : forall x e r,
  const 0 <{{A}} [1]^^x *> 0 >> [1]^^(S (S e)) *> 0 >> r -->*
  const 0 <{{A}} [1]^^(x + 4) *> 0 >> [1]^^(S e) *> 0 >> r.
Proof.
  intros. execute. follow walkH. execute. follow walkF. do 3 st.
  finish_norm.
Qed.

Lemma zigFA : forall j l r, [0;1]^^j *> l <{{F}} r -->* l <{{F}} [0;1]^^j *> r.
Proof. induction j; intros. - finish. - execute. follow IHj. finish_norm. Qed.

Lemma peel1 : forall j l y r,
  [0;1]^^j *> l {{D}}> [1]^^(S (S y)) *> 0 >> 1 >> 0 >> r -->*
  [0;1]^^(S j) *> l {{D}}> [1]^^(S (S y)) *> 0 >> r.
Proof.
  intros. execute. follow walkH. execute. follow walkC. execute. finish_norm.
Qed.

Lemma peel : forall n j l y r,
  [0;1]^^j *> l {{D}}> [1]^^(S (S y)) *> 0 >> [1;0]^^n *> r -->*
  [0;1]^^(j + n) *> l {{D}}> [1]^^(S (S y)) *> 0 >> r.
Proof.
  induction n; intros.
  - rewrite Nat.add_0_r. finish.
  - simpl. follow peel1. follow IHn. replace (S j + n) with (j + S n) by lia. finish.
Qed.

Lemma Dend_E : forall j y e r,
  [0;1]^^j *> const 0 {{D}}> [1]^^(S (S y)) *> 0 >> [1]^^(S (S e)) *> 0 >> r -->*
  const 0 <{{A}} [1;0]^^(S j) *> [1]^^(S (S y)) *> 0 >> [1]^^(S e) *> 0 >> r.
Proof.
  intros. execute. follow walkH. execute. follow walkF. st. st. follow zigFA. st. finish_norm.
Qed.

Lemma Dend_X : forall j l y r,
  [0;1]^^j *> l {{D}}> [1]^^(S (S y)) *> 0 >> 0 >> r -->*
  (0 >> [1]^^(S y) *> [0;1]^^(S j) *> l) {{J}}> r.
Proof.
  intros. execute. follow walkH. execute.
Qed.

Lemma A_start : forall x r,
  const 0 <{{A}} [1]^^x *> 0 >> 1 >> 0 >> r -->*
  [0;1]^^0 *> const 0 {{D}}> [1]^^(S (S (x + 2))) *> 0 >> r.
Proof.
  intros. execute. follow walkH. execute. follow walkC. execute; try finish_norm.
Qed.

Lemma E1raw : forall x p e r,
  const 0 <{{A}} [1]^^x *> 0 >> [1;0]^^(S p) *> [1]^^(S (S e)) *> 0 >> r -->*
  const 0 <{{A}} [1;0]^^(S p) *> [1]^^(x + 4) *> 0 >> [1]^^(S e) *> 0 >> r.
Proof.
  intros. simpl lpow. follow A_start. follow peel. follow Dend_E.
  replace (x + 4) with (S (S (x + 2))) by lia. finish.
Qed.

Lemma EXraw : forall x n r,
  const 0 <{{A}} [1]^^x *> 0 >> [1;0]^^(S n) *> 0 >> r -->*
  (0 >> [1]^^(x + 3) *> [0;1]^^(S n) *> const 0) {{J}}> r.
Proof.
  intros. simpl lpow. follow A_start. follow peel. follow Dend_X.
  replace (x + 3) with (S (x + 2)) by lia. finish.
Qed.

(** ** Digit lists *)
Fixpoint rl (ds : list nat) (r : side) : side :=
  match ds with
  | [] => r
  | d :: t => [1]^^d *> 0 >> rl t r
  end.

Lemma rl_app : forall a b r, rl (a ++ b) r = rl a (rl b r).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

Lemma rl_rep1 : forall n r, rl (repeat 1%nat n) r = [1;0]^^n *> r.
Proof. induction n; intros; simpl. - reflexivity. - rewrite IHn. reflexivity. Qed.

Lemma rep_snoc : forall m (x : nat) ds, repeat x m ++ x :: ds = repeat x (S m) ++ ds.
Proof. induction m; intros; simpl. - reflexivity. - rewrite IHm. reflexivity. Qed.

Definition CA (x : nat) (ds : list nat) (r : side) : Q * tape := const 0 <{{A}} [1]^^x *> 0 >> rl ds r.

Lemma CA_E0 : forall x e ds r, CA x (S (S e) :: ds) r -->* CA (x + 4) (S e :: ds) r.
Proof. intros. unfold CA. simpl rl. apply E0. Qed.

Lemma CA_E1 : forall x p e ds r,
  CA x (repeat 1%nat (S p) ++ S (S e) :: ds) r -->* CA 1 (repeat 1%nat p ++ (x + 4) :: S e :: ds) r.
Proof.
  intros. unfold CA. rewrite !rl_app, !rl_rep1. simpl rl.
  follow E1raw. finish_norm.
Qed.



Lemma LV : forall m e x ds r,
  CA x (repeat 1%nat m ++ S e :: ds) r -->* CA (iter e (h m) x) (repeat 1%nat (S m) ++ ds) r.
Proof.
  induction m as [| m IHm]; intros e; induction e as [| e IHe]; intros x ds r.
  - simpl. finish.
  - simpl app. follow CA_E0. follow IHe. rewrite iter_S'. finish.
  - rewrite rep_snoc. finish.
  - follow CA_E1. replace (x + 4)%nat with (S (x + 3)) by lia.
    follow (IHm (x + 3)%nat 1%nat (S e :: ds) r).
    follow IHe. rewrite iter_S'. finish.
Qed.

Lemma Chain : forall ds m x r, Forall (fun d => d <> 0%nat) ds ->
  CA x (repeat 1%nat m ++ ds) r -->* CA (engf m ds x) (repeat 1%nat (m + length ds)) r.
Proof.
  induction ds as [| d ds IH]; intros m x r Hd.
  - rewrite app_nil_r, Nat.add_0_r. finish.
  - inversion Hd as [| ? ? Hd0 Hds]; subst. destruct d as [| e]; [congruence |].
    follow (LV m e x ds r). simpl engf. replace (S e - 1)%nat with e by lia.
    follow IH. simpl length. replace (S m + length ds)%nat with (m + S (length ds))%nat by lia. finish.
Qed.

Lemma CA_exit : forall x n r, CA x (repeat 1%nat (S n)) (0 >> r) -->*
  (0 >> [1]^^(x + 3) *> [0;1]^^(S n) *> const 0) {{J}}> r.
Proof. intros. unfold CA. rewrite rl_rep1. apply EXraw. Qed.

(** ** J level: passed blocks on the left *)
Fixpoint LP (ms : list nat) : side :=
  match ms with
  | [] => const 0
  | m :: t => [0;1]^^m *> 0 >> LP t
  end.

Definition JC (x : nat) (ms : list nat) (r : side) : Q * tape := (0 >> [1]^^x *> LP ms) {{J}}> r.

Lemma J_E_raw : forall x n l r,
  (0 >> [1]^^(S x) *> 0 >> l) {{J}}> [1;0]^^(S (S n)) *> 0 >> r -->*
  (0 >> [1]^^(x + 3) *> [0;1]^^(S n) *> 0 >> 0 >> l) {{J}}> r.
Proof.
  intros. simpl lpow. execute. follow walkO. execute. rewrite one_shift. execute. follow walkH. execute.
  follow walkC. execute. rewrite !ones_snoc. replace (S (S (S (S x)))) with (S (S (x + 2))) by lia.
  follow (peel n 0 (0 >> 0 >> l)). follow Dend_X. finish_norm.
Qed.

Lemma zigMN : forall n l r, [1;1]^^n *> l <{{M}} r -->* l <{{M}} [0;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma pow11 : forall j, @lpow Sym [1;1] j = [1]^^(2 * j)%nat.
Proof.
  induction j; [reflexivity |].
  replace (2 * S j)%nat with (S (S (2 * j))) by lia. simpl. rewrite IHj. reflexivity.
Qed.

Lemma J_dec_raw : forall k d l r,
  (0 >> 1 >> [1;1]^^(S k) *> 1 >> 0 >> l) {{J}}> 1 >> 1 >> [1]^^d *> r -->*
  l <{{A}} 1 >> 1 >> 1 >> 1 >> [0;1]^^k *> 1 >> 0 >> 0 >> 1 >> [1]^^d *> r.
Proof.
  intros. execute. follow zigMN. simpl lpow. rewrite pair_shift. execute; try finish_norm.
Qed.

Lemma RW : forall ms r, Forall (fun m => m <> 0%nat) ms ->
  LP ms <{{A}} r -->* const 0 <{{A}} fold_left (fun acc m => [1;0]^^m *> 0 >> acc) ms r.
Proof.
  induction ms as [| m ms IH]; intros r Hm.
  - simpl. finish.
  - inversion Hm as [| ? ? Hm0 Hms]; subst. destruct m as [| m]; [congruence |].
    simpl LP. simpl lpow. execute. follow zigFA. execute. follow IH.
    rewrite (align_lpow 0 [1]). simpl app. finish.
Qed.

Lemma Dend_Eg : forall j l y e r,
  [0;1]^^j *> 0 >> l {{D}}> [1]^^(S (S y)) *> 0 >> [1]^^(S (S e)) *> 0 >> r -->*
  l <{{A}} [1;0]^^(S j) *> [1]^^(S (S y)) *> 0 >> [1]^^(S e) *> 0 >> r.
Proof.
  intros. execute. follow walkH. execute. follow walkF. st. st. follow zigFA. st. finish_norm.
Qed.

Lemma J_est0_raw : forall x e l r,
  (0 >> [1]^^(S x) *> 0 >> l) {{J}}> 1 >> 0 >> [1]^^(S (S e)) *> r -->*
  (0 >> l) <{{A}} [1]^^(x + 4) *> 0 >> [1]^^(S e) *> r.
Proof.
  intros. execute. follow walkO. execute. rewrite one_shift. execute. follow walkH. execute.
  follow walkF. st. finish_norm.
Qed.

Lemma J_est1_raw : forall x p e l r,
  (0 >> [1]^^(S x) *> 0 >> l) {{J}}> 1 >> 0 >> [1;0]^^(S p) *> [1]^^(S (S e)) *> 0 >> r -->*
  (0 >> l) <{{A}} [1;0]^^(S p) *> [1]^^(x + 4) *> 0 >> [1]^^(S e) *> 0 >> r.
Proof.
  intros. simpl lpow. execute. follow walkO. execute. rewrite one_shift. execute. follow walkH. execute.
  follow walkC. execute. rewrite !ones_snoc. replace (S (S (S (S x)))) with (S (S (x + 2))) by lia.
  follow (peel p 0 (0 >> 0 >> l)). follow Dend_Eg. finish_norm.
Qed.

Lemma J_P_raw : forall x l r,
  (0 >> [1]^^(S x) *> 0 >> l) {{J}}> 1 >> 0 >> 0 >> r -->*
  (0 >> [1]^^(x + 3) *> 0 >> 0 >> l) {{J}}> r.
Proof.
  intros. execute. follow walkO. execute. rewrite one_shift. execute. follow walkH. execute. finish_norm.
Qed.

Lemma zig8 : forall n l r, [1;1;1;1;1;1;1;1]^^n *> l <{{RR}} r -->* l <{{RR}} [1;1;0;0;1;1;0;0]^^n *> r.
Proof.
  induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma pow8 : forall j, @lpow Sym [1;1;1;1;1;1;1;1] j = [1]^^(8 * j)%nat.
Proof.
  induction j; [reflexivity |].
  replace (8 * S j)%nat with (S (S (S (S (S (S (S (S (8 * j))))))))) by lia. simpl. rewrite IHj. reflexivity.
Qed.

Lemma pat8 : forall n (r : side), [1;1;0;0;1;1;0;0]^^n *> r = [1;1;0;0]^^(2 * n)%nat *> r.
Proof.
  induction n; intros; [reflexivity |]. replace (2 * S n)%nat with (S (S (2 * n))) by lia.
  simpl. rewrite IHn. reflexivity.
Qed.

Definition Halt_cfg (l r : side) : Q * tape := l <{{RR}} r.

Lemma refill_halt : forall q l,
  (0 >> [1]^^(8 * q)%nat *> 0 >> l) {{J}}> const 0 -->*
  Halt_cfg (0 >> l) ([1;1;0;0;1;1;0;0]^^q *> 1 >> 1 >> const 0).
Proof.
  intros. rewrite <- pow8. execute. follow zig8. unfold Halt_cfg. finish.
Qed.

Lemma refill_cont_a : forall q m l,
  (0 >> [1]^^(8 * q + 2)%nat *> 0 >> [0;1]^^(S m) *> 0 >> l) {{J}}> const 0 -->*
  (0 >> [1]^^2 *> [0;1]^^(S m) *> 0 >> l) {{J}}> [1;1;0;0;1;1;0;0]^^q *> 1 >> 1 >> const 0.
Proof.
  intros. rewrite <- (ones_add (8 * q) 2). rewrite <- pow8.
  simpl lpow. execute. follow zig8. execute. destruct m as [| m].
  - execute; try finish_norm.
  - simpl lpow. execute; try finish_norm.
Qed.

Lemma zigX8 : forall n l r, [1;1;1;1;1;1;1;1]^^n *> l <{{XX}} r -->* l <{{XX}} [0;0;1;1;0;0;1;1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma oct_rot : forall q (r : side), [0;0;1;1;0;0;1;1]^^q *> 0 >> 0 >> r = 0 >> 0 >> [1;1;0;0;1;1;0;0]^^q *> r.
Proof. induction q; intros; [reflexivity |]. simpl. rewrite IHq. reflexivity. Qed.

Lemma refill_cont_b : forall q m l,
  (0 >> [1]^^(8 * q + 6)%nat *> 0 >> [0;1]^^(S m) *> 0 >> l) {{J}}> const 0 -->*
  (0 >> [1]^^2 *> [0;1]^^(S m) *> 0 >> l) {{J}}> [1;1;0;0;1;1;0;0]^^q *> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> const 0.
Proof.
  intros. replace (8 * q + 6)%nat with (6 + 8 * q)%nat by lia. rewrite <- (ones_add 6 (8 * q)). rewrite <- pow8.
  simpl lpow. execute. follow zigX8. rewrite oct_rot. execute. destruct m as [| m].
  - execute; try finish_norm.
  - simpl lpow. execute; try finish_norm.
Qed.

Lemma refill_V : forall q m l,
  (0 >> [1]^^(8 * q + 4)%nat *> 0 >> [0;1]^^(S (S m)) *> 0 >> l) {{J}}> const 0 -->*
  l <{{A}} [1;0]^^(S m) *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> [1;1;0;0;1;1;0;0]^^q *> 1 >> 1 >> const 0.
Proof.
  intros. rewrite <- (ones_add (8 * q) 4). rewrite <- pow8.
  simpl lpow. execute. follow zig8. execute. follow zigFA. execute. rewrite pair10. finish_norm.
Qed.

Lemma J_dec2_raw : forall d l r,
  (0 >> 1 >> 1 >> 0 >> l) {{J}}> 1 >> 1 >> [1]^^d *> r -->*
  l <{{A}} 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1]^^d *> r.
Proof. intros. execute; try finish_norm. Qed.

Lemma MergeStep : forall m l0 r,
  (1 >> [0;1]^^m *> 0 >> l0) <{{A}} r -->* l0 <{{A}} [1;0]^^(S m) *> r.
Proof.
  intros. execute. follow zigFA. execute; try finish_norm.
  all: rewrite (align_lpow 0 [1]); simpl app; finish_norm.
Qed.

(** ** Block level *)
Fixpoint rb (bs : list (list nat)) (r : side) : side :=
  match bs with
  | [] => r
  | b :: t => rl b (0 >> rb t r)
  end.

Definition AT (bs : list (list nat)) : Q * tape := const 0 <{{A}} rb bs (const 0).

Lemma rb_app : forall a b r, rb (a ++ b) r = rb a (rb b r).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.


Lemma fold_restore : forall ms bs r,
  fold_left (fun acc m => [1;0]^^m *> 0 >> acc) ms (rb bs r) = rb (restore ms ++ bs) r.
Proof.
  unfold restore. induction ms as [| m ms IH]; intros bs r; simpl.
  - reflexivity.
  - replace ([1;0]^^m *> 0 >> rb bs r) with (rb (repeat 1%nat m :: bs) r)
      by (simpl; rewrite rl_rep1; reflexivity).
    rewrite IH. rewrite <- app_assoc. reflexivity.
Qed.

Lemma RWb : forall ms bs, Forall (fun m => m <> 0%nat) ms ->
  LP ms <{{A}} rb bs (const 0) -->* AT (restore ms ++ bs).
Proof. intros. follow RW. rewrite fold_restore. finish. Qed.

Lemma Xcells : forall k r,
  1 >> 1 >> 1 >> 1 >> [0;1]^^k *> 1 >> 0 >> r = rl (Xl k) r.
Proof.
  destruct k; intros; simpl.
  - reflexivity.
  - rewrite rl_app, rl_rep1. simpl. rewrite pair10. reflexivity.
Qed.

Lemma LP1 : forall n, [0;1]^^n *> const 0 = LP [n].
Proof. intros. simpl. rewrite <- const_unfold. reflexivity. Qed.

Lemma B_engine : forall x d ds R, Forall (fun d => d <> 0%nat) (d :: ds) ->
  AT ((x :: d :: ds) :: R) -->* JC (engf 0 (d :: ds) x + 3) [length (d :: ds)] (rb R (const 0)).
Proof.
  intros x d ds R Hd. unfold AT. simpl rb.
  change (const 0 <{{A}} [1]^^x *> 0 >> rl (d :: ds) (0 >> rb R (const 0))) with
    (CA x (repeat 1%nat 0 ++ d :: ds) (0 >> rb R (const 0))).
  follow (Chain (d :: ds) 0 x (0 >> rb R (const 0)) Hd).
  simpl length. follow CA_exit. unfold JC. rewrite LP1. finish.
Qed.

Lemma B_E : forall x m ms n R r,
  JC (S x) (S m :: ms) (rb (repeat 1%nat (S (S n)) :: R) r) -->* JC (S x + 2) (S n :: S m :: ms) (rb R r).
Proof.
  intros. unfold JC. simpl rb. rewrite rl_rep1. simpl LP. simpl lpow.
  follow J_E_raw. simpl LP. finish_norm.
Qed.

Lemma acc_form : forall k (l : side), [1]^^(2 * k + 4)%nat *> l = 1 >> [1;1]^^(S k) *> 1 >> l.
Proof.
  intros. rewrite pow11. replace (2 * k + 4)%nat with (S (2 * S k + 1)) by lia.
  simpl. rewrite <- ones_add. simpl. reflexivity.
Qed.

Lemma B_dec : forall k m ms d T R, Forall (fun m => m <> 0%nat) ms ->
  JC (2 * k + 4) (S m :: ms) (rb ((S (S d) :: T) :: R) (const 0)) -->*
  AT (restore ms ++ (repeat 1%nat (S m) ++ Xl k) :: (S d :: T) :: R).
Proof.
  intros k m ms d T R Hms. unfold JC. rewrite acc_form. simpl rb. simpl LP. simpl lpow.
  follow J_dec_raw. rewrite Xcells. follow MergeStep.
  replace ([1;0]^^(S m) *> rl (Xl k) (0 >> 1 >> [1]^^d *> 0 >> rl T (0 >> rb R (const 0))))
    with (rb ((repeat 1%nat (S m) ++ Xl k) :: (S d :: T) :: R) (const 0))
    by (simpl; rewrite rl_app, rl_rep1; reflexivity).
  apply RWb. exact Hms.
Qed.

Lemma B_est : forall x m ms p e T R, Forall (fun m => m <> 0%nat) ms ->
  JC (S x) (S m :: ms) (rb ((1%nat :: repeat 1%nat p ++ S (S e) :: T) :: R) (const 0)) -->*
  AT (restore (S m :: ms) ++ (repeat 1%nat p ++ (x + 4)%nat :: S e :: T) :: R).
Proof.
  intros x m ms p e T R Hms. unfold JC. simpl rb. rewrite rl_app, rl_rep1.
  assert (Hnz : Forall (fun m => m <> 0%nat) (S m :: ms)) by (constructor; [lia | exact Hms]).
  destruct p as [| p].
  - simpl lpow. simpl rl. simpl LP. simpl lpow.
    follow J_est0_raw.
    replace ([1]^^(x + 4) *> 0 >> [1]^^(S e) *> 0 >> rl T (0 >> rb R (const 0)))
      with (rb ((x + 4 :: S e :: T)%nat :: R) (const 0)) by reflexivity.
    change (0 >> 1 >> [0;1]^^m *> 0 >> LP ms) with (LP (S m :: ms)).
    apply RWb. exact Hnz.
  - simpl rl. simpl LP. simpl lpow.
    follow J_est1_raw.
    replace ([1;0]^^(S p) *> [1]^^(x + 4) *> 0 >> [1]^^(S e) *> 0 >> rl T (0 >> rb R (const 0)))
      with (rb ((repeat 1%nat (S p) ++ (x + 4)%nat :: S e :: T) :: R) (const 0))
      by (simpl; rewrite rl_app, rl_rep1; reflexivity).
    change (0 >> 1 >> [0;1]^^m *> 0 >> LP ms) with (LP (S m :: ms)).
    apply RWb. exact Hnz.
Qed.

Lemma LP_head : forall ms, Forall (fun m => m <> 0%nat) ms -> exists l, LP ms = 0 >> l.
Proof.
  intros [| m ms] H.
  - exists (const 0). simpl. apply const_unfold.
  - inversion H; subst. destruct m as [| m]; [congruence |]. simpl. eexists. reflexivity.
Qed.

Lemma B_P : forall k ms R, Forall (fun m => m <> 0%nat) ms ->
  JC (2 * k + 2) ms (rb ([1%nat] :: [2%nat] :: R) (const 0)) -->* AT (restore ms ++ Xl k :: [1%nat] :: R).
Proof.
  intros k ms R Hms. destruct (LP_head ms Hms) as [l Hl].
  unfold JC. replace (2 * k + 2)%nat with (S (2 * k + 1)) by lia.
  simpl rb. simpl rl. rewrite Hl. follow J_P_raw.
  replace (2 * k + 1 + 3)%nat with (2 * k + 4)%nat by lia. rewrite acc_form.
  change ([1]^^2 *> 0 >> 0 >> rb R (const 0)) with (1 >> 1 >> [1]^^0 *> 0 >> 0 >> rb R (const 0)).
  follow (J_dec_raw k 0 (0 >> l) (0 >> 0 >> rb R (const 0))). rewrite Xcells. rewrite <- Hl.
  replace (rl (Xl k) (0 >> 1 >> [1]^^0 *> 0 >> 0 >> rb R (const 0)))
    with (rb (Xl k :: [1%nat] :: R) (const 0)) by reflexivity.
  apply RWb. exact Hms.
Qed.

Lemma B_halt : forall q ms, Forall (fun m => m <> 0%nat) ms ->
  exists c, JC (8 * q + 6) ms (rb [[1%nat]] (const 0)) -->* c /\ halted tm c.
Proof.
  intros q ms Hms. destruct (LP_head ms Hms) as [l Hl].
  eexists. split.
  - unfold JC. replace (8 * q + 6)%nat with (S (8 * q + 5)) by lia.
    simpl rb. simpl rl. rewrite Hl. follow J_P_raw.
    replace (8 * q + 5 + 3)%nat with (8 * S q)%nat by lia.
    apply refill_halt.
  - reflexivity.
Qed.

Lemma B_haltc : forall q ms, Forall (fun m => m <> 0%nat) ms ->
  JC (8 * q + 6) ms (rb [[1%nat]] (const 0)) -->* Halt_cfg (0 >> LP ms) ([1;1;0;0;1;1;0;0]^^(S q) *> 1 >> 1 >> const 0).
Proof.
  intros q ms Hms. destruct (LP_head ms Hms) as [l Hl].
  unfold JC. replace (8 * q + 6)%nat with (S (8 * q + 5)) by lia.
  simpl rb. simpl rl. rewrite Hl. follow J_P_raw.
  replace (8 * q + 5 + 3)%nat with (8 * S q)%nat by lia.
  apply refill_halt.
Qed.

Lemma twos_tail : forall q, [1;1;0;0]^^q *> 1 >> 1 >> const 0 = rb (repeat [2%nat] (S q)) (const 0).
Proof.
  induction q.
  - simpl. rewrite <- !const_unfold. reflexivity.
  - simpl lpow. simpl Str_app. rewrite IHq. reflexivity.
Qed.

Lemma twos_tail8 : forall q, [1;1;0;0;1;1;0;0]^^q *> 1 >> 1 >> const 0 = rb (repeat [2%nat] (S (2 * q))) (const 0).
Proof. intros. rewrite pat8. apply twos_tail. Qed.

Lemma twos_tail8b : forall q, [1;1;0;0;1;1;0;0]^^q *> 1 >> 1 >> 0 >> 0 >> 1 >> 1 >> const 0 = rb (repeat [2%nat] (S (S (2 * q)))) (const 0).
Proof.
  intros. rewrite pat8. replace (S (S (2 * q))) with (S (2 * q + 1)) by lia. rewrite <- twos_tail.
  replace (2 * q + 1)%nat with (S (2 * q)) by lia. clear. generalize (2 * q)%nat. intros n.
  induction n; [reflexivity |]. simpl. rewrite IHn. reflexivity.
Qed.

(** continue after the refill: the nearest passed block (S m ones) gets 4,1; twos follow *)
Lemma B_cont_tail : forall m ms n, Forall (fun m => m <> 0%nat) ms ->
  (0 >> [1]^^2 *> [0;1]^^(S m) *> 0 >> LP ms) {{J}}> rb (repeat [2%nat] (S n)) (const 0) -->*
  AT (restore ms ++ (repeat 1%nat (S m) ++ [4%nat; 1%nat]) :: repeat [2%nat] n).
Proof.
  intros m ms n Hms. simpl repeat. simpl rb. simpl rl.
  follow (J_dec2_raw 0 (1 >> [0;1]^^m *> 0 >> LP ms) (0 >> 0 >> rb (repeat [2%nat] n) (const 0))).
  follow MergeStep.
  replace ([1;0]^^(S m) *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> [1]^^0 *> 0 >> 0 >> rb (repeat [2%nat] n) (const 0))
    with (rb ((repeat 1%nat (S m) ++ [4%nat; 1%nat]) :: repeat [2%nat] n) (const 0))
    by (simpl; rewrite rl_app, rl_rep1; reflexivity).
  apply RWb. exact Hms.
Qed.

Lemma B_refillA : forall q m ms, Forall (fun m => m <> 0%nat) ms ->
  JC (8 * S q) (S m :: ms) (rb [[1%nat]] (const 0)) -->*
  AT (restore ms ++ (repeat 1%nat (S m) ++ [4%nat; 1%nat]) :: repeat [2%nat] (2 * S q)).
Proof.
  intros q m ms Hms. unfold JC.
  replace (8 * S q)%nat with (S (8 * q + 7)) by lia.
  simpl rb. simpl rl. simpl LP. simpl lpow. follow J_P_raw.
  replace (8 * q + 7 + 3)%nat with (8 * S q + 2)%nat by lia.
  change (0 >> 1 >> [0;1]^^m *> 0 >> LP ms) with ([0;1]^^(S m) *> 0 >> LP ms).
  follow (refill_cont_a (S q) m (LP ms)). rewrite twos_tail8.
  apply B_cont_tail. exact Hms.
Qed.

Lemma B_refillB : forall q m ms, Forall (fun m => m <> 0%nat) ms ->
  JC (8 * q + 4) (S m :: ms) (rb [[1%nat]] (const 0)) -->*
  AT (restore ms ++ (repeat 1%nat (S m) ++ [4%nat; 1%nat]) :: repeat [2%nat] (2 * q + 1)).
Proof.
  intros q m ms Hms. unfold JC.
  replace (8 * q + 4)%nat with (S (8 * q + 3)) by lia.
  simpl rb. simpl rl. simpl LP. simpl lpow. follow J_P_raw.
  replace (8 * q + 3 + 3)%nat with (8 * q + 6)%nat by lia.
  change (0 >> 1 >> [0;1]^^m *> 0 >> LP ms) with ([0;1]^^(S m) *> 0 >> LP ms).
  follow (refill_cont_b q m (LP ms)). rewrite twos_tail8b.
  replace (S (S (2 * q))) with (S (2 * q + 1)) by lia.
  apply B_cont_tail. exact Hms.
Qed.

Lemma B_refillV : forall q m ms, Forall (fun m => m <> 0%nat) ms ->
  JC (8 * q + 2) (S (S m) :: ms) (rb [[1%nat]] (const 0)) -->*
  AT (restore ms ++ (repeat 1%nat (S m) ++ [4%nat; 1%nat]) :: repeat [2%nat] (2 * q + 1)).
Proof.
  intros q m ms Hms. unfold JC.
  replace (8 * q + 2)%nat with (S (8 * q + 1)) by lia.
  simpl rb. simpl rl. simpl LP. simpl lpow. follow J_P_raw.
  replace (8 * q + 1 + 3)%nat with (8 * q + 4)%nat by lia.
  change (0 >> 1 >> 0 >> 1 >> [0;1]^^m *> 0 >> LP ms) with ([0;1]^^(S (S m)) *> 0 >> LP ms).
  follow (refill_V q m (LP ms)).
  replace ([1;0]^^(S m) *> 1 >> 1 >> 1 >> 1 >> 0 >> 1 >> 0 >> 0 >> [1;1;0;0;1;1;0;0]^^q *> 1 >> 1 >> const 0)
    with (rb ((repeat 1%nat (S m) ++ [4%nat; 1%nat]) :: repeat [2%nat] (2 * q + 1)) (const 0)).
  - apply RWb. exact Hms.
  - rewrite twos_tail8. replace (2 * q + 1)%nat with (S (2 * q)) by lia. simpl. rewrite rl_app, rl_rep1. reflexivity.
Qed.

Lemma boot : c0 -->* AT [[1%nat; 1%nat; 4%nat; 1%nat; 2%nat]; [1%nat]].
Proof.
  unfold c0, AT. simpl. do 162 st. rewrite <- ?const_unfold. finish.
Qed.
