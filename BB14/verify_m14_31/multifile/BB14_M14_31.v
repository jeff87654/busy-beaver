(** * The 14-state machine M14_31 achieves > f_(omega+2)^31(f_omega^2(3)) and > f_(omega+2)^30(f_(omega+1)^2(3)) and halts *)

From BB8 Require Import Individual142.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB1RA_1RI1RC_0LD1LG_0RE1LD_0RN1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_0LK0LH_1LM--- *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, B)  | A, 1 => Some (1, TM.R, A)
  | B, 0 => Some (1, TM.R, I)  | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)  | C, 1 => Some (1, TM.L, G)
  | D, 0 => Some (0, TM.R, E)  | D, 1 => Some (1, TM.L, D)
  | E, 0 => Some (0, TM.R, N)  | E, 1 => Some (1, TM.R, F)
  | F, 0 => Some (1, TM.R, M)  | F, 1 => Some (0, TM.R, A)
  | G, 0 => Some (1, TM.R, A)  | G, 1 => Some (0, TM.L, H)
  | H, 0 => Some (1, TM.L, G)  | H, 1 => Some (1, TM.L, H)
  | I, 0 => Some (1, TM.R, E)  | I, 1 => Some (0, TM.L, J)
  | J, 0 => Some (1, TM.L, H)  | J, 1 => Some (1, TM.L, I)
  | K, 0 => Some (0, TM.L, L)  | K, 1 => Some (0, TM.L, L)
  | L, 0 => Some (0, TM.L, H)  | L, 1 => Some (1, TM.L, K)
  | M, 0 => Some (0, TM.L, K)  | M, 1 => Some (0, TM.L, H)
  | N, 0 => Some (1, TM.L, M)  | N, 1 => None
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

Lemma lpow_double : forall {T} (xs : list T) m, xs^^(2 * m) = (xs ++ xs)^^m.
Proof.
  induction m. - reflexivity.
  - replace (2 * S m)%nat with (S (S (2 * m))) by lia. cbn [lpow]. rewrite IHm, app_assoc. reflexivity.
Qed.

(** ** Basic shift lemmas *)

Lemma cr_AR_1_1 : forall n l r, l {{A}}> [1]^^n *> r -->* [1]^^n *> l {{A}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_DL_1_1 : forall n l r, [1]^^n *> l <{{D}} r -->* l <{{D}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_HL_1_1 : forall n l r, [1]^^n *> l <{{H}} r -->* l <{{H}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_HL_01_01 : forall n l r, [0; 1]^^n *> l <{{H}} r -->* l <{{H}} [0; 1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_IL_11_10 : forall n l r, [1; 1]^^n *> l <{{I}} r -->* l <{{I}} [1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_KL_11_10 : forall n l r, [1; 1]^^n *> l <{{K}} r -->* l <{{K}} [1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_KL_01_10 : forall n l r, [0; 1]^^n *> l <{{K}} r -->* l <{{K}} [1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** ** Configurations and inner cascade rules *)

Definition z0 : side := const 0.
Definition z1 : side := 0 >> 1 >> const 0.

Definition Ca (j b : nat) (z : side) : Q * tape :=
  ([1]^^b *> [0; 1]^^j *> const 0) {{A}}> (0 >> z).

Definition Ch (j b : nat) (z : side) : Q * tape :=
  ([0; 1]^^j *> const 0) <{{H}} (1 >> [1]^^b *> 0 >> z).

Definition Ce_z (p a c d : nat) (z : side) : Q * tape :=
  ([1]^^(a + 2) *> [0; 1]^^p *> const 0) {{I}}> ([1; 0]^^c *> 0 >> [1; 0]^^d *> z).

Definition Cd_z (p b d : nat) (z : side) : Q * tape :=
  ([1]^^(b + 2) *> [0; 1]^^p *> const 0) {{I}}> ([1; 0]^^d *> z).

Definition blk (a : nat) (z : side) : side :=
  1 >> [1]^^a *> 0 >> z.

Lemma CA_SH : forall j b z,
  Ca j b (1 >> 0 >> z) -->+ Ca (S j) b z.
Proof.
  intros j b z. unfold Ca.
  start_progress.
  follow cr_DL_1_1.
  align_tape.
  execute.
  follow cr_AR_1_1.
  finish_norm.
Qed.

Lemma CA_SH_iter : forall k j b z,
  Ca j b ([1; 0]^^k *> z) -->* Ca (j + k) b z.
Proof.
  induction k; intros j b z.
  - replace (j + 0)%nat with j by lia. finish.
  - simpl.
    eapply evstep_trans; [apply progress_evstep, CA_SH |].
    follow (IHk (S j) b z).
    replace (S j + k)%nat with (j + S k)%nat by lia. finish.
Qed.

Lemma CA_EXIT : forall j b z,
  Ca j b (0 >> z) -->+ ([1]^^(b + 2) *> [0; 1]^^j *> const 0) {{I}}> z.
Proof.
  intros j b z. unfold Ca.
  start_progress.
  finish_norm.
Qed.

Lemma CA_CH : forall j b y,
  Ca j b (1 >> 1 >> y) -->+ Ch j b (1 >> y).
Proof.
  intros j b y. unfold Ca, Ch.
  start_progress.
  follow cr_HL_1_1.
  finish_norm.
Qed.

Lemma CH_0 : forall b z,
  Ch 0 b z -->+ Ca 0 (b + 3) z.
Proof.
  intros b z. unfold Ch, Ca. simpl lpow.
  start_progress.
  follow cr_AR_1_1.
  finish_norm.
Qed.

Lemma CH_S_aux : forall j b z,
  Ch (S j) b z -->+ Ca 0 2 ([1; 0]^^j *> blk (S b) z).
Proof.
  intros j b z. unfold Ch, Ca, blk.
  start_progress.
  follow cr_HL_01_01.
  align_tape.
  execute; finish_norm.
Qed.

Lemma CH_S : forall j b z,
  Ch (S j) b z -->+ Ca j 2 (blk (S b) z).
Proof.
  intros j b z.
  eapply progress_evstep_trans; [apply CH_S_aux |].
  follow (CA_SH_iter j 0 2 (blk (S b) z)).
  finish_norm.
Qed.

Lemma E_EVEN : forall p' k r,
  ([1]^^(2 * k + 2) *> [0; 1]^^(S p') *> const 0) {{I}}> (1 >> 0 >> r) -->+
  Ch p' 1 ([1; 0]^^(S k) *> 0 >> r).
Proof.
  intros p' k r. unfold Ch.
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_IL_11_10.
  execute; finish_norm.
Qed.

Lemma D_REL_2_aux : forall p' k z',
  Ce_z (S p') (2 * k) 0 1 (0 >> z') -->+ Ch p' 0 (0 >> [1; 0]^^(k + 2) *> 0 >> z').
Proof.
  intros p' k z'. unfold Ce_z, Ch.
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_KL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma D_REL_1_z0_aux : forall p' k,
  Ce_z (S p') (2 * k) 0 0 z0 -->+ Ch p' 0 (0 >> [1; 0]^^(k + 1) *> z1).
Proof.
  intros p' k. unfold Ce_z, Ch, z0, z1.
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_KL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma C_REL_aux : forall p' m d z,
  Cd_z (S p') (2 * m + 1) (S d) z -->+ Ch p' 3 (0 >> [1; 0]^^m *> 0 >> [1; 0]^^d *> z).
Proof.
  intros p' m d z. unfold Cd_z, Ch.
  replace (2 * m + 1 + 2)%nat with (1 + (2 * m + 2))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] m). cbn [app].
  start_progress.
  follow cr_IL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma D_STEP_aux : forall p a d z,
  Ce_z p a 0 (S (S d)) z -->+ Ch p (a + 4) (0 >> [1; 0]^^d *> z).
Proof.
  intros p a d z. unfold Ce_z, Ch. norm_nat.
  start_progress.
  follow cr_HL_1_1.
  finish_norm.
Qed.

(** ** K-reload steps and Halting step *)

Lemma K_REL_z0_step1 : forall p m,
  Cd_z p (2 * m + 1) 0 z0 -->+ ([0; 1]^^p *> const 0) <{{K}} ([1; 0]^^(m + 2) *> z1).
Proof.
  intros p m. unfold Cd_z, z0, z1.
  replace (2 * m + 1 + 2)%nat with (1 + (2 * m + 2))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] m). cbn [app].
  start_progress.
  follow cr_KL_11_10.
  finish_norm.
Qed.

Lemma K_REL_z1_step1 : forall p m,
  Cd_z p (2 * m + 1) 0 z1 -->+ ([0; 1]^^p *> const 0) <{{K}} ([1; 0]^^(m + 3) *> z0).
Proof.
  intros p m. unfold Cd_z, z0, z1.
  replace (2 * m + 1 + 2)%nat with (1 + (2 * m + 2))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] m). cbn [app].
  start_progress.
  follow cr_KL_11_10.
  finish_norm.
Qed.

Lemma K_REL_step2_sub : forall d' z,
  const 0 <{{K}} ([1; 0]^^(S d') *> z) -->+ Cd_z 2 3 d' z.
Proof.
  intros d' z. unfold Cd_z. cbn [lpow Str_app].
  start_progress.
Qed.

Lemma K_REL_step2 : forall p d z,
  ([0; 1]^^p *> const 0) <{{K}} ([1; 0]^^(S d) *> z) -->+ Cd_z 2 3 (p + d) z.
Proof.
  intros p d z.
  eapply evstep_progress_trans; [apply cr_KL_01_10 |].
  rewrite <- Str_app_assoc, <- lpow_add.
  replace (p + S d)%nat with (S (p + d))%nat by lia.
  apply K_REL_step2_sub.
Qed.

Definition c_end (p a : nat) : Q * tape :=
  (0 >> 1 >> [1]^^(a + 2) *> [0; 1]^^p *> const 0) {{N}}> (1 >> const 0).

Lemma HALT_step : forall p a,
  Ce_z p a 0 0 z1 -->+ c_end p a.
Proof.
  intros p a. unfold Ce_z, z1, c_end. cbn [lpow Str_app].
  start_progress.
Qed.

Lemma c_end_halted : forall p a, halted tm (c_end p a).
Proof. intros p a. unfold c_end. reflexivity. Qed.

(** ** Exact hierarchy function W and inner transitions *)

From Coq Require Import ZArith.
Close Scope Z_scope.
Local Open Scope nat_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Fixpoint iter {X : Type} (n : nat) (g : X -> X) (x : X) : X :=
  match n with
  | O => x
  | S n' => g (iter n' g x)
  end.

Lemma iter_S' : forall {X : Type} n (g : X -> X) x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl. - reflexivity. - rewrite <- IHn. reflexivity. Qed.

Lemma iter_add : forall {X : Type} a b (g : X -> X) x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl. - reflexivity. - rewrite IHa. reflexivity. Qed.

Fixpoint W (j : nat) (b : nat) : nat :=
  match j with
  | O => b + 3
  | S j' => iter (S b) (W j') 2
  end.

Lemma W_0 : forall b, W 0 b = b + 3.
Proof. reflexivity. Qed.

Lemma W_S : forall j b, W (S j) b = iter (S b) (W j) 2.
Proof. reflexivity. Qed.

Lemma BLK_iter_aux : forall j,
  (forall b z, Ch j b z -->+ Ca j (W j b) z) ->
  forall a b z, Ca j b (blk a z) -->+ Ca (S j) (iter a (W j) b) z.
Proof.
  intros j HCh a. induction a as [| a IHa]; intros b z.
  - apply CA_SH.
  - eapply progress_evstep_trans; [apply CA_CH |].
    eapply evstep_trans; [apply progress_evstep, HCh |].
    rewrite iter_S'.
    apply progress_evstep, IHa.
Qed.

Lemma CH_CA : forall j b z,
  Ch j b z -->+ Ca j (W j b) z.
Proof.
  induction j as [| j IHj]; intros b z.
  - apply CH_0.
  - eapply progress_evstep_trans; [apply CH_S |].
    apply progress_evstep.
    apply (BLK_iter_aux j IHj (S b) 2 z).
Qed.

Lemma CE_EVEN : forall p' k c d z,
  Ce_z (S p') (2 * k) (S c) d z -->+ Ce_z (p' + S k) (W p' 1) c d z.
Proof.
  intros p' k c d z. unfold Ce_z.
  cbn [lpow Str_app].
  eapply progress_evstep_trans; [apply E_EVEN |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  follow (CA_SH_iter (S k) p' (W p' 1) (0 >> [1; 0]^^c *> 0 >> [1; 0]^^d *> z)%sym).
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma D_REL_2 : forall p' k (z' : side),
  Ce_z (S p') (2 * k) 0 1 (0 >> z')%sym -->+ Cd_z p' (W p' 0) (k + 2) (0 >> z')%sym.
Proof.
  intros p' k z'. unfold Cd_z.
  eapply progress_evstep_trans; [apply D_REL_2_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma D_REL_2_z0 : forall p' k,
  Ce_z (S p') (2 * k) 0 1 z0 -->+ Cd_z p' (W p' 0) (k + 2) z0.
Proof.
  intros p' k. unfold z0. rewrite const_unfold. apply D_REL_2.
Qed.

Lemma D_REL_2_z1 : forall p' k,
  Ce_z (S p') (2 * k) 0 1 z1 -->+ Cd_z p' (W p' 0) (k + 2) z1.
Proof.
  intros p' k. unfold z1. apply D_REL_2.
Qed.

Lemma D_REL_1_z0 : forall p' k,
  Ce_z (S p') (2 * k) 0 0 z0 -->+ Cd_z p' (W p' 0) (k + 1) z1.
Proof.
  intros p' k. unfold Cd_z.
  eapply progress_evstep_trans; [apply D_REL_1_z0_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma C_REL : forall p' m d z,
  Cd_z (S p') (2 * m + 1) (S d) z -->+ Ce_z p' (W p' 3) m d z.
Proof.
  intros p' m d z. unfold Ce_z.
  eapply progress_evstep_trans; [apply C_REL_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma D_STEP : forall p a d z,
  Ce_z p a 0 (S (S d)) z -->+ Cd_z p (W p (a + 4)) d z.
Proof.
  intros p a d z. unfold Cd_z.
  eapply progress_evstep_trans; [apply D_STEP_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

(** ** Initial 118 concrete steps from blank tape *)

Lemma init_118 : c0 -->* Cd_z 2 3 5 z0.
Proof.
  unfold Cd_z, z0. cbn [lpow Str_app].
  do 118 step. finish_norm.
Qed.

(** ** Growth, parity, and 3-adic mod-3^17 invariants *)

Ltac absmod x k :=
  let q := fresh "q" in let r := fresh "r" in
  let H1 := fresh "Hdm" in let H2 := fresh "Hmb" in
  pose proof (Nat.div_mod_eq x k) as H1;
  assert (H2 : x mod k < k) by (apply Nat.mod_upper_bound; discriminate);
  set (q := x / k) in *; set (r := x mod k) in *; clearbody q r.
Ltac mods :=
  repeat match goal with
  | H : context[?x mod ?k] |- _ => absmod x k
  | |- context[?x mod ?k] => absmod x k
  | H : context[?x / ?k] |- _ => absmod x k
  | |- context[?x / ?k] => absmod x k
  end.

Lemma iter_lin3 : forall g, (forall a, a + 3 <= g a) -> forall n x, x + 3 * n <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl; [lia |].
  specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_par_nat : forall g, (forall y, g y mod 2 = (y + 1) mod 2) ->
  forall n x, iter n g x mod 2 = (x + n) mod 2.
Proof.
  intros g Hg. induction n; intros x; cbn [iter].
  - f_equal; lia.
  - rewrite Hg. pose proof (IHn x). mods; lia.
Qed.

Lemma W_grow : forall j b, b + 3 <= W j b.
Proof.
  induction j as [| j IHj]; intros b.
  - rewrite W_0. lia.
  - rewrite W_S. pose proof (iter_lin3 (W j) IHj (S b) 2). lia.
Qed.

Lemma W_S_lin3 : forall j b, 3 * b + 5 <= W (S j) b.
Proof.
  intros j b. rewrite W_S.
  pose proof (iter_lin3 (W j) (W_grow j) (S b) 2). lia.
Qed.

Lemma W_par : forall j b, W j b mod 2 = (b + 1) mod 2.
Proof.
  induction j as [| j IHj]; intros b.
  - rewrite W_0. mods; lia.
  - rewrite W_S. rewrite (iter_par_nat (W j) IHj). mods; lia.
Qed.

Lemma iter_W0 : forall n x, iter n (W 0) x = x + 3 * n.
Proof. induction n; intros x; cbn [iter]; [lia | rewrite W_0, IHn; lia]. Qed.

Lemma W_1 : forall b, W 1 b = 3 * b + 5.
Proof. intros b. rewrite W_S, iter_W0. lia. Qed.

Lemma iter_W1_closed : forall n,
  2 * iter n (W 1) 2 + 5 = 3 ^ (n + 2).
Proof.
  induction n as [| n IHn]; cbn [iter].
  - reflexivity.
  - rewrite W_1.
    change (S n + 2) with (S (n + 2)).
    rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma W2_closed : forall b,
  2 * W 2 b + 5 = 3 ^ (b + 3).
Proof.
  intros b. rewrite W_S.
  replace (b + 3) with (S b + 2) by lia.
  apply iter_W1_closed.
Qed.

Lemma W2_ge : forall y, 9 * y + 11 <= W 2 y.
Proof.
  intros y. rewrite W_S.
  change (iter (S y) (W 1) 2) with (W 1 (iter y (W 1) 2)).
  pose proof (iter_lin3 (W 1) (W_grow 1) y 2).
  rewrite W_1. lia.
Qed.

Lemma W_ge3_S_is_W2 : forall j b,
  exists y, 29 <= y /\ W (S (S (S j))) (S b) = W 2 y.
Proof.
  induction j as [| j IHj]; intros b.
  - change (W 3 (S b)) with (W 2 (iter (S b) (W 2) 2)).
    exists (iter (S b) (W 2) 2). split; [| reflexivity].
    change (iter (S b) (W 2) 2) with (W 2 (iter b (W 2) 2)).
    pose proof (iter_lin3 (W 2) (W_grow 2) b 2) as H0.
    pose proof (W2_ge (iter b (W 2) 2)) as H1. lia.
  - change (W (S (S (S (S j)))) (S b)) with (W (S (S (S j))) (iter (S b) (W (S (S (S j)))) 2)).
    pose proof (iter_lin3 (W (S (S (S j)))) (W_grow (S (S (S j)))) (S b) 2) as H0.
    destruct (iter (S b) (W (S (S (S j)))) 2) as [| z]; [lia |].
    apply IHj.
Qed.

Definition is_W_even (a : nat) : Prop :=
  2 <= a /\ a mod 2 = 0 /\ 136 <= a / 2 /\
  (Z.of_nat (a / 2) mod 129140163 = 96855121)%Z /\
  (Z.of_nat ((a / 2 + 2) / 3) mod 43046721 = 32285041)%Z /\
  a / 2 + 2 = 3 * ((a / 2 + 2) / 3).

Definition is_W_odd (b : nat) : Prop :=
  b = 2 * (b / 2) + 1 /\ 59 <= b / 2 /\
  (Z.of_nat (b / 2) mod 129140163 = 32285039)%Z.

Lemma Z_pow_3_17 : Z.of_nat (3 ^ 17) = 129140163%Z.
Proof.
  rewrite Nat2Z.inj_pow. reflexivity.
Qed.

Lemma W_ge3_odd : forall p b,
  3 <= p -> b mod 2 = 1 -> is_W_even (W p b).
Proof.
  intros [| [| [| j]]] [| b'] Hp Hb; try lia.
  - cbn in Hb. discriminate.
  - destruct (W_ge3_S_is_W2 j b') as [y [Hy Hw]].
    pose proof (W_par (S (S (S j))) (S b')) as Hpar.
    rewrite Hw in *.
    pose proof (W2_ge y) as Hge.
    assert (Hev : W 2 y mod 2 = 0) by (mods; lia).
    assert (Hpow : 2 * W 2 y + 5 = 3 ^ (y - 14) * 3 ^ 17).
    { rewrite W2_closed. replace (y + 3) with ((y - 14) + 17) by lia. apply Nat.pow_add_r. }
    set (a := W 2 y) in *. clearbody a. clear Hw Hpar.
    assert (Ha2 : a = 2 * (a / 2) /\ 136 <= a / 2) by (mods; lia).
    destruct Ha2 as [Ha_eq Ha_ge].
    assert (Hpow4 : 4 * (a / 2) + 5 = 3 ^ (y - 14) * 3 ^ 17) by lia.
    pose proof (f_equal Z.of_nat Hpow4) as HZ4.
    rewrite Nat2Z.inj_add, !Nat2Z.inj_mul, Z_pow_3_17 in HZ4.
    change (Z.of_nat 4) with 4%Z in HZ4.
    change (Z.of_nat 5) with 5%Z in HZ4.
    clear Hpow Hpow4.
    set (q := Z.of_nat (3 ^ (y - 14))) in *. clearbody q.
    assert (Hm1 : (Z.of_nat (a / 2) mod 129140163 = 96855121)%Z).
    { assert (Hz : (Z.of_nat (a / 2) = 96855121 + (32285041 * q - Z.of_nat (a / 2) - 2) * 129140163)%Z) by lia.
      rewrite Hz, Z.mod_add by lia. reflexivity. }
    assert (Ha6 : a / 2 + 2 = 3 * ((a / 2 + 2) / 3)).
    { pose proof (Nat.div_mod_eq (a / 2 + 2) 3) as Hdm.
      assert ((a / 2 + 2) mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
      set (d3 := (a / 2 + 2) / 3) in *. set (r3 := (a / 2 + 2) mod 3) in *. clearbody d3 r3.
      lia. }
    unfold is_W_even.
    split; [lia | split; [exact Hev | split; [exact Ha_ge | split; [exact Hm1 | split; [| exact Ha6]]]]].
    pose proof (f_equal Z.of_nat Ha6) as HZa6.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul in HZa6.
    change (Z.of_nat 2) with 2%Z in HZa6.
    change (Z.of_nat 3) with 3%Z in HZa6.
    assert (Hz : (Z.of_nat ((a / 2 + 2) / 3) = 32285041 + (32285041 * q - 3 * Z.of_nat ((a / 2 + 2) / 3)) * 43046721)%Z) by lia.
    rewrite Hz, Z.mod_add by lia. reflexivity.
Qed.

Lemma W_ge3_even : forall p b,
  3 <= p -> 1 <= b -> b mod 2 = 0 -> is_W_odd (W p b).
Proof.
  intros [| [| [| j]]] [| b'] Hp Hb Hev; try lia.
  destruct (W_ge3_S_is_W2 j b') as [y [Hy Hw]].
  pose proof (W_par (S (S (S j))) (S b')) as Hpar.
  rewrite Hw in *.
  pose proof (W2_ge y) as Hge.
  assert (Hodd : W 2 y mod 2 = 1) by (mods; lia).
  assert (Hpow : 2 * W 2 y + 5 = 3 ^ (y - 14) * 3 ^ 17).
  { rewrite W2_closed. replace (y + 3) with ((y - 14) + 17) by lia. apply Nat.pow_add_r. }
  set (w := W 2 y) in *. clearbody w. clear Hw Hpar.
  assert (Hw2 : w = 2 * (w / 2) + 1 /\ 59 <= w / 2) by (mods; lia).
  destruct Hw2 as [Hw_eq Hw_ge].
  assert (Hpow4 : 4 * (w / 2) + 7 = 3 ^ (y - 14) * 3 ^ 17) by lia.
  pose proof (f_equal Z.of_nat Hpow4) as HZ4.
  rewrite Nat2Z.inj_add, !Nat2Z.inj_mul, Z_pow_3_17 in HZ4.
  change (Z.of_nat 4) with 4%Z in HZ4.
  change (Z.of_nat 7) with 7%Z in HZ4.
  clear Hpow Hpow4.
  set (q := Z.of_nat (3 ^ (y - 14))) in *. clearbody q.
  unfold is_W_odd.
  split; [exact Hw_eq | split; [exact Hw_ge |]].
  assert (Hz : (Z.of_nat (w / 2) = 32285039 + (32285041 * q - Z.of_nat (w / 2) - 2) * 129140163)%Z) by lia.
  rewrite Hz, Z.mod_add by lia. reflexivity.
Qed.

Lemma W_ge4_zero : forall p',
  4 <= p' -> is_W_odd (W p' 0).
Proof.
  intros [| p''] Hp'; [lia |].
  change (W (S p'') 0) with (W p'' 2).
  apply W_ge3_even; [lia | lia | reflexivity].
Qed.

Lemma mod2_even : forall a, a mod 2 = 0 -> a = 2 * (a / 2).
Proof.
  intros a Ha. pose proof (Nat.div_mod_eq a 2). lia.
Qed.

Opaque W.

(** ** Macro-step functions and modular transition rules *)

Definition Kc (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  (p + a / 2, W (p - 1) 1).

Definition Kc_full (pb : nat * nat) : nat * nat :=
  let '(p, b) := pb in
  iter (b / 2) Kc (p - 1, W (p - 1) 3).

Definition Kd_step (pb : nat * nat) : nat * nat :=
  let '(p', a') := Kc_full pb in
  (p', W p' (a' + 4)).

Definition Kd_iter (m : nat) (pb : nat * nat) : nat * nat :=
  iter m Kd_step pb.

Definition D_reload (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  (p - 1, W (p - 1) 0).

Definition pb_K0 : nat * nat :=
  (8, W 8 8).

Definition D2_round (pa : nat * nat) : nat * nat :=
  Kd_iter ((snd pa / 2 + 2) / 3) (D_reload pa).

Definition D1_round (pa : nat * nat) : nat * nat :=
  Kc_full (Kd_iter ((snd pa / 2 + 2) / 3 - 1) (D_reload pa)).

Definition K0_z0_round (pb : nat * nat) : nat * nat :=
  Kd_iter ((fst pb + snd pb / 2 - 2) / 3) pb_K0.

Definition K1_z0_round (pb : nat * nat) : nat * nat :=
  Kc_full (Kd_iter ((fst pb + snd pb / 2 - 3) / 3) pb_K0).

Definition K2_z0_round (pb : nat * nat) : nat * nat :=
  Kc_full (Kd_iter ((fst pb + snd pb / 2 - 4) / 3) pb_K0).

Definition K0_z1_round (pb : nat * nat) : nat * nat :=
  Kd_iter ((fst pb + snd pb / 2 - 1) / 3) pb_K0.

Definition K1_z1_round (pb : nat * nat) : nat * nat :=
  Kc_full (Kd_iter ((fst pb + snd pb / 2 - 2) / 3) pb_K0).

Definition K2_z1_round (pb : nat * nat) : nat * nat :=
  Kc_full (Kd_iter ((fst pb + snd pb / 2 - 3) / 3) pb_K0).

Lemma Kc_unfold : forall p a, Kc (p, a) = (p + a / 2, W (p - 1) 1). Proof. reflexivity. Qed.
Lemma Kc_full_unfold : forall p b, Kc_full (p, b) = iter (b / 2) Kc (p - 1, W (p - 1) 3). Proof. reflexivity. Qed.
Lemma Kd_step_unfold : forall pb, Kd_step pb = let '(p', a') := Kc_full pb in (p', W p' (a' + 4)). Proof. reflexivity. Qed.
Lemma Kd_iter_unfold : forall m pb, Kd_iter m pb = iter m Kd_step pb. Proof. reflexivity. Qed.
Lemma D_reload_unfold : forall p a, D_reload (p, a) = (p - 1, W (p - 1) 0). Proof. reflexivity. Qed.
Lemma pb_K0_unfold : pb_K0 = (8, W 8 8). Proof. reflexivity. Qed.

Lemma step_2_3 : forall d' z,
  Cd_z 2 3 (S (S (S d'))) z -->+ Cd_z (fst pb_K0) (snd pb_K0) d' z.
Proof.
  intros d' z. unfold pb_K0. cbn [fst snd].
  eapply progress_evstep_trans; [apply (C_REL 1 1 (S (S d')) z) |].
  Transparent W.
  change (W 1 3) with (2 * 7).
  eapply evstep_trans; [apply progress_evstep, (CE_EVEN 0 7 0 (S (S d')) z) |].
  change (0 + S 7) with 8.
  change (W 0 1) with 4.
  Opaque W.
  apply progress_evstep, D_STEP.
Qed.

Lemma K_REL_z0 : forall p m,
  2 <= m ->
  Cd_z p (2 * m + 1) 0 z0 -->+ Cd_z (fst pb_K0) (snd pb_K0) (p + m - 2) z1.
Proof.
  intros p m Hm.
  eapply progress_evstep_trans; [apply K_REL_z0_step1 |].
  replace (m + 2) with (S (m + 1)) by lia.
  eapply evstep_trans; [apply progress_evstep, K_REL_step2 |].
  replace (p + (m + 1)) with (S (S (S (p + m - 2)))) at 1 by lia.
  apply progress_evstep, step_2_3.
Qed.

Lemma K_REL_z1 : forall p m,
  1 <= m ->
  Cd_z p (2 * m + 1) 0 z1 -->+ Cd_z (fst pb_K0) (snd pb_K0) (p + m - 1) z0.
Proof.
  intros p m Hm.
  eapply progress_evstep_trans; [apply K_REL_z1_step1 |].
  replace (m + 3) with (S (m + 2)) by lia.
  eapply evstep_trans; [apply progress_evstep, K_REL_step2 |].
  replace (p + (m + 2)) with (S (S (S (p + m - 1)))) at 1 by lia.
  apply progress_evstep, step_2_3.
Qed.

Lemma init_pb0 : c0 -->* Cd_z (fst pb_K0) (snd pb_K0) 2 z0.
Proof.
  eapply evstep_trans; [exact init_118 |].
  apply progress_evstep, (step_2_3 2 z0).
Qed.

Lemma Z_div3_nat : forall (d r : nat) (M c : Z),
  (0 < M)%Z ->
  r <= d ->
  (Z.of_nat d mod (3 * M) = c)%Z ->
  (c mod 3 = Z.of_nat r)%Z ->
  d = 3 * ((d - r) / 3) + r /\
  (Z.of_nat ((d - r) / 3) mod M = (c / 3) mod M)%Z.
Proof.
  intros d r M c HM Hrd Hd Hcr.
  assert (Hc_bound : (0 <= c < 3 * M)%Z) by (rewrite <- Hd; apply Z.mod_pos_bound; lia).
  pose proof (Z.div_mod (Z.of_nat d) (3 * M) ltac:(lia)) as HdmZ.
  rewrite Hd in HdmZ.
  pose proof (Z.div_mod c 3 ltac:(lia)) as HcmZ.
  rewrite Hcr in HcmZ.
  pose proof (Nat.div_mod_eq (d - r) 3) as HdmN.
  assert (HremN : (d - r) mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
  pose proof (f_equal Z.of_nat HdmN) as HdmNZ.
  rewrite Nat2Z.inj_sub, Nat2Z.inj_add, Nat2Z.inj_mul in HdmNZ by lia.
  change (Z.of_nat 3) with 3%Z in HdmNZ.
  set (qZ := (Z.of_nat d / (3 * M))%Z) in *. clearbody qZ.
  set (qc := (c / 3)%Z) in *. clearbody qc.
  set (qN := (d - r) / 3) in *. clearbody qN.
  set (rN := (d - r) mod 3) in *. clearbody rN.
  assert (HrN0 : rN = 0) by lia.
  split; [lia |].
  assert (Hq_eq : (Z.of_nat qN = qc + qZ * M)%Z) by lia.
  rewrite Hq_eq, Z.mod_add by lia. reflexivity.
Qed.

Lemma Z_mod_div_factor : forall (x M1 M2 : Z),
  (0 < M1)%Z -> (0 < M2)%Z -> (M1 mod M2 = 0)%Z ->
  ((x mod M1) mod M2 = x mod M2)%Z.
Proof.
  intros x M1 M2 HM1 HM2 Hdiv.
  pose proof (Z.div_mod M1 M2 ltac:(lia)) as HM.
  rewrite Hdiv in HM.
  pose proof (Z.div_mod x M1 ltac:(lia)) as Hx.
  replace x with (x mod M1 + (M1 / M2 * (x / M1)) * M2)%Z at 2 by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma Kc_step : forall c d z pa,
  1 <= fst pa -> snd pa mod 2 = 0 ->
  Ce_z (fst pa) (snd pa) (S c) d z -->+ Ce_z (fst (Kc pa)) (snd (Kc pa)) c d z.
Proof.
  intros c d z [p a] Hp Hev. cbn [fst snd Kc] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  pose proof (mod2_even a Hev) as Ha.
  replace (S p' + a / 2) with (p' + S (a / 2)) by lia.
  rewrite Ha at 1.
  apply CE_EVEN.
Qed.

Lemma Kc_props_mod : forall pa,
  4 <= fst pa -> is_W_even (snd pa) ->
  fst pa + 1 <= fst (Kc pa) /\
  (Z.of_nat (fst (Kc pa)) mod 129140163 = (Z.of_nat (fst pa) + 96855121) mod 129140163)%Z /\
  is_W_even (snd (Kc pa)).
Proof.
  intros [p a] Hp Ha. cbn [fst snd Kc] in *.
  assert (Hw : is_W_even (W (p - 1) 1)) by (apply W_ge3_odd; [lia | reflexivity]).
  destruct Ha as [_ [_ [Ha_ge [Ha_mod _]]]].
  split; [lia | split; [| exact Hw]].
  rewrite Nat2Z.inj_add.
  rewrite <- Zplus_mod_idemp_r, Ha_mod. reflexivity.
Qed.

Lemma Kc_loop_mod : forall c d z pa,
  4 <= fst pa -> is_W_even (snd pa) ->
  Ce_z (fst pa) (snd pa) c d z -->* Ce_z (fst (iter c Kc pa)) (snd (iter c Kc pa)) 0 d z /\
  fst pa + c <= fst (iter c Kc pa) /\
  (Z.of_nat (fst (iter c Kc pa)) mod 129140163 =
    (Z.of_nat (fst pa) + 96855121 * Z.of_nat c) mod 129140163)%Z /\
  is_W_even (snd (iter c Kc pa)).
Proof.
  induction c as [| c IHc]; intros d z pa Hp Ha.
  - cbn [iter]. split; [finish | split; [lia | split; [f_equal; lia | exact Ha]]].
  - rewrite iter_S'.
    destruct Ha as [Ha_ge [Hev [Ha2_ge [Ha_mod [Ha_div3 Ha_eq3]]]]].
    assert (Ha_full : is_W_even (snd pa))
      by (unfold is_W_even; exact (conj Ha_ge (conj Hev (conj Ha2_ge (conj Ha_mod (conj Ha_div3 Ha_eq3)))))).
    destruct (Kc_props_mod pa Hp Ha_full) as [Hp1 [Hm1 Ha1]].
    destruct (IHc d z (Kc pa) ltac:(lia) Ha1) as [Hrun [Hp2 [Hm2 Ha2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, (Kc_step c d z pa ltac:(lia) Hev) | exact Hrun].
    + lia.
    + rewrite Hm2, <- Zplus_mod_idemp_l, Hm1, Zplus_mod_idemp_l.
      f_equal; lia.
    + exact Ha2.
Qed.

Lemma Kc_full_all : forall d z pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) (S d) z -->+ Ce_z (fst (Kc_full pb)) (snd (Kc_full pb)) 0 d z /\
  fst pb + 58 <= fst (Kc_full pb) /\
  (Z.of_nat (fst (Kc_full pb)) mod 129140163 =
    (Z.of_nat (fst pb) + 121068904) mod 129140163)%Z /\
  is_W_even (snd (Kc_full pb)).
Proof.
  intros d z [p b] Hp [Hb_eq [Hb_ge Hb_mod]]. cbn [fst snd Kc_full] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  assert (Hw3 : is_W_even (W p' 3)) by (apply W_ge3_odd; [lia | reflexivity]).
  destruct (Kc_loop_mod (b / 2) d z (p', W p' 3) ltac:(cbn; lia) Hw3)
    as [Hrun [Hp1 [Hm1 Ha1]]].
  cbn [fst snd] in *.
  split; [| split; [| split]].
  - rewrite Hb_eq at 1.
    eapply progress_evstep_trans; [apply C_REL | exact Hrun].
  - lia.
  - rewrite Hm1, <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hb_mod, Zplus_mod_idemp_r.
    replace (Z.of_nat p' + 96855121 * 32285039)%Z
      with ((Z.of_nat (S p') + 121068904) + 24213778 * 129140163)%Z by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - exact Ha1.
Qed.

Lemma Kd_step_all : forall d z pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) (S (S (S d))) z -->+ Cd_z (fst (Kd_step pb)) (snd (Kd_step pb)) d z /\
  fst pb + 58 <= fst (Kd_step pb) /\
  (Z.of_nat (fst (Kd_step pb)) mod 129140163 =
    (Z.of_nat (fst pb) + 121068904) mod 129140163)%Z /\
  is_W_odd (snd (Kd_step pb)).
Proof.
  intros d z pb Hp Hb.
  unfold Kd_step.
  destruct (Kc_full_all (S (S d)) z pb Hp Hb) as [Hkc [Hp1 [Hm1 Ha1]]].
  set (pa' := Kc_full pb) in *.
  destruct pa' as [p' a']. cbn [fst snd] in *.
  destruct Ha1 as [_ [Ha_ev _]].
  pose proof (mod2_even a' Ha_ev) as Ha_eq.
  assert (Ha4_ev : (a' + 4) mod 2 = 0).
  { replace (a' + 4) with (0 + (a' / 2 + 2) * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (Hw : is_W_odd (W p' (a' + 4))) by (apply W_ge3_even; [lia | lia | exact Ha4_ev]).
  split; [| split; [| split]].
  - eapply progress_evstep_trans; [exact Hkc | apply progress_evstep, D_STEP].
  - exact Hp1.
  - exact Hm1.
  - exact Hw.
Qed.

Lemma Kd_loop : forall m r z pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) (3 * m + r) z -->* Cd_z (fst (Kd_iter m pb)) (snd (Kd_iter m pb)) r z /\
  fst pb + 58 * m <= fst (Kd_iter m pb) /\
  (Z.of_nat (fst (Kd_iter m pb)) mod 129140163 =
    (Z.of_nat (fst pb) + 121068904 * Z.of_nat m) mod 129140163)%Z /\
  is_W_odd (snd (Kd_iter m pb)).
Proof.
  unfold Kd_iter.
  induction m as [| m IHm]; intros r z pb Hp Hb.
  - cbn [iter]. replace (3 * 0 + r) with r by lia.
    split; [finish | split; [lia | split; [f_equal; lia | exact Hb]]].
  - rewrite iter_S'.
    replace (3 * S m + r) with (S (S (S (3 * m + r)))) by lia.
    destruct (Kd_step_all (3 * m + r) z pb Hp Hb) as [Hstep [Hp1 [Hm1 Hb1]]].
    destruct (IHm r z (Kd_step pb) ltac:(lia) Hb1) as [Hrun [Hp2 [Hm2 Hb2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, Hstep | exact Hrun].
    + lia.
    + rewrite Hm2, <- Zplus_mod_idemp_l, Hm1, Zplus_mod_idemp_l.
      f_equal; lia.
    + exact Hb2.
Qed.

Lemma D_reload_2_z0_all : forall pa,
  6 <= fst pa -> 2 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_z (fst pa) (snd pa) 0 1 z0 -->+ Cd_z (fst (D_reload pa)) (snd (D_reload pa)) (snd pa / 2 + 2) z0 /\
  5 <= fst (D_reload pa) /\
  fst (D_reload pa) = fst pa - 1 /\
  is_W_odd (snd (D_reload pa)).
Proof.
  intros [p a] Hp Ha Hev. cbn [fst snd D_reload] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  pose proof (mod2_even a Hev) as Ha_eq.
  assert (Hw : is_W_odd (W p' 0)) by (apply W_ge4_zero; lia).
  split; [| split; [| split]].
  - rewrite Ha_eq at 1. apply D_REL_2_z0.
  - lia.
  - reflexivity.
  - exact Hw.
Qed.

Lemma D_reload_2_z1_all : forall pa,
  6 <= fst pa -> 2 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_z (fst pa) (snd pa) 0 1 z1 -->+ Cd_z (fst (D_reload pa)) (snd (D_reload pa)) (snd pa / 2 + 2) z1 /\
  5 <= fst (D_reload pa) /\
  fst (D_reload pa) = fst pa - 1 /\
  is_W_odd (snd (D_reload pa)).
Proof.
  intros [p a] Hp Ha Hev. cbn [fst snd D_reload] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  pose proof (mod2_even a Hev) as Ha_eq.
  assert (Hw : is_W_odd (W p' 0)) by (apply W_ge4_zero; lia).
  split; [| split; [| split]].
  - rewrite Ha_eq at 1. apply D_REL_2_z1.
  - lia.
  - reflexivity.
  - exact Hw.
Qed.

Lemma D_reload_1_z0_all : forall pa,
  6 <= fst pa -> 2 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_z (fst pa) (snd pa) 0 0 z0 -->+ Cd_z (fst (D_reload pa)) (snd (D_reload pa)) (snd pa / 2 + 1) z1 /\
  5 <= fst (D_reload pa) /\
  fst (D_reload pa) = fst pa - 1 /\
  is_W_odd (snd (D_reload pa)).
Proof.
  intros [p a] Hp Ha Hev. cbn [fst snd D_reload] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  pose proof (mod2_even a Hev) as Ha_eq.
  assert (Hw : is_W_odd (W p' 0)) by (apply W_ge4_zero; lia).
  split; [| split; [| split]].
  - rewrite Ha_eq at 1. apply D_REL_1_z0.
  - lia.
  - reflexivity.
  - exact Hw.
Qed.

Lemma pb_K0_props :
  7 <= fst pb_K0 /\
  (Z.of_nat (fst pb_K0) mod 129140163 = 8)%Z /\
  is_W_odd (snd pb_K0).
Proof.
  unfold pb_K0. cbn [fst snd].
  assert (Hw : is_W_odd (W 8 8)) by (apply W_ge3_even; [lia | lia | reflexivity]).
  split; [lia | split; [reflexivity | exact Hw]].
Qed.

Lemma K_reload_z0_all : forall pb,
  7 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) 0 z0 -->+ Cd_z (fst pb_K0) (snd pb_K0) (fst pb + snd pb / 2 - 2) z1 /\
  7 <= fst pb_K0 /\
  (Z.of_nat (fst pb_K0) mod 129140163 = 8)%Z /\
  is_W_odd (snd pb_K0).
Proof.
  intros [p b] Hp [Hb_eq [Hb_ge _]]. cbn [fst snd] in *.
  destruct pb_K0_props as [HpK [HmK HbK]].
  split; [| split; [exact HpK | split; [exact HmK | exact HbK]]].
  rewrite Hb_eq at 1. apply K_REL_z0; lia.
Qed.

Lemma K_reload_z1_all : forall pb,
  7 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) 0 z1 -->+ Cd_z (fst pb_K0) (snd pb_K0) (fst pb + snd pb / 2 - 1) z0 /\
  7 <= fst pb_K0 /\
  (Z.of_nat (fst pb_K0) mod 129140163 = 8)%Z /\
  is_W_odd (snd pb_K0).
Proof.
  intros [p b] Hp [Hb_eq [Hb_ge _]]. cbn [fst snd] in *.
  destruct pb_K0_props as [HpK [HmK HbK]].
  split; [| split; [exact HpK | split; [exact HmK | exact HbK]]].
  rewrite Hb_eq at 1. apply K_REL_z1; lia.
Qed.

Opaque Kc Kc_full Kd_step Kd_iter D_reload pb_K0
  D2_round D1_round K0_z0_round K1_z0_round K2_z0_round K0_z1_round K1_z1_round K2_z1_round.

Lemma round_D2_z0_step : forall pa (M r_in r_out : Z),
  (c0 -->* Ce_z (fst pa) (snd pa) 0 1 z0 /\
   7 <= fst pa /\
   (Z.of_nat (fst pa) mod M = r_in)%Z /\
   is_W_even (snd pa)) ->
  (0 < M)%Z ->
  (43046721 mod M = 0)%Z ->
  ((r_in + 30267225) mod M = r_out)%Z ->
  c0 -->* Cd_z (fst (D2_round pa)) (snd (D2_round pa)) 0 z0 /\
  7 <= fst (D2_round pa) /\
  (Z.of_nat (fst (D2_round pa)) mod M = r_out)%Z /\
  is_W_odd (snd (D2_round pa)).
Proof.
  intros pa M r_in r_out [Hrun [Hp [Hm_in Ha]]] HM HdivM Hr_out.
  Transparent D2_round. unfold D2_round. Opaque D2_round.
  destruct Ha as [Ha_ge [Ha_ev [Ha2_ge [_ [Hm_div3 Ha_eq3]]]]].
  destruct (D_reload_2_z0_all pa ltac:(lia) Ha_ge Ha_ev) as [Hrel [Hp0 [Hf0 Hb0]]].
  destruct (Kd_loop ((snd pa / 2 + 2) / 3) 0 z0 (D_reload pa) Hp0 Hb0)
    as [Hloop [Hp1 [Hm1 Hb1]]].
  assert (Hdiv17 : (129140163 mod M = 0)%Z).
  { pose proof (Z.div_mod 43046721 M ltac:(lia)) as Hdm. rewrite HdivM in Hdm.
    replace 129140163%Z with ((3 * (43046721 / M)) * M)%Z by lia.
    apply Z_mod_mult. }
  split; [| split; [lia | split; [| exact Hb1]]].
  - eapply evstep_trans; [exact Hrun |].
    eapply evstep_trans; [apply progress_evstep, Hrel |].
    replace (snd pa / 2 + 2) with (3 * ((snd pa / 2 + 2) / 3) + 0) at 1 by lia.
    exact Hloop.
  - rewrite <- (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    rewrite Hm1, Hf0, (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    assert (Hm_M : (Z.of_nat ((snd pa / 2 + 2) / 3) mod M = 32285041 mod M)%Z).
    { rewrite <- (Z_mod_div_factor _ 43046721 M ltac:(lia) HM HdivM), Hm_div3.
      reflexivity. }
    rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hm_M, Zmult_mod_idemp_r, Zplus_mod_idemp_r.
    rewrite Nat2Z.inj_sub by lia. change (Z.of_nat 1) with 1%Z.
    pose proof (Z.div_mod 43046721 M ltac:(lia)) as HdmM. rewrite HdivM in HdmM.
    replace (Z.of_nat (fst pa) - 1 + 121068904 * 32285041)%Z
      with ((Z.of_nat (fst pa) + 30267225) + (90801678 * (43046721 / M)) * M)%Z by lia.
    rewrite Z.mod_add by lia.
    rewrite <- Zplus_mod_idemp_l, Hm_in. exact Hr_out.
Qed.

Lemma round_D2_z1_step : forall pa (M r_in r_out : Z),
  (c0 -->* Ce_z (fst pa) (snd pa) 0 1 z1 /\
   7 <= fst pa /\
   (Z.of_nat (fst pa) mod M = r_in)%Z /\
   is_W_even (snd pa)) ->
  (0 < M)%Z ->
  (43046721 mod M = 0)%Z ->
  ((r_in + 30267225) mod M = r_out)%Z ->
  c0 -->* Cd_z (fst (D2_round pa)) (snd (D2_round pa)) 0 z1 /\
  7 <= fst (D2_round pa) /\
  (Z.of_nat (fst (D2_round pa)) mod M = r_out)%Z /\
  is_W_odd (snd (D2_round pa)).
Proof.
  intros pa M r_in r_out [Hrun [Hp [Hm_in Ha]]] HM HdivM Hr_out.
  Transparent D2_round. unfold D2_round. Opaque D2_round.
  destruct Ha as [Ha_ge [Ha_ev [Ha2_ge [_ [Hm_div3 Ha_eq3]]]]].
  destruct (D_reload_2_z1_all pa ltac:(lia) Ha_ge Ha_ev) as [Hrel [Hp0 [Hf0 Hb0]]].
  destruct (Kd_loop ((snd pa / 2 + 2) / 3) 0 z1 (D_reload pa) Hp0 Hb0)
    as [Hloop [Hp1 [Hm1 Hb1]]].
  assert (Hdiv17 : (129140163 mod M = 0)%Z).
  { pose proof (Z.div_mod 43046721 M ltac:(lia)) as Hdm. rewrite HdivM in Hdm.
    replace 129140163%Z with ((3 * (43046721 / M)) * M)%Z by lia.
    apply Z_mod_mult. }
  split; [| split; [lia | split; [| exact Hb1]]].
  - eapply evstep_trans; [exact Hrun |].
    eapply evstep_trans; [apply progress_evstep, Hrel |].
    replace (snd pa / 2 + 2) with (3 * ((snd pa / 2 + 2) / 3) + 0) at 1 by lia.
    exact Hloop.
  - rewrite <- (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    rewrite Hm1, Hf0, (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    assert (Hm_M : (Z.of_nat ((snd pa / 2 + 2) / 3) mod M = 32285041 mod M)%Z).
    { rewrite <- (Z_mod_div_factor _ 43046721 M ltac:(lia) HM HdivM), Hm_div3.
      reflexivity. }
    rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hm_M, Zmult_mod_idemp_r, Zplus_mod_idemp_r.
    rewrite Nat2Z.inj_sub by lia. change (Z.of_nat 1) with 1%Z.
    pose proof (Z.div_mod 43046721 M ltac:(lia)) as HdmM. rewrite HdivM in HdmM.
    replace (Z.of_nat (fst pa) - 1 + 121068904 * 32285041)%Z
      with ((Z.of_nat (fst pa) + 30267225) + (90801678 * (43046721 / M)) * M)%Z by lia.
    rewrite Z.mod_add by lia.
    rewrite <- Zplus_mod_idemp_l, Hm_in. exact Hr_out.
Qed.

Lemma round_D1_z0_step : forall pa (M r_in r_out : Z),
  (c0 -->* Ce_z (fst pa) (snd pa) 0 0 z0 /\
   7 <= fst pa /\
   (Z.of_nat (fst pa) mod M = r_in)%Z /\
   is_W_even (snd pa)) ->
  (0 < M)%Z ->
  (43046721 mod M = 0)%Z ->
  ((r_in + 30267225) mod M = r_out)%Z ->
  c0 -->* Ce_z (fst (D1_round pa)) (snd (D1_round pa)) 0 1 z1 /\
  7 <= fst (D1_round pa) /\
  (Z.of_nat (fst (D1_round pa)) mod M = r_out)%Z /\
  is_W_even (snd (D1_round pa)).
Proof.
  intros pa M r_in r_out [Hrun [Hp [Hm_in Ha]]] HM HdivM Hr_out.
  Transparent D1_round. unfold D1_round. Opaque D1_round.
  destruct Ha as [Ha_ge [Ha_ev [Ha2_ge [_ [Hm_div3 Ha_eq3]]]]].
  destruct (D_reload_1_z0_all pa ltac:(lia) Ha_ge Ha_ev) as [Hrel [Hp0 [Hf0 Hb0]]].
  set (m := (snd pa / 2 + 2) / 3) in *.
  assert (Hm_pos : 1 <= m) by lia.
  destruct (Kd_loop (m - 1) 2 z1 (D_reload pa) Hp0 Hb0)
    as [Hloop [Hp1 [Hm1 Hb1]]].
  destruct (Kc_full_all 1 z1 (Kd_iter (m - 1) (D_reload pa)) ltac:(lia) Hb1)
    as [Hkc [Hp2 [Hm2 Ha2]]].
  assert (Hdiv17 : (129140163 mod M = 0)%Z).
  { pose proof (Z.div_mod 43046721 M ltac:(lia)) as Hdm. rewrite HdivM in Hdm.
    replace 129140163%Z with ((3 * (43046721 / M)) * M)%Z by lia.
    apply Z_mod_mult. }
  split; [| split; [lia | split; [| exact Ha2]]].
  - eapply evstep_trans; [exact Hrun |].
    eapply evstep_trans; [apply progress_evstep, Hrel |].
    replace (snd pa / 2 + 1) with (3 * (m - 1) + 2) at 1 by lia.
    eapply evstep_trans; [exact Hloop |].
    apply progress_evstep, Hkc.
  - rewrite <- (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    rewrite Hm2, <- Zplus_mod_idemp_l, Hm1, Zplus_mod_idemp_l.
    rewrite Nat2Z.inj_sub by lia. change (Z.of_nat 1) with 1%Z.
    replace (Z.of_nat (fst (D_reload pa)) + 121068904 * (Z.of_nat m - 1) + 121068904)%Z
      with (Z.of_nat (fst (D_reload pa)) + 121068904 * Z.of_nat m)%Z by lia.
    rewrite Hf0, (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    assert (Hm_M : (Z.of_nat m mod M = 32285041 mod M)%Z).
    { rewrite <- (Z_mod_div_factor _ 43046721 M ltac:(lia) HM HdivM), Hm_div3.
      reflexivity. }
    rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hm_M, Zmult_mod_idemp_r, Zplus_mod_idemp_r.
    rewrite Nat2Z.inj_sub by lia. change (Z.of_nat 1) with 1%Z.
    pose proof (Z.div_mod 43046721 M ltac:(lia)) as HdmM. rewrite HdivM in HdmM.
    replace (Z.of_nat (fst pa) - 1 + 121068904 * 32285041)%Z
      with ((Z.of_nat (fst pa) + 30267225) + (90801678 * (43046721 / M)) * M)%Z by lia.
    rewrite Z.mod_add by lia.
    rewrite <- Zplus_mod_idemp_l, Hm_in. exact Hr_out.
Qed.

Lemma K_z0_div3_props : forall pb (r : nat) (M r_in c : Z),
  (0 < M)%Z ->
  (43046721 mod M = 0)%Z ->
  7 <= fst pb ->
  is_W_odd (snd pb) ->
  (Z.of_nat (fst pb) mod (3 * M) = r_in)%Z ->
  ((r_in + 32285037) mod (3 * M) = c)%Z ->
  (c mod 3 = Z.of_nat r)%Z ->
  r <= 2 ->
  fst pb + snd pb / 2 - 2 = 3 * ((fst pb + snd pb / 2 - 2 - r) / 3) + r /\
  (Z.of_nat ((fst pb + snd pb / 2 - 2 - r) / 3) mod M = (c / 3) mod M)%Z.
Proof.
  intros [p b] r M r_in c HM HdivM Hp [Hb_eq [Hb_ge Hb_mod]] Hm_in Hc Hcr Hr.
  cbn [fst snd] in *.
  set (d := p + b / 2 - 2).
  assert (Hdiv3M : (129140163 mod (3 * M) = 0)%Z).
  { pose proof (Z.div_mod 43046721 M ltac:(lia)) as Hdm. rewrite HdivM in Hdm.
    replace 129140163%Z with ((43046721 / M) * (3 * M))%Z by lia.
    apply Z_mod_mult. }
  assert (Hb_3M : (Z.of_nat (b / 2) mod (3 * M) = 32285039 mod (3 * M))%Z).
  { rewrite <- (Z_mod_div_factor _ 129140163 (3 * M) ltac:(lia) ltac:(lia) Hdiv3M), Hb_mod.
    reflexivity. }
  assert (Hd_3M : (Z.of_nat d mod (3 * M) = c)%Z).
  { unfold d.
    replace (p + b / 2 - 2) with (p + (b / 2 - 2)) by lia.
    rewrite Nat2Z.inj_add, Nat2Z.inj_sub by lia.
    change (Z.of_nat 2) with 2%Z.
    rewrite <- Zplus_mod_idemp_l, Hm_in, <- Zplus_mod_idemp_r.
    rewrite <- Zminus_mod_idemp_l, Hb_3M, Zminus_mod_idemp_l, Zplus_mod_idemp_r.
    replace (r_in + (32285039 - 2))%Z with (r_in + 32285037)%Z by lia.
    exact Hc. }
  apply (Z_div3_nat d r M c HM ltac:(unfold d; lia) Hd_3M Hcr).
Qed.

Lemma K_z1_div3_props : forall pb (r : nat) (M r_in c : Z),
  (0 < M)%Z ->
  (43046721 mod M = 0)%Z ->
  7 <= fst pb ->
  is_W_odd (snd pb) ->
  (Z.of_nat (fst pb) mod (3 * M) = r_in)%Z ->
  ((r_in + 32285038) mod (3 * M) = c)%Z ->
  (c mod 3 = Z.of_nat r)%Z ->
  r <= 2 ->
  fst pb + snd pb / 2 - 1 = 3 * ((fst pb + snd pb / 2 - 1 - r) / 3) + r /\
  (Z.of_nat ((fst pb + snd pb / 2 - 1 - r) / 3) mod M = (c / 3) mod M)%Z.
Proof.
  intros [p b] r M r_in c HM HdivM Hp [Hb_eq [Hb_ge Hb_mod]] Hm_in Hc Hcr Hr.
  cbn [fst snd] in *.
  set (d := p + b / 2 - 1).
  assert (Hdiv3M : (129140163 mod (3 * M) = 0)%Z).
  { pose proof (Z.div_mod 43046721 M ltac:(lia)) as Hdm. rewrite HdivM in Hdm.
    replace 129140163%Z with ((43046721 / M) * (3 * M))%Z by lia.
    apply Z_mod_mult. }
  assert (Hb_3M : (Z.of_nat (b / 2) mod (3 * M) = 32285039 mod (3 * M))%Z).
  { rewrite <- (Z_mod_div_factor _ 129140163 (3 * M) ltac:(lia) ltac:(lia) Hdiv3M), Hb_mod.
    reflexivity. }
  assert (Hd_3M : (Z.of_nat d mod (3 * M) = c)%Z).
  { unfold d.
    replace (p + b / 2 - 1) with (p + (b / 2 - 1)) by lia.
    rewrite Nat2Z.inj_add, Nat2Z.inj_sub by lia.
    change (Z.of_nat 1) with 1%Z.
    rewrite <- Zplus_mod_idemp_l, Hm_in, <- Zplus_mod_idemp_r.
    rewrite <- Zminus_mod_idemp_l, Hb_3M, Zminus_mod_idemp_l, Zplus_mod_idemp_r.
    replace (r_in + (32285039 - 1))%Z with (r_in + 32285038)%Z by lia.
    exact Hc. }
  apply (Z_div3_nat d r M c HM ltac:(unfold d; lia) Hd_3M Hcr).
Qed.

Lemma round_K0_z0_step : forall pb (M r_in r_out : Z),
  (c0 -->* Cd_z (fst pb) (snd pb) 0 z0 /\
   7 <= fst pb /\
   (Z.of_nat (fst pb) mod (3 * M) = r_in)%Z /\
   is_W_odd (snd pb)) ->
  (0 < M)%Z ->
  (43046721 mod M = 0)%Z ->
  (((r_in + 32285037) mod (3 * M)) mod 3 = 0)%Z ->
  ((8 + 121068904 * (((r_in + 32285037) mod (3 * M)) / 3)) mod M = r_out)%Z ->
  c0 -->* Cd_z (fst (K0_z0_round pb)) (snd (K0_z0_round pb)) 0 z1 /\
  7 <= fst (K0_z0_round pb) /\
  (Z.of_nat (fst (K0_z0_round pb)) mod M = r_out)%Z /\
  is_W_odd (snd (K0_z0_round pb)).
Proof.
  intros pb M r_in r_out [Hrun [Hp [Hm_in Hb]]] HM HdivM Hc0 Hr_out.
  Transparent K0_z0_round. unfold K0_z0_round. Opaque K0_z0_round.
  destruct (K_reload_z0_all pb Hp Hb) as [Hrel [HpK [HmK HbK]]].
  destruct (K_z0_div3_props pb 0 M r_in ((r_in + 32285037) mod (3 * M))%Z
              HM HdivM Hp Hb Hm_in eq_refl Hc0 ltac:(lia))
    as [Hd_eq Hm_div].
  replace (fst pb + snd pb / 2 - 2 - 0) with (fst pb + snd pb / 2 - 2) in Hd_eq, Hm_div by lia.
  set (m := (fst pb + snd pb / 2 - 2) / 3) in *.
  destruct (Kd_loop m 0 z1 pb_K0 ltac:(lia) HbK) as [Hloop [Hp1 [Hm1 Hb1]]].
  assert (Hdiv17 : (129140163 mod M = 0)%Z).
  { pose proof (Z.div_mod 43046721 M ltac:(lia)) as Hdm. rewrite HdivM in Hdm.
    replace 129140163%Z with ((3 * (43046721 / M)) * M)%Z by lia.
    apply Z_mod_mult. }
  split; [| split; [lia | split; [| exact Hb1]]].
  - eapply evstep_trans; [exact Hrun |].
    eapply evstep_trans; [apply progress_evstep, Hrel |].
    rewrite Hd_eq at 1. exact Hloop.
  - rewrite <- (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    rewrite Hm1, <- Zplus_mod_idemp_l, HmK.
    rewrite (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hm_div, Zmult_mod_idemp_r, Zplus_mod_idemp_r.
    exact Hr_out.
Qed.

Lemma round_K2_z0_step : forall pb (M r_in r_out : Z),
  (c0 -->* Cd_z (fst pb) (snd pb) 0 z0 /\
   7 <= fst pb /\
   (Z.of_nat (fst pb) mod (3 * M) = r_in)%Z /\
   is_W_odd (snd pb)) ->
  (0 < M)%Z ->
  (43046721 mod M = 0)%Z ->
  (((r_in + 32285037) mod (3 * M)) mod 3 = 2)%Z ->
  ((121068912 + 121068904 * (((r_in + 32285037) mod (3 * M)) / 3)) mod M = r_out)%Z ->
  c0 -->* Ce_z (fst (K2_z0_round pb)) (snd (K2_z0_round pb)) 0 1 z1 /\
  7 <= fst (K2_z0_round pb) /\
  (Z.of_nat (fst (K2_z0_round pb)) mod M = r_out)%Z /\
  is_W_even (snd (K2_z0_round pb)).
Proof.
  intros pb M r_in r_out [Hrun [Hp [Hm_in Hb]]] HM HdivM Hc2 Hr_out.
  Transparent K2_z0_round. unfold K2_z0_round. Opaque K2_z0_round.
  destruct (K_reload_z0_all pb Hp Hb) as [Hrel [HpK [HmK HbK]]].
  destruct (K_z0_div3_props pb 2 M r_in ((r_in + 32285037) mod (3 * M))%Z
              HM HdivM Hp Hb Hm_in eq_refl Hc2 ltac:(lia))
    as [Hd_eq Hm_div].
  replace (fst pb + snd pb / 2 - 2 - 2) with (fst pb + snd pb / 2 - 4) in Hd_eq, Hm_div by lia.
  set (m := (fst pb + snd pb / 2 - 4) / 3) in *.
  destruct (Kd_loop m 2 z1 pb_K0 ltac:(lia) HbK) as [Hloop [Hp1 [Hm1 Hb1]]].
  destruct (Kc_full_all 1 z1 (Kd_iter m pb_K0) ltac:(lia) Hb1) as [Hkc [Hp2 [Hm2 Ha2]]].
  assert (Hdiv17 : (129140163 mod M = 0)%Z).
  { pose proof (Z.div_mod 43046721 M ltac:(lia)) as Hdm. rewrite HdivM in Hdm.
    replace 129140163%Z with ((3 * (43046721 / M)) * M)%Z by lia.
    apply Z_mod_mult. }
  split; [| split; [lia | split; [| exact Ha2]]].
  - eapply evstep_trans; [exact Hrun |].
    eapply evstep_trans; [apply progress_evstep, Hrel |].
    rewrite Hd_eq at 1.
    eapply evstep_trans; [exact Hloop |].
    apply progress_evstep, Hkc.
  - rewrite <- (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    rewrite Hm2, <- Zplus_mod_idemp_l, Hm1, Zplus_mod_idemp_l.
    replace (Z.of_nat (fst pb_K0) + 121068904 * Z.of_nat m + 121068904)%Z
      with (Z.of_nat (fst pb_K0) + (121068904 * Z.of_nat m + 121068904))%Z by lia.
    rewrite <- Zplus_mod_idemp_l, HmK.
    rewrite (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    replace (8 + (121068904 * Z.of_nat m + 121068904))%Z
      with (121068912 + 121068904 * Z.of_nat m)%Z by lia.
    rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hm_div, Zmult_mod_idemp_r, Zplus_mod_idemp_r.
    exact Hr_out.
Qed.

Lemma round_K0_z1_step : forall pb (M r_in r_out : Z),
  (c0 -->* Cd_z (fst pb) (snd pb) 0 z1 /\
   7 <= fst pb /\
   (Z.of_nat (fst pb) mod (3 * M) = r_in)%Z /\
   is_W_odd (snd pb)) ->
  (0 < M)%Z ->
  (43046721 mod M = 0)%Z ->
  (((r_in + 32285038) mod (3 * M)) mod 3 = 0)%Z ->
  ((8 + 121068904 * (((r_in + 32285038) mod (3 * M)) / 3)) mod M = r_out)%Z ->
  c0 -->* Cd_z (fst (K0_z1_round pb)) (snd (K0_z1_round pb)) 0 z0 /\
  7 <= fst (K0_z1_round pb) /\
  (Z.of_nat (fst (K0_z1_round pb)) mod M = r_out)%Z /\
  is_W_odd (snd (K0_z1_round pb)).
Proof.
  intros pb M r_in r_out [Hrun [Hp [Hm_in Hb]]] HM HdivM Hc0 Hr_out.
  Transparent K0_z1_round. unfold K0_z1_round. Opaque K0_z1_round.
  destruct (K_reload_z1_all pb Hp Hb) as [Hrel [HpK [HmK HbK]]].
  destruct (K_z1_div3_props pb 0 M r_in ((r_in + 32285038) mod (3 * M))%Z
              HM HdivM Hp Hb Hm_in eq_refl Hc0 ltac:(lia))
    as [Hd_eq Hm_div].
  replace (fst pb + snd pb / 2 - 1 - 0) with (fst pb + snd pb / 2 - 1) in Hd_eq, Hm_div by lia.
  set (m := (fst pb + snd pb / 2 - 1) / 3) in *.
  destruct (Kd_loop m 0 z0 pb_K0 ltac:(lia) HbK) as [Hloop [Hp1 [Hm1 Hb1]]].
  assert (Hdiv17 : (129140163 mod M = 0)%Z).
  { pose proof (Z.div_mod 43046721 M ltac:(lia)) as Hdm. rewrite HdivM in Hdm.
    replace 129140163%Z with ((3 * (43046721 / M)) * M)%Z by lia.
    apply Z_mod_mult. }
  split; [| split; [lia | split; [| exact Hb1]]].
  - eapply evstep_trans; [exact Hrun |].
    eapply evstep_trans; [apply progress_evstep, Hrel |].
    rewrite Hd_eq at 1. exact Hloop.
  - rewrite <- (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    rewrite Hm1, <- Zplus_mod_idemp_l, HmK.
    rewrite (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hm_div, Zmult_mod_idemp_r, Zplus_mod_idemp_r.
    exact Hr_out.
Qed.

Lemma round_K1_z1_step : forall pb (M r_in r_out : Z),
  (c0 -->* Cd_z (fst pb) (snd pb) 0 z1 /\
   7 <= fst pb /\
   (Z.of_nat (fst pb) mod (3 * M) = r_in)%Z /\
   is_W_odd (snd pb)) ->
  (0 < M)%Z ->
  (43046721 mod M = 0)%Z ->
  (((r_in + 32285038) mod (3 * M)) mod 3 = 1)%Z ->
  ((121068912 + 121068904 * (((r_in + 32285038) mod (3 * M)) / 3)) mod M = r_out)%Z ->
  c0 -->* Ce_z (fst (K1_z1_round pb)) (snd (K1_z1_round pb)) 0 0 z0 /\
  7 <= fst (K1_z1_round pb) /\
  (Z.of_nat (fst (K1_z1_round pb)) mod M = r_out)%Z /\
  is_W_even (snd (K1_z1_round pb)).
Proof.
  intros pb M r_in r_out [Hrun [Hp [Hm_in Hb]]] HM HdivM Hc1 Hr_out.
  Transparent K1_z1_round. unfold K1_z1_round. Opaque K1_z1_round.
  destruct (K_reload_z1_all pb Hp Hb) as [Hrel [HpK [HmK HbK]]].
  destruct (K_z1_div3_props pb 1 M r_in ((r_in + 32285038) mod (3 * M))%Z
              HM HdivM Hp Hb Hm_in eq_refl Hc1 ltac:(lia))
    as [Hd_eq Hm_div].
  replace (fst pb + snd pb / 2 - 1 - 1) with (fst pb + snd pb / 2 - 2) in Hd_eq, Hm_div by lia.
  set (m := (fst pb + snd pb / 2 - 2) / 3) in *.
  destruct (Kd_loop m 1 z0 pb_K0 ltac:(lia) HbK) as [Hloop [Hp1 [Hm1 Hb1]]].
  destruct (Kc_full_all 0 z0 (Kd_iter m pb_K0) ltac:(lia) Hb1) as [Hkc [Hp2 [Hm2 Ha2]]].
  assert (Hdiv17 : (129140163 mod M = 0)%Z).
  { pose proof (Z.div_mod 43046721 M ltac:(lia)) as Hdm. rewrite HdivM in Hdm.
    replace 129140163%Z with ((3 * (43046721 / M)) * M)%Z by lia.
    apply Z_mod_mult. }
  split; [| split; [lia | split; [| exact Ha2]]].
  - eapply evstep_trans; [exact Hrun |].
    eapply evstep_trans; [apply progress_evstep, Hrel |].
    rewrite Hd_eq at 1.
    eapply evstep_trans; [exact Hloop |].
    apply progress_evstep, Hkc.
  - rewrite <- (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    rewrite Hm2, <- Zplus_mod_idemp_l, Hm1, Zplus_mod_idemp_l.
    replace (Z.of_nat (fst pb_K0) + 121068904 * Z.of_nat m + 121068904)%Z
      with (Z.of_nat (fst pb_K0) + (121068904 * Z.of_nat m + 121068904))%Z by lia.
    rewrite <- Zplus_mod_idemp_l, HmK.
    rewrite (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    replace (8 + (121068904 * Z.of_nat m + 121068904))%Z
      with (121068912 + 121068904 * Z.of_nat m)%Z by lia.
    rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hm_div, Zmult_mod_idemp_r, Zplus_mod_idemp_r.
    exact Hr_out.
Qed.

Lemma round_K2_z1_step : forall pb (M r_in r_out : Z),
  (c0 -->* Cd_z (fst pb) (snd pb) 0 z1 /\
   7 <= fst pb /\
   (Z.of_nat (fst pb) mod (3 * M) = r_in)%Z /\
   is_W_odd (snd pb)) ->
  (0 < M)%Z ->
  (43046721 mod M = 0)%Z ->
  (((r_in + 32285038) mod (3 * M)) mod 3 = 2)%Z ->
  ((121068912 + 121068904 * (((r_in + 32285038) mod (3 * M)) / 3)) mod M = r_out)%Z ->
  c0 -->* Ce_z (fst (K2_z1_round pb)) (snd (K2_z1_round pb)) 0 1 z0 /\
  7 <= fst (K2_z1_round pb) /\
  (Z.of_nat (fst (K2_z1_round pb)) mod M = r_out)%Z /\
  is_W_even (snd (K2_z1_round pb)).
Proof.
  intros pb M r_in r_out [Hrun [Hp [Hm_in Hb]]] HM HdivM Hc2 Hr_out.
  Transparent K2_z1_round. unfold K2_z1_round. Opaque K2_z1_round.
  destruct (K_reload_z1_all pb Hp Hb) as [Hrel [HpK [HmK HbK]]].
  destruct (K_z1_div3_props pb 2 M r_in ((r_in + 32285038) mod (3 * M))%Z
              HM HdivM Hp Hb Hm_in eq_refl Hc2 ltac:(lia))
    as [Hd_eq Hm_div].
  replace (fst pb + snd pb / 2 - 1 - 2) with (fst pb + snd pb / 2 - 3) in Hd_eq, Hm_div by lia.
  set (m := (fst pb + snd pb / 2 - 3) / 3) in *.
  destruct (Kd_loop m 2 z0 pb_K0 ltac:(lia) HbK) as [Hloop [Hp1 [Hm1 Hb1]]].
  destruct (Kc_full_all 1 z0 (Kd_iter m pb_K0) ltac:(lia) Hb1) as [Hkc [Hp2 [Hm2 Ha2]]].
  assert (Hdiv17 : (129140163 mod M = 0)%Z).
  { pose proof (Z.div_mod 43046721 M ltac:(lia)) as Hdm. rewrite HdivM in Hdm.
    replace 129140163%Z with ((3 * (43046721 / M)) * M)%Z by lia.
    apply Z_mod_mult. }
  split; [| split; [lia | split; [| exact Ha2]]].
  - eapply evstep_trans; [exact Hrun |].
    eapply evstep_trans; [apply progress_evstep, Hrel |].
    rewrite Hd_eq at 1.
    eapply evstep_trans; [exact Hloop |].
    apply progress_evstep, Hkc.
  - rewrite <- (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    rewrite Hm2, <- Zplus_mod_idemp_l, Hm1, Zplus_mod_idemp_l.
    replace (Z.of_nat (fst pb_K0) + 121068904 * Z.of_nat m + 121068904)%Z
      with (Z.of_nat (fst pb_K0) + (121068904 * Z.of_nat m + 121068904))%Z by lia.
    rewrite <- Zplus_mod_idemp_l, HmK.
    rewrite (Z_mod_div_factor _ 129140163 M ltac:(lia) HM Hdiv17).
    replace (8 + (121068904 * Z.of_nat m + 121068904))%Z
      with (121068912 + 121068904 * Z.of_nat m)%Z by lia.
    rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hm_div, Zmult_mod_idemp_r, Zplus_mod_idemp_r.
    exact Hr_out.
Qed.

Lemma round_K1_z0_halt : forall pb (r_in : Z),
  (c0 -->* Cd_z (fst pb) (snd pb) 0 z0 /\
   7 <= fst pb /\
   (Z.of_nat (fst pb) mod 3 = r_in)%Z /\
   is_W_odd (snd pb)) ->
  (((r_in + 32285037) mod 3) mod 3 = 1)%Z ->
  c0 -->* c_end (fst (K1_z0_round pb)) (snd (K1_z0_round pb)).
Proof.
  intros pb r_in [Hrun [Hp [Hm_in Hb]]] Hc1.
  Transparent K1_z0_round. unfold K1_z0_round. Opaque K1_z0_round.
  destruct (K_reload_z0_all pb Hp Hb) as [Hrel [HpK [HmK HbK]]].
  destruct (K_z0_div3_props pb 1 1 r_in ((r_in + 32285037) mod 3)%Z
              ltac:(lia) eq_refl Hp Hb Hm_in eq_refl Hc1 ltac:(lia))
    as [Hd_eq _].
  replace (fst pb + snd pb / 2 - 2 - 1) with (fst pb + snd pb / 2 - 3) in Hd_eq by lia.
  set (m := (fst pb + snd pb / 2 - 3) / 3) in *.
  destruct (Kd_loop m 1 z1 pb_K0 ltac:(lia) HbK) as [Hloop [Hp1 [_ Hb1]]].
  destruct (Kc_full_all 0 z1 (Kd_iter m pb_K0) ltac:(lia) Hb1) as [Hkc _].
  eapply evstep_trans; [exact Hrun |].
  eapply evstep_trans; [apply progress_evstep, Hrel |].
  rewrite Hd_eq at 1.
  eapply evstep_trans; [exact Hloop |].
  eapply evstep_trans; [apply progress_evstep, Hkc |].
  apply progress_evstep, HALT_step.
Qed.

(** ** The 32-round trajectory of M14_31 *)

Definition pa1 : nat * nat := Kc_full pb_K0.
Definition pb2  : nat * nat := D2_round pa1.
Definition pb3  : nat * nat := K0_z0_round pb2.
Definition pa4  : nat * nat := K2_z1_round pb3.
Definition pb5  : nat * nat := D2_round pa4.
Definition pb6  : nat * nat := K0_z0_round pb5.
Definition pb7  : nat * nat := K0_z1_round pb6.
Definition pa8  : nat * nat := K2_z0_round pb7.
Definition pb9  : nat * nat := D2_round pa8.
Definition pa10 : nat * nat := K2_z1_round pb9.
Definition pb11 : nat * nat := D2_round pa10.
Definition pa12 : nat * nat := K2_z0_round pb11.
Definition pb13 : nat * nat := D2_round pa12.
Definition pa14 : nat * nat := K1_z1_round pb13.
Definition pa15 : nat * nat := D1_round pa14.
Definition pb16 : nat * nat := D2_round pa15.
Definition pa17 : nat * nat := K1_z1_round pb16.
Definition pa18 : nat * nat := D1_round pa17.
Definition pb19 : nat * nat := D2_round pa18.
Definition pb20 : nat * nat := K0_z1_round pb19.
Definition pa21 : nat * nat := K2_z0_round pb20.
Definition pb22 : nat * nat := D2_round pa21.
Definition pa23 : nat * nat := K1_z1_round pb22.
Definition pa24 : nat * nat := D1_round pa23.
Definition pb25 : nat * nat := D2_round pa24.
Definition pa26 : nat * nat := K2_z1_round pb25.
Definition pb27 : nat * nat := D2_round pa26.
Definition pa28 : nat * nat := K2_z0_round pb27.
Definition pb29 : nat * nat := D2_round pa28.
Definition pa30 : nat * nat := K2_z1_round pb29.
Definition pb31 : nat * nat := D2_round pa30.
Definition pa32 : nat * nat := K1_z0_round pb31.

Lemma pa1_def : pa1 = Kc_full pb_K0. Proof. reflexivity. Qed.
Lemma pb2_def : pb2 = D2_round pa1. Proof. reflexivity. Qed.
Lemma pb3_def : pb3 = K0_z0_round pb2. Proof. reflexivity. Qed.
Lemma pa4_def : pa4 = K2_z1_round pb3. Proof. reflexivity. Qed.
Lemma pb5_def : pb5 = D2_round pa4. Proof. reflexivity. Qed.
Lemma pb6_def : pb6 = K0_z0_round pb5. Proof. reflexivity. Qed.
Lemma pb7_def : pb7 = K0_z1_round pb6. Proof. reflexivity. Qed.
Lemma pa8_def : pa8 = K2_z0_round pb7. Proof. reflexivity. Qed.
Lemma pb9_def : pb9 = D2_round pa8. Proof. reflexivity. Qed.
Lemma pa10_def : pa10 = K2_z1_round pb9. Proof. reflexivity. Qed.
Lemma pb11_def : pb11 = D2_round pa10. Proof. reflexivity. Qed.
Lemma pa12_def : pa12 = K2_z0_round pb11. Proof. reflexivity. Qed.
Lemma pb13_def : pb13 = D2_round pa12. Proof. reflexivity. Qed.
Lemma pa14_def : pa14 = K1_z1_round pb13. Proof. reflexivity. Qed.
Lemma pa15_def : pa15 = D1_round pa14. Proof. reflexivity. Qed.
Lemma pb16_def : pb16 = D2_round pa15. Proof. reflexivity. Qed.
Lemma pa17_def : pa17 = K1_z1_round pb16. Proof. reflexivity. Qed.
Lemma pa18_def : pa18 = D1_round pa17. Proof. reflexivity. Qed.
Lemma pb19_def : pb19 = D2_round pa18. Proof. reflexivity. Qed.
Lemma pb20_def : pb20 = K0_z1_round pb19. Proof. reflexivity. Qed.
Lemma pa21_def : pa21 = K2_z0_round pb20. Proof. reflexivity. Qed.
Lemma pb22_def : pb22 = D2_round pa21. Proof. reflexivity. Qed.
Lemma pa23_def : pa23 = K1_z1_round pb22. Proof. reflexivity. Qed.
Lemma pa24_def : pa24 = D1_round pa23. Proof. reflexivity. Qed.
Lemma pb25_def : pb25 = D2_round pa24. Proof. reflexivity. Qed.
Lemma pa26_def : pa26 = K2_z1_round pb25. Proof. reflexivity. Qed.
Lemma pb27_def : pb27 = D2_round pa26. Proof. reflexivity. Qed.
Lemma pa28_def : pa28 = K2_z0_round pb27. Proof. reflexivity. Qed.
Lemma pb29_def : pb29 = D2_round pa28. Proof. reflexivity. Qed.
Lemma pa30_def : pa30 = K2_z1_round pb29. Proof. reflexivity. Qed.
Lemma pb31_def : pb31 = D2_round pa30. Proof. reflexivity. Qed.
Lemma pa32_def : pa32 = K1_z0_round pb31. Proof. reflexivity. Qed.

Opaque pa1 pb2 pb3 pa4 pb5 pb6 pb7 pa8 pb9 pa10 pb11 pa12 pb13 pa14 pa15 pb16 pa17 pa18 pb19 pb20 pa21 pb22 pa23 pa24 pb25 pa26 pb27 pa28 pb29 pa30 pb31 pa32.

Lemma run_pa1 :
  c0 -->* Ce_z (fst pa1) (snd pa1) 0 1 z0 /\
  7 <= fst pa1 /\
  (Z.of_nat (fst pa1) mod 43046721 = 34975470)%Z /\
  is_W_even (snd pa1).
Proof.
  rewrite pa1_def.
  destruct pb_K0_props as [HpK [HmK HbK]].
  destruct (Kc_full_all 1 z0 pb_K0 ltac:(lia) HbK) as [Hkc [Hp1 [Hm1 Ha1]]].
  split; [| split; [lia | split; [| exact Ha1]]].
  - eapply evstep_trans; [exact init_pb0 | apply progress_evstep, Hkc].
  - rewrite <- (Z_mod_div_factor _ 129140163 43046721 ltac:(lia) ltac:(lia) eq_refl).
    rewrite Hm1, <- Zplus_mod_idemp_l, HmK. reflexivity.
Qed.

Lemma run_pb2 :
  c0 -->* Cd_z (fst pb2) (snd pb2) 0 z0 /\
  7 <= fst pb2 /\
  (Z.of_nat (fst pb2) mod 43046721 = 22195974)%Z /\
  is_W_odd (snd pb2).
Proof.
  rewrite pb2_def.
  eapply (round_D2_z0_step pa1 43046721 34975470 22195974);
    [exact run_pa1 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pb3 :
  c0 -->* Cd_z (fst pb3) (snd pb3) 0 z1 /\
  7 <= fst pb3 /\
  (Z.of_nat (fst pb3) mod 14348907 = 13494148)%Z /\
  is_W_odd (snd pb3).
Proof.
  rewrite pb3_def.
  eapply (round_K0_z0_step pb2 14348907 22195974 13494148);
    [exact run_pb2 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pa4 :
  c0 -->* Ce_z (fst pa4) (snd pa4) 0 1 z0 /\
  7 <= fst pa4 /\
  (Z.of_nat (fst pa4) mod 4782969 = 483738)%Z /\
  is_W_even (snd pa4).
Proof.
  rewrite pa4_def.
  eapply (round_K2_z1_step pb3 4782969 13494148 483738);
    [exact run_pb3 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pb5 :
  c0 -->* Cd_z (fst pb5) (snd pb5) 0 z0 /\
  7 <= fst pb5 /\
  (Z.of_nat (fst pb5) mod 4782969 = 2053149)%Z /\
  is_W_odd (snd pb5).
Proof.
  rewrite pb5_def.
  eapply (round_D2_z0_step pa4 4782969 483738 2053149);
    [exact run_pa4 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pb6 :
  c0 -->* Cd_z (fst pb6) (snd pb6) 0 z1 /\
  7 <= fst pb6 /\
  (Z.of_nat (fst pb6) mod 1594323 = 1036913)%Z /\
  is_W_odd (snd pb6).
Proof.
  rewrite pb6_def.
  eapply (round_K0_z0_step pb5 1594323 2053149 1036913);
    [exact run_pb5 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pb7 :
  c0 -->* Cd_z (fst pb7) (snd pb7) 0 z0 /\
  7 <= fst pb7 /\
  (Z.of_nat (fst pb7) mod 531441 = 468578)%Z /\
  is_W_odd (snd pb7).
Proof.
  rewrite pb7_def.
  eapply (round_K0_z1_step pb6 531441 1036913 468578);
    [exact run_pb6 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pa8 :
  c0 -->* Ce_z (fst pa8) (snd pa8) 0 1 z1 /\
  7 <= fst pa8 /\
  (Z.of_nat (fst pa8) mod 177147 = 33250)%Z /\
  is_W_even (snd pa8).
Proof.
  rewrite pa8_def.
  eapply (round_K2_z0_step pb7 177147 468578 33250);
    [exact run_pb7 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pb9 :
  c0 -->* Cd_z (fst pb9) (snd pb9) 0 z1 /\
  7 <= fst pb9 /\
  (Z.of_nat (fst pb9) mod 177147 = 8338)%Z /\
  is_W_odd (snd pb9).
Proof.
  rewrite pb9_def.
  eapply (round_D2_z1_step pa8 177147 33250 8338);
    [exact run_pa8 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pa10 :
  c0 -->* Ce_z (fst pa10) (snd pa10) 0 1 z0 /\
  7 <= fst pa10 /\
  (Z.of_nat (fst pa10) mod 59049 = 54053)%Z /\
  is_W_even (snd pa10).
Proof.
  rewrite pa10_def.
  eapply (round_K2_z1_step pb9 59049 8338 54053);
    [exact run_pb9 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pb11 :
  c0 -->* Cd_z (fst pb11) (snd pb11) 0 z0 /\
  7 <= fst pb11 /\
  (Z.of_nat (fst pb11) mod 59049 = 29141)%Z /\
  is_W_odd (snd pb11).
Proof.
  rewrite pb11_def.
  eapply (round_D2_z0_step pa10 59049 54053 29141);
    [exact run_pa10 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pa12 :
  c0 -->* Ce_z (fst pa12) (snd pa12) 0 1 z1 /\
  7 <= fst pa12 /\
  (Z.of_nat (fst pa12) mod 19683 = 15540)%Z /\
  is_W_even (snd pa12).
Proof.
  rewrite pa12_def.
  eapply (round_K2_z0_step pb11 19683 29141 15540);
    [exact run_pb11 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pb13 :
  c0 -->* Cd_z (fst pb13) (snd pb13) 0 z1 /\
  7 <= fst pb13 /\
  (Z.of_nat (fst pb13) mod 19683 = 10311)%Z /\
  is_W_odd (snd pb13).
Proof.
  rewrite pb13_def.
  eapply (round_D2_z1_step pa12 19683 15540 10311);
    [exact run_pa12 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pa14 :
  c0 -->* Ce_z (fst pa14) (snd pa14) 0 0 z0 /\
  7 <= fst pa14 /\
  (Z.of_nat (fst pa14) mod 6561 = 6447)%Z /\
  is_W_even (snd pa14).
Proof.
  rewrite pa14_def.
  eapply (round_K1_z1_step pb13 6561 10311 6447);
    [exact run_pb13 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pa15 :
  c0 -->* Ce_z (fst pa15) (snd pa15) 0 1 z1 /\
  7 <= fst pa15 /\
  (Z.of_nat (fst pa15) mod 6561 = 1218)%Z /\
  is_W_even (snd pa15).
Proof.
  rewrite pa15_def.
  eapply (round_D1_z0_step pa14 6561 6447 1218);
    [exact run_pa14 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pb16 :
  c0 -->* Cd_z (fst pb16) (snd pb16) 0 z1 /\
  7 <= fst pb16 /\
  (Z.of_nat (fst pb16) mod 6561 = 2550)%Z /\
  is_W_odd (snd pb16).
Proof.
  rewrite pb16_def.
  eapply (round_D2_z1_step pa15 6561 1218 2550);
    [exact run_pa15 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pa17 :
  c0 -->* Ce_z (fst pa17) (snd pa17) 0 0 z0 /\
  7 <= fst pa17 /\
  (Z.of_nat (fst pa17) mod 2187 = 1598)%Z /\
  is_W_even (snd pa17).
Proof.
  rewrite pa17_def.
  eapply (round_K1_z1_step pb16 2187 2550 1598);
    [exact run_pb16 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pa18 :
  c0 -->* Ce_z (fst pa18) (snd pa18) 0 1 z1 /\
  7 <= fst pa18 /\
  (Z.of_nat (fst pa18) mod 2187 = 743)%Z /\
  is_W_even (snd pa18).
Proof.
  rewrite pa18_def.
  eapply (round_D1_z0_step pa17 2187 1598 743);
    [exact run_pa17 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pb19 :
  c0 -->* Cd_z (fst pb19) (snd pb19) 0 z1 /\
  7 <= fst pb19 /\
  (Z.of_nat (fst pb19) mod 2187 = 2075)%Z /\
  is_W_odd (snd pb19).
Proof.
  rewrite pb19_def.
  eapply (round_D2_z1_step pa18 2187 743 2075);
    [exact run_pa18 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pb20 :
  c0 -->* Cd_z (fst pb20) (snd pb20) 0 z0 /\
  7 <= fst pb20 /\
  (Z.of_nat (fst pb20) mod 729 = 179)%Z /\
  is_W_odd (snd pb20).
Proof.
  rewrite pb20_def.
  eapply (round_K0_z1_step pb19 729 2075 179);
    [exact run_pb19 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pa21 :
  c0 -->* Ce_z (fst pa21) (snd pa21) 0 1 z1 /\
  7 <= fst pa21 /\
  (Z.of_nat (fst pa21) mod 243 = 36)%Z /\
  is_W_even (snd pa21).
Proof.
  rewrite pa21_def.
  eapply (round_K2_z0_step pb20 243 179 36);
    [exact run_pb20 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pb22 :
  c0 -->* Cd_z (fst pb22) (snd pb22) 0 z1 /\
  7 <= fst pb22 /\
  (Z.of_nat (fst pb22) mod 243 = 153)%Z /\
  is_W_odd (snd pb22).
Proof.
  rewrite pb22_def.
  eapply (round_D2_z1_step pa21 243 36 153);
    [exact run_pa21 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pa23 :
  c0 -->* Ce_z (fst pa23) (snd pa23) 0 0 z0 /\
  7 <= fst pa23 /\
  (Z.of_nat (fst pa23) mod 81 = 67)%Z /\
  is_W_even (snd pa23).
Proof.
  rewrite pa23_def.
  eapply (round_K1_z1_step pb22 81 153 67);
    [exact run_pb22 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pa24 :
  c0 -->* Ce_z (fst pa24) (snd pa24) 0 1 z1 /\
  7 <= fst pa24 /\
  (Z.of_nat (fst pa24) mod 81 = 22)%Z /\
  is_W_even (snd pa24).
Proof.
  rewrite pa24_def.
  eapply (round_D1_z0_step pa23 81 67 22);
    [exact run_pa23 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pb25 :
  c0 -->* Cd_z (fst pb25) (snd pb25) 0 z1 /\
  7 <= fst pb25 /\
  (Z.of_nat (fst pb25) mod 81 = 58)%Z /\
  is_W_odd (snd pb25).
Proof.
  rewrite pb25_def.
  eapply (round_D2_z1_step pa24 81 22 58);
    [exact run_pa24 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pa26 :
  c0 -->* Ce_z (fst pa26) (snd pa26) 0 1 z0 /\
  7 <= fst pa26 /\
  (Z.of_nat (fst pa26) mod 27 = 2)%Z /\
  is_W_even (snd pa26).
Proof.
  rewrite pa26_def.
  eapply (round_K2_z1_step pb25 27 58 2);
    [exact run_pb25 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pb27 :
  c0 -->* Cd_z (fst pb27) (snd pb27) 0 z0 /\
  7 <= fst pb27 /\
  (Z.of_nat (fst pb27) mod 27 = 11)%Z /\
  is_W_odd (snd pb27).
Proof.
  rewrite pb27_def.
  eapply (round_D2_z0_step pa26 27 2 11);
    [exact run_pa26 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pa28 :
  c0 -->* Ce_z (fst pa28) (snd pa28) 0 1 z1 /\
  7 <= fst pa28 /\
  (Z.of_nat (fst pa28) mod 9 = 1)%Z /\
  is_W_even (snd pa28).
Proof.
  rewrite pa28_def.
  eapply (round_K2_z0_step pb27 9 11 1);
    [exact run_pb27 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pb29 :
  c0 -->* Cd_z (fst pb29) (snd pb29) 0 z1 /\
  7 <= fst pb29 /\
  (Z.of_nat (fst pb29) mod 9 = 1)%Z /\
  is_W_odd (snd pb29).
Proof.
  rewrite pb29_def.
  eapply (round_D2_z1_step pa28 9 1 1);
    [exact run_pa28 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pa30 :
  c0 -->* Ce_z (fst pa30) (snd pa30) 0 1 z0 /\
  7 <= fst pa30 /\
  (Z.of_nat (fst pa30) mod 3 = 1)%Z /\
  is_W_even (snd pa30).
Proof.
  rewrite pa30_def.
  eapply (round_K2_z1_step pb29 3 1 1);
    [exact run_pb29 | lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma run_pb31 :
  c0 -->* Cd_z (fst pb31) (snd pb31) 0 z0 /\
  7 <= fst pb31 /\
  (Z.of_nat (fst pb31) mod 3 = 1)%Z /\
  is_W_odd (snd pb31).
Proof.
  rewrite pb31_def.
  eapply (round_D2_z0_step pa30 3 1 1);
    [exact run_pa30 | lia | reflexivity | reflexivity].
Qed.

Lemma run_pa32 :
  c0 -->* c_end (fst pa32) (snd pa32).
Proof.
  rewrite pa32_def.
  eapply (round_K1_z0_halt pb31 1); [exact run_pb31 | reflexivity].
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run_pa32) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply c_end_halted.
Qed.

(** ** Fast-growing hierarchy up to omega + 2 and tape ones *)

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | O => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.
Definition f_omega1 (n : nat) : nat := iter n f_omega n.
Definition f_omega2 (n : nat) : nat := iter n f_omega1 n.

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

Lemma ones_c_end : forall p a, ones (c_end p a) (p + a + 4).
Proof.
  intros p a.
  eexists. exists ([S0; S1] ++ [S1]^^(a + 2) ++ [S0; S1]^^p), (@nil Sym), S1.
  split.
  - unfold c_end. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

Theorem score_exact :
  exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa32 + snd pa32 + 4).
Proof.
  exists (c_end (fst pa32) (snd pa32)).
  split; [exact run_pa32 |].
  split; [apply c_end_halted |].
  apply ones_c_end.
Qed.

(** ** Iteration and hierarchy monotonicity *)

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

Lemma iter_lin1 : forall g, (forall a, 1 <= a -> a + 1 <= g a) -> forall n x, 1 <= x -> x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x Hx; simpl. - lia.
  - specialize (IHn x Hx). specialize (Hg (iter n g x) ltac:(lia)). lia.
Qed.

Lemma iter_dom : forall K g h, (forall n z, K * n <= z -> K * g n <= h z) ->
  forall m n z, K * n <= z -> K * iter m g n <= iter m h z.
Proof. intros K g h Hd. induction m; intros n z Hz; simpl; auto. Qed.

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

Lemma f_omega_id : forall n, n <= f_omega n.
Proof. intros n. unfold f_omega. apply f_id. Qed.

Lemma f_omega_dbl : forall n, 1 <= n -> 2 * n <= f_omega n.
Proof. intros n Hn. unfold f_omega. apply f_dbl. exact Hn. Qed.

Lemma f_omega_mono : forall a b, a <= b -> f_omega a <= f_omega b.
Proof.
  intros [| a'] b Hab.
  - destruct b as [| b'].
    + reflexivity.
    + change (f_omega 0) with 1. pose proof (f_omega_id (S b')). lia.
  - unfold f_omega.
    pose proof (f_level_mono (b - S a') (S a') (S a') ltac:(lia)) as L1.
    replace (b - S a' + S a') with b in L1 by lia.
    pose proof (f_mono b (S a') b Hab). lia.
Qed.

Lemma f_omega1_id : forall n, n <= f_omega1 n.
Proof. intros n. unfold f_omega1. apply iter_ge, f_omega_id. Qed.

Lemma f_omega1_mono : forall a b, a <= b -> f_omega1 a <= f_omega1 b.
Proof.
  intros a b Hab. unfold f_omega1.
  transitivity (iter a f_omega b).
  - apply iter_mono_x; [apply f_omega_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega_id | exact Hab].
Qed.

Lemma f_omega1_gt : forall a, 1 <= a -> a + 1 <= f_omega1 a.
Proof.
  intros [| a'] Ha; [lia |].
  unfold f_omega1. cbn [iter].
  pose proof (iter_ge f_omega f_omega_id a' (S a')).
  pose proof (f_omega_dbl (iter a' f_omega (S a')) ltac:(lia)).
  lia.
Qed.

Lemma f_omega2_id : forall n, n <= f_omega2 n.
Proof. intros n. unfold f_omega2. apply iter_ge, f_omega1_id. Qed.

Lemma f_omega2_mono : forall a b, a <= b -> f_omega2 a <= f_omega2 b.
Proof.
  intros a b Hab. unfold f_omega2.
  transitivity (iter a f_omega1 b).
  - apply iter_mono_x; [apply f_omega1_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega1_id | exact Hab].
Qed.

Lemma f_omega2_le_iter_2n : forall n,
  1 <= n -> f_omega2 n <= iter (2 * n) f_omega1 3.
Proof.
  intros n Hn.
  replace (2 * n) with (n + n) by lia.
  rewrite iter_add.
  pose proof (iter_lin1 f_omega1 f_omega1_gt n 3 ltac:(lia)) as Hlin.
  unfold f_omega2.
  apply iter_mono_x; [apply f_omega1_mono | lia].
Qed.

Lemma f_omega2_ge_iter3 : forall n,
  3 <= n -> iter 2 f_omega1 3 <= f_omega2 n.
Proof.
  intros n Hn.
  transitivity (f_omega2 3); [| apply f_omega2_mono; exact Hn].
  unfold f_omega2. apply iter_mono_n; [apply f_omega1_id | lia].
Qed.

Opaque f f_omega f_omega1 f_omega2.

(** ** Lower bound for W *)

Lemma W1_val : forall b, W 1 b = 3 * b + 5.
Proof. exact W_1. Qed.

Lemma W_S_0 : forall j, W (S j) 0 = W j 2.
Proof. intros j. rewrite W_S. reflexivity. Qed.

Lemma W_S' : forall j b, W (S j) b = iter b (W j) (W j 2).
Proof. intros j b. rewrite W_S, iter_S'. reflexivity. Qed.

Lemma W_S_2 : forall j, W (S j) 2 = W j (W j (W j 2)).
Proof. intros j. rewrite W_S. reflexivity. Qed.

Lemma pow2_ge : forall j, j + 2 <= 2 ^ (j + 1).
Proof. induction j. - simpl. lia. - change (S j + 1) with (S (j + 1)). rewrite Nat.pow_succ_r'. lia. Qed.

Lemma W_bound_all : forall j,
  (forall n z, 2 ^ (j + 1) * n <= z -> 2 ^ (j + 1) * f (S j) n <= W (S j) z) /\
  2 ^ (j + 2) * (j + 1) <= W (S j) 2.
Proof.
  induction j as [| j [Hw Hx]].
  - split.
    + intros n z Hz. rewrite W1_val, f1. simpl (2 ^ (0 + 1)) in *. lia.
    + rewrite W1_val. simpl. lia.
  - pose proof (pow2_ge j) as HKj.
    set (K := 2 ^ (j + 1)) in *.
    assert (HK1 : 2 ^ (S j + 1) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK2 : 2 ^ (j + 2) = 2 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    assert (HK3 : 2 ^ (S j + 2) = 4 * K) by (unfold K; rewrite !Nat.pow_add_r; simpl; lia).
    rewrite HK2 in Hx.
    assert (HX1 : K * 1 <= W (S j) 2) by nia.
    split.
    + intros n y Hy. rewrite HK1 in *. rewrite W_S', f_S.
      destruct n as [| n']. { cbn [iter]. lia. }
      set (n := S n') in *.
      assert (Hm : 2 * n + 1 <= y) by nia.
      pose proof (iter_dom K (f (S j)) (W (S j)) Hw y 1 (W (S j) 2) HX1) as Hd.
      assert (Hc : 2 * iter n (f (S j)) n <= iter y (f (S j)) 1).
      { transitivity (iter (2 * n + 1) (f (S j)) 1).
        2:{ apply iter_mono_n; [apply f_id | exact Hm]. }
        replace (2 * n + 1) with (1 + (n + n)) by lia. rewrite !iter_add.
        change (iter 1 (f (S j)) ?z) with (f (S j) z).
        pose proof (iter_lin1 (f (S j)) ltac:(intros a Ha; pose proof (f_gt (S j) a Ha); lia) n 1 ltac:(lia)).
        pose proof (iter_mono_x (f (S j)) (f_mono (S j)) n n (iter n (f (S j)) 1) ltac:(lia)).
        pose proof (f_dbl (S j) (iter n (f (S j)) (iter n (f (S j)) 1)) ltac:(lia)).
        lia. }
      nia.
    + rewrite HK3, W_S_2.
      pose proof (Hw (2 * (j + 1)) (W (S j) 2) ltac:(nia)) as H1.
      pose proof (f_dbl (S j) (2 * (j + 1)) ltac:(lia)) as H2.
      pose proof (Hw (4 * (j + 1)) (W (S j) (W (S j) 2)) ltac:(nia)) as H3.
      pose proof (f_dbl (S j) (4 * (j + 1)) ltac:(lia)) as H4.
      nia.
Qed.

Lemma W_omega_bound0 : forall m,
  2 * f_omega (S m) + 3 <= W (S (S m)) 2.
Proof.
  intros m.
  rewrite W_S_2.
  destruct (W_bound_all m) as [Hwb Hx].
  assert (H1 : 2 ^ (m + 1) * (2 * (m + 1)) <= W (S m) 2).
  { replace (m + 2) with (m + 1 + 1) in Hx by lia.
    rewrite Nat.pow_add_r in Hx. simpl (2 ^ 1) in Hx. nia. }
  pose proof (Hwb (2 * (m + 1)) (W (S m) 2) H1) as H2.
  pose proof (W_grow (S m) (W (S m) (W (S m) 2))) as H3.
  assert (H4 : f (S m) (S m) <= f (S m) (2 * (m + 1))) by (apply f_mono; lia).
  assert (H5 : 2 <= 2 ^ (m + 1)) by (pose proof (pow2_ge m); lia).
  Transparent f_omega. unfold f_omega. Opaque f_omega.
  set (P := 2 ^ (m + 1)) in *.
  set (F1 := f (S m) (S m)) in *.
  set (F2 := f (S m) (2 * (m + 1))) in *.
  set (Z := W (S m) (W (S m) (W (S m) 2))) in *.
  nia.
Qed.

Lemma W_omega_bound : forall m,
  4 * f_omega (S m) + 4 <= W (S (S (S m))) 1.
Proof.
  intros m.
  rewrite W_S. cbn [iter].
  pose proof (W_omega_bound0 m) as H0.
  set (Z := W (S (S m)) 2) in *. clearbody Z.
  rewrite W_S.
  pose proof (iter_lin3 (W (S m)) (W_grow (S m)) (S Z) 2).
  lia.
Qed.

(** ** Domination across Kc, Kc_full, Kd_step, Kd_iter, D_round, and K_round *)

Lemma Kc_dom1 : forall pa,
  4 <= fst pa -> 6 <= snd pa ->
  fst pa + 3 <= fst (Kc pa) /\
  fst pa + snd pa / 2 <= fst (Kc pa) /\
  4 * f_omega (fst pa - 3) + 4 <= snd (Kc pa).
Proof.
  intros [p a] Hp Ha. rewrite Kc_unfold. cbn [fst snd] in *.
  destruct p as [| [| [| [| m]]]]; try lia.
  replace (S (S (S (S m))) - 1) with (S (S (S m))) by lia.
  replace (S (S (S (S m))) - 3) with (S m) by lia.
  pose proof (W_omega_bound m) as Hw.
  set (z := f_omega (S m)) in *.
  set (w := W (S (S (S m))) 1) in *.
  assert (Hdiv : 3 <= a / 2) by (mods; lia).
  split; [lia | split; lia].
Qed.

Lemma Kc_dom2 : forall pa,
  4 <= fst pa -> 6 <= snd pa ->
  4 <= fst (iter 2 Kc pa) /\
  6 <= snd (iter 2 Kc pa) /\
  f_omega (fst pa - 3) + 4 <= fst (iter 2 Kc pa).
Proof.
  intros pa Hp Ha. cbn [iter].
  destruct (Kc_dom1 pa Hp Ha) as [Hp1 [_ Ha1]].
  pose proof (f_omega_id (fst pa - 3)) as Hid.
  assert (Ha1' : 6 <= snd (Kc pa)) by lia.
  destruct (Kc_dom1 (Kc pa) ltac:(lia) Ha1') as [Hp2 [Hdiv2 Ha2]].
  pose proof (f_omega_id (fst (Kc pa) - 3)) as Hid2.
  assert (Hq : 2 * f_omega (fst pa - 3) + 2 <= snd (Kc pa) / 2)
    by (set (z := f_omega (fst pa - 3)) in *; set (s := snd (Kc pa)) in *; mods; lia).
  split; [lia | split; [lia | lia]].
Qed.

Lemma Kc_dom_even : forall k pa,
  4 <= fst pa -> 6 <= snd pa ->
  4 <= fst (iter (2 * k) Kc pa) /\
  6 <= snd (iter (2 * k) Kc pa) /\
  iter k f_omega (fst pa - 3) <= fst (iter (2 * k) Kc pa) - 3.
Proof.
  induction k as [| k IHk]; intros pa Hp Ha.
  - change (2 * 0) with 0. cbn [iter]. split; [lia | split; [lia | lia]].
  - replace (2 * S k) with (2 + 2 * k) by lia.
    rewrite iter_add.
    change (iter (S k) f_omega (fst pa - 3)) with (f_omega (iter k f_omega (fst pa - 3))).
    destruct (IHk pa Hp Ha) as [Hp1 [Ha1 Hdom1]].
    destruct (Kc_dom2 (iter (2 * k) Kc pa) Hp1 Ha1) as [Hp2 [Ha2 Hdom2]].
    pose proof (f_omega_mono _ _ Hdom1).
    split; [exact Hp2 | split; [exact Ha2 | lia]].
Qed.

Lemma Kc_dom_any : forall c' pa,
  4 <= fst pa -> 6 <= snd pa ->
  4 <= fst (iter c' Kc pa) /\
  6 <= snd (iter c' Kc pa) /\
  iter (c' / 2) f_omega (fst pa - 3) <= fst (iter c' Kc pa) - 3.
Proof.
  intros c' pa Hp Ha.
  assert (Hc : c' = 2 * (c' / 2) \/ c' = 1 + 2 * (c' / 2)) by (mods; lia).
  set (k := c' / 2) in *.
  destruct Hc as [Hev | Hodd].
  - rewrite Hev. apply Kc_dom_even; assumption.
  - rewrite Hodd. rewrite iter_add. cbn [iter].
    destruct (Kc_dom_even k pa Hp Ha) as [Hp1 [Ha1 Hdom1]].
    destruct (Kc_dom1 (iter (2 * k) Kc pa) Hp1 Ha1) as [Hp2 [_ Ha2]].
    pose proof (f_omega_id (fst (iter (2 * k) Kc pa) - 3)).
    split; [lia | split; [lia | lia]].
Qed.

Definition ok_pb (n : nat) (pb : nat * nat) : Prop :=
  n + 4 <= fst pb /\ 4 * n + 2 <= snd pb.

Definition ok_pb_strong (n : nat) (pb : nat * nat) : Prop :=
  5 <= fst pb /\ 18 * n + 17 <= snd pb.

Definition ok_pa (n : nat) (pa : nat * nat) : Prop :=
  n + 6 <= fst pa /\ 6 * n + 2 <= snd pa.

Lemma ok_pb_mono : forall m n pb,
  m <= n -> ok_pb n pb -> ok_pb m pb.
Proof. intros m n pb Hmn [H1 H2]. split; lia. Qed.

Lemma ok_pb_strong_mono : forall m n pb,
  m <= n -> ok_pb_strong n pb -> ok_pb_strong m pb.
Proof. intros m n pb Hmn [H1 H2]. split; lia. Qed.

Lemma ok_pa_mono : forall m n pa,
  m <= n -> ok_pa n pa -> ok_pa m pa.
Proof. intros m n pa Hmn [H1 H2]. split; lia. Qed.

Lemma ok_pa_score_gt : forall B pa,
  ok_pa B pa -> fst pa + snd pa + 4 > B.
Proof. intros B [p a] [Hp Ha]. cbn [fst snd] in *. lia. Qed.

Lemma Kc_full_dom : forall n pb,
  1 <= n -> ok_pb n pb -> ok_pa (f_omega1 n) (Kc_full pb).
Proof.
  intros n [p b] Hn [Hp Hb]. unfold ok_pb, ok_pa in *. cbn [fst snd] in *.
  rewrite Kc_full_unfold.
  assert (Hb_ge : 1 <= b / 2) by (mods; lia).
  replace (b / 2) with (S (b / 2 - 1)) by lia.
  cbn [iter].
  pose proof (W_grow (p - 1) 3) as Hwg0.
  destruct (Kc_dom_any (b / 2 - 1) (p - 1, W (p - 1) 3) ltac:(cbn; lia) ltac:(cbn; lia))
    as [Hp1 [Ha1 Hdom1]].
  cbn [fst snd] in Hdom1. replace (p - 1 - 3) with (p - 4) in Hdom1 by lia.
  set (pa' := iter (b / 2 - 1) Kc (p - 1, W (p - 1) 3)) in *.
  destruct (Kc_dom1 pa' Hp1 Ha1) as [Hp2 [_ Ha2]].
  assert (Hdiv : n <= (b / 2 - 1) / 2) by (mods; lia).
  assert (H1 : f_omega1 n <= iter ((b / 2 - 1) / 2) f_omega (p - 4)).
  { Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
    transitivity (iter n f_omega (p - 4)).
    - apply iter_mono_x; [apply f_omega_mono | lia].
    - apply iter_mono_n; [apply f_omega_id | exact Hdiv]. }
  pose proof (f_omega1_id n) as Hid1.
  pose proof (f_omega_dbl (fst pa' - 3) ltac:(lia)) as Hdbl.
  split; lia.
Qed.

Lemma Kd_step_dom : forall n pb,
  1 <= n -> ok_pb n pb -> ok_pb (f_omega1 n) (Kd_step pb).
Proof.
  intros n pb Hn Hok.
  rewrite Kd_step_unfold.
  destruct (Kc_full_dom n pb Hn Hok) as [Hp' Ha'].
  set (pa' := Kc_full pb) in *.
  destruct pa' as [p' a']. cbn [fst snd] in *.
  pose proof (W_grow p' (a' + 4)) as Hwg.
  unfold ok_pb. cbn [fst snd].
  split; lia.
Qed.

Lemma Kd_step_dom_strong : forall n pb,
  1 <= n -> ok_pb n pb -> ok_pb_strong (f_omega1 n) (Kd_step pb).
Proof.
  intros n pb Hn Hok.
  rewrite Kd_step_unfold.
  destruct (Kc_full_dom n pb Hn Hok) as [Hp' Ha'].
  set (pa' := Kc_full pb) in *.
  destruct pa' as [p' a']. cbn [fst snd] in *.
  destruct p' as [| j']; [lia |].
  pose proof (W_S_lin3 j' (a' + 4)) as Hwg.
  unfold ok_pb_strong. cbn [fst snd].
  split; lia.
Qed.

Lemma Kd_iter_dom : forall m n pb,
  1 <= n -> ok_pb n pb -> ok_pb (iter m f_omega1 n) (Kd_iter m pb).
Proof.
  intros m n pb. rewrite Kd_iter_unfold.
  induction m as [| m IHm]; intros Hn Hok.
  - cbn [iter]. exact Hok.
  - cbn [iter]. apply Kd_step_dom.
    + pose proof (iter_ge f_omega1 f_omega1_id m n). lia.
    + apply IHm; assumption.
Qed.

Lemma D_reload_dom : forall n pa,
  1 <= n -> n + 6 <= fst pa -> ok_pb n (D_reload pa).
Proof.
  intros n [p a] Hn Hp. cbn [fst snd] in *.
  rewrite D_reload_unfold. unfold ok_pb. cbn [fst snd].
  destruct p as [| [| [| [| [| [| [| m]]]]]]]; try lia.
  replace (S (S (S (S (S (S (S m)))))) - 1) with (S (S (S (S (S (S m)))))) by lia.
  rewrite W_S_0.
  pose proof (W_omega_bound0 (S (S (S m)))) as Hw0.
  pose proof (f_omega_dbl (S (S (S (S m)))) ltac:(lia)) as Hdbl.
  lia.
Qed.

Lemma pb_K0_dom4 : ok_pb 4 pb_K0.
Proof.
  rewrite pb_K0_unfold. unfold ok_pb. cbn [fst snd].
  pose proof (W_S_lin3 7 8). lia.
Qed.

Lemma pb_K0_dom : ok_pb 3 pb_K0.
Proof.
  eapply ok_pb_mono; [| exact pb_K0_dom4]. lia.
Qed.

Lemma round_D2_dom : forall n pa,
  1 <= n -> ok_pa n pa ->
  ok_pb_strong (f_omega2 n) (D2_round pa).
Proof.
  intros n pa Hn [Hp Ha].
  Transparent D2_round. unfold D2_round. Opaque D2_round.
  pose proof (D_reload_dom n pa Hn Hp) as Hrel.
  assert (Hdiv : n + 1 <= (snd pa / 2 + 2) / 3) by (mods; lia).
  set (m := (snd pa / 2 + 2) / 3) in *.
  replace m with (S (m - 1)) by lia.
  rewrite Kd_iter_unfold. cbn [iter]. rewrite <- Kd_iter_unfold.
  pose proof (Kd_iter_dom (m - 1) n (D_reload pa) Hn Hrel) as Hloop.
  assert (Hok2 : ok_pb (f_omega2 n) (Kd_iter (m - 1) (D_reload pa))).
  { eapply ok_pb_mono; [| exact Hloop].
    Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    apply iter_mono_n; [apply f_omega1_id | lia]. }
  assert (Hf2_pos : 1 <= f_omega2 n) by (pose proof (f_omega2_id n); lia).
  pose proof (Kd_step_dom_strong (f_omega2 n) (Kd_iter (m - 1) (D_reload pa)) Hf2_pos Hok2) as Hlast.
  eapply ok_pb_strong_mono; [apply f_omega1_id | exact Hlast].
Qed.

Lemma round_D1_dom : forall n pa,
  1 <= n -> ok_pa n pa ->
  ok_pa (f_omega2 n) (D1_round pa).
Proof.
  intros n pa Hn [Hp Ha].
  Transparent D1_round. unfold D1_round. Opaque D1_round.
  pose proof (D_reload_dom n pa Hn Hp) as Hrel.
  assert (Hdiv : n + 1 <= (snd pa / 2 + 2) / 3) by (mods; lia).
  set (m := (snd pa / 2 + 2) / 3) in *.
  pose proof (Kd_iter_dom (m - 1) n (D_reload pa) Hn Hrel) as Hloop.
  assert (Hok2 : ok_pb (f_omega2 n) (Kd_iter (m - 1) (D_reload pa))).
  { eapply ok_pb_mono; [| exact Hloop].
    Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    apply iter_mono_n; [apply f_omega1_id | lia]. }
  assert (Hf2_pos : 1 <= f_omega2 n) by (pose proof (f_omega2_id n); lia).
  pose proof (Kc_full_dom (f_omega2 n) (Kd_iter (m - 1) (D_reload pa)) Hf2_pos Hok2) as Hkc.
  eapply ok_pa_mono; [apply f_omega1_id | exact Hkc].
Qed.

Lemma K_count_ge : forall n pb d,
  d <= 4 -> ok_pb_strong n pb ->
  2 * n + 1 <= (fst pb + snd pb / 2 - d) / 3.
Proof.
  intros n [p b] d Hd [Hp Hb]. cbn [fst snd] in *.
  mods; lia.
Qed.

Lemma round_K0_z0_dom : forall n pb,
  1 <= n -> ok_pb_strong n pb ->
  ok_pb_strong (f_omega2 n) (K0_z0_round pb).
Proof.
  intros n pb Hn Hok.
  Transparent K0_z0_round. unfold K0_z0_round. Opaque K0_z0_round.
  pose proof (K_count_ge n pb 2 ltac:(lia) Hok) as Hm.
  set (m := (fst pb + snd pb / 2 - 2) / 3) in *.
  replace m with (S (m - 1)) by lia.
  rewrite Kd_iter_unfold. cbn [iter]. rewrite <- Kd_iter_unfold.
  pose proof (Kd_iter_dom (m - 1) 3 pb_K0 ltac:(lia) pb_K0_dom) as Hloop.
  assert (Hle : f_omega2 n <= iter (m - 1) f_omega1 3).
  { transitivity (iter (2 * n) f_omega1 3).
    - apply f_omega2_le_iter_2n; exact Hn.
    - apply iter_mono_n; [apply f_omega1_id | lia]. }
  assert (Hok2 : ok_pb (f_omega2 n) (Kd_iter (m - 1) pb_K0))
    by (eapply ok_pb_mono; [exact Hle | exact Hloop]).
  assert (Hf2_pos : 1 <= f_omega2 n) by (pose proof (f_omega2_id n); lia).
  pose proof (Kd_step_dom_strong (f_omega2 n) (Kd_iter (m - 1) pb_K0) Hf2_pos Hok2) as Hlast.
  eapply ok_pb_strong_mono; [apply f_omega1_id | exact Hlast].
Qed.

Lemma round_K1_z0_dom : forall n pb,
  1 <= n -> ok_pb_strong n pb ->
  ok_pa (f_omega2 n) (K1_z0_round pb).
Proof.
  intros n pb Hn Hok.
  Transparent K1_z0_round. unfold K1_z0_round. Opaque K1_z0_round.
  pose proof (K_count_ge n pb 3 ltac:(lia) Hok) as Hm.
  set (m := (fst pb + snd pb / 2 - 3) / 3) in *.
  pose proof (Kd_iter_dom m 3 pb_K0 ltac:(lia) pb_K0_dom) as Hloop.
  assert (Hle : f_omega2 n <= iter m f_omega1 3).
  { transitivity (iter (2 * n) f_omega1 3).
    - apply f_omega2_le_iter_2n; exact Hn.
    - apply iter_mono_n; [apply f_omega1_id | lia]. }
  assert (Hok2 : ok_pb (f_omega2 n) (Kd_iter m pb_K0))
    by (eapply ok_pb_mono; [exact Hle | exact Hloop]).
  assert (Hf2_pos : 1 <= f_omega2 n) by (pose proof (f_omega2_id n); lia).
  pose proof (Kc_full_dom (f_omega2 n) (Kd_iter m pb_K0) Hf2_pos Hok2) as Hkc.
  eapply ok_pa_mono; [apply f_omega1_id | exact Hkc].
Qed.

Lemma round_K2_z0_dom : forall n pb,
  1 <= n -> ok_pb_strong n pb ->
  ok_pa (f_omega2 n) (K2_z0_round pb).
Proof.
  intros n pb Hn Hok.
  Transparent K2_z0_round. unfold K2_z0_round. Opaque K2_z0_round.
  pose proof (K_count_ge n pb 4 ltac:(lia) Hok) as Hm.
  set (m := (fst pb + snd pb / 2 - 4) / 3) in *.
  pose proof (Kd_iter_dom m 3 pb_K0 ltac:(lia) pb_K0_dom) as Hloop.
  assert (Hle : f_omega2 n <= iter m f_omega1 3).
  { transitivity (iter (2 * n) f_omega1 3).
    - apply f_omega2_le_iter_2n; exact Hn.
    - apply iter_mono_n; [apply f_omega1_id | lia]. }
  assert (Hok2 : ok_pb (f_omega2 n) (Kd_iter m pb_K0))
    by (eapply ok_pb_mono; [exact Hle | exact Hloop]).
  assert (Hf2_pos : 1 <= f_omega2 n) by (pose proof (f_omega2_id n); lia).
  pose proof (Kc_full_dom (f_omega2 n) (Kd_iter m pb_K0) Hf2_pos Hok2) as Hkc.
  eapply ok_pa_mono; [apply f_omega1_id | exact Hkc].
Qed.

Lemma round_K0_z1_dom : forall n pb,
  1 <= n -> ok_pb_strong n pb ->
  ok_pb_strong (f_omega2 n) (K0_z1_round pb).
Proof.
  intros n pb Hn Hok.
  Transparent K0_z1_round. unfold K0_z1_round. Opaque K0_z1_round.
  pose proof (K_count_ge n pb 1 ltac:(lia) Hok) as Hm.
  set (m := (fst pb + snd pb / 2 - 1) / 3) in *.
  replace m with (S (m - 1)) by lia.
  rewrite Kd_iter_unfold. cbn [iter]. rewrite <- Kd_iter_unfold.
  pose proof (Kd_iter_dom (m - 1) 3 pb_K0 ltac:(lia) pb_K0_dom) as Hloop.
  assert (Hle : f_omega2 n <= iter (m - 1) f_omega1 3).
  { transitivity (iter (2 * n) f_omega1 3).
    - apply f_omega2_le_iter_2n; exact Hn.
    - apply iter_mono_n; [apply f_omega1_id | lia]. }
  assert (Hok2 : ok_pb (f_omega2 n) (Kd_iter (m - 1) pb_K0))
    by (eapply ok_pb_mono; [exact Hle | exact Hloop]).
  assert (Hf2_pos : 1 <= f_omega2 n) by (pose proof (f_omega2_id n); lia).
  pose proof (Kd_step_dom_strong (f_omega2 n) (Kd_iter (m - 1) pb_K0) Hf2_pos Hok2) as Hlast.
  eapply ok_pb_strong_mono; [apply f_omega1_id | exact Hlast].
Qed.

Lemma round_K1_z1_dom : forall n pb,
  1 <= n -> ok_pb_strong n pb ->
  ok_pa (f_omega2 n) (K1_z1_round pb).
Proof.
  intros n pb Hn Hok.
  Transparent K1_z1_round. unfold K1_z1_round. Opaque K1_z1_round.
  pose proof (K_count_ge n pb 2 ltac:(lia) Hok) as Hm.
  set (m := (fst pb + snd pb / 2 - 2) / 3) in *.
  pose proof (Kd_iter_dom m 3 pb_K0 ltac:(lia) pb_K0_dom) as Hloop.
  assert (Hle : f_omega2 n <= iter m f_omega1 3).
  { transitivity (iter (2 * n) f_omega1 3).
    - apply f_omega2_le_iter_2n; exact Hn.
    - apply iter_mono_n; [apply f_omega1_id | lia]. }
  assert (Hok2 : ok_pb (f_omega2 n) (Kd_iter m pb_K0))
    by (eapply ok_pb_mono; [exact Hle | exact Hloop]).
  assert (Hf2_pos : 1 <= f_omega2 n) by (pose proof (f_omega2_id n); lia).
  pose proof (Kc_full_dom (f_omega2 n) (Kd_iter m pb_K0) Hf2_pos Hok2) as Hkc.
  eapply ok_pa_mono; [apply f_omega1_id | exact Hkc].
Qed.

Lemma round_K2_z1_dom : forall n pb,
  1 <= n -> ok_pb_strong n pb ->
  ok_pa (f_omega2 n) (K2_z1_round pb).
Proof.
  intros n pb Hn Hok.
  Transparent K2_z1_round. unfold K2_z1_round. Opaque K2_z1_round.
  pose proof (K_count_ge n pb 3 ltac:(lia) Hok) as Hm.
  set (m := (fst pb + snd pb / 2 - 3) / 3) in *.
  pose proof (Kd_iter_dom m 3 pb_K0 ltac:(lia) pb_K0_dom) as Hloop.
  assert (Hle : f_omega2 n <= iter m f_omega1 3).
  { transitivity (iter (2 * n) f_omega1 3).
    - apply f_omega2_le_iter_2n; exact Hn.
    - apply iter_mono_n; [apply f_omega1_id | lia]. }
  assert (Hok2 : ok_pb (f_omega2 n) (Kd_iter m pb_K0))
    by (eapply ok_pb_mono; [exact Hle | exact Hloop]).
  assert (Hf2_pos : 1 <= f_omega2 n) by (pose proof (f_omega2_id n); lia).
  pose proof (Kc_full_dom (f_omega2 n) (Kd_iter m pb_K0) Hf2_pos Hok2) as Hkc.
  eapply ok_pa_mono; [apply f_omega1_id | exact Hkc].
Qed.

(** ** Round 1 through Round 32 lower bounds *)

Definition B0 : nat := iter 2 f_omega 3.
Definition B1 : nat := iter 2 f_omega1 3.

Lemma B0_def : B0 = iter 2 f_omega 3. Proof. reflexivity. Qed.
Lemma B1_def : B1 = iter 2 f_omega1 3. Proof. reflexivity. Qed.

Lemma B0_ge_3 : 3 <= B0.
Proof.
  unfold B0. pose proof (iter_ge f_omega f_omega_id 2 3). lia.
Qed.

Lemma B0_pos : forall k, 1 <= iter k f_omega2 B0.
Proof.
  intros k.
  pose proof (iter_ge f_omega2 f_omega2_id k B0).
  pose proof B0_ge_3. lia.
Qed.

Lemma B1_le_f_omega2_B0 : B1 <= iter 1 f_omega2 B0.
Proof.
  cbn [iter]. unfold B1. apply f_omega2_ge_iter3. exact B0_ge_3.
Qed.

Lemma B1_le_iter_B0 : forall k,
  iter k f_omega2 B1 <= iter (S k) f_omega2 B0.
Proof.
  induction k as [| k IHk].
  - exact B1_le_f_omega2_B0.
  - change (iter (S k) f_omega2 B1) with (f_omega2 (iter k f_omega2 B1)).
    change (iter (S (S k)) f_omega2 B0) with (f_omega2 (iter (S k) f_omega2 B0)).
    apply f_omega2_mono. exact IHk.
Qed.

Lemma B0_le_f_omega1_4 : B0 <= f_omega1 4.
Proof.
  unfold B0. Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
  transitivity (iter 2 f_omega 4).
  - apply iter_mono_x; [apply f_omega_mono | lia].
  - apply iter_mono_n; [apply f_omega_id | lia].
Qed.

Lemma pa1_dom : ok_pa (iter 0 f_omega2 B0) pa1.
Proof.
  cbn [iter]. rewrite pa1_def.
  eapply ok_pa_mono; [exact B0_le_f_omega1_4 |].
  apply (Kc_full_dom 4 pb_K0 ltac:(lia) pb_K0_dom4).
Qed.

Opaque f f_omega f_omega1 f_omega2 B0 B1.

Lemma pb2_dom : ok_pb_strong (iter 1 f_omega2 B0) pb2.
Proof.
  rewrite pb2_def. apply (round_D2_dom (iter 0 f_omega2 B0) pa1); [apply B0_pos | exact pa1_dom].
Qed.

Lemma pb3_dom : ok_pb_strong (iter 2 f_omega2 B0) pb3.
Proof.
  rewrite pb3_def. apply (round_K0_z0_dom (iter 1 f_omega2 B0) pb2); [apply B0_pos | exact pb2_dom].
Qed.

Lemma pa4_dom : ok_pa (iter 3 f_omega2 B0) pa4.
Proof.
  rewrite pa4_def. apply (round_K2_z1_dom (iter 2 f_omega2 B0) pb3); [apply B0_pos | exact pb3_dom].
Qed.

Lemma pb5_dom : ok_pb_strong (iter 4 f_omega2 B0) pb5.
Proof.
  rewrite pb5_def. apply (round_D2_dom (iter 3 f_omega2 B0) pa4); [apply B0_pos | exact pa4_dom].
Qed.

Lemma pb6_dom : ok_pb_strong (iter 5 f_omega2 B0) pb6.
Proof.
  rewrite pb6_def. apply (round_K0_z0_dom (iter 4 f_omega2 B0) pb5); [apply B0_pos | exact pb5_dom].
Qed.

Lemma pb7_dom : ok_pb_strong (iter 6 f_omega2 B0) pb7.
Proof.
  rewrite pb7_def. apply (round_K0_z1_dom (iter 5 f_omega2 B0) pb6); [apply B0_pos | exact pb6_dom].
Qed.

Lemma pa8_dom : ok_pa (iter 7 f_omega2 B0) pa8.
Proof.
  rewrite pa8_def. apply (round_K2_z0_dom (iter 6 f_omega2 B0) pb7); [apply B0_pos | exact pb7_dom].
Qed.

Lemma pb9_dom : ok_pb_strong (iter 8 f_omega2 B0) pb9.
Proof.
  rewrite pb9_def. apply (round_D2_dom (iter 7 f_omega2 B0) pa8); [apply B0_pos | exact pa8_dom].
Qed.

Lemma pa10_dom : ok_pa (iter 9 f_omega2 B0) pa10.
Proof.
  rewrite pa10_def. apply (round_K2_z1_dom (iter 8 f_omega2 B0) pb9); [apply B0_pos | exact pb9_dom].
Qed.

Lemma pb11_dom : ok_pb_strong (iter 10 f_omega2 B0) pb11.
Proof.
  rewrite pb11_def. apply (round_D2_dom (iter 9 f_omega2 B0) pa10); [apply B0_pos | exact pa10_dom].
Qed.

Lemma pa12_dom : ok_pa (iter 11 f_omega2 B0) pa12.
Proof.
  rewrite pa12_def. apply (round_K2_z0_dom (iter 10 f_omega2 B0) pb11); [apply B0_pos | exact pb11_dom].
Qed.

Lemma pb13_dom : ok_pb_strong (iter 12 f_omega2 B0) pb13.
Proof.
  rewrite pb13_def. apply (round_D2_dom (iter 11 f_omega2 B0) pa12); [apply B0_pos | exact pa12_dom].
Qed.

Lemma pa14_dom : ok_pa (iter 13 f_omega2 B0) pa14.
Proof.
  rewrite pa14_def. apply (round_K1_z1_dom (iter 12 f_omega2 B0) pb13); [apply B0_pos | exact pb13_dom].
Qed.

Lemma pa15_dom : ok_pa (iter 14 f_omega2 B0) pa15.
Proof.
  rewrite pa15_def. apply (round_D1_dom (iter 13 f_omega2 B0) pa14); [apply B0_pos | exact pa14_dom].
Qed.

Lemma pb16_dom : ok_pb_strong (iter 15 f_omega2 B0) pb16.
Proof.
  rewrite pb16_def. apply (round_D2_dom (iter 14 f_omega2 B0) pa15); [apply B0_pos | exact pa15_dom].
Qed.

Lemma pa17_dom : ok_pa (iter 16 f_omega2 B0) pa17.
Proof.
  rewrite pa17_def. apply (round_K1_z1_dom (iter 15 f_omega2 B0) pb16); [apply B0_pos | exact pb16_dom].
Qed.

Lemma pa18_dom : ok_pa (iter 17 f_omega2 B0) pa18.
Proof.
  rewrite pa18_def. apply (round_D1_dom (iter 16 f_omega2 B0) pa17); [apply B0_pos | exact pa17_dom].
Qed.

Lemma pb19_dom : ok_pb_strong (iter 18 f_omega2 B0) pb19.
Proof.
  rewrite pb19_def. apply (round_D2_dom (iter 17 f_omega2 B0) pa18); [apply B0_pos | exact pa18_dom].
Qed.

Lemma pb20_dom : ok_pb_strong (iter 19 f_omega2 B0) pb20.
Proof.
  rewrite pb20_def. apply (round_K0_z1_dom (iter 18 f_omega2 B0) pb19); [apply B0_pos | exact pb19_dom].
Qed.

Lemma pa21_dom : ok_pa (iter 20 f_omega2 B0) pa21.
Proof.
  rewrite pa21_def. apply (round_K2_z0_dom (iter 19 f_omega2 B0) pb20); [apply B0_pos | exact pb20_dom].
Qed.

Lemma pb22_dom : ok_pb_strong (iter 21 f_omega2 B0) pb22.
Proof.
  rewrite pb22_def. apply (round_D2_dom (iter 20 f_omega2 B0) pa21); [apply B0_pos | exact pa21_dom].
Qed.

Lemma pa23_dom : ok_pa (iter 22 f_omega2 B0) pa23.
Proof.
  rewrite pa23_def. apply (round_K1_z1_dom (iter 21 f_omega2 B0) pb22); [apply B0_pos | exact pb22_dom].
Qed.

Lemma pa24_dom : ok_pa (iter 23 f_omega2 B0) pa24.
Proof.
  rewrite pa24_def. apply (round_D1_dom (iter 22 f_omega2 B0) pa23); [apply B0_pos | exact pa23_dom].
Qed.

Lemma pb25_dom : ok_pb_strong (iter 24 f_omega2 B0) pb25.
Proof.
  rewrite pb25_def. apply (round_D2_dom (iter 23 f_omega2 B0) pa24); [apply B0_pos | exact pa24_dom].
Qed.

Lemma pa26_dom : ok_pa (iter 25 f_omega2 B0) pa26.
Proof.
  rewrite pa26_def. apply (round_K2_z1_dom (iter 24 f_omega2 B0) pb25); [apply B0_pos | exact pb25_dom].
Qed.

Lemma pb27_dom : ok_pb_strong (iter 26 f_omega2 B0) pb27.
Proof.
  rewrite pb27_def. apply (round_D2_dom (iter 25 f_omega2 B0) pa26); [apply B0_pos | exact pa26_dom].
Qed.

Lemma pa28_dom : ok_pa (iter 27 f_omega2 B0) pa28.
Proof.
  rewrite pa28_def. apply (round_K2_z0_dom (iter 26 f_omega2 B0) pb27); [apply B0_pos | exact pb27_dom].
Qed.

Lemma pb29_dom : ok_pb_strong (iter 28 f_omega2 B0) pb29.
Proof.
  rewrite pb29_def. apply (round_D2_dom (iter 27 f_omega2 B0) pa28); [apply B0_pos | exact pa28_dom].
Qed.

Lemma pa30_dom : ok_pa (iter 29 f_omega2 B0) pa30.
Proof.
  rewrite pa30_def. apply (round_K2_z1_dom (iter 28 f_omega2 B0) pb29); [apply B0_pos | exact pb29_dom].
Qed.

Lemma pb31_dom : ok_pb_strong (iter 30 f_omega2 B0) pb31.
Proof.
  rewrite pb31_def. apply (round_D2_dom (iter 29 f_omega2 B0) pa30); [apply B0_pos | exact pa30_dom].
Qed.

Lemma pa32_dom : ok_pa (iter 31 f_omega2 B0) pa32.
Proof.
  rewrite pa32_def. apply (round_K1_z0_dom (iter 30 f_omega2 B0) pb31); [apply B0_pos | exact pb31_dom].
Qed.

Lemma pa32_dom_fw1 : ok_pa (iter 30 f_omega2 (iter 2 f_omega1 3)) pa32.
Proof.
  rewrite <- B1_def. eapply ok_pa_mono; [apply (B1_le_iter_B0 30) | exact pa32_dom].
Qed.

Theorem sigma_bound :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
  n > iter 31 f_omega2 (iter 2 f_omega 3).
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (fst pa32 + snd pa32 + 4).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  rewrite <- B0_def. apply ok_pa_score_gt. exact pa32_dom.
Qed.

Theorem sigma_bound_fw1 :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
  n > iter 30 f_omega2 (iter 2 f_omega1 3).
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (fst pa32 + snd pa32 + 4).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  apply ok_pa_score_gt. exact pa32_dom_fw1.
Qed.

Print Assumptions halt.
Print Assumptions sigma_bound.
Print Assumptions sigma_bound_fw1.
