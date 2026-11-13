(* machine: 1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_1LN1LK_1RK0LH_1LD0RK *)
(** * New BB(14) Champion M14_fw3 achieves > f_(omega+3)(f_omega(3)) and halts *)

From BB8 Require Import Individual142.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(* M12-core A-started machine string:
   1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_1LN1LK_1RK0LH_1LD0RK
   (First-visit canonical TNF string:
   1RB1RA_1RC1RJ_1RD0LK_0LE1RI_---0LF_1LG1LE_1LH0RE_0RD1LH_1RL0RA_0LH1LN_1LM1LC_1RE0LM_1LN1LM_1RA0LM) *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, B)  | A, 1 => Some (1, TM.R, A)
  | B, 0 => Some (1, TM.R, I)  | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)  | C, 1 => Some (1, TM.L, G)
  | D, 0 => Some (0, TM.R, E)  | D, 1 => Some (1, TM.L, D)
  | E, 0 => Some (0, TM.L, K)  | E, 1 => Some (1, TM.R, F)
  | F, 0 => Some (1, TM.R, M)  | F, 1 => Some (0, TM.R, A)
  | G, 0 => Some (1, TM.R, A)  | G, 1 => Some (0, TM.L, H)
  | H, 0 => Some (1, TM.L, G)  | H, 1 => Some (1, TM.L, H)
  | I, 0 => Some (1, TM.R, E)  | I, 1 => Some (0, TM.L, J)
  | J, 0 => Some (1, TM.L, H)  | J, 1 => Some (1, TM.L, I)
  | K, 0 => None               | K, 1 => Some (0, TM.L, L)
  | L, 0 => Some (1, TM.L, N)  | L, 1 => Some (1, TM.L, K)
  | M, 0 => Some (1, TM.R, K)  | M, 1 => Some (0, TM.L, H)
  | N, 0 => Some (1, TM.L, D)  | N, 1 => Some (0, TM.R, K)
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

Lemma cr_LK_11_01 : forall n l r, [1; 1]^^n *> l <{{L}} r -->* l <{{L}} [0; 1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** ** Configurations and inner M12 cascade rules *)

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

(** ** Outer 2-phase counter rules (N_bounce, Phase1_reload, Phase2_reload, Halt_E0) *)

Lemma N_bounce : forall p d z,
  ([0; 1]^^(S (S (S p))) *> const 0) <{{L}} (0 >> [1; 0]^^(S d) *> z) -->+
  Cd_z (S (S p)) 1 (S d) z.
Proof.
  intros p d z. unfold Cd_z. cbn [lpow Str_app].
  start_progress; finish_norm.
Qed.

Lemma Phase1_reload_aux : forall p' k z,
  Ce_z p' (2 * k) 0 0 (0 >> z) -->+
  ([0; 1]^^p' *> const 0) <{{L}} (0 >> [1; 0]^^(S k) *> (0 >> z)).
Proof.
  intros p' k z. unfold Ce_z.
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_KL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma Phase1_reload : forall p k z,
  Ce_z (S (S (S p))) (2 * k) 0 0 (0 >> z) -->+
  Cd_z (S (S p)) 1 (S k) (0 >> z).
Proof.
  intros p k z.
  eapply progress_evstep_trans; [apply Phase1_reload_aux |].
  apply progress_evstep, N_bounce.
Qed.

Lemma Phase2_reload_aux : forall p' k zE,
  Ce_z p' (2 * k) 0 1 (0 >> 1 >> zE) -->+
  ([0; 1]^^p' *> const 0) <{{L}} (0 >> [1; 0]^^(k + 3) *> zE).
Proof.
  intros p' k zE. unfold Ce_z.
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_KL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma Phase2_reload : forall p k E,
  Ce_z (S (S (S p))) (2 * k) 0 1 (0 >> [1; 0]^^(S E) *> const 0) -->+
  Cd_z (S (S p)) 1 (k + 3) (0 >> [1; 0]^^E *> const 0).
Proof.
  intros p k E.
  change (0 >> [1; 0]^^(S E) *> const 0)%sym with (0 >> 1 >> (0 >> [1; 0]^^E *> const 0))%sym.
  eapply progress_evstep_trans; [apply Phase2_reload_aux |].
  replace (k + 3)%nat with (S (k + 2))%nat by lia.
  apply progress_evstep, N_bounce.
Qed.

Definition c_end (p a : nat) : Q * tape :=
  ([1]^^(a + 6) *> [0; 1]^^p *> const 0) {{K}}> const 0.

Lemma HALT_E0 : forall p a,
  Ce_z p a 0 1 (0 >> const 0) -->+ c_end p a.
Proof.
  intros p a. unfold Ce_z, c_end. cbn [lpow Str_app].
  rewrite const_unfold at 2.
  start_progress; finish_norm.
Qed.

Lemma c_end_halted : forall p a, halted tm (c_end p a).
Proof. intros p a. unfold c_end. reflexivity. Qed.

(** ** Exact hierarchy function W and inner transitions *)

Local Open Scope nat_scope.

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

Lemma N_bounce_step : forall p d z,
  Cd_z (S p) 1 (S (S (S d))) z -->+ Cd_z p (W p (W p 3 + 4)) d z.
Proof.
  intros p d z.
  eapply progress_evstep_trans; [apply (C_REL p 0 (S (S d)) z) |].
  apply progress_evstep, D_STEP.
Qed.

(** ** Concrete boot segments (139 steps from c0 + 72-step bridge) *)

Lemma Boot_139 : c0 -->* Ch 3 3 (const S0).
Proof.
  unfold Ch. cbn [lpow Str_app].
  do 139 step; finish_norm.
Qed.

Lemma Boot_bridge_72 : forall z,
  ([S1]^^8 *> const S0) {{I}}> ([S1; S0]^^29 *> z) -->* Cd_z 4 3 28 z.
Proof.
  intros z. unfold Cd_z. cbn [lpow Str_app].
  do 72 step; finish_norm.
Qed.

(** ** Growth, parity, and mod-6 invariants of W *)

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
  a = 2 * (a / 2) /\ 136 <= a / 2 /\ a / 2 + 2 = 3 * ((a / 2 + 2) / 3).

Definition is_W_odd (b : nat) : Prop :=
  b = 2 * (b / 2) + 1 /\ 59 <= b / 2.

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
    assert (Hpow : 2 * W 2 y + 5 = 9 * 3 ^ (y + 1)).
    { rewrite W2_closed. replace (y + 3) with (2 + (y + 1)) by lia.
      rewrite Nat.pow_add_r. change (3 ^ 2) with 9. lia. }
    set (a := W 2 y) in *; clearbody a; clear Hw Hpar.
    unfold is_W_even.
    assert (Ha_eq : a = 2 * (a / 2) /\ 136 <= a / 2) by (mods; lia).
    destruct Ha_eq as [H1 H2].
    split; [exact H1 | split; [exact H2 |]].
    set (p3 := 3 ^ (y + 1)) in *; clearbody p3.
    mods; lia.
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
  set (w := W 2 y) in *; clearbody w; clear Hw Hpar.
  unfold is_W_odd. mods; lia.
Qed.

Lemma W2_1_val : W 2 1 = 38.
Proof. reflexivity. Qed.

Lemma W2_2_val : W 2 2 = 119.
Proof.
  pose proof (W2_closed 2) as H.
  change (3 ^ (2 + 3)) with 243 in H. lia.
Qed.

Lemma W1_3_val : W 1 3 = 14.
Proof. reflexivity. Qed.

Lemma W1_18_val : W 1 18 = 59.
Proof. rewrite W_1. lia. Qed.

Lemma W0_3_val : W 0 3 = 6.
Proof. reflexivity. Qed.

Opaque W.
Strategy opaque [W].

(** ** Macro-step functions and outer 2-phase execution *)

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

Definition N_bounce_pb (p : nat) : nat * nat :=
  (p, W p (W p 3 + 4)).

Definition Phase1_pa (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  Kc_full (Kd_iter ((a / 2 + 2) / 3 - 2) (N_bounce_pb (p - 2))).

Definition Phase2_pa (pa1 : nat * nat) : nat * nat :=
  let '(p1, a1) := pa1 in
  Kc_full (Kd_iter ((a1 / 2 + 2) / 3 - 1) (N_bounce_pb (p1 - 2))).

Definition Outer_step (pa : nat * nat) : nat * nat :=
  Phase2_pa (Phase1_pa pa).

Lemma Kc_unfold : forall p a, Kc (p, a) = (p + a / 2, W (p - 1) 1). Proof. reflexivity. Qed.
Lemma Kc_full_unfold : forall p b, Kc_full (p, b) = iter (b / 2) Kc (p - 1, W (p - 1) 3). Proof. reflexivity. Qed.
Lemma Kd_step_unfold : forall pb, Kd_step pb = let '(p', a') := Kc_full pb in (p', W p' (a' + 4)). Proof. reflexivity. Qed.
Lemma Kd_iter_unfold : forall m pb, Kd_iter m pb = iter m Kd_step pb. Proof. reflexivity. Qed.

Lemma Kc_step : forall c d z pa,
  1 <= fst pa -> snd pa = 2 * (snd pa / 2) ->
  Ce_z (fst pa) (snd pa) (S c) d z -->+ Ce_z (fst (Kc pa)) (snd (Kc pa)) c d z.
Proof.
  intros c d z [p a] Hp Ha_eq. cbn [fst snd Kc] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  replace (S p' + a / 2) with (p' + S (a / 2)) by lia.
  rewrite Ha_eq at 1.
  apply CE_EVEN.
Qed.

Lemma Kc_loop : forall c d z pa,
  4 <= fst pa -> is_W_even (snd pa) ->
  Ce_z (fst pa) (snd pa) c d z -->* Ce_z (fst (iter c Kc pa)) (snd (iter c Kc pa)) 0 d z /\
  fst pa + c <= fst (iter c Kc pa) /\
  is_W_even (snd (iter c Kc pa)).
Proof.
  induction c as [| c IHc]; intros d z pa Hp Ha.
  - cbn [iter]. split; [finish | split; [lia | exact Ha]].
  - rewrite iter_S'.
    destruct Ha as [Ha_eq [Ha_ge Ha_div3]].
    assert (Hw1 : is_W_even (snd (Kc pa))).
    { destruct pa as [p a]. cbn [fst snd Kc] in *. apply W_ge3_odd; [lia | reflexivity]. }
    assert (Hp1 : fst pa + 1 <= fst (Kc pa)).
    { destruct pa as [p a]. cbn [fst snd Kc] in *. lia. }
    destruct (IHc d z (Kc pa) ltac:(lia) Hw1) as [Hrun [Hp2 Ha2]].
    split; [| split].
    + eapply evstep_trans; [apply progress_evstep, (Kc_step c d z pa ltac:(lia) Ha_eq) | exact Hrun].
    + lia.
    + exact Ha2.
Qed.

Lemma Kc_full_all : forall d z pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) (S d) z -->+ Ce_z (fst (Kc_full pb)) (snd (Kc_full pb)) 0 d z /\
  fst pb + 58 <= fst (Kc_full pb) /\
  is_W_even (snd (Kc_full pb)).
Proof.
  intros d z [p b] Hp [Hb_eq Hb_ge]. cbn [fst snd Kc_full] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  assert (Hw3 : is_W_even (W p' 3)) by (apply W_ge3_odd; [lia | reflexivity]).
  destruct (Kc_loop (b / 2) d z (p', W p' 3) ltac:(cbn; lia) Hw3) as [Hrun [Hp1 Ha1]].
  cbn [fst snd] in *.
  split; [| split].
  - rewrite Hb_eq at 1.
    eapply progress_evstep_trans; [apply C_REL | exact Hrun].
  - lia.
  - exact Ha1.
Qed.

Lemma Kd_step_all : forall d z pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) (S (S (S d))) z -->+ Cd_z (fst (Kd_step pb)) (snd (Kd_step pb)) d z /\
  fst pb + 58 <= fst (Kd_step pb) /\
  is_W_odd (snd (Kd_step pb)).
Proof.
  intros d z pb Hp Hb.
  unfold Kd_step.
  destruct (Kc_full_all (S (S d)) z pb Hp Hb) as [Hkc [Hp1 Ha1]].
  set (pa' := Kc_full pb) in *.
  destruct pa' as [p' a']. cbn [fst snd] in *.
  destruct Ha1 as [Ha_eq _].
  assert (Ha4_ev : (a' + 4) mod 2 = 0).
  { replace (a' + 4) with (0 + (a' / 2 + 2) * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (Hw : is_W_odd (W p' (a' + 4))) by (apply W_ge3_even; [lia | lia | exact Ha4_ev]).
  split; [| split].
  - eapply progress_evstep_trans; [exact Hkc | apply progress_evstep, D_STEP].
  - exact Hp1.
  - exact Hw.
Qed.

Lemma Kd_loop : forall m r z pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) (3 * m + r) z -->* Cd_z (fst (Kd_iter m pb)) (snd (Kd_iter m pb)) r z /\
  fst pb + 58 * m <= fst (Kd_iter m pb) /\
  is_W_odd (snd (Kd_iter m pb)).
Proof.
  unfold Kd_iter.
  induction m as [| m IHm]; intros r z pb Hp Hb.
  - cbn [iter]. replace (3 * 0 + r) with r by lia.
    split; [finish | split; [lia | exact Hb]].
  - rewrite iter_S'.
    replace (3 * S m + r) with (S (S (S (3 * m + r)))) by lia.
    destruct (Kd_step_all (3 * m + r) z pb Hp Hb) as [Hstep [Hp1 Hb1]].
    destruct (IHm r z (Kd_step pb) ltac:(lia) Hb1) as [Hrun [Hp2 Hb2]].
    split; [| split].
    + eapply evstep_trans; [apply progress_evstep, Hstep | exact Hrun].
    + lia.
    + exact Hb2.
Qed.

Lemma N_bounce_pb_props : forall p,
  5 <= p ->
  fst (N_bounce_pb p) = p /\
  is_W_odd (snd (N_bounce_pb p)).
Proof.
  intros p Hp. unfold N_bounce_pb. cbn [fst snd].
  split; [reflexivity |].
  destruct (W_ge3_odd p 3 ltac:(lia) eq_refl) as [Hw_eq _].
  assert (Hev : (W p 3 + 4) mod 2 = 0).
  { replace (W p 3 + 4) with (0 + (W p 3 / 2 + 2) * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  apply W_ge3_even; [lia | lia | exact Hev].
Qed.

Lemma Phase1_exec : forall z pa,
  7 <= fst pa -> is_W_even (snd pa) ->
  Ce_z (fst pa) (snd pa) 0 0 (S0 >> z) -->+ Ce_z (fst (Phase1_pa pa)) (snd (Phase1_pa pa)) 0 1 (S0 >> z) /\
  7 <= fst (Phase1_pa pa) /\
  is_W_even (snd (Phase1_pa pa)).
Proof.
  intros z [p a] Hp [Ha_eq [Ha_ge Ha_div3]]. cbn [fst snd Phase1_pa] in *.
  set (M := (a / 2 + 2) / 3) in *.
  assert (HM_ge : 46 <= M) by (unfold M in *; lia).
  destruct (N_bounce_pb_props (p - 2) ltac:(lia)) as [Hnb_p Hnb_odd].
  destruct (Kd_loop (M - 2) 2 (S0 >> z) (N_bounce_pb (p - 2)) ltac:(lia) Hnb_odd)
    as [Hkd [Hkd_p Hkd_odd]].
  destruct (Kc_full_all 1 (S0 >> z) (Kd_iter (M - 2) (N_bounce_pb (p - 2))) ltac:(lia) Hkd_odd)
    as [Hkc [Hkc_p Hkc_ev]].
  split; [| split; [lia | exact Hkc_ev]].
  replace p with (S (S (S (p - 3)))) at 1 by lia.
  rewrite Ha_eq at 1.
  eapply progress_evstep_trans; [apply Phase1_reload |].
  replace (S (S (p - 3))) with (S (p - 2)) by lia.
  assert (HSa : S (a / 2) = S (S (S (3 * (M - 2) + 2)))) by (unfold M in *; lia).
  rewrite HSa.
  eapply evstep_trans; [apply progress_evstep, N_bounce_step |].
  change (Cd_z (p - 2) (W (p - 2) (W (p - 2) 3 + 4)) (3 * (M - 2) + 2) (S0 >> z))
    with (Cd_z (fst (N_bounce_pb (p - 2))) (snd (N_bounce_pb (p - 2))) (3 * (M - 2) + 2) (S0 >> z)).
  eapply evstep_trans; [exact Hkd |].
  apply progress_evstep, Hkc.
Qed.

Lemma Phase2_exec : forall E pa1,
  7 <= fst pa1 -> is_W_even (snd pa1) ->
  Ce_z (fst pa1) (snd pa1) 0 1 (S0 >> [S1; S0]^^(S E) *> const S0) -->+
  Ce_z (fst (Phase2_pa pa1)) (snd (Phase2_pa pa1)) 0 0 (S0 >> [S1; S0]^^E *> const S0) /\
  7 <= fst (Phase2_pa pa1) /\
  is_W_even (snd (Phase2_pa pa1)).
Proof.
  intros E [p1 a1] Hp1 [Ha1_eq [Ha1_ge Ha1_div3]]. cbn [fst snd Phase2_pa] in *.
  set (M1 := (a1 / 2 + 2) / 3) in *.
  assert (HM1_ge : 46 <= M1) by (unfold M1 in *; lia).
  destruct (N_bounce_pb_props (p1 - 2) ltac:(lia)) as [Hnb_p Hnb_odd].
  destruct (Kd_loop (M1 - 1) 1 (S0 >> [S1; S0]^^E *> const S0) (N_bounce_pb (p1 - 2)) ltac:(lia) Hnb_odd)
    as [Hkd [Hkd_p Hkd_odd]].
  destruct (Kc_full_all 0 (S0 >> [S1; S0]^^E *> const S0) (Kd_iter (M1 - 1) (N_bounce_pb (p1 - 2))) ltac:(lia) Hkd_odd)
    as [Hkc [Hkc_p Hkc_ev]].
  split; [| split; [lia | exact Hkc_ev]].
  replace p1 with (S (S (S (p1 - 3)))) at 1 by lia.
  rewrite Ha1_eq at 1.
  eapply progress_evstep_trans; [apply Phase2_reload |].
  replace (S (S (p1 - 3))) with (S (p1 - 2)) by lia.
  assert (HSa1 : a1 / 2 + 3 = S (S (S (3 * (M1 - 1) + 1)))) by (unfold M1 in *; lia).
  rewrite HSa1.
  eapply evstep_trans; [apply progress_evstep, N_bounce_step |].
  change (Cd_z (p1 - 2) (W (p1 - 2) (W (p1 - 2) 3 + 4)) (3 * (M1 - 1) + 1) (S0 >> [S1; S0]^^E *> const S0))
    with (Cd_z (fst (N_bounce_pb (p1 - 2))) (snd (N_bounce_pb (p1 - 2))) (3 * (M1 - 1) + 1) (S0 >> [S1; S0]^^E *> const S0)).
  eapply evstep_trans; [exact Hkd |].
  apply progress_evstep, Hkc.
Qed.

Lemma Outer_step_unfold : forall pa, Outer_step pa = Phase2_pa (Phase1_pa pa).
Proof. reflexivity. Qed.

Opaque Kc Kc_full Kd_step Kd_iter N_bounce_pb Phase1_pa Phase2_pa Outer_step.

Lemma Outer_loop : forall E pa,
  7 <= fst pa -> is_W_even (snd pa) ->
  Ce_z (fst pa) (snd pa) 0 0 (S0 >> [S1; S0]^^E *> const S0) -->*
  Ce_z (fst (iter E Outer_step pa)) (snd (iter E Outer_step pa)) 0 0 (S0 >> const S0) /\
  7 <= fst (iter E Outer_step pa) /\
  is_W_even (snd (iter E Outer_step pa)).
Proof.
  induction E as [| E IHE]; intros pa Hp Ha.
  - cbn [iter lpow Str_app]. split; [finish | split; [exact Hp | exact Ha]].
  - rewrite iter_S'.
    destruct (Phase1_exec ([S1; S0]^^(S E) *> const S0) pa Hp Ha) as [Hp1_run [Hp1_ge Hp1_ev]].
    destruct (Phase2_exec E (Phase1_pa pa) Hp1_ge Hp1_ev) as [Hp2_run [Hp2_ge Hp2_ev]].
    rewrite <- Outer_step_unfold in *.
    destruct (IHE (Outer_step pa) Hp2_ge Hp2_ev) as [Hrest [Hfin_ge Hfin_ev]].
    split; [| split; [exact Hfin_ge | exact Hfin_ev]].
    eapply evstep_trans; [apply progress_evstep, Hp1_run |].
    eapply evstep_trans; [apply progress_evstep, Hp2_run | exact Hrest].
Qed.

(** ** Boot from blank tape c0 to Outer_loop entry *)

Definition E0 : nat := W 3 3 / 2 - 3.

Definition pb_boot : nat * nat :=
  (3 + W 3 3 / 2, W (3 + W 3 3 / 2) (W 2 1 + 4)).

Definition pa_init : nat * nat :=
  Kc_full (Kd_iter 8 pb_boot).

Definition pa_final : nat * nat :=
  Phase1_pa (iter E0 Outer_step pa_init).

Lemma W3_3_even : is_W_even (W 3 3).
Proof. apply W_ge3_odd; [lia | reflexivity]. Qed.

Lemma E0_ge_133 : 133 <= E0.
Proof.
  unfold E0. destruct W3_3_even as [_ [Hge _]]. lia.
Qed.

Lemma I_const0_to_Ce : forall p a,
  ([S1]^^(a + 2) *> [S0; S1]^^p *> const S0) {{I}}> (const S0) =
  Ce_z p a 0 0 (S0 >> const S0).
Proof.
  intros p a. unfold Ce_z. cbn [lpow Str_app].
  do 2 f_equal. cbn [Streams.tl]. apply const_unfold.
Qed.

Lemma Boot_to_Cd4 :
  c0 -->* Cd_z 4 3 28 (S0 >> [S1; S0]^^E0 *> const S0).
Proof.
  destruct W3_3_even as [Hw_eq [Hw_ge _]].
  eapply evstep_trans; [exact Boot_139 |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  rewrite const_unfold at 1.
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  rewrite I_const0_to_Ce.
  rewrite Hw_eq at 1.
  eapply evstep_trans; [apply progress_evstep, (Phase1_reload 0 (W 3 3 / 2) (const S0)) |].
  rewrite <- const_unfold.
  replace (S (W 3 3 / 2)) with (S (S (S (S E0)))) by (unfold E0; lia).
  eapply evstep_trans; [apply progress_evstep, (C_REL 1 0 (S (S (S E0))) (const S0)) |].
  rewrite W1_3_val.
  eapply evstep_trans; [apply progress_evstep, (D_STEP 1 14 (S E0) (const S0)) |].
  change (14 + 4) with 18. rewrite W1_18_val.
  change 59 with (2 * 29 + 1).
  eapply evstep_trans; [apply progress_evstep, (C_REL 0 29 E0 (const S0)) |].
  rewrite W0_3_val.
  unfold Ce_z. cbn [Nat.add lpow Str_app].
  apply Boot_bridge_72.
Qed.

Lemma Boot_to_pa_init :
  c0 -->* Ce_z (fst pa_init) (snd pa_init) 0 0 (S0 >> [S1; S0]^^E0 *> const S0) /\
  7 <= fst pa_init /\
  is_W_even (snd pa_init).
Proof.
  destruct W3_3_even as [Hw_eq [Hw_ge _]].
  set (zE := (S0 >> [S1; S0]^^E0 *> const S0)).
  assert (Hpb_odd : is_W_odd (snd pb_boot)).
  { unfold pb_boot. cbn [snd]. rewrite W2_1_val.
    apply W_ge3_even; [lia | lia | reflexivity]. }
  assert (Hpb_ge : 5 <= fst pb_boot) by (unfold pb_boot; cbn [fst]; lia).
  destruct (Kd_loop 8 1 zE pb_boot Hpb_ge Hpb_odd) as [Hkd [Hkd_p Hkd_odd]].
  destruct (Kc_full_all 0 zE (Kd_iter 8 pb_boot) ltac:(lia) Hkd_odd) as [Hkc [Hkc_p Hkc_ev]].
  unfold pa_init.
  split; [| split; [lia | exact Hkc_ev]].
  eapply evstep_trans; [exact Boot_to_Cd4 |].
  fold zE.
  eapply evstep_trans; [apply progress_evstep, (C_REL 3 1 27 zE) |].
  eapply evstep_trans; [apply progress_evstep, (Kc_step 0 27 zE (3, W 3 3) ltac:(cbn; lia) Hw_eq) |].
  rewrite Kc_unfold. cbn [fst snd]. replace (3 - 1) with 2 by lia.
  eapply evstep_trans; [apply progress_evstep, (D_STEP (3 + W 3 3 / 2) (W 2 1) 25 zE) |].
  change (Cd_z (3 + W 3 3 / 2) (W (3 + W 3 3 / 2) (W 2 1 + 4)) 25 zE)
    with (Cd_z (fst pb_boot) (snd pb_boot) (3 * 8 + 1) zE).
  eapply evstep_trans; [exact Hkd |].
  apply progress_evstep, Hkc.
Qed.

Lemma run_to_end :
  c0 -->* c_end (fst pa_final) (snd pa_final).
Proof.
  destruct Boot_to_pa_init as [Hboot [Hp0 Ha0]].
  destruct (Outer_loop E0 pa_init Hp0 Ha0) as [Hloop [HpE HaE]].
  destruct (Phase1_exec (const S0) (iter E0 Outer_step pa_init) HpE HaE) as [Hp1 _].
  unfold pa_final.
  eapply evstep_trans; [exact Hboot |].
  eapply evstep_trans; [exact Hloop |].
  eapply evstep_trans; [apply progress_evstep, Hp1 |].
  apply progress_evstep, HALT_E0.
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run_to_end) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply c_end_halted.
Qed.

(** ** Fast-growing hierarchy up to omega + 3 and Sigma(14) lower bound *)

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | O => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.
Definition f_omega1 (n : nat) : nat := iter n f_omega n.
Definition f_omega2 (n : nat) : nat := iter n f_omega1 n.
Definition f_omega3 (n : nat) : nat := iter n f_omega2 n.

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

Lemma ones_c_end : forall p a, ones (c_end p a) (p + a + 6).
Proof.
  intros p a.
  eexists. exists ([S1]^^(a + 6) ++ [S0; S1]^^p), (@nil Sym), S0.
  split.
  - unfold c_end. rewrite !Str_app_assoc. cbn [Str_app Streams.hd Streams.tl]. reflexivity.
  - rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

Theorem score_exact :
  exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa_final + snd pa_final + 6).
Proof.
  exists (c_end (fst pa_final) (snd pa_final)).
  split; [exact run_to_end |].
  split; [apply c_end_halted |].
  apply ones_c_end.
Qed.

(** ** Hierarchy monotonicity and W lower bounds *)

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

Lemma f_omega1_ge2 : forall n, 1 <= n -> 2 <= f_omega1 n.
Proof.
  intros [| n'] Hn; [lia |].
  unfold f_omega1. cbn [iter].
  pose proof (iter_ge f_omega f_omega_id n' (S n')).
  pose proof (f_omega_dbl (iter n' f_omega (S n')) ltac:(lia)). lia.
Qed.

Lemma f_omega1_mono : forall a b, a <= b -> f_omega1 a <= f_omega1 b.
Proof.
  intros a b Hab. unfold f_omega1.
  transitivity (iter a f_omega b).
  - apply iter_mono_x; [apply f_omega_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega_id | exact Hab].
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
    + intros n z Hz. rewrite W_1, f1. simpl (2 ^ (0 + 1)) in *. lia.
    + rewrite W_1. simpl. lia.
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
  unfold f_omega.
  set (P := 2 ^ (m + 1)) in *; set (F1 := f (S m) (S m)) in *;
  set (F2 := f (S m) (2 * (m + 1))) in *; set (Z := W (S m) (W (S m) (W (S m) 2))) in *.
  nia.
Qed.

Lemma W_omega_bound : forall m,
  4 * f_omega (S m) + 4 <= W (S (S (S m))) 1.
Proof.
  intros m.
  rewrite W_S. cbn [iter].
  pose proof (W_omega_bound0 m) as H0.
  set (Z := W (S (S m)) 2) in *; clearbody Z.
  rewrite W_S.
  pose proof (iter_lin3 (W (S m)) (W_grow (S m)) (S Z) 2).
  lia.
Qed.

Lemma f_3_unfold : forall k, f (S k) 3 = f k (f k (f k 3)).
Proof. intros k. rewrite f_S. reflexivity. Qed.

Opaque f.
Strategy opaque [f].

Lemma f_omega_3_eq : f_omega 3 = f 2 (f 2 (f 2 3)).
Proof. unfold f_omega. apply (f_3_unfold 2). Qed.

Opaque f_omega f_omega1 f_omega2 f_omega3.

Lemma E0_ge_f_omega_3 : f_omega 3 <= E0.
Proof.
  unfold E0.
  assert (HW3 : W 3 3 = W 2 (W 2 (W 2 (W 2 2)))).
  { rewrite W_S. cbn [iter]. reflexivity. }
  rewrite W2_2_val in HW3.
  destruct (W_bound_all 1) as [Hw2 _].
  simpl (2 ^ (1 + 1)) in Hw2.
  assert (H1 : 4 * f 2 3 <= W 2 119) by (apply Hw2; lia).
  assert (H2 : 4 * f 2 (f 2 3) <= W 2 (W 2 119)) by (apply Hw2; exact H1).
  assert (H3 : 4 * f 2 (f 2 (f 2 3)) <= W 2 (W 2 (W 2 119))) by (apply Hw2; exact H2).
  rewrite <- f_omega_3_eq, <- HW3 in H3.
  pose proof (f_omega_dbl 3 ltac:(lia)) as Hge6.
  set (F := f_omega 3) in *; set (X := W 3 3) in *.
  mods; lia.
Qed.

Opaque E0.

(** ** Domination across Kc, Kc_full, Kd_step, Kd_iter, Phase1, Phase2, and Outer_loop *)

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
  set (z := f_omega (S m)) in *; set (w := W (S (S (S m))) 1) in *.
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

Definition ok_pa (n : nat) (pa : nat * nat) : Prop :=
  n + 6 <= fst pa /\ 6 * n + 8 <= snd pa.

Lemma ok_pb_mono : forall m n pb,
  m <= n -> ok_pb n pb -> ok_pb m pb.
Proof. intros m n pb Hmn [H1 H2]. split; lia. Qed.

Lemma ok_pa_mono : forall m n pa,
  m <= n -> ok_pa n pa -> ok_pa m pa.
Proof. intros m n pa Hmn [H1 H2]. split; lia. Qed.

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
  pose proof (f_omega1_ge2 n Hn) as Hge2.
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

Lemma N_bounce_pb_dom : forall n p,
  1 <= n -> n + 4 <= p -> ok_pb n (N_bounce_pb p).
Proof.
  intros n p Hn Hp.
  Transparent N_bounce_pb. unfold N_bounce_pb, ok_pb. Opaque N_bounce_pb.
  cbn [fst snd].
  destruct p as [| [| [| [| m]]]]; try lia.
  pose proof (W_omega_bound0 (S m)) as Hw0.
  pose proof (f_omega_dbl (S (S m)) ltac:(lia)) as Hdbl.
  assert (Hw3 : W (S (S (S m))) 2 <= W (S (S (S (S m)))) 3).
  { rewrite (W_S (S (S (S m))) 3). cbn [iter].
    pose proof (W_grow (S (S (S m))) (W (S (S (S m))) 2)) as Hg2.
    pose proof (W_grow (S (S (S m))) (W (S (S (S m))) (W (S (S (S m))) 2))) as Hg3.
    pose proof (W_grow (S (S (S m))) (W (S (S (S m))) (W (S (S (S m))) (W (S (S (S m))) 2)))) as Hg4.
    lia. }
  pose proof (W_grow (S (S (S (S m)))) (W (S (S (S (S m)))) 3 + 4)) as Hwg.
  split; lia.
Qed.

Lemma Phase1_dom : forall n pa,
  1 <= n -> ok_pa n pa -> ok_pa (f_omega2 n) (Phase1_pa pa).
Proof.
  intros n [p a] Hn [Hp Ha]. cbn [fst snd] in *.
  Transparent Phase1_pa. unfold Phase1_pa. Opaque Phase1_pa.
  pose proof (N_bounce_pb_dom n (p - 2) Hn ltac:(lia)) as Hnb.
  assert (Hm : n <= (a / 2 + 2) / 3 - 2) by (mods; lia).
  set (m := (a / 2 + 2) / 3 - 2) in *.
  pose proof (Kd_iter_dom m n (N_bounce_pb (p - 2)) Hn Hnb) as Hloop.
  assert (Hok2 : ok_pb (f_omega2 n) (Kd_iter m (N_bounce_pb (p - 2)))).
  { eapply ok_pb_mono; [| exact Hloop].
    Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    apply iter_mono_n; [apply f_omega1_id | exact Hm]. }
  assert (Hf2_pos : 1 <= f_omega2 n) by (pose proof (f_omega2_id n); lia).
  pose proof (Kc_full_dom (f_omega2 n) (Kd_iter m (N_bounce_pb (p - 2))) Hf2_pos Hok2) as Hkc.
  eapply ok_pa_mono; [apply f_omega1_id | exact Hkc].
Qed.

Lemma Phase2_dom : forall n pa1,
  1 <= n -> ok_pa n pa1 -> ok_pa (f_omega2 n) (Phase2_pa pa1).
Proof.
  intros n [p1 a1] Hn [Hp1 Ha1]. cbn [fst snd] in *.
  Transparent Phase2_pa. unfold Phase2_pa. Opaque Phase2_pa.
  pose proof (N_bounce_pb_dom n (p1 - 2) Hn ltac:(lia)) as Hnb.
  assert (Hm : n <= (a1 / 2 + 2) / 3 - 1) by (mods; lia).
  set (m := (a1 / 2 + 2) / 3 - 1) in *.
  pose proof (Kd_iter_dom m n (N_bounce_pb (p1 - 2)) Hn Hnb) as Hloop.
  assert (Hok2 : ok_pb (f_omega2 n) (Kd_iter m (N_bounce_pb (p1 - 2)))).
  { eapply ok_pb_mono; [| exact Hloop].
    Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    apply iter_mono_n; [apply f_omega1_id | exact Hm]. }
  assert (Hf2_pos : 1 <= f_omega2 n) by (pose proof (f_omega2_id n); lia).
  pose proof (Kc_full_dom (f_omega2 n) (Kd_iter m (N_bounce_pb (p1 - 2))) Hf2_pos Hok2) as Hkc.
  eapply ok_pa_mono; [apply f_omega1_id | exact Hkc].
Qed.

Lemma Outer_step_dom : forall n pa,
  1 <= n -> ok_pa n pa -> ok_pa (iter 2 f_omega2 n) (Outer_step pa).
Proof.
  intros n pa Hn Hok.
  rewrite Outer_step_unfold. cbn [iter].
  pose proof (Phase1_dom n pa Hn Hok) as H1.
  pose proof (f_omega2_id n) as Hid.
  apply Phase2_dom; [lia | exact H1].
Qed.

Lemma Outer_loop_dom : forall E n pa,
  1 <= n -> ok_pa n pa -> ok_pa (iter (2 * E) f_omega2 n) (iter E Outer_step pa).
Proof.
  induction E as [| E IHE]; intros n pa Hn Hok.
  - change (2 * 0) with 0. cbn [iter]. exact Hok.
  - replace (2 * S E) with (2 + 2 * E) by lia.
    rewrite iter_add. cbn [iter].
    pose proof (IHE n pa Hn Hok) as H1.
    pose proof (iter_ge f_omega2 f_omega2_id (2 * E) n) as Hge.
    exact (Outer_step_dom (iter (2 * E) f_omega2 n) (iter E Outer_step pa) ltac:(lia) H1).
Qed.

Lemma pa_init_dom : ok_pa (f_omega2 3) pa_init.
Proof.
  unfold pa_init.
  assert (Hpb0 : ok_pb 3 pb_boot).
  { unfold pb_boot, ok_pb. cbn [fst snd].
    destruct W3_3_even as [_ [Hw_ge _]].
    rewrite W2_1_val. change (38 + 4) with 42.
    pose proof (W_grow (3 + W 3 3 / 2) 42). lia. }
  pose proof (Kd_iter_dom 8 3 pb_boot ltac:(lia) Hpb0) as Hkd.
  assert (Hok2 : ok_pb (f_omega2 3) (Kd_iter 8 pb_boot)).
  { eapply ok_pb_mono; [| exact Hkd].
    Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    apply iter_mono_n; [apply f_omega1_id | lia]. }
  assert (Hf2 : 1 <= f_omega2 3) by (pose proof (f_omega2_id 3); lia).
  pose proof (Kc_full_dom (f_omega2 3) (Kd_iter 8 pb_boot) Hf2 Hok2) as Hkc.
  eapply ok_pa_mono; [apply f_omega1_id | exact Hkc].
Qed.

Lemma pa_final_dom_iter : ok_pa (iter (S (2 * E0)) f_omega2 (f_omega2 3)) pa_final.
Proof.
  unfold pa_final. cbn [iter].
  assert (Hf2 : 1 <= f_omega2 3) by (pose proof (f_omega2_id 3); lia).
  pose proof (Outer_loop_dom E0 (f_omega2 3) pa_init Hf2 pa_init_dom) as Hloop.
  pose proof (iter_ge f_omega2 f_omega2_id (2 * E0) (f_omega2 3)) as Hge.
  apply Phase1_dom; [lia | exact Hloop].
Qed.

Opaque pb_boot pa_init pa_final.

Lemma pa_final_dom_fw3 : ok_pa (f_omega3 (f_omega 3)) pa_final.
Proof.
  eapply ok_pa_mono; [| exact pa_final_dom_iter].
  pose proof E0_ge_f_omega_3 as HE.
  Transparent f_omega3. unfold f_omega3. Opaque f_omega3.
  replace (S (2 * E0)) with (f_omega 3 + (S (2 * E0) - f_omega 3)) by lia.
  rewrite iter_add.
  apply iter_mono_x; [apply f_omega2_mono |].
  pose proof (iter_ge f_omega2 f_omega2_id (S (2 * E0) - f_omega 3) (f_omega2 3)) as H1.
  (* Also bound E0 <= iter (S (2 * E0) - f_omega 3) f_omega2 (f_omega2 3): *)
  assert (Hf2_gt : forall a, 1 <= a -> a + 1 <= f_omega2 a).
  { intros a Ha. Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    destruct a as [| a']; [lia |]. cbn [iter].
    pose proof (iter_ge f_omega1 f_omega1_id a' (S a')) as Hg.
    Transparent f_omega1. unfold f_omega1 at 1. Opaque f_omega1.
    destruct (iter a' f_omega1 (S a')) as [| z'] eqn:Ez; [lia |].
    cbn [iter].
    pose proof (iter_ge f_omega f_omega_id z' (S z')).
    pose proof (f_omega_dbl (iter z' f_omega (S z')) ltac:(lia)). lia. }
  pose proof (f_omega2_id 3) as H3.
  pose proof (iter_lin1 f_omega2 Hf2_gt (S (2 * E0) - f_omega 3) (f_omega2 3) ltac:(lia)) as Hlin.
  lia.
Qed.

Lemma pa_final_dom_M14_31 : ok_pa (iter 31 f_omega2 (iter 2 f_omega 3)) pa_final.
Proof.
  eapply ok_pa_mono; [| exact pa_final_dom_iter].
  pose proof E0_ge_133 as HE133.
  assert (Hbase : iter 2 f_omega 3 <= f_omega2 3).
  { transitivity (f_omega1 3).
    - Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
      apply iter_mono_n; [apply f_omega_id | lia].
    - Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
      cbn [iter].
      pose proof (f_omega1_id 3) as H1.
      pose proof (f_omega1_id (f_omega1 3)) as H2.
      pose proof (f_omega1_id (f_omega1 (f_omega1 3))) as H3. lia. }
  transitivity (iter 31 f_omega2 (f_omega2 3)).
  - apply iter_mono_x; [apply f_omega2_mono | exact Hbase].
  - apply iter_mono_n; [apply f_omega2_id | lia].
Qed.

Lemma ok_pa_score_gt : forall B pa,
  ok_pa B pa -> fst pa + snd pa + 6 > B.
Proof. intros B [p a] [Hp Ha]. cbn [fst snd] in *. lia. Qed.

Theorem sigma_bound :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
  n > f_omega3 (f_omega 3).
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (fst pa_final + snd pa_final + 6).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  apply ok_pa_score_gt. exact pa_final_dom_fw3.
Qed.

Corollary beats_M14_31 :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
  n > iter 31 f_omega2 (iter 2 f_omega 3).
Proof.
  destruct score_exact as [c [H1 [H2 H3]]].
  exists c, (fst pa_final + snd pa_final + 6).
  split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  apply ok_pa_score_gt. exact pa_final_dom_M14_31.
Qed.

(** ** Strict first-visit canonical TNF isomorphism (tm_tnf) *)

(* Strict first-visit canonical TNF string:
   1RB1RA_1RC1RJ_1RD0LK_0LE1RI_---0LF_1LG1LE_1LH0RE_0RD1LH_1RL0RA_0LH1LN_1LM1LC_1RE0LM_1LN1LM_1RA0LM *)
Definition tm_tnf : TM := fun '(q, s) =>
  match q, s with
  | A, S0 => Some (S1, TM.R, B) | A, S1 => Some (S1, TM.R, A)
  | B, S0 => Some (S1, TM.R, C) | B, S1 => Some (S1, TM.R, J)
  | C, S0 => Some (S1, TM.R, D) | C, S1 => Some (S0, TM.L, K)
  | D, S0 => Some (S0, TM.L, E) | D, S1 => Some (S1, TM.R, I)
  | E, S0 => None               | E, S1 => Some (S0, TM.L, F)
  | F, S0 => Some (S1, TM.L, G) | F, S1 => Some (S1, TM.L, E)
  | G, S0 => Some (S1, TM.L, H) | G, S1 => Some (S0, TM.R, E)
  | H, S0 => Some (S0, TM.R, D) | H, S1 => Some (S1, TM.L, H)
  | I, S0 => Some (S1, TM.R, L) | I, S1 => Some (S0, TM.R, A)
  | J, S0 => Some (S0, TM.L, H) | J, S1 => Some (S1, TM.L, N)
  | K, S0 => Some (S1, TM.L, M) | K, S1 => Some (S1, TM.L, C)
  | L, S0 => Some (S1, TM.R, E) | L, S1 => Some (S0, TM.L, M)
  | M, S0 => Some (S1, TM.L, N) | M, S1 => Some (S1, TM.L, M)
  | N, S0 => Some (S1, TM.R, A) | N, S1 => Some (S0, TM.L, M)
  end.

Definition perm_f (q : Q) : Q :=
  match q with
  | A => A | B => B | C => J | D => H | E => D | F => I | G => N
  | H => M | I => C | J => K | K => E | L => F | M => L | N => G
  end.

Lemma tm_perm_tnf : Perm tm tm_tnf perm_f.
Proof.
  split.
  - intros [] [] H; inversion H; reflexivity.
  - intros [] [] s' d q' H; inversion H; subst; reflexivity.
Qed.

Lemma perm_evstep : forall tm1 tm2 g,
  Perm tm1 tm2 g -> forall c c',
  c -[ tm1 ]->* c' ->
  (g (fst c), snd c) -[ tm2 ]->* (g (fst c'), snd c').
Proof.
  intros tm1 tm2 g HP c c' H.
  induction H as [[q t] | [q t] [q1 t1] [q2 t2] H1 _ IH]; cbn [fst snd] in *.
  - apply evstep_refl.
  - eapply evstep_step; [eapply perm_step; eauto | exact IH].
Qed.

Theorem halt_tnf : halts tm_tnf c0.
Proof.
  change c0 with (perm_f A;; tape0).
  exact (perm_halts tm tm_tnf perm_f A tape0 tm_perm_tnf halt).
Qed.

Theorem sigma_bound_tnf :
  exists c n, c0 -[ tm_tnf ]->* c /\ halted tm_tnf c /\ ones c n /\
  n > f_omega3 (f_omega 3).
Proof.
  destruct sigma_bound as [[q t] [n [Hrun [Hhalt [Hones Hgt]]]]].
  exists (perm_f q, t), n.
  split.
  - exact (perm_evstep tm tm_tnf perm_f tm_perm_tnf c0 (q, t) Hrun).
  - split.
    + exact (perm_halted tm tm_tnf perm_f q t tm_perm_tnf Hhalt).
    + split; [| exact Hgt].
      destruct Hones as [q' [L [R [s [Heq Hn]]]]].
      inversion Heq; subst.
      exists (perm_f q'), L, R, s. auto.
Qed.

Corollary beats_M14_31_tnf :
  exists c n, c0 -[ tm_tnf ]->* c /\ halted tm_tnf c /\ ones c n /\
  n > iter 31 f_omega2 (iter 2 f_omega 3).
Proof.
  destruct beats_M14_31 as [[q t] [n [Hrun [Hhalt [Hones Hgt]]]]].
  exists (perm_f q, t), n.
  split.
  - exact (perm_evstep tm tm_tnf perm_f tm_perm_tnf c0 (q, t) Hrun).
  - split.
    + exact (perm_halted tm tm_tnf perm_f q t tm_perm_tnf Hhalt).
    + split; [| exact Hgt].
      destruct Hones as [q' [L [R [s [Heq Hn]]]]].
      inversion Heq; subst.
      exists (perm_f q'), L, R, s. auto.
Qed.

Print Assumptions halt.
Print Assumptions sigma_bound.
Print Assumptions beats_M14_31.
Print Assumptions halt_tnf.
Print Assumptions sigma_bound_tnf.
Print Assumptions beats_M14_31_tnf.
