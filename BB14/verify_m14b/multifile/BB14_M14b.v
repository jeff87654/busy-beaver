(** * The 14-state machine M14b achieves > f_(omega+2)^9(f_(omega+1)^2(3)) and halts *)

From BB8 Require Import Individual142.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LN0LL_0LH1LK_---0LH_0RJ0LI *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, B)  | A, 1 => Some (1, TM.R, A)
  | B, 0 => Some (1, TM.R, I)  | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)  | C, 1 => Some (1, TM.L, G)
  | D, 0 => Some (0, TM.R, E)  | D, 1 => Some (1, TM.L, D)
  | E, 0 => Some (1, TM.L, K)  | E, 1 => Some (1, TM.R, F)
  | F, 0 => Some (1, TM.R, M)  | F, 1 => Some (0, TM.R, A)
  | G, 0 => Some (1, TM.R, A)  | G, 1 => Some (0, TM.L, H)
  | H, 0 => Some (1, TM.L, G)  | H, 1 => Some (1, TM.L, H)
  | I, 0 => Some (1, TM.R, E)  | I, 1 => Some (0, TM.L, J)
  | J, 0 => Some (1, TM.L, H)  | J, 1 => Some (1, TM.L, I)
  | K, 0 => Some (0, TM.L, N)  | K, 1 => Some (0, TM.L, L)
  | L, 0 => Some (0, TM.L, H)  | L, 1 => Some (1, TM.L, K)
  | M, 0 => None               | M, 1 => Some (0, TM.L, H)
  | N, 0 => Some (0, TM.R, J)  | N, 1 => Some (0, TM.L, I)
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

Lemma tail_10_const : forall n,
  [1; 0]^^n *> 1 >> const 0 = [1; 0]^^(n + 1) *> const 0.
Proof.
  intros n. rewrite lpow_add, Str_app_assoc. cbn [lpow Str_app].
  rewrite const_unfold at 1. reflexivity.
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

Lemma cr_KN_0101_1010 : forall n l r, [0; 1; 0; 1]^^n *> l <{{K}} r -->* l <{{K}} [1; 0; 1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_KN_even : forall q l r,
  ([0; 1]^^(2 * q) *> l) <{{K}} r -->* l <{{K}} ([1; 0]^^(2 * q) *> r).
Proof.
  intros q l r.
  rewrite (lpow_double [0; 1] q), (lpow_double [1; 0] q).
  apply cr_KN_0101_1010.
Qed.

(** ** Configurations and inner cascade rules *)

Definition Ca (j b : nat) (z : side) : Q * tape :=
  ([1]^^b *> [0; 1]^^j *> const 0) {{A}}> (0 >> z).

Definition Ch (j b : nat) (z : side) : Q * tape :=
  ([0; 1]^^j *> const 0) <{{H}} (1 >> [1]^^b *> 0 >> z).

Definition Ce (p a c d : nat) : Q * tape :=
  ([1]^^(a + 2) *> [0; 1]^^p *> const 0) {{I}}> ([1; 0]^^c *> 0 >> [1; 0]^^d *> const 0).

Definition Cd (p b d : nat) : Q * tape :=
  ([1]^^(b + 2) *> [0; 1]^^p *> const 0) {{I}}> ([1; 0]^^d *> const 0).

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

Lemma D_REL_aux : forall p' k,
  Ce (S p') (2 * k) 0 0 -->+ Ch p' 0 (0 >> [1; 0]^^(k + 2) *> const 0).
Proof.
  intros p' k. unfold Ce, Ch.
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_KL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma C_REL_aux : forall p' m d,
  Cd (S p') (2 * m + 1) (S d) -->+ Ch p' 3 (0 >> [1; 0]^^m *> 0 >> [1; 0]^^d *> const 0).
Proof.
  intros p' m d. unfold Cd, Ch.
  replace (2 * m + 1 + 2)%nat with (1 + (2 * m + 2))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] m). cbn [app].
  start_progress.
  follow cr_IL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma D_STEP_aux : forall p a d,
  Ce p a 0 (S (S d)) -->+ Ch p (a + 4) (0 >> [1; 0]^^d *> const 0).
Proof.
  intros p a d. unfold Ce, Ch. norm_nat.
  start_progress.
  follow cr_HL_1_1.
  finish_norm.
Qed.

(** ** K-reload step 1, step 2 (odd & even p), and Halting step *)

Lemma K_REL_step1 : forall p m,
  Cd p (2 * m + 1) 0 -->+ ([0; 1]^^p *> const 0) <{{K}} ([1; 0]^^(m + 2) *> 1 >> const 0).
Proof.
  intros p m. unfold Cd.
  replace (2 * m + 1 + 2)%nat with (1 + (2 * m + 2))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] m). cbn [app].
  start_progress.
  follow cr_KL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma K_REL_step2_odd : forall q d,
  ([0; 1]^^(2 * q + 1) *> const 0) <{{K}} ([1; 0]^^(S d) *> const 0) -->+ Cd 2 3 (2 * q + 1 + d).
Proof.
  intros q d. unfold Cd.
  rewrite lpow_add, Str_app_assoc.
  eapply evstep_progress_trans; [apply cr_KN_even |].
  rewrite <- Str_app_assoc, <- lpow_add.
  replace (2 * q + S d)%nat with (S (2 * q + d))%nat by lia.
  replace (2 * q + 1 + d)%nat with (S (2 * q + d))%nat by lia.
  cbn [lpow Str_app].
  start_progress; finish_norm.
Qed.

Lemma K_REL_step2_even : forall q d,
  ([0; 1]^^(2 * q) *> const 0) <{{K}} ([1; 0]^^(S d) *> const 0) -->+ Ca 0 4 ([1; 0]^^(2 * q + d) *> const 0).
Proof.
  intros q d. unfold Ca.
  eapply evstep_progress_trans; [apply cr_KN_even |].
  rewrite <- Str_app_assoc, <- lpow_add.
  replace (2 * q + S d)%nat with (S (2 * q + d))%nat by lia.
  cbn [lpow Str_app].
  start_progress; finish_norm.
Qed.

Definition c_end (p a : nat) : Q * tape :=
  ([1]^^(a + 5) *> [0; 1]^^p *> const 0) {{M}}> const 0.

Lemma HALT_step : forall p a,
  Ce p a 0 1 -->+ c_end p a.
Proof.
  intros p a. unfold Ce, c_end. cbn [lpow Str_app].
  start_progress. finish_norm.
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

Lemma CE_EVEN : forall p' k c d,
  Ce (S p') (2 * k) (S c) d -->+ Ce (p' + S k) (W p' 1) c d.
Proof.
  intros p' k c d. unfold Ce.
  cbn [lpow Str_app].
  eapply progress_evstep_trans; [apply E_EVEN |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  follow (CA_SH_iter (S k) p' (W p' 1) (0 >> [1; 0]^^c *> 0 >> [1; 0]^^d *> const 0)%sym).
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma D_REL : forall p' k,
  Ce (S p') (2 * k) 0 0 -->+ Cd p' (W p' 0) (k + 2).
Proof.
  intros p' k. unfold Cd.
  eapply progress_evstep_trans; [apply D_REL_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma C_REL : forall p' m d,
  Cd (S p') (2 * m + 1) (S d) -->+ Ce p' (W p' 3) m d.
Proof.
  intros p' m d. unfold Ce.
  eapply progress_evstep_trans; [apply C_REL_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma D_STEP : forall p a d,
  Ce p a 0 (S (S d)) -->+ Cd p (W p (a + 4)) d.
Proof.
  intros p a d. unfold Cd.
  eapply progress_evstep_trans; [apply D_STEP_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma K_REL_step3 : forall d',
  Cd 2 3 (S (S (S d'))) -->+ Cd 8 (W 8 8) d'.
Proof.
  intros d'.
  eapply progress_evstep_trans; [apply (C_REL 1 1 (S (S d'))) |].
  change (W 1 3) with 14.
  eapply evstep_trans; [apply progress_evstep, (CE_EVEN 0 7 0 (S (S d'))) |].
  change (0 + S 7)%nat with 8%nat. change (W 0 1) with 4.
  apply progress_evstep, D_STEP.
Qed.

Lemma K_REL_odd : forall q m,
  Cd (2 * q + 1) (2 * m + 1) 0 -->+ Cd 8 (W 8 8) (2 * q + 1 + m - 1).
Proof.
  intros q m.
  eapply progress_evstep_trans; [apply K_REL_step1 |].
  rewrite tail_10_const.
  replace (m + 2 + 1) with (S (m + 2)) by lia.
  eapply evstep_trans; [apply progress_evstep, K_REL_step2_odd |].
  replace (2 * q + 1 + (m + 2)) with (S (S (S (2 * q + 1 + m - 1)))) by lia.
  apply progress_evstep, K_REL_step3.
Qed.

Lemma K_REL_even : forall q m,
  Cd (2 * q) (2 * m + 1) 0 -->+ Ce (2 * q + m + 2) 4 0 0.
Proof.
  intros q m. unfold Ce.
  eapply progress_evstep_trans; [apply K_REL_step1 |].
  rewrite tail_10_const.
  replace (m + 2 + 1) with (S (m + 2)) by lia.
  eapply evstep_trans; [apply progress_evstep, K_REL_step2_even |].
  follow (CA_SH_iter (2 * q + (m + 2)) 0 4 (const 0%sym)).
  eapply evstep_trans; [rewrite const_unfold at 1; apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

(** ** Initial 352 steps from blank tape *)

Lemma init_53 : c0 -->* Cd 2 3 1.
Proof.
  unfold Cd. cbn [lpow Str_app].
  do 53 step. finish_norm.
Qed.

Lemma init_352 : c0 -->* Ce 8 4 0 0.
Proof.
  follow init_53.
  eapply evstep_trans; [apply progress_evstep, (C_REL 1 1 0) |].
  change (W 1 3) with 14.
  eapply evstep_trans; [apply progress_evstep, (CE_EVEN 0 7 0 0) |].
  change (0 + S 7) with 8. change (W 0 1) with 4.
  apply evstep_refl.
Qed.

(** ** Growth, parity, and 3-adic mod-972 invariants *)

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
  intros g Hg. induction n; intros; simpl. - lia.
  - specialize (IHn x). specialize (Hg (iter n g x)). lia.
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
  - rewrite W_S.
    pose proof (iter_lin3 (W j) IHj (S b) 2). lia.
Qed.

Lemma W_par : forall j b, W j b mod 2 = (b + 1) mod 2.
Proof.
  induction j as [| j IHj]; intros b.
  - rewrite W_0. mods; lia.
  - rewrite W_S. rewrite (iter_par_nat (W j) IHj). mods; lia.
Qed.

Lemma iter_W0 : forall n x, iter n (W 0) x = x + 3 * n.
Proof.
  induction n as [| n IHn]; intros x; cbn [iter].
  - lia.
  - rewrite W_0, IHn. lia.
Qed.

Lemma W_1 : forall b, W 1 b = 3 * b + 5.
Proof.
  intros b. rewrite W_S, iter_W0. lia.
Qed.

Lemma iter_W1_mod972 : forall b,
  iter (S (S (S b))) (W 1) 2 mod 972 = (if S (S b) mod 2 =? 0 then 119 else 362).
Proof.
  induction b as [| b IHb].
  - reflexivity.
  - change (iter (S (S (S (S b)))) (W 1) 2) with (W 1 (iter (S (S (S b))) (W 1) 2)).
    rewrite W_1.
    destruct (S (S b) mod 2 =? 0) eqn:Heq1;
      [apply Nat.eqb_eq in Heq1 | apply Nat.eqb_neq in Heq1];
    (destruct (S (S (S b)) mod 2 =? 0) eqn:Heq2;
      [apply Nat.eqb_eq in Heq2 | apply Nat.eqb_neq in Heq2]);
    mods; lia.
Qed.

Lemma W_SS_SS_mod972 : forall j b,
  W (S (S j)) (S (S b)) mod 972 = (if S (S b) mod 2 =? 0 then 119 else 362).
Proof.
  induction j as [| j IHj]; intros b.
  - rewrite W_S. apply iter_W1_mod972.
  - change (W (S (S (S j))) (S (S b))) with (W (S (S j)) (iter (S (S b)) (W (S (S j))) 2)).
    pose proof (W_grow (S (S j)) (iter (S b) (W (S (S j))) 2)) as Hgrow.
    pose proof (iter_par_nat (W (S (S j))) (W_par (S (S j))) (S (S b)) 2) as Hpar.
    change (iter (S (S b)) (W (S (S j))) 2) with (W (S (S j)) (iter (S b) (W (S (S j))) 2)) in *.
    destruct (W (S (S j)) (iter (S b) (W (S (S j))) 2)) as [| [| y']] eqn:Hy; [lia | lia |].
    rewrite (IHj y').
    replace (S (S y') mod 2) with (S (S b) mod 2) by (mods; lia).
    reflexivity.
Qed.

Lemma W_SSS_mod972 : forall j b,
  W (S (S (S j))) b mod 972 = (if b mod 2 =? 0 then 119 else 362).
Proof.
  intros j [| [| b']].
  - change (W (S (S (S j))) 0) with (W (S (S j)) 2).
    apply (W_SS_SS_mod972 j 0).
  - change (W (S (S (S j))) 1) with (W (S (S j)) (W (S (S j)) 2)).
    pose proof (W_grow (S (S j)) 2) as Hgrow.
    pose proof (W_par (S (S j)) 2) as Hpar.
    destruct (W (S (S j)) 2) as [| [| y']] eqn:Hy; [lia | lia |].
    rewrite (W_SS_SS_mod972 j y').
    assert (Hneq : S (S y') mod 2 =? 0 = false) by (apply Nat.eqb_neq; mods; lia).
    rewrite Hneq. reflexivity.
  - apply (W_SS_SS_mod972 (S j) b').
Qed.

Lemma W_ge3_even_mod972 : forall p b,
  3 <= p -> b mod 2 = 0 -> W p b mod 972 = 119.
Proof.
  intros [| [| [| j]]] b Hp Hev; try lia.
  rewrite W_SSS_mod972.
  apply Nat.eqb_eq in Hev. rewrite Hev. reflexivity.
Qed.

Lemma W_ge3_odd_mod972 : forall p b,
  3 <= p -> b mod 2 = 1 -> W p b mod 972 = 362.
Proof.
  intros [| [| [| j]]] b Hp Hodd; try lia.
  rewrite W_SSS_mod972.
  assert (Hneq : b mod 2 =? 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hneq. reflexivity.
Qed.

Opaque W.

(** ** Macro-step functions Kc, Kc_full, Kd_step, Kd_iter, D_reload, D_round, K_odd_reload, K_even_reload *)

Lemma mod2_even : forall a, a mod 2 = 0 -> a = 2 * (a / 2).
Proof.
  intros a Ha. pose proof (Nat.div_mod_eq a 2). lia.
Qed.

Lemma mod2_odd : forall a, a mod 2 = 1 -> a = 2 * (a / 2) + 1.
Proof.
  intros a Ha. pose proof (Nat.div_mod_eq a 2). lia.
Qed.

Lemma mod_factor : forall x k m,
  (x mod (k * m)) mod k = x mod k.
Proof.
  intros x k m.
  pose proof (Nat.div_mod_eq x (k * m)) as Hdm.
  replace x with (x mod (k * m) + (m * (x / (k * m))) * k) at 2 by lia.
  rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma pred_mod : forall x k c,
  x mod k = c -> 1 <= c -> (x - 1) mod k = (c - 1) mod k.
Proof.
  intros x k c Hx Hc.
  pose proof (Nat.div_mod_eq x k) as Hdm. rewrite Hx in Hdm.
  replace (x - 1) with ((c - 1) + (x / k) * k) by lia.
  rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma mod972_362_props : forall a,
  a mod 972 = 362 ->
  2 <= a /\ a mod 2 = 0 /\
  1 <= a / 2 /\
  (a / 2) mod 162 = 19 /\
  (a / 6 + 1) mod 162 = 61 /\
  a / 2 + 2 = 3 * (a / 6 + 1) + 0.
Proof.
  intros a Ha.
  pose proof (Nat.div_mod_eq a 972) as Hdm. rewrite Ha in Hdm.
  set (q := a / 972) in *. clearbody q. clear Ha.
  assert (Ha2 : a / 2 = 19 + (3 * q + 1) * 162).
  { replace a with (362 + (486 * q) * 2) by lia.
    rewrite Nat.div_add by lia. change (362 / 2) with 181. lia. }
  assert (Ha6 : a / 6 + 1 = 61 + (q * 1) * 162).
  { replace a with (362 + (162 * q) * 6) by lia.
    rewrite Nat.div_add by lia. change (362 / 6) with 60. lia. }
  assert (Hev : a mod 2 = 0).
  { replace a with (0 + (486 * q + 181) * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  split; [lia | split; [exact Hev | split; [lia | split; [| split; [| lia]]]]].
  - rewrite Ha2, Nat.Div0.mod_add. reflexivity.
  - rewrite Ha6, Nat.Div0.mod_add. reflexivity.
Qed.

Lemma mod972_119_props : forall b,
  b mod 972 = 119 ->
  b = 2 * (b / 2) + 1 /\
  59 <= b / 2 /\
  (b / 2) mod 162 = 59.
Proof.
  intros b Hb.
  pose proof (Nat.div_mod_eq b 972) as Hdm. rewrite Hb in Hdm.
  set (q := b / 972) in *. clearbody q. clear Hb.
  assert (Hb2 : b / 2 = 59 + (3 * q) * 162).
  { replace b with (119 + (486 * q) * 2) by lia.
    rewrite Nat.div_add by lia. change (119 / 2) with 59. lia. }
  split; [lia | split; [lia |]].
  rewrite Hb2, Nat.Div0.mod_add. reflexivity.
Qed.

Lemma div3_props : forall d k c,
  k <> 0 -> d mod (3 * k) = c ->
  d = 3 * ((d - c mod 3) / 3) + c mod 3 /\
  ((d - c mod 3) / 3) mod k = (c / 3) mod k.
Proof.
  intros d k c Hk Hd.
  pose proof (Nat.div_mod_eq d (3 * k)) as Hdm.
  assert (Hc : c < 3 * k) by (rewrite <- Hd; apply Nat.mod_upper_bound; lia).
  rewrite Hd in Hdm.
  set (q := d / (3 * k)) in *. clearbody q. clear Hd.
  pose proof (Nat.div_mod_eq c 3) as Hcm.
  assert (Hcr : c mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
  assert (Hdiv : (d - c mod 3) / 3 = c / 3 + q * k).
  { replace (d - c mod 3) with ((c / 3 + q * k) * 3) by lia.
    apply Nat.div_mul. lia. }
  split; [lia |].
  rewrite Hdiv, Nat.Div0.mod_add. reflexivity.
Qed.

Definition Kc (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  (p + a / 2, W (p - 1) 1).

Lemma Kc_step : forall c d pa,
  1 <= fst pa -> snd pa mod 2 = 0 ->
  Ce (fst pa) (snd pa) (S c) d -->+ Ce (fst (Kc pa)) (snd (Kc pa)) c d.
Proof.
  intros c d [p a] Hp Hev. cbn [fst snd Kc] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  pose proof (mod2_even a Hev) as Ha.
  replace (S p' + a / 2) with (p' + S (a / 2)) by lia.
  rewrite Ha at 1.
  apply CE_EVEN.
Qed.

Lemma Kc_props_mod : forall pa,
  4 <= fst pa -> snd pa mod 972 = 362 ->
  fst pa + 1 <= fst (Kc pa) /\
  fst (Kc pa) mod 162 = (fst pa + 19) mod 162 /\
  snd (Kc pa) mod 972 = 362.
Proof.
  intros [p a] Hp Ha. cbn [fst snd Kc] in *.
  assert (Hm : W (p - 1) 1 mod 972 = 362) by (apply W_ge3_odd_mod972; [lia | reflexivity]).
  destruct (mod972_362_props a Ha) as [_ [_ [Ha_ge [Ha_mod _]]]].
  split; [lia | split; [| exact Hm]].
  rewrite <- Nat.Div0.add_mod_idemp_r, Ha_mod. reflexivity.
Qed.

Lemma Kc_loop_mod : forall c d pa,
  4 <= fst pa -> snd pa mod 972 = 362 ->
  Ce (fst pa) (snd pa) c d -->* Ce (fst (iter c Kc pa)) (snd (iter c Kc pa)) 0 d /\
  fst pa + c <= fst (iter c Kc pa) /\
  fst (iter c Kc pa) mod 162 = (fst pa + 19 * c) mod 162 /\
  snd (iter c Kc pa) mod 972 = 362.
Proof.
  induction c as [| c IHc]; intros d pa Hp Ha.
  - cbn [iter]. split; [finish | split; [lia | split; [f_equal; lia | exact Ha]]].
  - rewrite iter_S'.
    destruct (mod972_362_props (snd pa) Ha) as [_ [Hev _]].
    destruct (Kc_props_mod pa Hp Ha) as [Hp1 [Hm162 Ha1]].
    destruct (IHc d (Kc pa) ltac:(lia) Ha1) as [Hrun [Hp2 [Hm162' Ha2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, (Kc_step c d pa ltac:(lia) Hev) | exact Hrun].
    + lia.
    + rewrite Hm162', <- Nat.Div0.add_mod_idemp_l, Hm162, Nat.Div0.add_mod_idemp_l.
      f_equal; lia.
    + exact Ha2.
Qed.

Definition Kc_full (pb : nat * nat) : nat * nat :=
  let '(p, b) := pb in
  iter (b / 2) Kc (p - 1, W (p - 1) 3).

Lemma Kc_full_all : forall d pb,
  5 <= fst pb -> snd pb mod 972 = 119 ->
  Cd (fst pb) (snd pb) (S d) -->+ Ce (fst (Kc_full pb)) (snd (Kc_full pb)) 0 d /\
  fst pb + 1 <= fst (Kc_full pb) /\
  fst (Kc_full pb) mod 162 = (fst pb + 148) mod 162 /\
  snd (Kc_full pb) mod 972 = 362.
Proof.
  intros d [p b] Hp Hb. cbn [fst snd Kc_full] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  destruct (mod972_119_props b Hb) as [Hb_eq [Hb_ge Hb_mod]].
  assert (Hw3 : W p' 3 mod 972 = 362) by (apply W_ge3_odd_mod972; [lia | reflexivity]).
  destruct (Kc_loop_mod (b / 2) d (p', W p' 3) ltac:(cbn; lia) Hw3)
    as [Hrun [Hp1 [Hm162 Ha1]]].
  cbn [fst snd] in *.
  split; [| split; [| split]].
  - rewrite Hb_eq at 1.
    eapply progress_evstep_trans; [apply C_REL | exact Hrun].
  - lia.
  - rewrite Hm162, <- Nat.Div0.add_mod_idemp_r, <- Nat.Div0.mul_mod_idemp_r, Hb_mod, Nat.Div0.add_mod_idemp_r.
    replace (p' + 19 * 59) with (S p' + 148 + 6 * 162) by lia.
    rewrite Nat.Div0.mod_add. reflexivity.
  - exact Ha1.
Qed.

Definition Kd_step (pb : nat * nat) : nat * nat :=
  let '(p', a') := Kc_full pb in
  (p', W p' (a' + 4)).

Lemma Kd_step_all : forall d pb,
  5 <= fst pb -> snd pb mod 972 = 119 ->
  Cd (fst pb) (snd pb) (S (S (S d))) -->+ Cd (fst (Kd_step pb)) (snd (Kd_step pb)) d /\
  fst pb + 1 <= fst (Kd_step pb) /\
  fst (Kd_step pb) mod 162 = (fst pb + 148) mod 162 /\
  snd (Kd_step pb) mod 972 = 119.
Proof.
  intros d pb Hp Hb.
  unfold Kd_step.
  destruct (Kc_full_all (S (S d)) pb Hp Hb) as [Hkc [Hp1 [Hm162 Ha1]]].
  set (pa' := Kc_full pb) in *.
  destruct pa' as [p' a']. cbn [fst snd] in *.
  destruct (mod972_362_props a' Ha1) as [_ [Ha_ev _]].
  pose proof (mod2_even a' Ha_ev) as Ha_eq.
  assert (Ha4_ev : (a' + 4) mod 2 = 0).
  { replace (a' + 4) with (0 + (a' / 2 + 2) * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (Hw : W p' (a' + 4) mod 972 = 119) by (apply W_ge3_even_mod972; [lia | exact Ha4_ev]).
  split; [| split; [| split]].
  - eapply progress_evstep_trans; [exact Hkc | apply progress_evstep, D_STEP].
  - exact Hp1.
  - exact Hm162.
  - exact Hw.
Qed.

Definition Kd_iter (m : nat) (pb : nat * nat) : nat * nat :=
  iter m Kd_step pb.

Lemma Kd_loop : forall m r pb,
  5 <= fst pb -> snd pb mod 972 = 119 ->
  Cd (fst pb) (snd pb) (3 * m + r) -->* Cd (fst (Kd_iter m pb)) (snd (Kd_iter m pb)) r /\
  fst pb <= fst (Kd_iter m pb) /\
  fst (Kd_iter m pb) mod 162 = (fst pb + 148 * m) mod 162 /\
  snd (Kd_iter m pb) mod 972 = 119.
Proof.
  unfold Kd_iter.
  induction m as [| m IHm]; intros r pb Hp Hb.
  - cbn [iter]. replace (3 * 0 + r) with r by lia.
    split; [finish | split; [lia | split; [f_equal; lia | exact Hb]]].
  - rewrite iter_S'.
    replace (3 * S m + r) with (S (S (S (3 * m + r)))) by lia.
    destruct (Kd_step_all (3 * m + r) pb Hp Hb) as [Hstep [Hp1 [Hm162 Hb1]]].
    destruct (IHm r (Kd_step pb) ltac:(lia) Hb1) as [Hrun [Hp2 [Hm162' Hb2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, Hstep | exact Hrun].
    + lia.
    + rewrite Hm162', <- Nat.Div0.add_mod_idemp_l, Hm162, Nat.Div0.add_mod_idemp_l.
      f_equal; lia.
    + exact Hb2.
Qed.

Definition D_reload (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  (p - 1, W (p - 1) 0).

Lemma D_reload_all : forall pa,
  6 <= fst pa -> 2 <= snd pa -> snd pa mod 2 = 0 ->
  Ce (fst pa) (snd pa) 0 0 -->+ Cd (fst (D_reload pa)) (snd (D_reload pa)) (snd pa / 2 + 2) /\
  5 <= fst (D_reload pa) /\
  snd (D_reload pa) mod 972 = 119.
Proof.
  intros [p a] Hp Ha Hev. cbn [fst snd D_reload] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  pose proof (mod2_even a Hev) as Ha_eq.
  assert (Hw : W p' 0 mod 972 = 119) by (apply W_ge3_even_mod972; [lia | reflexivity]).
  split; [| split].
  - rewrite Ha_eq at 1. apply D_REL.
  - lia.
  - exact Hw.
Qed.

Definition pb_K0 : nat * nat := (8, W 8 8).

Lemma K_odd_reload_all : forall pb,
  5 <= fst pb -> fst pb mod 2 = 1 -> snd pb mod 972 = 119 ->
  Cd (fst pb) (snd pb) 0 -->+ Cd (fst pb_K0) (snd pb_K0) (fst pb + snd pb / 2 - 1) /\
  5 <= fst pb_K0 /\
  fst pb_K0 = 8 /\
  snd pb_K0 mod 972 = 119.
Proof.
  intros [p b] Hp Hodd Hb. cbn [fst snd pb_K0] in *.
  pose proof (mod2_odd p Hodd) as Hp_eq.
  destruct (mod972_119_props b Hb) as [Hb_eq _].
  assert (Hw : W 8 8 mod 972 = 119) by (apply W_ge3_even_mod972; [lia | reflexivity]).
  split; [| split; [| split]].
  - rewrite Hp_eq at 1. rewrite Hb_eq at 1.
    replace (p + b / 2 - 1) with (2 * (p / 2) + 1 + b / 2 - 1) by lia.
    apply K_REL_odd.
  - lia.
  - reflexivity.
  - exact Hw.
Qed.

Definition K_even_reload (pb : nat * nat) : nat * nat :=
  let '(p, b) := pb in
  Kc_full (Kd_step (D_reload (p + b / 2 + 2, 4))).

Lemma K_even_reload_all : forall pb,
  5 <= fst pb -> fst pb mod 2 = 0 -> snd pb mod 972 = 119 ->
  Cd (fst pb) (snd pb) 0 -->+ Ce (fst (K_even_reload pb)) (snd (K_even_reload pb)) 0 0 /\
  6 <= fst (K_even_reload pb) /\
  fst pb <= fst (K_even_reload pb) /\
  fst (K_even_reload pb) mod 162 = (fst pb + 32) mod 162 /\
  snd (K_even_reload pb) mod 972 = 362.
Proof.
  intros [p b] Hp Hev Hb. cbn [fst snd K_even_reload] in *.
  pose proof (mod2_even p Hev) as Hp_eq.
  destruct (mod972_119_props b Hb) as [Hb_eq [Hb_ge Hb_mod]].
  assert (Hke : Cd p b 0 -->+ Ce (p + b / 2 + 2) 4 0 0).
  { rewrite Hp_eq at 1. rewrite Hb_eq at 1.
    replace (p + b / 2 + 2) with (2 * (p / 2) + b / 2 + 2) by lia.
    apply K_REL_even. }
  destruct (D_reload_all (p + b / 2 + 2, 4) ltac:(cbn; lia) ltac:(cbn; lia) eq_refl)
    as [Hrel [Hp0 Hb0]].
  cbn [fst snd] in Hrel. change (4 / 2 + 2) with (S (S (S 1))) in Hrel.
  assert (Hf0 : fst (D_reload (p + b / 2 + 2, 4)) = p + b / 2 + 1) by (cbn; lia).
  destruct (Kd_step_all 1 (D_reload (p + b / 2 + 2, 4)) Hp0 Hb0)
    as [Hkd [Hp1 [Hm1 Hb1]]].
  destruct (Kc_full_all 0 (Kd_step (D_reload (p + b / 2 + 2, 4))) ltac:(lia) Hb1)
    as [Hkc [Hp2 [Hm2 Ha2]]].
  split; [| split; [lia | split; [lia | split; [| exact Ha2]]]].
  - eapply progress_evstep_trans; [exact Hke |].
    eapply evstep_trans; [apply progress_evstep, Hrel |].
    eapply evstep_trans; [apply progress_evstep, Hkd |].
    apply progress_evstep, Hkc.
  - rewrite Hm2, <- Nat.Div0.add_mod_idemp_l, Hm1, Nat.Div0.add_mod_idemp_l, Hf0.
    replace (p + b / 2 + 1 + 148 + 148) with ((p + 297) + b / 2) by lia.
    rewrite <- Nat.Div0.add_mod_idemp_r, Hb_mod.
    replace (p + 297 + 59) with (p + 32 + 2 * 162) by lia.
    rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma D_round_all : forall pa,
  6 <= fst pa -> snd pa mod 972 = 362 ->
  Ce (fst pa) (snd pa) 0 0 -->* Cd (fst (Kd_iter (snd pa / 6 + 1) (D_reload pa))) (snd (Kd_iter (snd pa / 6 + 1) (D_reload pa))) 0 /\
  5 <= fst (Kd_iter (snd pa / 6 + 1) (D_reload pa)) /\
  fst (Kd_iter (snd pa / 6 + 1) (D_reload pa)) mod 162 = (fst pa + 117) mod 162 /\
  snd (Kd_iter (snd pa / 6 + 1) (D_reload pa)) mod 972 = 119.
Proof.
  intros pa Hp Ha.
  destruct (mod972_362_props (snd pa) Ha) as [Ha_ge [Ha_ev [_ [_ [Hm_div Hd]]]]].
  destruct (D_reload_all pa Hp Ha_ge Ha_ev) as [Hrel [Hp0 Hb0]].
  destruct (Kd_loop (snd pa / 6 + 1) 0 (D_reload pa) Hp0 Hb0)
    as [Hloop [Hp1 [Hm1 Hb1]]].
  assert (Hf0 : fst (D_reload pa) = fst pa - 1) by (destruct pa; reflexivity).
  split; [| split; [lia | split; [| exact Hb1]]].
  - eapply evstep_trans; [apply progress_evstep, Hrel |].
    rewrite Hd. exact Hloop.
  - rewrite Hm1, Hf0, <- Nat.Div0.add_mod_idemp_r, <- Nat.Div0.mul_mod_idemp_r, Hm_div, Nat.Div0.add_mod_idemp_r.
    replace (fst pa - 1 + 148 * 61) with (fst pa + 117 + 55 * 162) by lia.
    rewrite Nat.Div0.mod_add. reflexivity.
Qed.

(** ** The 13-round trajectory of M14b *)

Definition pb1_0 : nat * nat := D_reload (8, 4).
Definition pb1_1 : nat * nat := Kd_step pb1_0.
Definition pa1 : nat * nat := Kc_full pb1_1.

Definition pb2 : nat * nat := Kd_iter (snd pa1 / 6 + 1) (D_reload pa1).
Definition pa3 : nat * nat := K_even_reload pb2.
Definition pb4 : nat * nat := Kd_iter (snd pa3 / 6 + 1) (D_reload pa3).

Definition d5 : nat := fst pb4 + snd pb4 / 2 - 1.
Definition pb5 : nat * nat := Kd_iter (d5 / 3) pb_K0.
Definition pa6 : nat * nat := K_even_reload pb5.
Definition pb7 : nat * nat := Kd_iter (snd pa6 / 6 + 1) (D_reload pa6).

Definition d8 : nat := fst pb7 + snd pb7 / 2 - 1.
Definition pb8_1 : nat * nat := Kd_iter ((d8 - 1) / 3) pb_K0.
Definition pa8 : nat * nat := Kc_full pb8_1.
Definition pb9 : nat * nat := Kd_iter (snd pa8 / 6 + 1) (D_reload pa8).

Definition d10 : nat := fst pb9 + snd pb9 / 2 - 1.
Definition pb10 : nat * nat := Kd_iter (d10 / 3) pb_K0.
Definition pa11 : nat * nat := K_even_reload pb10.
Definition pb12 : nat * nat := Kd_iter (snd pa11 / 6 + 1) (D_reload pa11).

Definition d13 : nat := fst pb12 + snd pb12 / 2 - 1.
Definition pb13_1 : nat * nat := Kd_iter ((d13 - 2) / 3) pb_K0.
Definition pa13 : nat * nat := Kc_full pb13_1.

Lemma pb1_0_def : pb1_0 = D_reload (8, 4). Proof. reflexivity. Qed.
Lemma pb1_1_def : pb1_1 = Kd_step pb1_0. Proof. reflexivity. Qed.
Lemma pa1_def : pa1 = Kc_full pb1_1. Proof. reflexivity. Qed.
Lemma pb2_def : pb2 = Kd_iter (snd pa1 / 6 + 1) (D_reload pa1). Proof. reflexivity. Qed.
Lemma pa3_def : pa3 = K_even_reload pb2. Proof. reflexivity. Qed.
Lemma pb4_def : pb4 = Kd_iter (snd pa3 / 6 + 1) (D_reload pa3). Proof. reflexivity. Qed.
Lemma d5_def : d5 = fst pb4 + snd pb4 / 2 - 1. Proof. reflexivity. Qed.
Lemma pb5_def : pb5 = Kd_iter (d5 / 3) pb_K0. Proof. reflexivity. Qed.
Lemma pa6_def : pa6 = K_even_reload pb5. Proof. reflexivity. Qed.
Lemma pb7_def : pb7 = Kd_iter (snd pa6 / 6 + 1) (D_reload pa6). Proof. reflexivity. Qed.
Lemma d8_def : d8 = fst pb7 + snd pb7 / 2 - 1. Proof. reflexivity. Qed.
Lemma pb8_1_def : pb8_1 = Kd_iter ((d8 - 1) / 3) pb_K0. Proof. reflexivity. Qed.
Lemma pa8_def : pa8 = Kc_full pb8_1. Proof. reflexivity. Qed.
Lemma pb9_def : pb9 = Kd_iter (snd pa8 / 6 + 1) (D_reload pa8). Proof. reflexivity. Qed.
Lemma d10_def : d10 = fst pb9 + snd pb9 / 2 - 1. Proof. reflexivity. Qed.
Lemma pb10_def : pb10 = Kd_iter (d10 / 3) pb_K0. Proof. reflexivity. Qed.
Lemma pa11_def : pa11 = K_even_reload pb10. Proof. reflexivity. Qed.
Lemma pb12_def : pb12 = Kd_iter (snd pa11 / 6 + 1) (D_reload pa11). Proof. reflexivity. Qed.
Lemma d13_def : d13 = fst pb12 + snd pb12 / 2 - 1. Proof. reflexivity. Qed.
Lemma pb13_1_def : pb13_1 = Kd_iter ((d13 - 2) / 3) pb_K0. Proof. reflexivity. Qed.
Lemma pa13_def : pa13 = Kc_full pb13_1. Proof. reflexivity. Qed.
Lemma D_reload_8_4_fst : fst (D_reload (8, 4)) = 7. Proof. reflexivity. Qed.

Opaque Kc Kc_full Kd_step Kd_iter D_reload pb_K0 K_even_reload
  pb1_0 pb1_1 pa1 pb2 pa3 pb4 d5 pb5 pa6 pb7 d8 pb8_1 pa8 pb9 d10 pb10 pa11 pb12 d13 pb13_1 pa13.

Lemma mod_162_54 : forall x, (x mod 162) mod 54 = x mod 54.
Proof. intros x. apply (mod_factor x 54 3). Qed.

Lemma mod_162_18 : forall x, (x mod 162) mod 18 = x mod 18.
Proof. intros x. apply (mod_factor x 18 9). Qed.

Lemma mod_162_6 : forall x, (x mod 162) mod 6 = x mod 6.
Proof. intros x. apply (mod_factor x 6 27). Qed.

Lemma mod_162_2 : forall x, (x mod 162) mod 2 = x mod 2.
Proof. intros x. apply (mod_factor x 2 81). Qed.

Lemma mod_54_2 : forall x, (x mod 54) mod 2 = x mod 2.
Proof. intros x. apply (mod_factor x 2 27). Qed.

Lemma mod_18_2 : forall x, (x mod 18) mod 2 = x mod 2.
Proof. intros x. apply (mod_factor x 2 9). Qed.

Lemma mod_6_2 : forall x, (x mod 6) mod 2 = x mod 2.
Proof. intros x. apply (mod_factor x 2 3). Qed.

Lemma run_pa1 :
  c0 -->* Ce (fst pa1) (snd pa1) 0 0 /\
  6 <= fst pa1 /\ fst pa1 mod 162 = 141 /\ snd pa1 mod 972 = 362.
Proof.
  rewrite pa1_def, pb1_1_def, pb1_0_def.
  destruct (D_reload_all (8, 4) ltac:(cbn; lia) ltac:(cbn; lia) eq_refl)
    as [Hrel1 [Hp0 Hb0]].
  cbn [fst snd] in Hrel1. change (4 / 2 + 2) with (S (S (S 1))) in Hrel1.
  destruct (Kd_step_all 1 (D_reload (8, 4)) Hp0 Hb0)
    as [Hkd1 [Hp1 [Hm1 Hb1]]].
  destruct (Kc_full_all 0 (Kd_step (D_reload (8, 4))) ltac:(lia) Hb1)
    as [Hkc1 [Hp2 [Hm2 Ha2]]].
  pose proof D_reload_8_4_fst as Hp0_eq.
  split; [| split; [lia | split; [| exact Ha2]]].
  - follow init_352.
    eapply evstep_trans; [apply progress_evstep, Hrel1 |].
    eapply evstep_trans; [apply progress_evstep, Hkd1 |].
    apply progress_evstep, Hkc1.
  - rewrite Hm2, <- Nat.Div0.add_mod_idemp_l, Hm1, Hp0_eq. reflexivity.
Qed.

Lemma run_pb2 :
  c0 -->* Cd (fst pb2) (snd pb2) 0 /\
  5 <= fst pb2 /\ fst pb2 mod 162 = 96 /\ snd pb2 mod 972 = 119.
Proof.
  destruct run_pa1 as [Hrun1 [Hp1 [Hm1 Ha1]]].
  rewrite !pb2_def.
  destruct (D_round_all pa1 Hp1 Ha1) as [Hstep [Hp2 [Hm2 Hb2]]].
  split; [follow Hrun1; exact Hstep | split; [exact Hp2 | split; [| exact Hb2]]].
  rewrite Hm2, <- Nat.Div0.add_mod_idemp_l, Hm1. reflexivity.
Qed.

Lemma run_pa3 :
  c0 -->* Ce (fst pa3) (snd pa3) 0 0 /\
  6 <= fst pa3 /\ fst pa3 mod 162 = 128 /\ snd pa3 mod 972 = 362.
Proof.
  destruct run_pb2 as [Hrun2 [Hp2 [Hm2 Hb2]]].
  rewrite !pa3_def.
  assert (Hev : fst pb2 mod 2 = 0) by (rewrite <- mod_162_2, Hm2; reflexivity).
  destruct (K_even_reload_all pb2 Hp2 Hev Hb2) as [Hstep [Hp3 [_ [Hm3 Ha3]]]].
  split; [follow Hrun2; apply progress_evstep, Hstep | split; [exact Hp3 | split; [| exact Ha3]]].
  rewrite Hm3, <- Nat.Div0.add_mod_idemp_l, Hm2. reflexivity.
Qed.

Lemma run_pb4 :
  c0 -->* Cd (fst pb4) (snd pb4) 0 /\
  5 <= fst pb4 /\ fst pb4 mod 162 = 83 /\ snd pb4 mod 972 = 119.
Proof.
  destruct run_pa3 as [Hrun3 [Hp3 [Hm3 Ha3]]].
  rewrite !pb4_def.
  destruct (D_round_all pa3 Hp3 Ha3) as [Hstep [Hp4 [Hm4 Hb4]]].
  split; [follow Hrun3; exact Hstep | split; [exact Hp4 | split; [| exact Hb4]]].
  rewrite Hm4, <- Nat.Div0.add_mod_idemp_l, Hm3. reflexivity.
Qed.

Lemma run_pb5 :
  c0 -->* Cd (fst pb5) (snd pb5) 0 /\
  5 <= fst pb5 /\ fst pb5 mod 54 = 52 /\ snd pb5 mod 972 = 119.
Proof.
  destruct run_pb4 as [Hrun4 [Hp4 [Hm4 Hb4]]].
  rewrite !pb5_def, !d5_def.
  assert (Hodd : fst pb4 mod 2 = 1) by (rewrite <- mod_162_2, Hm4; reflexivity).
  destruct (K_odd_reload_all pb4 Hp4 Hodd Hb4) as [Hrel5 [HpK [HfK HbK]]].
  set (d := fst pb4 + snd pb4 / 2 - 1) in *.
  destruct (mod972_119_props (snd pb4) Hb4) as [_ [Hb4_ge Hb4_162]].
  pose proof (pred_mod (fst pb4) 162 83 Hm4 ltac:(lia)) as Hp4_pred.
  assert (Hd_mod : d mod (3 * 54) = 141).
  { change (3 * 54) with 162.
    replace d with ((fst pb4 - 1) + snd pb4 / 2) by (unfold d; lia).
    rewrite <- Nat.Div0.add_mod_idemp_l, Hp4_pred, <- Nat.Div0.add_mod_idemp_r, Hb4_162.
    reflexivity. }
  destruct (div3_props d 54 141 ltac:(lia) Hd_mod) as [Hd5 Hm_div].
  change (141 mod 3) with 0 in Hd5, Hm_div.
  change ((141 / 3) mod 54) with 47 in Hm_div.
  replace (d - 0) with d in Hd5, Hm_div by lia.
  destruct (Kd_loop (d / 3) 0 pb_K0 HpK HbK)
    as [Hloop5 [Hp5 [Hm5 Hb5]]].
  split; [| split; [lia | split; [| exact Hb5]]].
  - follow Hrun4.
    eapply evstep_trans; [apply progress_evstep, Hrel5 |].
    rewrite Hd5 at 1. exact Hloop5.
  - rewrite <- mod_162_54, Hm5, mod_162_54, HfK.
    rewrite <- Nat.Div0.add_mod_idemp_r, <- Nat.Div0.mul_mod_idemp_r, Hm_div.
    reflexivity.
Qed.

Lemma run_pa6 :
  c0 -->* Ce (fst pa6) (snd pa6) 0 0 /\
  6 <= fst pa6 /\ fst pa6 mod 54 = 30 /\ snd pa6 mod 972 = 362.
Proof.
  destruct run_pb5 as [Hrun5 [Hp5 [Hm5 Hb5]]].
  rewrite !pa6_def.
  assert (Hev : fst pb5 mod 2 = 0) by (rewrite <- mod_54_2, Hm5; reflexivity).
  destruct (K_even_reload_all pb5 Hp5 Hev Hb5) as [Hstep [Hp6 [_ [Hm6 Ha6]]]].
  split; [follow Hrun5; apply progress_evstep, Hstep | split; [exact Hp6 | split; [| exact Ha6]]].
  rewrite <- mod_162_54, Hm6, mod_162_54, <- Nat.Div0.add_mod_idemp_l, Hm5. reflexivity.
Qed.

Lemma run_pb7 :
  c0 -->* Cd (fst pb7) (snd pb7) 0 /\
  5 <= fst pb7 /\ fst pb7 mod 54 = 39 /\ snd pb7 mod 972 = 119.
Proof.
  destruct run_pa6 as [Hrun6 [Hp6 [Hm6 Ha6]]].
  rewrite !pb7_def.
  destruct (D_round_all pa6 Hp6 Ha6) as [Hstep [Hp7 [Hm7 Hb7]]].
  split; [follow Hrun6; exact Hstep | split; [exact Hp7 | split; [| exact Hb7]]].
  rewrite <- mod_162_54, Hm7, mod_162_54, <- Nat.Div0.add_mod_idemp_l, Hm6. reflexivity.
Qed.

Lemma run_pa8 :
  c0 -->* Ce (fst pa8) (snd pa8) 0 0 /\
  6 <= fst pa8 /\ fst pa8 mod 18 = 14 /\ snd pa8 mod 972 = 362.
Proof.
  destruct run_pb7 as [Hrun7 [Hp7 [Hm7 Hb7]]].
  rewrite !pa8_def, !pb8_1_def, !d8_def.
  assert (Hodd : fst pb7 mod 2 = 1) by (rewrite <- mod_54_2, Hm7; reflexivity).
  destruct (K_odd_reload_all pb7 Hp7 Hodd Hb7) as [Hrel8 [HpK [HfK HbK]]].
  set (d := fst pb7 + snd pb7 / 2 - 1) in *.
  destruct (mod972_119_props (snd pb7) Hb7) as [_ [Hb7_ge Hb7_162]].
  assert (Hb7_div : (snd pb7 / 2) mod 54 = 5) by (rewrite <- mod_162_54, Hb7_162; reflexivity).
  pose proof (pred_mod (fst pb7) 54 39 Hm7 ltac:(lia)) as Hp7_pred.
  assert (Hd_mod : d mod (3 * 18) = 43).
  { change (3 * 18) with 54.
    replace d with ((fst pb7 - 1) + snd pb7 / 2) by (unfold d; lia).
    rewrite <- Nat.Div0.add_mod_idemp_l, Hp7_pred, <- Nat.Div0.add_mod_idemp_r, Hb7_div.
    reflexivity. }
  destruct (div3_props d 18 43 ltac:(lia) Hd_mod) as [Hd8 Hm_div].
  change (43 mod 3) with 1 in Hd8, Hm_div.
  change ((43 / 3) mod 18) with 14 in Hm_div.
  destruct (Kd_loop ((d - 1) / 3) 1 pb_K0 HpK HbK)
    as [Hloop8 [Hp8_1 [Hm8_1 Hb8_1]]].
  destruct (Kc_full_all 0 (Kd_iter ((d - 1) / 3) pb_K0) ltac:(lia) Hb8_1)
    as [Hkc8 [Hp8 [Hm8 Ha8]]].
  split; [| split; [lia | split; [| exact Ha8]]].
  - follow Hrun7.
    eapply evstep_trans; [apply progress_evstep, Hrel8 |].
    rewrite Hd8 at 1.
    follow Hloop8.
    apply progress_evstep, Hkc8.
  - rewrite <- mod_162_18, Hm8, <- Nat.Div0.add_mod_idemp_l, Hm8_1, Nat.Div0.add_mod_idemp_l, mod_162_18, HfK.
    replace (8 + 148 * ((d - 1) / 3) + 148) with (156 + 148 * ((d - 1) / 3)) by lia.
    rewrite <- Nat.Div0.add_mod_idemp_r, <- Nat.Div0.mul_mod_idemp_r, Hm_div.
    reflexivity.
Qed.

Lemma run_pb9 :
  c0 -->* Cd (fst pb9) (snd pb9) 0 /\
  5 <= fst pb9 /\ fst pb9 mod 18 = 5 /\ snd pb9 mod 972 = 119.
Proof.
  destruct run_pa8 as [Hrun8 [Hp8 [Hm8 Ha8]]].
  rewrite !pb9_def.
  destruct (D_round_all pa8 Hp8 Ha8) as [Hstep [Hp9 [Hm9 Hb9]]].
  split; [follow Hrun8; exact Hstep | split; [exact Hp9 | split; [| exact Hb9]]].
  rewrite <- mod_162_18, Hm9, mod_162_18, <- Nat.Div0.add_mod_idemp_l, Hm8. reflexivity.
Qed.

Lemma run_pb10 :
  c0 -->* Cd (fst pb10) (snd pb10) 0 /\
  5 <= fst pb10 /\ fst pb10 mod 6 = 2 /\ snd pb10 mod 972 = 119.
Proof.
  destruct run_pb9 as [Hrun9 [Hp9 [Hm9 Hb9]]].
  rewrite !pb10_def, !d10_def.
  assert (Hodd : fst pb9 mod 2 = 1) by (rewrite <- mod_18_2, Hm9; reflexivity).
  destruct (K_odd_reload_all pb9 Hp9 Hodd Hb9) as [Hrel10 [HpK [HfK HbK]]].
  set (d := fst pb9 + snd pb9 / 2 - 1) in *.
  destruct (mod972_119_props (snd pb9) Hb9) as [_ [Hb9_ge Hb9_162]].
  assert (Hb9_div : (snd pb9 / 2) mod 18 = 5) by (rewrite <- mod_162_18, Hb9_162; reflexivity).
  pose proof (pred_mod (fst pb9) 18 5 Hm9 ltac:(lia)) as Hp9_pred.
  assert (Hd_mod : d mod (3 * 6) = 9).
  { change (3 * 6) with 18.
    replace d with ((fst pb9 - 1) + snd pb9 / 2) by (unfold d; lia).
    rewrite <- Nat.Div0.add_mod_idemp_l, Hp9_pred, <- Nat.Div0.add_mod_idemp_r, Hb9_div.
    reflexivity. }
  destruct (div3_props d 6 9 ltac:(lia) Hd_mod) as [Hd10 Hm_div].
  change (9 mod 3) with 0 in Hd10, Hm_div.
  change ((9 / 3) mod 6) with 3 in Hm_div.
  replace (d - 0) with d in Hd10, Hm_div by lia.
  destruct (Kd_loop (d / 3) 0 pb_K0 HpK HbK)
    as [Hloop10 [Hp10 [Hm10 Hb10]]].
  split; [| split; [lia | split; [| exact Hb10]]].
  - follow Hrun9.
    eapply evstep_trans; [apply progress_evstep, Hrel10 |].
    rewrite Hd10 at 1. exact Hloop10.
  - rewrite <- mod_162_6, Hm10, mod_162_6, HfK.
    rewrite <- Nat.Div0.add_mod_idemp_r, <- Nat.Div0.mul_mod_idemp_r, Hm_div.
    reflexivity.
Qed.

Lemma run_pa11 :
  c0 -->* Ce (fst pa11) (snd pa11) 0 0 /\
  6 <= fst pa11 /\ fst pa11 mod 6 = 4 /\ snd pa11 mod 972 = 362.
Proof.
  destruct run_pb10 as [Hrun10 [Hp10 [Hm10 Hb10]]].
  rewrite !pa11_def.
  assert (Hev : fst pb10 mod 2 = 0) by (rewrite <- mod_6_2, Hm10; reflexivity).
  destruct (K_even_reload_all pb10 Hp10 Hev Hb10) as [Hstep [Hp11 [_ [Hm11 Ha11]]]].
  split; [follow Hrun10; apply progress_evstep, Hstep | split; [exact Hp11 | split; [| exact Ha11]]].
  rewrite <- mod_162_6, Hm11, mod_162_6, <- Nat.Div0.add_mod_idemp_l, Hm10. reflexivity.
Qed.

Lemma run_pb12 :
  c0 -->* Cd (fst pb12) (snd pb12) 0 /\
  5 <= fst pb12 /\ fst pb12 mod 6 = 1 /\ snd pb12 mod 972 = 119.
Proof.
  destruct run_pa11 as [Hrun11 [Hp11 [Hm11 Ha11]]].
  rewrite !pb12_def.
  destruct (D_round_all pa11 Hp11 Ha11) as [Hstep [Hp12 [Hm12 Hb12]]].
  split; [follow Hrun11; exact Hstep | split; [exact Hp12 | split; [| exact Hb12]]].
  rewrite <- mod_162_6, Hm12, mod_162_6, <- Nat.Div0.add_mod_idemp_l, Hm11. reflexivity.
Qed.

Lemma run_pa13 :
  c0 -->* c_end (fst pa13) (snd pa13).
Proof.
  destruct run_pb12 as [Hrun12 [Hp12 [Hm12 Hb12]]].
  rewrite !pa13_def, !pb13_1_def, !d13_def.
  assert (Hodd : fst pb12 mod 2 = 1) by (rewrite <- mod_6_2, Hm12; reflexivity).
  destruct (K_odd_reload_all pb12 Hp12 Hodd Hb12) as [Hrel13 [HpK [HfK HbK]]].
  set (d := fst pb12 + snd pb12 / 2 - 1) in *.
  destruct (mod972_119_props (snd pb12) Hb12) as [_ [Hb12_ge Hb12_162]].
  assert (Hb12_div : (snd pb12 / 2) mod 6 = 5) by (rewrite <- mod_162_6, Hb12_162; reflexivity).
  pose proof (pred_mod (fst pb12) 6 1 Hm12 ltac:(lia)) as Hp12_pred.
  assert (Hd_mod : d mod (3 * 2) = 5).
  { change (3 * 2) with 6.
    replace d with ((fst pb12 - 1) + snd pb12 / 2) by (unfold d; lia).
    rewrite <- Nat.Div0.add_mod_idemp_l, Hp12_pred, <- Nat.Div0.add_mod_idemp_r, Hb12_div.
    reflexivity. }
  destruct (div3_props d 2 5 ltac:(lia) Hd_mod) as [Hd13 _].
  change (5 mod 3) with 2 in Hd13.
  destruct (Kd_loop ((d - 2) / 3) 2 pb_K0 HpK HbK)
    as [Hloop13 [Hp13_1 [_ Hb13_1]]].
  destruct (Kc_full_all 1 (Kd_iter ((d - 2) / 3) pb_K0) ltac:(lia) Hb13_1)
    as [Hkc13 _].
  follow Hrun12.
  eapply evstep_trans; [apply progress_evstep, Hrel13 |].
  rewrite Hd13 at 1.
  follow Hloop13.
  eapply evstep_trans; [apply progress_evstep, Hkc13 |].
  apply progress_evstep, HALT_step.
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run_pa13) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply c_end_halted.
Qed.
