(** * The 13-state machine M13b achieves > f_(omega+2)^6(f_(omega+1)^2(3)) and halts *)

From BB8 Require Import Individual132.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RM0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_0LL0LL_0LH1LK_---0LH *)
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
  | K, 0 => Some (0, TM.L, L)  | K, 1 => Some (0, TM.L, L)
  | L, 0 => Some (0, TM.L, H)  | L, 1 => Some (1, TM.L, K)
  | M, 0 => None               | M, 1 => Some (0, TM.L, H)
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

Lemma cr_KL_01_10 : forall n l r, [0; 1]^^n *> l <{{K}} r -->* l <{{K}} [1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

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

(** ** K-reload step 1, step 2, and Halting step *)

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

Lemma K_REL_step2 : forall p d,
  ([0; 1]^^p *> const 0) <{{K}} ([1; 0]^^(S d) *> const 0) -->+ Cd 2 3 (p + d).
Proof.
  intros p d. unfold Cd.
  eapply evstep_progress_trans; [apply cr_KL_01_10 |].
  rewrite <- Str_app_assoc, <- lpow_add.
  replace (p + S d)%nat with (S (p + d))%nat by lia.
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

Lemma K_REL : forall p m,
  1 <= p ->
  Cd p (2 * m + 1) 0 -->+ Cd 8 (W 8 8) (p + m - 1).
Proof.
  intros p m Hp.
  eapply progress_evstep_trans; [apply K_REL_step1 |].
  rewrite tail_10_const.
  replace (m + 2 + 1) with (S (m + 2)) by lia.
  eapply evstep_trans; [apply progress_evstep, K_REL_step2 |].
  replace (p + (m + 2)) with (S (S (S (p + m - 1)))) by lia.
  apply progress_evstep, K_REL_step3.
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

(** ** Growth, parity, and 3-adic mod-162 invariants *)

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

Lemma iter_W1_mod162 : forall b,
  iter (S (S b)) (W 1) 2 mod 162 = (if S b mod 2 =? 0 then 119 else 38).
Proof.
  induction b as [| b IHb].
  - reflexivity.
  - change (iter (S (S (S b))) (W 1) 2) with (W 1 (iter (S (S b)) (W 1) 2)).
    rewrite W_1.
    destruct (S b mod 2 =? 0) eqn:Heq1;
      [apply Nat.eqb_eq in Heq1 | apply Nat.eqb_neq in Heq1];
    (destruct (S (S b) mod 2 =? 0) eqn:Heq2;
      [apply Nat.eqb_eq in Heq2 | apply Nat.eqb_neq in Heq2]);
    mods; lia.
Qed.

Lemma W_SS_S_mod162 : forall j b,
  W (S (S j)) (S b) mod 162 = (if S b mod 2 =? 0 then 119 else 38).
Proof.
  induction j as [| j IHj]; intros b.
  - rewrite W_S. apply iter_W1_mod162.
  - change (W (S (S (S j))) (S b)) with (W (S (S j)) (iter (S b) (W (S (S j))) 2)).
    pose proof (W_grow (S (S j)) (iter b (W (S (S j))) 2)) as Hgrow.
    pose proof (iter_par_nat (W (S (S j))) (W_par (S (S j))) (S b) 2) as Hpar.
    destruct (iter (S b) (W (S (S j))) 2) as [| y'] eqn:Hy.
    + cbn [iter] in Hy. lia.
    + rewrite (IHj y').
      replace (S y' mod 2) with (S b mod 2) by (mods; lia).
      reflexivity.
Qed.

Lemma W_SSS_mod162 : forall j b,
  W (S (S (S j))) b mod 162 = (if b mod 2 =? 0 then 119 else 38).
Proof.
  intros j [| b'].
  - change (W (S (S (S j))) 0) with (W (S (S j)) 2).
    apply (W_SS_S_mod162 j 1).
  - apply (W_SS_S_mod162 (S j) b').
Qed.

Lemma W_ge3_even_mod162 : forall p b,
  3 <= p -> b mod 2 = 0 -> W p b mod 162 = 119.
Proof.
  intros [| [| [| j]]] b Hp Hev; try lia.
  rewrite W_SSS_mod162.
  apply Nat.eqb_eq in Hev. rewrite Hev. reflexivity.
Qed.

Lemma W_ge3_odd_mod162 : forall p b,
  3 <= p -> b mod 2 = 1 -> W p b mod 162 = 38.
Proof.
  intros [| [| [| j]]] b Hp Hodd; try lia.
  rewrite W_SSS_mod162.
  assert (Hneq : b mod 2 =? 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hneq. reflexivity.
Qed.

Opaque W.

(** ** Macro-step functions Kc, Kc_full, Kd_step, Kd_iter, D_reload, K_reload *)

Lemma mod2_even : forall a, a mod 2 = 0 -> a = 2 * (a / 2).
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

Lemma mod162_38_props : forall a,
  a mod 162 = 38 ->
  2 <= a /\ a mod 2 = 0 /\
  1 <= a / 2 /\
  (a / 2) mod 81 = 19 /\
  (a / 6 + 1) mod 27 = 7 /\
  a / 2 + 2 = 3 * (a / 6 + 1) + 0.
Proof.
  intros a Ha.
  pose proof (Nat.div_mod_eq a 162) as Hdm. rewrite Ha in Hdm.
  set (q := a / 162) in *. clearbody q. clear Ha.
  assert (Ha2 : a / 2 = 19 + (q * 1) * 81).
  { replace a with (38 + (81 * q) * 2) by lia.
    rewrite Nat.div_add by lia. change (38 / 2) with 19. lia. }
  assert (Ha6 : a / 6 + 1 = 7 + (q * 1) * 27).
  { replace a with (38 + (27 * q) * 6) by lia.
    rewrite Nat.div_add by lia. change (38 / 6) with 6. lia. }
  assert (Hev : a mod 2 = 0).
  { replace a with (0 + (81 * q + 19) * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  split; [lia | split; [exact Hev | split; [lia | split; [| split; [| lia]]]]].
  - rewrite Ha2, Nat.Div0.mod_add. reflexivity.
  - rewrite Ha6, Nat.Div0.mod_add. reflexivity.
Qed.

Lemma mod162_119_props : forall b,
  b mod 162 = 119 ->
  b = 2 * (b / 2) + 1 /\
  59 <= b / 2 /\
  (b / 2) mod 81 = 59.
Proof.
  intros b Hb.
  pose proof (Nat.div_mod_eq b 162) as Hdm. rewrite Hb in Hdm.
  set (q := b / 162) in *. clearbody q. clear Hb.
  assert (Hb2 : b / 2 = 59 + (q * 1) * 81).
  { replace b with (119 + (81 * q) * 2) by lia.
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
  4 <= fst pa -> snd pa mod 162 = 38 ->
  fst pa + 1 <= fst (Kc pa) /\
  fst (Kc pa) mod 81 = (fst pa + 19) mod 81 /\
  snd (Kc pa) mod 162 = 38.
Proof.
  intros [p a] Hp Ha. cbn [fst snd Kc] in *.
  assert (Hm : W (p - 1) 1 mod 162 = 38) by (apply W_ge3_odd_mod162; [lia | reflexivity]).
  destruct (mod162_38_props a Ha) as [_ [_ [Ha_ge [Ha_mod _]]]].
  split; [lia | split; [| exact Hm]].
  rewrite <- Nat.Div0.add_mod_idemp_r, Ha_mod. reflexivity.
Qed.

Lemma Kc_loop_mod : forall c d pa,
  4 <= fst pa -> snd pa mod 162 = 38 ->
  Ce (fst pa) (snd pa) c d -->* Ce (fst (iter c Kc pa)) (snd (iter c Kc pa)) 0 d /\
  fst pa + c <= fst (iter c Kc pa) /\
  fst (iter c Kc pa) mod 81 = (fst pa + 19 * c) mod 81 /\
  snd (iter c Kc pa) mod 162 = 38.
Proof.
  induction c as [| c IHc]; intros d pa Hp Ha.
  - cbn [iter]. split; [finish | split; [lia | split; [f_equal; lia | exact Ha]]].
  - rewrite iter_S'.
    destruct (mod162_38_props (snd pa) Ha) as [_ [Hev _]].
    destruct (Kc_props_mod pa Hp Ha) as [Hp1 [Hm81 Ha1]].
    destruct (IHc d (Kc pa) ltac:(lia) Ha1) as [Hrun [Hp2 [Hm81' Ha2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, (Kc_step c d pa ltac:(lia) Hev) | exact Hrun].
    + lia.
    + rewrite Hm81', <- Nat.Div0.add_mod_idemp_l, Hm81, Nat.Div0.add_mod_idemp_l.
      f_equal; lia.
    + exact Ha2.
Qed.

Definition Kc_full (pb : nat * nat) : nat * nat :=
  let '(p, b) := pb in
  iter (b / 2) Kc (p - 1, W (p - 1) 3).

Lemma Kc_full_all : forall d pb,
  5 <= fst pb -> snd pb mod 162 = 119 ->
  Cd (fst pb) (snd pb) (S d) -->+ Ce (fst (Kc_full pb)) (snd (Kc_full pb)) 0 d /\
  fst pb + 1 <= fst (Kc_full pb) /\
  fst (Kc_full pb) mod 81 = (fst pb + 67) mod 81 /\
  snd (Kc_full pb) mod 162 = 38.
Proof.
  intros d [p b] Hp Hb. cbn [fst snd Kc_full] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  destruct (mod162_119_props b Hb) as [Hb_eq [Hb_ge Hb_mod]].
  assert (Hw3 : W p' 3 mod 162 = 38) by (apply W_ge3_odd_mod162; [lia | reflexivity]).
  destruct (Kc_loop_mod (b / 2) d (p', W p' 3) ltac:(cbn; lia) Hw3)
    as [Hrun [Hp1 [Hm81 Ha1]]].
  cbn [fst snd] in *.
  split; [| split; [| split]].
  - rewrite Hb_eq at 1.
    eapply progress_evstep_trans; [apply C_REL | exact Hrun].
  - lia.
  - rewrite Hm81, <- Nat.Div0.add_mod_idemp_r, <- Nat.Div0.mul_mod_idemp_r, Hb_mod, Nat.Div0.add_mod_idemp_r.
    replace (p' + 19 * 59) with (S p' + 67 + 13 * 81) by lia.
    rewrite Nat.Div0.mod_add. reflexivity.
  - exact Ha1.
Qed.

Definition Kd_step (pb : nat * nat) : nat * nat :=
  let '(p', a') := Kc_full pb in
  (p', W p' (a' + 4)).

Lemma Kd_step_all : forall d pb,
  5 <= fst pb -> snd pb mod 162 = 119 ->
  Cd (fst pb) (snd pb) (S (S (S d))) -->+ Cd (fst (Kd_step pb)) (snd (Kd_step pb)) d /\
  fst pb + 1 <= fst (Kd_step pb) /\
  fst (Kd_step pb) mod 81 = (fst pb + 67) mod 81 /\
  snd (Kd_step pb) mod 162 = 119.
Proof.
  intros d pb Hp Hb.
  unfold Kd_step.
  destruct (Kc_full_all (S (S d)) pb Hp Hb) as [Hkc [Hp1 [Hm81 Ha1]]].
  set (pa' := Kc_full pb) in *.
  destruct pa' as [p' a']. cbn [fst snd] in *.
  destruct (mod162_38_props a' Ha1) as [_ [Ha_ev _]].
  pose proof (mod2_even a' Ha_ev) as Ha_eq.
  assert (Ha4_ev : (a' + 4) mod 2 = 0).
  { replace (a' + 4) with (0 + (a' / 2 + 2) * 2) by lia.
    rewrite Nat.Div0.mod_add. reflexivity. }
  assert (Hw : W p' (a' + 4) mod 162 = 119) by (apply W_ge3_even_mod162; [lia | exact Ha4_ev]).
  split; [| split; [| split]].
  - eapply progress_evstep_trans; [exact Hkc | apply progress_evstep, D_STEP].
  - exact Hp1.
  - exact Hm81.
  - exact Hw.
Qed.

Definition Kd_iter (m : nat) (pb : nat * nat) : nat * nat :=
  iter m Kd_step pb.

Lemma Kd_loop : forall m r pb,
  5 <= fst pb -> snd pb mod 162 = 119 ->
  Cd (fst pb) (snd pb) (3 * m + r) -->* Cd (fst (Kd_iter m pb)) (snd (Kd_iter m pb)) r /\
  fst pb <= fst (Kd_iter m pb) /\
  fst (Kd_iter m pb) mod 81 = (fst pb + 67 * m) mod 81 /\
  snd (Kd_iter m pb) mod 162 = 119.
Proof.
  unfold Kd_iter.
  induction m as [| m IHm]; intros r pb Hp Hb.
  - cbn [iter]. replace (3 * 0 + r) with r by lia.
    split; [finish | split; [lia | split; [f_equal; lia | exact Hb]]].
  - rewrite iter_S'.
    replace (3 * S m + r) with (S (S (S (3 * m + r)))) by lia.
    destruct (Kd_step_all (3 * m + r) pb Hp Hb) as [Hstep [Hp1 [Hm81 Hb1]]].
    destruct (IHm r (Kd_step pb) ltac:(lia) Hb1) as [Hrun [Hp2 [Hm81' Hb2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, Hstep | exact Hrun].
    + lia.
    + rewrite Hm81', <- Nat.Div0.add_mod_idemp_l, Hm81, Nat.Div0.add_mod_idemp_l.
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
  snd (D_reload pa) mod 162 = 119.
Proof.
  intros [p a] Hp Ha Hev. cbn [fst snd D_reload] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  pose proof (mod2_even a Hev) as Ha_eq.
  assert (Hw : W p' 0 mod 162 = 119) by (apply W_ge3_even_mod162; [lia | reflexivity]).
  split; [| split].
  - rewrite Ha_eq at 1. apply D_REL.
  - lia.
  - exact Hw.
Qed.

Definition pb_K0 : nat * nat := (8, W 8 8).

Lemma K_reload_all : forall pb,
  5 <= fst pb -> snd pb mod 162 = 119 ->
  Cd (fst pb) (snd pb) 0 -->+ Cd (fst pb_K0) (snd pb_K0) (fst pb + snd pb / 2 - 1) /\
  5 <= fst pb_K0 /\
  fst pb_K0 = 8 /\
  snd pb_K0 mod 162 = 119.
Proof.
  intros [p b] Hp Hb. cbn [fst snd pb_K0] in *.
  destruct (mod162_119_props b Hb) as [Hb_eq _].
  assert (Hw : W 8 8 mod 162 = 119) by (apply W_ge3_even_mod162; [lia | reflexivity]).
  split; [| split; [| split]].
  - rewrite Hb_eq at 1. apply K_REL. lia.
  - lia.
  - reflexivity.
  - exact Hw.
Qed.

(** ** The 7-round trajectory of M13b *)

Definition pb1_0 : nat * nat := D_reload (8, 4).
Definition pb1_1 : nat * nat := Kd_step pb1_0.
Definition pa1 : nat * nat := Kc_full pb1_1.

Definition pb2_0 : nat * nat := D_reload pa1.
Definition pb2 : nat * nat := Kd_iter (snd pa1 / 6 + 1) pb2_0.

Definition d3 : nat := fst pb2 + snd pb2 / 2 - 1.
Definition pb3_1 : nat * nat := Kd_iter ((d3 - 1) / 3) pb_K0.
Definition pa3 : nat * nat := Kc_full pb3_1.

Definition pb4_0 : nat * nat := D_reload pa3.
Definition pb4 : nat * nat := Kd_iter (snd pa3 / 6 + 1) pb4_0.

Definition d5 : nat := fst pb4 + snd pb4 / 2 - 1.
Definition pb5_1 : nat * nat := Kd_iter ((d5 - 1) / 3) pb_K0.
Definition pa5 : nat * nat := Kc_full pb5_1.

Definition pb6_0 : nat * nat := D_reload pa5.
Definition pb6 : nat * nat := Kd_iter (snd pa5 / 6 + 1) pb6_0.

Definition d7 : nat := fst pb6 + snd pb6 / 2 - 1.
Definition pb7_1 : nat * nat := Kd_iter ((d7 - 2) / 3) pb_K0.
Definition pa7 : nat * nat := Kc_full pb7_1.

Lemma pb1_0_def : pb1_0 = D_reload (8, 4). Proof. reflexivity. Qed.
Lemma pb1_1_def : pb1_1 = Kd_step pb1_0. Proof. reflexivity. Qed.
Lemma pa1_def : pa1 = Kc_full pb1_1. Proof. reflexivity. Qed.
Lemma pb2_0_def : pb2_0 = D_reload pa1. Proof. reflexivity. Qed.
Lemma pb2_def : pb2 = Kd_iter (snd pa1 / 6 + 1) pb2_0. Proof. reflexivity. Qed.
Lemma d3_def : d3 = fst pb2 + snd pb2 / 2 - 1. Proof. reflexivity. Qed.
Lemma pb3_1_def : pb3_1 = Kd_iter ((d3 - 1) / 3) pb_K0. Proof. reflexivity. Qed.
Lemma pa3_def : pa3 = Kc_full pb3_1. Proof. reflexivity. Qed.
Lemma pb4_0_def : pb4_0 = D_reload pa3. Proof. reflexivity. Qed.
Lemma pb4_def : pb4 = Kd_iter (snd pa3 / 6 + 1) pb4_0. Proof. reflexivity. Qed.
Lemma d5_def : d5 = fst pb4 + snd pb4 / 2 - 1. Proof. reflexivity. Qed.
Lemma pb5_1_def : pb5_1 = Kd_iter ((d5 - 1) / 3) pb_K0. Proof. reflexivity. Qed.
Lemma pa5_def : pa5 = Kc_full pb5_1. Proof. reflexivity. Qed.
Lemma pb6_0_def : pb6_0 = D_reload pa5. Proof. reflexivity. Qed.
Lemma pb6_def : pb6 = Kd_iter (snd pa5 / 6 + 1) pb6_0. Proof. reflexivity. Qed.
Lemma d7_def : d7 = fst pb6 + snd pb6 / 2 - 1. Proof. reflexivity. Qed.
Lemma pb7_1_def : pb7_1 = Kd_iter ((d7 - 2) / 3) pb_K0. Proof. reflexivity. Qed.
Lemma pa7_def : pa7 = Kc_full pb7_1. Proof. reflexivity. Qed.
Lemma D_reload_8_4_fst : fst (D_reload (8, 4)) = 7. Proof. reflexivity. Qed.

Opaque Kc Kc_full Kd_step Kd_iter D_reload pb_K0
  pb1_0 pb1_1 pa1 pb2_0 pb2 d3 pb3_1 pa3 pb4_0 pb4 d5 pb5_1 pa5 pb6_0 pb6 d7 pb7_1 pa7.

Lemma mod_81_27 : forall x, (x mod 81) mod 27 = x mod 27.
Proof. intros x. apply (mod_factor x 27 3). Qed.

Lemma mod_81_9 : forall x, (x mod 81) mod 9 = x mod 9.
Proof. intros x. apply (mod_factor x 9 9). Qed.

Lemma mod_81_3 : forall x, (x mod 81) mod 3 = x mod 3.
Proof. intros x. apply (mod_factor x 3 27). Qed.

Lemma run_pa1 :
  c0 -->* Ce (fst pa1) (snd pa1) 0 0 /\
  6 <= fst pa1 /\ fst pa1 mod 81 = 60 /\ snd pa1 mod 162 = 38.
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
  5 <= fst pb2 /\ fst pb2 mod 27 = 15 /\ snd pb2 mod 162 = 119.
Proof.
  destruct run_pa1 as [Hrun1 [Hp1 [Hm1 Ha1]]].
  rewrite !pb2_def, !pb2_0_def.
  destruct (mod162_38_props (snd pa1) Ha1) as [Ha1_ge [Ha1_ev [_ [_ [Hm_div Hd2]]]]].
  destruct (D_reload_all pa1 Hp1 Ha1_ge Ha1_ev) as [Hrel2 [Hp2_0 Hb2_0]].
  destruct (Kd_loop (snd pa1 / 6 + 1) 0 (D_reload pa1) Hp2_0 Hb2_0)
    as [Hloop2 [Hp2 [Hm2 Hb2]]].
  Transparent D_reload.
  assert (Hf0 : fst (D_reload pa1) = fst pa1 - 1) by (destruct pa1; reflexivity).
  Opaque D_reload.
  assert (Hp1_27 : fst pa1 mod 27 = 6) by (rewrite <- mod_81_27, Hm1; reflexivity).
  pose proof (pred_mod (fst pa1) 27 6 Hp1_27 ltac:(lia)) as Hp1_pred.
  split; [| split; [lia | split; [| exact Hb2]]].
  - follow Hrun1.
    eapply evstep_trans; [apply progress_evstep, Hrel2 |].
    rewrite Hd2. exact Hloop2.
  - rewrite <- mod_81_27, Hm2, mod_81_27, Hf0.
    rewrite <- Nat.Div0.add_mod_idemp_l, Hp1_pred.
    rewrite <- Nat.Div0.add_mod_idemp_r, <- Nat.Div0.mul_mod_idemp_r, Hm_div.
    reflexivity.
Qed.

Lemma run_pa3 :
  c0 -->* Ce (fst pa3) (snd pa3) 0 0 /\
  6 <= fst pa3 /\ fst pa3 mod 9 = 0 /\ snd pa3 mod 162 = 38.
Proof.
  destruct run_pb2 as [Hrun2 [Hp2 [Hm2 Hb2]]].
  rewrite !pa3_def, !pb3_1_def, !d3_def.
  destruct (K_reload_all pb2 Hp2 Hb2) as [Hrel3 [HpK [HfK HbK]]].
  set (d := fst pb2 + snd pb2 / 2 - 1) in *.
  destruct (mod162_119_props (snd pb2) Hb2) as [_ [_ Hb2_81]].
  assert (Hb2_div : (snd pb2 / 2) mod 27 = 5) by (rewrite <- mod_81_27, Hb2_81; reflexivity).
  pose proof (pred_mod (fst pb2) 27 15 Hm2 ltac:(lia)) as Hp2_pred.
  assert (Hd_mod : d mod 27 = 19).
  { replace d with ((fst pb2 - 1) + snd pb2 / 2) by (unfold d; lia).
    rewrite <- Nat.Div0.add_mod_idemp_l, Hp2_pred, <- Nat.Div0.add_mod_idemp_r, Hb2_div.
    reflexivity. }
  destruct (div3_props d 9 19 ltac:(lia) Hd_mod) as [Hd3 Hm_div].
  change (19 mod 3) with 1 in Hd3, Hm_div.
  change ((19 / 3) mod 9) with 6 in Hm_div.
  destruct (Kd_loop ((d - 1) / 3) 1 pb_K0 HpK HbK)
    as [Hloop3 [Hp3_1 [Hm3_1 Hb3_1]]].
  destruct (Kc_full_all 0 (Kd_iter ((d - 1) / 3) pb_K0) ltac:(lia) Hb3_1)
    as [Hkc3 [Hp3 [Hm3 Ha3]]].
  split; [| split; [lia | split; [| exact Ha3]]].
  - follow Hrun2.
    eapply evstep_trans; [apply progress_evstep, Hrel3 |].
    rewrite Hd3 at 1.
    follow Hloop3.
    apply progress_evstep, Hkc3.
  - rewrite <- mod_81_9, Hm3, <- Nat.Div0.add_mod_idemp_l, Hm3_1, Nat.Div0.add_mod_idemp_l, mod_81_9, HfK.
    replace (8 + 67 * ((d - 1) / 3) + 67) with (75 + 67 * ((d - 1) / 3)) by lia.
    rewrite <- Nat.Div0.add_mod_idemp_r, <- Nat.Div0.mul_mod_idemp_r, Hm_div.
    reflexivity.
Qed.

Lemma run_pb4 :
  c0 -->* Cd (fst pb4) (snd pb4) 0 /\
  5 <= fst pb4 /\ fst pb4 mod 9 = 0 /\ snd pb4 mod 162 = 119.
Proof.
  destruct run_pa3 as [Hrun3 [Hp3 [Hm3 Ha3]]].
  rewrite !pb4_def, !pb4_0_def.
  destruct (mod162_38_props (snd pa3) Ha3) as [Ha3_ge [Ha3_ev [_ [_ [Hm_27 Hd4]]]]].
  assert (Hm_div : (snd pa3 / 6 + 1) mod 9 = 7) by (rewrite <- (mod_factor _ 9 3); change (9 * 3) with 27; rewrite Hm_27; reflexivity).
  destruct (D_reload_all pa3 Hp3 Ha3_ge Ha3_ev) as [Hrel4 [Hp4_0 Hb4_0]].
  destruct (Kd_loop (snd pa3 / 6 + 1) 0 (D_reload pa3) Hp4_0 Hb4_0)
    as [Hloop4 [Hp4 [Hm4 Hb4]]].
  Transparent D_reload.
  assert (Hf0 : fst (D_reload pa3) = fst pa3 - 1) by (destruct pa3; reflexivity).
  Opaque D_reload.
  split; [| split; [lia | split; [| exact Hb4]]].
  - follow Hrun3.
    eapply evstep_trans; [apply progress_evstep, Hrel4 |].
    rewrite Hd4. exact Hloop4.
  - rewrite <- mod_81_9, Hm4, mod_81_9, Hf0.
    replace (fst pa3 - 1 + 67 * (snd pa3 / 6 + 1)) with (fst pa3 + (67 * (snd pa3 / 6 + 1) - 1)) by lia.
    rewrite <- Nat.Div0.add_mod_idemp_l, Hm3.
    assert (H67 : (67 * (snd pa3 / 6 + 1)) mod 9 = 1).
    { rewrite <- Nat.Div0.mul_mod_idemp_r, Hm_div. reflexivity. }
    pose proof (pred_mod (67 * (snd pa3 / 6 + 1)) 9 1 H67 ltac:(lia)) as Hpred.
    rewrite <- Nat.Div0.add_mod_idemp_r, Hpred. reflexivity.
Qed.

Lemma run_pa5 :
  c0 -->* Ce (fst pa5) (snd pa5) 0 0 /\
  6 <= fst pa5 /\ fst pa5 mod 3 = 1 /\ snd pa5 mod 162 = 38.
Proof.
  destruct run_pb4 as [Hrun4 [Hp4 [Hm4 Hb4]]].
  rewrite !pa5_def, !pb5_1_def, !d5_def.
  destruct (K_reload_all pb4 Hp4 Hb4) as [Hrel5 [HpK [HfK HbK]]].
  set (d := fst pb4 + snd pb4 / 2 - 1) in *.
  destruct (mod162_119_props (snd pb4) Hb4) as [_ [Hb4_ge Hb4_81]].
  assert (Hb4_div : (snd pb4 / 2) mod 9 = 5) by (rewrite <- mod_81_9, Hb4_81; reflexivity).
  pose proof (pred_mod (snd pb4 / 2) 9 5 Hb4_div ltac:(lia)) as Hb4_pred.
  assert (Hd_mod : d mod 9 = 4).
  { replace d with (fst pb4 + (snd pb4 / 2 - 1)) by (unfold d; lia).
    rewrite <- Nat.Div0.add_mod_idemp_l, Hm4, <- Nat.Div0.add_mod_idemp_r, Hb4_pred.
    reflexivity. }
  destruct (div3_props d 3 4 ltac:(lia) Hd_mod) as [Hd5 Hm_div].
  change (4 mod 3) with 1 in Hd5, Hm_div.
  change ((4 / 3) mod 3) with 1 in Hm_div.
  destruct (Kd_loop ((d - 1) / 3) 1 pb_K0 HpK HbK)
    as [Hloop5 [Hp5_1 [Hm5_1 Hb5_1]]].
  destruct (Kc_full_all 0 (Kd_iter ((d - 1) / 3) pb_K0) ltac:(lia) Hb5_1)
    as [Hkc5 [Hp5 [Hm5 Ha5]]].
  split; [| split; [lia | split; [| exact Ha5]]].
  - follow Hrun4.
    eapply evstep_trans; [apply progress_evstep, Hrel5 |].
    rewrite Hd5 at 1.
    follow Hloop5.
    apply progress_evstep, Hkc5.
  - rewrite <- mod_81_3, Hm5, <- Nat.Div0.add_mod_idemp_l, Hm5_1, Nat.Div0.add_mod_idemp_l, mod_81_3, HfK.
    replace (8 + 67 * ((d - 1) / 3) + 67) with (75 + 67 * ((d - 1) / 3)) by lia.
    rewrite <- Nat.Div0.add_mod_idemp_r, <- Nat.Div0.mul_mod_idemp_r, Hm_div.
    reflexivity.
Qed.

Lemma run_pb6 :
  c0 -->* Cd (fst pb6) (snd pb6) 0 /\
  5 <= fst pb6 /\ fst pb6 mod 3 = 1 /\ snd pb6 mod 162 = 119.
Proof.
  destruct run_pa5 as [Hrun5 [Hp5 [Hm5 Ha5]]].
  rewrite !pb6_def, !pb6_0_def.
  destruct (mod162_38_props (snd pa5) Ha5) as [Ha5_ge [Ha5_ev [_ [_ [Hm_27 Hd6]]]]].
  assert (Hm_div : (snd pa5 / 6 + 1) mod 3 = 1) by (rewrite <- (mod_factor _ 3 9); change (3 * 9) with 27; rewrite Hm_27; reflexivity).
  destruct (D_reload_all pa5 Hp5 Ha5_ge Ha5_ev) as [Hrel6 [Hp6_0 Hb6_0]].
  destruct (Kd_loop (snd pa5 / 6 + 1) 0 (D_reload pa5) Hp6_0 Hb6_0)
    as [Hloop6 [Hp6 [Hm6 Hb6]]].
  Transparent D_reload.
  assert (Hf0 : fst (D_reload pa5) = fst pa5 - 1) by (destruct pa5; reflexivity).
  Opaque D_reload.
  pose proof (pred_mod (fst pa5) 3 1 Hm5 ltac:(lia)) as Hp5_pred.
  split; [| split; [lia | split; [| exact Hb6]]].
  - follow Hrun5.
    eapply evstep_trans; [apply progress_evstep, Hrel6 |].
    rewrite Hd6. exact Hloop6.
  - rewrite <- mod_81_3, Hm6, mod_81_3, Hf0.
    rewrite <- Nat.Div0.add_mod_idemp_l, Hp5_pred.
    rewrite <- Nat.Div0.add_mod_idemp_r, <- Nat.Div0.mul_mod_idemp_r, Hm_div.
    reflexivity.
Qed.

Lemma run_pa7 :
  c0 -->* c_end (fst pa7) (snd pa7).
Proof.
  destruct run_pb6 as [Hrun6 [Hp6 [Hm6 Hb6]]].
  rewrite !pa7_def, !pb7_1_def, !d7_def.
  destruct (K_reload_all pb6 Hp6 Hb6) as [Hrel7 [HpK [HfK HbK]]].
  set (d := fst pb6 + snd pb6 / 2 - 1) in *.
  destruct (mod162_119_props (snd pb6) Hb6) as [_ [_ Hb6_81]].
  assert (Hb6_div : (snd pb6 / 2) mod 3 = 2) by (rewrite <- mod_81_3, Hb6_81; reflexivity).
  pose proof (pred_mod (fst pb6) 3 1 Hm6 ltac:(lia)) as Hp6_pred.
  assert (Hd_mod : d mod (3 * 1) = 2).
  { change (3 * 1) with 3.
    replace d with ((fst pb6 - 1) + snd pb6 / 2) by (unfold d; lia).
    rewrite <- Nat.Div0.add_mod_idemp_l, Hp6_pred, <- Nat.Div0.add_mod_idemp_r, Hb6_div.
    reflexivity. }
  destruct (div3_props d 1 2 ltac:(lia) Hd_mod) as [Hd7 _].
  change (2 mod 3) with 2 in Hd7.
  destruct (Kd_loop ((d - 2) / 3) 2 pb_K0 HpK HbK)
    as [Hloop7 [Hp7_1 [_ Hb7_1]]].
  destruct (Kc_full_all 1 (Kd_iter ((d - 2) / 3) pb_K0) ltac:(lia) Hb7_1)
    as [Hkc7 _].
  follow Hrun6.
  eapply evstep_trans; [apply progress_evstep, Hrel7 |].
  rewrite Hd7 at 1.
  follow Hloop7.
  eapply evstep_trans; [apply progress_evstep, Hkc7 |].
  apply progress_evstep, HALT_step.
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run_pa7) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply c_end_halted.
Qed.
