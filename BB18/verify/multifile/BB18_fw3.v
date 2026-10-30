(** * An 18-state f_(omega+3) halter built on Argon's BB16_fw4 stack-reflection engine *)

(* machine: 1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_1RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RQ0RG_0LG1LP_0LO1LP_1LQ0RR_1RZ0LP *)

(** The 16-state engine table of BB16_fw4.v is unchanged except N0, which now runs a two-state counter
    routine (QQ, RR = the letters Q, R of the machine string). N0 is read only at the start of a reflection pass.
    - Pass 1 start: the routine erases I's 1 at h+2 and plants a marker 1 at h+4, then the reflection runs as
      usual. Pass 1 runs in full (an f_(omega+3) growth step); the reload puts the next pass start at the same h.
    - Pass 2 start: QQ reads the marker, RR reads 0: halt.
    R0 (written 1RZ in the machine string) is the halt: [tm (RR, 0) = None]. It is read on a 0, so the standard
    score is sigma = N + 1, where N is the number of ones of the halted configuration.
    Main results (no axioms):
      [score_exact]: N = fst (Kpass1 pa_init) + snd (Kpass1 pa_init) + 5;
      [halt : halts tm c0];
      [sigma_lower_bound]: the halting tape holds N ones with f_omega2 (f_omega3 114) < N;
      [sigma_lower_bound_fw3]: ... f_omega3 114 < N.
    f is the standard fast-growing hierarchy: f 0 = S, f (S k) n = (f k)^n (n), f_omega n = f n n,
    f_omega1 n = f_omega^n (n), f_omega2 n = f_omega1^n (n), f_omega3 n = f_omega2^n (n). *)

From BB8 Require Import Individual182.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.L, B)  | A, 1 => Some (1, TM.L, A)
  | B, 0 => Some (1, TM.R, C)  | B, 1 => Some (0, TM.L, A)
  | C, 0 => Some (1, TM.R, D)  | C, 1 => Some (1, TM.R, C)
  | D, 0 => Some (1, TM.R, E)  | D, 1 => Some (1, TM.R, K)
  | E, 0 => Some (1, TM.R, F)  | E, 1 => Some (0, TM.L, J)
  | F, 0 => Some (1, TM.L, G)  | F, 1 => Some (1, TM.R, I)
  | G, 0 => Some (1, TM.R, M)  | G, 1 => Some (0, TM.L, M)
  | H, 0 => Some (1, TM.L, G)  | H, 1 => Some (0, TM.R, C)
  | I, 0 => Some (1, TM.R, N)  | I, 1 => Some (0, TM.L, E)
  | J, 0 => Some (1, TM.L, A)  | J, 1 => Some (1, TM.L, E)
  | K, 0 => Some (0, TM.L, L)  | K, 1 => Some (1, TM.L, B)
  | L, 0 => Some (0, TM.R, M)  | L, 1 => Some (1, TM.L, L)
  | M, 0 => Some (1, TM.L, F)  | M, 1 => Some (1, TM.R, H)
  | N, 0 => Some (0, TM.R, QQ) | N, 1 => Some (0, TM.R, G)
  | O, 0 => Some (0, TM.L, G)  | O, 1 => Some (1, TM.L, P)
  | P, 0 => Some (0, TM.L, O)  | P, 1 => Some (1, TM.L, P)
  | QQ, 0 => Some (1, TM.L, QQ) | QQ, 1 => Some (0, TM.R, RR)
  | RR, 0 => None               | RR, 1 => Some (0, TM.L, P)
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
  - replace (2 * S m) with (S (S (2 * m))) by lia. cbn [lpow]. rewrite IHm, app_assoc. reflexivity.
Qed.

(** ** Basic shift lemmas *)

Lemma cr_CR_1_1 : forall n l r, l {{C}}> [1]^^n *> r -->* [1]^^n *> l {{C}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_LL_1_1 : forall n l r, [1]^^n *> l <{{L}} r -->* l <{{L}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_AL_1_1 : forall n l r, [1]^^n *> l <{{A}} r -->* l <{{A}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_AL_01_01 : forall n l r, [0; 1]^^n *> l <{{A}} r -->* l <{{A}} [0; 1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_EL_11_10 : forall n l r, [1; 1]^^n *> l <{{E}} r -->* l <{{E}} [1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_ML_1_1 : forall n l r,
  ([1]^^n *> l) <{{M}} (0 >> r) -->* l <{{M}} (0 >> [1]^^n *> r).
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_PL_1_1 : forall n l r, [1]^^n *> l <{{P}} r -->* l <{{P}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_PL_01_10 : forall n l r, [0; 1]^^n *> l <{{P}} r -->* l <{{P}} [1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** ** Configurations and inner cascade rules *)

Definition Ca (j b : nat) (z : side) : Q * tape :=
  ([1]^^b *> [0; 1]^^j *> const 0) {{C}}> (0 >> z).

Definition Ch (j b : nat) (z : side) : Q * tape :=
  ([0; 1]^^j *> const 0) <{{A}} (1 >> [1]^^b *> 0 >> z).

Definition Ce_gen (p a c : nat) (r : side) : Q * tape :=
  ([1]^^(a + 2) *> [0; 1]^^p *> const 0) {{E}}> ([1; 0]^^c *> 0 >> r).

Definition blk (a : nat) (z : side) : side :=
  1 >> [1]^^a *> 0 >> z.

Lemma CA_SH : forall j b z,
  Ca j b (1 >> 0 >> z) -->+ Ca (S j) b z.
Proof.
  intros j b z. unfold Ca.
  start_progress.
  follow cr_LL_1_1.
  align_tape.
  execute.
  follow cr_CR_1_1.
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
  Ca j b (0 >> z) -->+ ([1]^^(b + 2) *> [0; 1]^^j *> const 0) {{E}}> z.
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
  follow cr_AL_1_1.
  finish_norm.
Qed.

Lemma CH_0 : forall b z,
  Ch 0 b z -->+ Ca 0 (b + 3) z.
Proof.
  intros b z. unfold Ch, Ca. simpl lpow.
  start_progress.
  follow cr_CR_1_1.
  finish_norm.
Qed.

Lemma CH_S_aux : forall j b z,
  Ch (S j) b z -->+ Ca 0 2 ([1; 0]^^j *> blk (S b) z).
Proof.
  intros j b z. unfold Ch, Ca, blk.
  start_progress.
  follow cr_AL_01_01.
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
  ([1]^^(2 * k + 2) *> [0; 1]^^(S p') *> const 0) {{E}}> (1 >> 0 >> r) -->+
  Ch p' 1 ([1; 0]^^(S k) *> 0 >> r).
Proof.
  intros p' k r. unfold Ch.
  replace (2 * k + 2)%nat with (1 + (2 * k + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_EL_11_10.
  execute; finish_norm.
Qed.

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

Fixpoint W (j : nat) (b : nat) : nat :=
  match j with
  | 0 => b + 3
  | S j' => iter (S b) (W j') 2
  end.

Lemma W_0 : forall b, W 0 b = b + 3.
Proof. reflexivity. Qed.

Lemma W_S : forall j b, W (S j) b = iter (S b) (W j) 2.
Proof. reflexivity. Qed.

Lemma W_0_1 : W 0 1 = 4.
Proof. reflexivity. Qed.

Lemma W_2_1 : W 2 1 = 38.
Proof. reflexivity. Qed.

Lemma iter1_W0_3 : iter 1 (W 0) 3 = 6.
Proof. reflexivity. Qed.

Lemma iter3_W1_6 : iter 3 (W 1) 6 = 227.
Proof. reflexivity. Qed.

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

Opaque W.

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

(** ** Generalized Level 1 and Reload transitions *)

Lemma CE_EVEN : forall p' k c r,
  Ce_gen (S p') (2 * k) (S c) r -->+ Ce_gen (p' + S k) (W p' 1) c r.
Proof.
  intros p' k c r. unfold Ce_gen.
  cbn [lpow Str_app].
  eapply progress_evstep_trans; [apply E_EVEN |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  follow (CA_SH_iter (S k) p' (W p' 1) (0 >> [1; 0]^^c *> 0 >> r)%sym).
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma D1_REL_gen_aux : forall p' a r,
  Ce_gen (S (S p')) a 0 (0 >> r)%sym -->+
  Ch p' 1 (0 >> 0 >> [1]^^(a + 3) *> r)%sym.
Proof.
  intros p' a r. unfold Ce_gen, Ch. cbn [lpow Str_app].
  start_progress.
  follow cr_ML_1_1.
  execute; finish_norm.
Qed.

Lemma D1_REL_gen : forall p' a r,
  Ce_gen (S (S p')) a 0 (0 >> r)%sym -->+
  Ce_gen p' (W p' 1) 0 ([1]^^(a + 3) *> r)%sym.
Proof.
  intros p' a r.
  eapply progress_evstep_trans; [apply D1_REL_gen_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  unfold Ce_gen. cbn [lpow Str_app]. finish_norm.
Qed.

(** ** D1_STEP sub-lemmas *)

Lemma D1_STEP_part1_aux : forall p k' d r,
  Ce_gen (S (S (S p))) (2 * k' + 4) 0 ([1]^^(S (S d)) *> r)%sym -->+
  Ch (S p) 4 (0 >> 0 >> 1 >> 1 >> [1; 0]^^(S k') *> 0 >> [1]^^d *> r)%sym.
Proof.
  intros p k' d r. unfold Ce_gen, Ch.
  replace (2 * k' + 4 + 2) with (2 * k' + 6) by lia.
  rewrite lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1]%sym k'). cbn [app].
  start_progress.
  follow cr_EL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma D1_STEP_part1 : forall p k' d r,
  Ce_gen (S (S (S p))) (2 * k' + 4) 0 ([1]^^(S (S d)) *> r)%sym -->+
  Ce_gen (S p) (W (S p) 4) 0 (1 >> 1 >> [1; 0]^^(S k') *> 0 >> [1]^^d *> r)%sym.
Proof.
  intros p k' d r.
  eapply progress_evstep_trans; [apply D1_STEP_part1_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  unfold Ce_gen. cbn [lpow Str_app]. finish_norm.
Qed.

Lemma D1_STEP_part2_aux : forall p m r,
  Ce_gen (S p) (2 * m + 1) 0 (1 >> 1 >> r)%sym -->+
  Ch p 1 ([1; 0]^^(S (S m)) *> 0 >> r)%sym.
Proof.
  intros p m r. unfold Ce_gen, Ch.
  replace (2 * m + 1 + 2) with (2 * m + 3) by lia.
  rewrite lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1]%sym m). cbn [app].
  start_progress.
  follow cr_EL_11_10.
  execute; finish_norm.
Qed.

Lemma D1_STEP_part2 : forall p m k' d r,
  Ce_gen (S p) (2 * m + 1) 0 (1 >> 1 >> [1; 0]^^(S k') *> 0 >> [1]^^d *> r)%sym -->+
  Ce_gen (p + S (S m)) (W p 1) (S k') ([1]^^d *> r)%sym.
Proof.
  intros p m k' d r.
  eapply progress_evstep_trans; [apply D1_STEP_part2_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  follow (CA_SH_iter (S (S m)) p (W p 1) (0 >> [1; 0]^^(S k') *> 0 >> [1]^^d *> r)%sym).
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  unfold Ce_gen. finish_norm.
Qed.

(** ** Stack-reflection (LEFT_DUMP) and Initial Bootstrap *)

Lemma P_DUMP_raw : forall p a,
  Ce_gen p a 0 ([1]^^1 *> const 0)%sym -->+
  (const 0)%sym <{{P}} ([1; 0]^^p *> [1]^^(a + 4) *> 0 >> 0 >> 1 >> const 0)%sym.
Proof.
  intros p a. unfold Ce_gen. cbn [lpow Str_app].
  start_progress.
  follow cr_PL_1_1.
  execute.
  follow cr_PL_01_10.
  finish_norm.
Qed.

Lemma P_BOOT_141 : forall z,
  (const 0)%sym <{{P}} ([1; 0]^^3 *> z)%sym -->+
  Ce_gen 3 4 1 (0 >> 1 >> 1 >> z)%sym.
Proof.
  intros z. unfold Ce_gen. cbn [lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 140 step. finish_norm.
Qed.

Lemma P_BOOT : forall z,
  (const 0)%sym <{{P}} ([1; 0]^^3 *> z)%sym -->+
  Ce_gen 3 (W 3 1) 0 ([1]^^41 *> 1 >> 1 >> z)%sym.
Proof.
  intros z.
  eapply progress_evstep_trans; [apply P_BOOT_141 |].
  eapply evstep_trans; [apply progress_evstep, (CE_EVEN 2 2 0 (0 >> 1 >> 1 >> z)%sym) |].
  change (2 + 3) with 5. rewrite W_2_1.
  eapply evstep_trans; [apply progress_evstep, (D1_REL_gen 3 38 (1 >> 1 >> z)%sym) |].
  change (38 + 3) with 41.
  apply evstep_refl.
Qed.

Lemma lpow_10_S : forall j y,
  ([1; 0]^^(S j) *> y)%sym = (1 >> [0; 1]^^j *> 0 >> y)%sym.
Proof.
  intros j y. cbn [lpow Str_app]. align_tape. reflexivity.
Qed.

Lemma P_DUMP_boot : forall j a,
  Ce_gen (j + 4) a 0 ([1]^^1 *> const 0)%sym -->+
  Ce_gen 3 (W 3 1) 0 ([1]^^44 *> [0; 1]^^j *> 0 >> [1]^^(a + 4) *> 0 >> 0 >> 1 >> const 0)%sym.
Proof.
  intros j a.
  eapply progress_evstep_trans; [apply P_DUMP_raw |].
  replace (j + 4) with (3 + S j) by lia.
  rewrite lpow_add, Str_app_assoc.
  rewrite (lpow_10_S j ([1]^^(a + 4) *> 0 >> 0 >> 1 >> const 0)%sym).
  eapply evstep_trans; [apply progress_evstep, P_BOOT |].
  unfold Ce_gen. finish_norm.
Qed.

(** ** Initial entry from blank tape c0 *)

Lemma init_37 : c0 -->* Ca 0 3 (blk 1 (blk 3 (0 >> 0 >> 0 >> const 0)%sym)).
Proof.
  unfold Ca, blk. cbn [lpow Str_app].
  do 37 step. autorewrite with tape_post. finish_norm.
Qed.

Lemma init_ce0 : c0 -->* Ce_gen 0 4 0 ([1]^^230 *> const 0)%sym.
Proof.
  eapply evstep_trans; [apply init_37 |].
  eapply evstep_trans; [apply progress_evstep, (BLK_iter_aux 0 (CH_CA 0) 1 3) |].
  rewrite iter1_W0_3.
  eapply evstep_trans; [apply progress_evstep, (BLK_iter_aux 1 (CH_CA 1) 3 6) |].
  rewrite iter3_W1_6.
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  eapply evstep_trans; [apply progress_evstep, (D1_REL_gen 0 227 (const 0)%sym) |].
  rewrite W_0_1. change (227 + 3) with 230.
  apply evstep_refl.
Qed.

Lemma init_116 : forall r,
  Ce_gen 0 4 0 (1 >> 1 >> r)%sym -->+
  Ce_gen 3 4 1 r.
Proof.
  intros r. unfold Ce_gen. cbn [lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 115 step. finish_norm.
Qed.

Lemma lpow_230_228 :
  ([1]^^230 *> const 0)%sym = (1 >> 1 >> [1]^^228 *> const 0)%sym.
Proof.
  change 230 with (2 + 228). rewrite lpow_add. reflexivity.
Qed.

Lemma init_ce : c0 -->* Ce_gen 5 38 0 ([1]^^228 *> const 0)%sym.
Proof.
  eapply evstep_trans; [apply init_ce0 |].
  rewrite lpow_230_228.
  eapply evstep_trans; [apply progress_evstep, init_116 |].
  eapply evstep_trans; [apply progress_evstep, (CE_EVEN 2 2 0 ([1]^^228 *> const 0)%sym) |].
  change (2 + 3) with 5. rewrite W_2_1.
  apply evstep_refl.
Qed.

(** ** Multi-level hierarchy loops *)

(** *** Level 1: Kc_loop (c-counter) *)

Definition Kc (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  (p + a / 2, W (p - 1) 1).

Lemma Kc_step : forall c r pa,
  1 <= fst pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) (S c) r -->+ Ce_gen (fst (Kc pa)) (snd (Kc pa)) c r.
Proof.
  intros c r [p a] Hp Hev. cbn [fst snd Kc] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  assert (Ha : a = 2 * (a / 2)) by (mods; lia).
  replace (S p' + a / 2) with (p' + S (a / 2)) by lia.
  rewrite Ha at 1.
  apply CE_EVEN.
Qed.

Lemma Kc_props : forall pa,
  1 <= fst pa -> 2 <= snd pa -> snd pa mod 2 = 0 ->
  fst pa + 1 <= fst (Kc pa) /\
  4 <= snd (Kc pa) /\
  snd (Kc pa) mod 2 = 0.
Proof.
  intros [p a] Hp Ha Hev. cbn [fst snd Kc] in *.
  pose proof (W_grow (p - 1) 1).
  pose proof (W_par (p - 1) 1).
  split; [| split]; mods; lia.
Qed.

Lemma Kc_loop : forall c r pa,
  1 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) c r -->* Ce_gen (fst (iter c Kc pa)) (snd (iter c Kc pa)) 0 r /\
  fst pa + c <= fst (iter c Kc pa) /\
  4 <= snd (iter c Kc pa) /\
  snd (iter c Kc pa) mod 2 = 0.
Proof.
  induction c as [| c IHc]; intros r pa Hp Ha Hev.
  - cbn [iter]. split; [finish | split; [lia | split; [lia | exact Hev]]].
  - rewrite iter_S'.
    destruct (Kc_props pa Hp ltac:(lia) Hev) as [Hp1 [Ha1 Hm1]].
    destruct (IHc r (Kc pa) ltac:(lia) Ha1 Hm1) as [Hrun [Hp2 [Ha2 Hm2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, (Kc_step c r pa Hp Hev) | exact Hrun].
    + lia.
    + exact Ha2.
    + exact Hm2.
Qed.

(** *** Level 2: Kd1_loop (d1-counter) *)

Definition Kd1_init (p : nat) : nat * nat :=
  (p - 3 + S (S (W (p - 2) 4 / 2)), W (p - 3) 1).

Lemma Kd1_init_props : forall p,
  3 <= p ->
  p + 2 <= fst (Kd1_init p) /\
  4 <= snd (Kd1_init p) /\
  snd (Kd1_init p) mod 2 = 0.
Proof.
  intros p Hp. unfold Kd1_init. cbn [fst snd].
  pose proof (W_grow (p - 2) 4) as Hw4.
  pose proof (W_grow (p - 3) 1) as Hw1.
  pose proof (W_par (p - 3) 1) as Hp1.
  set (w4 := W (p - 2) 4) in *.
  set (w1 := W (p - 3) 1) in *.
  split; [| split]; mods; lia.
Qed.

Definition Kd1_step (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  iter (a / 2 - 1) Kc (Kd1_init p).

Lemma Kd1_step_all : forall d r pa,
  3 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 ([1]^^(S (S d)) *> r)%sym -->+
    Ce_gen (fst (Kd1_step pa)) (snd (Kd1_step pa)) 0 ([1]^^d *> r)%sym /\
  fst pa + 2 <= fst (Kd1_step pa) /\
  4 <= snd (Kd1_step pa) /\
  snd (Kd1_step pa) mod 2 = 0.
Proof.
  intros d r [p a] Hp Ha Hev. cbn [fst snd Kd1_step] in *.
  destruct (Kd1_init_props p Hp) as [Hip [Hia Him]].
  destruct (Kc_loop (a / 2 - 1) ([1]^^d *> r)%sym (Kd1_init p) ltac:(lia) Hia Him)
    as [Hrun [Hp1 [Ha1 Hm1]]].
  destruct p as [| [| [| p']]]; try lia.
  assert (Ha_eq : a = 2 * (a / 2 - 2) + 4) by (mods; lia).
  assert (Hk_eq : a / 2 - 1 = S (a / 2 - 2)) by (mods; lia).
  pose proof (W_par (S p') 4) as Hwp4.
  assert (Hw4_eq : W (S p') 4 = 2 * (W (S p') 4 / 2) + 1)
    by (set (w4 := W (S p') 4) in *; mods; lia).
  split; [| split; [| split]].
  - rewrite Ha_eq at 1.
    eapply progress_evstep_trans; [apply D1_STEP_part1 |].
    rewrite Hw4_eq.
    eapply evstep_trans; [apply progress_evstep, D1_STEP_part2 |].
    rewrite <- Hk_eq.
    replace (p' + S (S (W (S p') 4 / 2))) with (fst (Kd1_init (S (S (S p')))))
      by (unfold Kd1_init; cbn [fst]; f_equal; lia).
    replace (W p' 1) with (snd (Kd1_init (S (S (S p')))))
      by (unfold Kd1_init; cbn [snd]; f_equal; lia).
    exact Hrun.
  - lia.
  - exact Ha1.
  - exact Hm1.
Qed.

Definition Kd1_iter (m1 : nat) (pa : nat * nat) : nat * nat :=
  iter m1 Kd1_step pa.

Lemma Kd1_loop : forall m1 d r pa,
  3 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 ([1]^^(2 * m1 + d) *> r)%sym -->*
    Ce_gen (fst (Kd1_iter m1 pa)) (snd (Kd1_iter m1 pa)) 0 ([1]^^d *> r)%sym /\
  fst pa + 2 * m1 <= fst (Kd1_iter m1 pa) /\
  4 <= snd (Kd1_iter m1 pa) /\
  snd (Kd1_iter m1 pa) mod 2 = 0.
Proof.
  unfold Kd1_iter.
  induction m1 as [| m1 IHm1]; intros d r pa Hp Ha Hev.
  - cbn [iter]. replace (2 * 0 + d) with d by lia.
    split; [finish | split; [lia | split; [lia | exact Hev]]].
  - rewrite iter_S'.
    replace (2 * S m1 + d) with (S (S (2 * m1 + d))) by lia.
    destruct (Kd1_step_all (2 * m1 + d) r pa Hp Ha Hev) as [Hstep [Hp1 [Ha1 Hm1]]].
    destruct (IHm1 d r (Kd1_step pa) ltac:(lia) Ha1 Hm1) as [Hrun [Hp2 [Ha2 Hm2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, Hstep | exact Hrun].
    + lia.
    + exact Ha2.
    + exact Hm2.
Qed.

(** *** Level 3: Krel_even, Kd2_step, Kd2_loop, and Krel_odd *)

Definition Krel_even (k : nat) (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  Kd1_iter (a / 2 + k + 2) (p - 2, W (p - 2) 1).

Lemma Krel_even_all : forall k r pa,
  5 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 (0 >> [1]^^(2 * k + 1) *> r)%sym -->+
    Ce_gen (fst (Krel_even k pa)) (snd (Krel_even k pa)) 0 r /\
  fst pa + 2 <= fst (Krel_even k pa) /\
  4 <= snd (Krel_even k pa) /\
  snd (Krel_even k pa) mod 2 = 0.
Proof.
  intros k r [p a] Hp Ha Hev. cbn [fst snd Krel_even] in *.
  destruct p as [| [| p']]; [lia | lia |].
  replace (S (S p') - 2) with p' by lia.
  assert (Ha_ev : (a + 3) + (2 * k + 1) = 2 * (a / 2 + k + 2) + 0) by (mods; lia).
  assert (Ha_div : 2 <= a / 2) by (mods; lia).
  pose proof (W_grow p' 1) as Hwg.
  pose proof (W_par p' 1) as Hwp.
  assert (Hwm : W p' 1 mod 2 = 0) by (mods; lia).
  destruct (Kd1_loop (a / 2 + k + 2) 0 r (p', W p' 1) ltac:(cbn; lia) ltac:(cbn; lia) Hwm)
    as [Hrun [Hp1 [Ha1 Hm1]]].
  cbn [fst snd] in *.
  split; [| split; [| split]].
  - eapply progress_evstep_trans; [apply D1_REL_gen |].
    rewrite <- Str_app_assoc, <- lpow_add, Ha_ev.
    exact Hrun.
  - lia.
  - exact Ha1.
  - exact Hm1.
Qed.

Definition Kd2_step (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  Kd1_iter (a / 2 + 2) (p - 2, W (p - 2) 1).

Lemma Kd2_step_eq_Krel_even : forall pa,
  Kd2_step pa = Krel_even 0 pa.
Proof.
  intros [p a]. unfold Kd2_step, Krel_even.
  replace (a / 2 + 0 + 2) with (a / 2 + 2) by lia.
  reflexivity.
Qed.

Lemma Kd2_step_all : forall r pa,
  5 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 (0 >> 1 >> r)%sym -->+
    Ce_gen (fst (Kd2_step pa)) (snd (Kd2_step pa)) 0 r /\
  fst pa + 2 <= fst (Kd2_step pa) /\
  4 <= snd (Kd2_step pa) /\
  snd (Kd2_step pa) mod 2 = 0.
Proof.
  intros r pa Hp Ha Hev.
  rewrite !Kd2_step_eq_Krel_even.
  exact (Krel_even_all 0 r pa Hp Ha Hev).
Qed.

Definition Kd2_iter (m2 : nat) (pa : nat * nat) : nat * nat :=
  iter m2 Kd2_step pa.

Theorem Kd2_loop : forall m2 r pa,
  5 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 ([0; 1]^^m2 *> r)%sym -->*
    Ce_gen (fst (Kd2_iter m2 pa)) (snd (Kd2_iter m2 pa)) 0 r /\
  fst pa + 2 * m2 <= fst (Kd2_iter m2 pa) /\
  4 <= snd (Kd2_iter m2 pa) /\
  snd (Kd2_iter m2 pa) mod 2 = 0.
Proof.
  unfold Kd2_iter.
  induction m2 as [| m2 IHm2]; intros r pa Hp Ha Hev.
  - cbn [iter lpow Str_app].
    split; [finish | split; [lia | split; [lia | exact Hev]]].
  - rewrite iter_S'. cbn [lpow Str_app].
    destruct (Kd2_step_all ([0; 1]^^m2 *> r)%sym pa Hp Ha Hev) as [Hstep [Hp1 [Ha1 Hm1]]].
    destruct (IHm2 r (Kd2_step pa) ltac:(lia) Ha1 Hm1) as [Hrun [Hp2 [Ha2 Hm2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, Hstep | exact Hrun].
    + lia.
    + exact Ha2.
    + exact Hm2.
Qed.

Definition Krel_odd (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  Kd1_iter (a / 2 + 1) (p - 2, W (p - 2) 1).

Lemma Krel_odd_all : forall pa,
  5 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 (const 0)%sym -->+
    Ce_gen (fst (Krel_odd pa)) (snd (Krel_odd pa)) 0 ([1]^^1 *> const 0)%sym /\
  fst pa + 2 <= fst (Krel_odd pa) /\
  4 <= snd (Krel_odd pa) /\
  snd (Krel_odd pa) mod 2 = 0.
Proof.
  intros [p a] Hp Ha Hev. cbn [fst snd Krel_odd] in *.
  destruct p as [| [| p']]; [lia | lia |].
  replace (S (S p') - 2) with p' by lia.
  assert (Ha_odd : a + 3 = 2 * (a / 2 + 1) + 1) by (mods; lia).
  assert (Ha_div : 2 <= a / 2) by (mods; lia).
  pose proof (W_grow p' 1) as Hwg.
  pose proof (W_par p' 1) as Hwp.
  assert (Hwm : W p' 1 mod 2 = 0) by (mods; lia).
  destruct (Kd1_loop (a / 2 + 1) 1 (const 0)%sym (p', W p' 1) ltac:(cbn; lia) ltac:(cbn; lia) Hwm)
    as [Hrun [Hp1 [Ha1 Hm1]]].
  cbn [fst snd] in *.
  split; [| split; [| split]].
  - rewrite (@const_unfold Sym 0%sym) at 1.
    eapply progress_evstep_trans; [apply D1_REL_gen |].
    rewrite Ha_odd.
    exact Hrun.
  - lia.
  - exact Ha1.
  - exact Hm1.
Qed.

(** *** Level 4: the stack-reflection pass (BB16_fw4 iterates it forever; here it runs once) *)

Lemma Kc_unfold : forall p a,
  Kc (p, a) = (p + a / 2, W (p - 1) 1).
Proof. reflexivity. Qed.

Lemma Kd1_step_unfold : forall p a,
  Kd1_step (p, a) = iter (a / 2 - 1) Kc (Kd1_init p).
Proof. reflexivity. Qed.

Lemma Kd1_iter_unfold : forall m1 pa,
  Kd1_iter m1 pa = iter m1 Kd1_step pa.
Proof. reflexivity. Qed.

Lemma Krel_even_unfold : forall k p a,
  Krel_even k (p, a) = Kd1_iter (a / 2 + k + 2) (p - 2, W (p - 2) 1).
Proof. reflexivity. Qed.

Lemma Kd2_step_unfold : forall p a,
  Kd2_step (p, a) = Kd1_iter (a / 2 + 2) (p - 2, W (p - 2) 1).
Proof. reflexivity. Qed.

Lemma Kd2_iter_unfold : forall m2 pa,
  Kd2_iter m2 pa = iter m2 Kd2_step pa.
Proof. reflexivity. Qed.

Lemma Krel_odd_unfold : forall p a,
  Krel_odd (p, a) = Kd1_iter (a / 2 + 1) (p - 2, W (p - 2) 1).
Proof. reflexivity. Qed.

Opaque Kc Kd1_init Kd1_step Kd1_iter Krel_even Kd2_step Kd2_iter Krel_odd.

Definition pa_dump0 : nat * nat :=
  Kd1_iter 22 (3, W 3 1).

Lemma pa_dump0_unfold :
  pa_dump0 = Kd1_iter 22 (3, W 3 1).
Proof. reflexivity. Qed.

Lemma pa_dump0_props :
  47 <= fst pa_dump0 /\
  4 <= snd pa_dump0 /\
  snd pa_dump0 mod 2 = 0 /\
  forall r,
    Ce_gen 3 (W 3 1) 0 ([1]^^44 *> r)%sym -->*
    Ce_gen (fst pa_dump0) (snd pa_dump0) 0 r.
Proof.
  pose proof (W_grow 3 1) as Hwg.
  pose proof (W_par 3 1) as Hwp.
  assert (H3 : 3 <= fst (3, W 3 1)) by apply Nat.le_refl.
  destruct (Kd1_loop 22 0 (const 0)%sym (3, W 3 1) H3 Hwg Hwp)
    as [_ [Hp1 [Ha1 Hm1]]].
  change (fst (3, W 3 1) + 2 * 22) with 47 in Hp1.
  fold pa_dump0 in Hp1, Ha1, Hm1.
  split; [exact Hp1 | split; [exact Ha1 | split; [exact Hm1 |]]].
  intros r.
  destruct (Kd1_loop 22 0 r (3, W 3 1) H3 Hwg Hwp)
    as [Hrun _].
  change (fst (3, W 3 1)) with 3 in Hrun.
  change (snd (3, W 3 1)) with (W 3 1) in Hrun.
  change (2 * 22 + 0) with 44 in Hrun.
  change ([1]^^0 *> r)%sym with r in Hrun.
  fold pa_dump0 in Hrun.
  exact Hrun.
Qed.

Opaque pa_dump0.

(** *** The single counted pass: reload over an even block (Krel_x), then Kpass1 *)

Definition Krel_x (k : nat) (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  Kd1_iter (a / 2 + k + 1) (p - 2, W (p - 2) 1).

Lemma Krel_x_unfold : forall k p a,
  Krel_x k (p, a) = Kd1_iter (a / 2 + k + 1) (p - 2, W (p - 2) 1).
Proof. reflexivity. Qed.

Lemma Krel_x_all : forall k r pa,
  5 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 (0 >> [1]^^(2 * k) *> r)%sym -->+
    Ce_gen (fst (Krel_x k pa)) (snd (Krel_x k pa)) 0 ([1]^^1 *> r)%sym /\
  fst pa + 2 <= fst (Krel_x k pa) /\
  4 <= snd (Krel_x k pa) /\
  snd (Krel_x k pa) mod 2 = 0.
Proof.
  intros k r [p a] Hp Ha Hev. rewrite Krel_x_unfold. cbn [fst snd] in *.
  destruct p as [| [| p']]; [lia | lia |].
  replace (S (S p') - 2) with p' by lia.
  assert (Ha_odd : (a + 3) + 2 * k = 2 * (a / 2 + k + 1) + 1) by (mods; lia).
  pose proof (W_grow p' 1) as Hwg.
  pose proof (W_par p' 1) as Hwp.
  assert (Hwm : W p' 1 mod 2 = 0) by (mods; lia).
  destruct (Kd1_loop (a / 2 + k + 1) 1 r (p', W p' 1) ltac:(cbn; lia) ltac:(cbn; lia) Hwm)
    as [Hrun [Hp1 [Ha1 Hm1]]].
  cbn [fst snd] in *.
  split; [| split; [| split]].
  - eapply progress_evstep_trans; [apply D1_REL_gen |].
    rewrite <- Str_app_assoc, <- lpow_add, Ha_odd.
    exact Hrun.
  - lia.
  - exact Ha1.
  - exact Hm1.
Qed.

Opaque Krel_x.

Definition Kpass1 (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  Krel_x (a / 2 + 2) (Kd2_iter (p - 4) pa_dump0).

Lemma Kpass1_unfold : forall p a,
  Kpass1 (p, a) = Krel_x (a / 2 + 2) (Kd2_iter (p - 4) pa_dump0).
Proof. reflexivity. Qed.

Lemma Kpass1_all : forall pa,
  5 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 ([1]^^1 *> const 0)%sym -->+
    Ce_gen (fst (Kpass1 pa)) (snd (Kpass1 pa)) 0 ([1]^^1 *> 0 >> 0 >> 1 >> const 0)%sym.
Proof.
  intros [p a] Hp Ha Hev. rewrite Kpass1_unfold. cbn [fst snd] in *.
  destruct (pa_dump0_props) as [Hd0p [Hd0a [Hd0m Hd0run]]].
  set (d0 := pa_dump0) in *; clearbody d0.
  destruct (Kd2_loop (p - 4) (0 >> [1]^^(a + 4) *> 0 >> 0 >> 1 >> const 0)%sym d0 ltac:(lia) Hd0a Hd0m)
    as [Hrun1 [Hp1 [Ha1 Hm1]]].
  set (pa1 := Kd2_iter (p - 4) d0) in *; clearbody pa1.
  destruct (Krel_x_all (a / 2 + 2) (0 >> 0 >> 1 >> const 0)%sym pa1 ltac:(lia) Ha1 Hm1)
    as [Hrun2 _].
  assert (Hp_eq : p = (p - 4) + 4) by lia.
  assert (Ha_ev : a + 4 = 2 * (a / 2 + 2)) by (mods; lia).
  rewrite Hp_eq at 1.
  eapply progress_evstep_trans; [apply P_DUMP_boot |].
  eapply evstep_trans; [apply Hd0run |].
  eapply evstep_trans; [exact Hrun1 |].
  rewrite Ha_ev.
  apply progress_evstep, Hrun2.
Qed.

Opaque Kpass1.

(** *** Pass 2 start: the routine reads the marker and halts *)

Definition c_end (p a : nat) : Q * tape :=
  (0 >> 0 >> 1 >> 1 >> 1 >> [1]^^(a + 2) *> [0; 1]^^p *> const 0)%sym {{RR}}> (const 0)%sym.

Lemma HALT_step : forall p a,
  Ce_gen p a 0 ([1]^^1 *> 0 >> 0 >> 1 >> const 0)%sym -->+ c_end p a.
Proof.
  intros p a. unfold Ce_gen, c_end. cbn [lpow Str_app].
  start_progress.
Qed.

Lemma c_end_halted : forall p a, halted tm (c_end p a).
Proof. intros p a. unfold c_end. reflexivity. Qed.

(** *** Initial pass from c0, the counted pass, and the halt *)

Definition pa_init : nat * nat :=
  Krel_odd (Kd1_iter 114 (5, 38)).

Lemma init_pass :
  c0 -->* Ce_gen (fst pa_init) (snd pa_init) 0 ([1]^^1 *> const 0)%sym /\
  233 <= fst pa_init /\
  4 <= snd pa_init /\
  snd pa_init mod 2 = 0.
Proof.
  unfold pa_init.
  destruct (Kd1_loop 114 0 (const 0)%sym (5, 38) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(reflexivity))
    as [Hrun1 [Hp1 [Ha1 Hm1]]].
  change (fst (5, 38)) with 5 in Hrun1, Hp1.
  change (snd (5, 38)) with 38 in Hrun1.
  change (2 * 114 + 0) with 228 in Hrun1.
  change ([1]^^0 *> const 0)%sym with (const 0)%sym in Hrun1.
  set (pa_boot := Kd1_iter 114 (5, 38)) in *.
  clearbody pa_boot.
  destruct (Krel_odd_all pa_boot ltac:(lia) Ha1 Hm1)
    as [Hrun2 [Hp2 [Ha2 Hm2]]].
  split; [| split; [| split]].
  - eapply evstep_trans; [apply init_ce |].
    eapply evstep_trans; [exact Hrun1 |].
    apply progress_evstep, Hrun2.
  - lia.
  - exact Ha2.
  - exact Hm2.
Qed.

Lemma run_end : c0 -->* c_end (fst (Kpass1 pa_init)) (snd (Kpass1 pa_init)).
Proof.
  destruct init_pass as [Hinit [Hp [Ha Hm]]].
  eapply evstep_trans; [exact Hinit |].
  eapply evstep_trans; [apply progress_evstep, (Kpass1_all pa_init ltac:(lia) Ha Hm) |].
  apply progress_evstep, HALT_step.
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run_end) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply c_end_halted.
Qed.

(** ** Fast-Growing Hierarchy up to f_(omega+4) and domination bounds *)

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | 0 => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega  (n : nat) : nat := f n n.
Definition f_omega1 (n : nat) : nat := iter n f_omega n.
Definition f_omega2 (n : nat) : nat := iter n f_omega1 n.
Definition f_omega3 (n : nat) : nat := iter n f_omega2 n.
Definition f_omega4 (n : nat) : nat := iter n f_omega3 n.

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

Lemma f_omega1_dbl : forall n, 1 <= n -> 2 * n <= f_omega1 n.
Proof.
  intros [| n'] Hn; [lia |].
  unfold f_omega1. rewrite iter_S'.
  transitivity (f_omega (S n')).
  - apply f_omega_dbl. lia.
  - apply iter_ge, f_omega_id.
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

Lemma f_omega2_dbl : forall n, 1 <= n -> 2 * n <= f_omega2 n.
Proof.
  intros [| n'] Hn; [lia |].
  unfold f_omega2. rewrite iter_S'.
  transitivity (f_omega1 (S n')).
  - apply f_omega1_dbl. lia.
  - apply iter_ge, f_omega1_id.
Qed.

Lemma f_omega2_mono : forall a b, a <= b -> f_omega2 a <= f_omega2 b.
Proof.
  intros a b Hab. unfold f_omega2.
  transitivity (iter a f_omega1 b).
  - apply iter_mono_x; [apply f_omega1_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega1_id | exact Hab].
Qed.

Lemma f_omega3_id : forall n, n <= f_omega3 n.
Proof. intros n. unfold f_omega3. apply iter_ge, f_omega2_id. Qed.

Lemma f_omega3_mono : forall a b, a <= b -> f_omega3 a <= f_omega3 b.
Proof.
  intros a b Hab. unfold f_omega3.
  transitivity (iter a f_omega2 b).
  - apply iter_mono_x; [apply f_omega2_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega2_id | exact Hab].
Qed.

Lemma f_omega4_id : forall n, n <= f_omega4 n.
Proof. intros n. unfold f_omega4. apply iter_ge, f_omega3_id. Qed.

Lemma f_omega4_mono : forall a b, a <= b -> f_omega4 a <= f_omega4 b.
Proof.
  intros a b Hab. unfold f_omega4.
  transitivity (iter a f_omega3 b).
  - apply iter_mono_x; [apply f_omega3_mono | exact Hab].
  - apply iter_mono_n; [apply f_omega3_id | exact Hab].
Qed.

Opaque f f_omega f_omega1 f_omega2 f_omega3 f_omega4.

(** ** Lower bound for W *)

Lemma iter_W0 : forall n x, iter n (W 0) x = x + 3 * n.
Proof. induction n; intros x; simpl. - lia. - rewrite W_0, IHn. lia. Qed.

Lemma W1_val : forall b, W 1 b = 3 * b + 5.
Proof. intros b. rewrite W_S, iter_W0. lia. Qed.

Lemma W_S' : forall j b, W (S j) b = iter b (W j) (W j 2).
Proof. intros j b. rewrite W_S, iter_S'. reflexivity. Qed.

Lemma W_S_2 : forall j, W (S j) 2 = W j (W j (W j 2)).
Proof. intros j. rewrite W_S. reflexivity. Qed.

Lemma W_S_lin3 : forall j b, 3 * b + 5 <= W (S j) b.
Proof.
  intros j b. rewrite W_S.
  pose proof (iter_lin3 (W j) (W_grow j) (S b) 2). lia.
Qed.

Lemma W_mono : forall j a b, a <= b -> W j a <= W j b.
Proof.
  induction j as [| j IHj]; intros a b Hab.
  - rewrite !W_0. lia.
  - rewrite !W_S. apply iter_mono_n; [| lia].
    intros x. pose proof (W_grow j x). lia.
Qed.

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

Lemma W_omega_bound : forall m b,
  2 * f_omega (S m) + 3 <= W (S (S (S m))) b.
Proof.
  intros m b.
  transitivity (W (S (S (S m))) 0); [| apply W_mono; lia].
  rewrite W_S. cbn [iter].
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

Lemma W_omega_bound1 : forall m b,
  1 <= b -> 6 * f_omega (S m) + 14 <= W (S (S (S m))) b.
Proof.
  intros m b Hb.
  transitivity (W (S (S (S m))) 1); [| apply W_mono; lia].
  rewrite W_S. cbn [iter].
  pose proof (W_omega_bound m 0) as H0.
  rewrite W_S in H0. cbn [iter] in H0.
  pose proof (W_S_lin3 (S m) (W (S (S m)) 2)) as H1.
  lia.
Qed.

(** ** Domination across Kc, Kd1_step, Kd1_iter, Krel_even, Kd2_iter, Krel_odd, and Kpass *)

Lemma Kc_dom1 : forall pa,
  4 <= fst pa -> 4 <= snd pa ->
  fst pa + 2 <= fst (Kc pa) /\
  fst pa + snd pa / 2 <= fst (Kc pa) /\
  6 * f_omega (fst pa - 3) + 14 <= snd (Kc pa).
Proof.
  intros [p a] Hp Ha. rewrite Kc_unfold. cbn [fst snd] in *.
  destruct p as [| [| [| [| m]]]]; try lia.
  replace (S (S (S (S m))) - 1) with (S (S (S m))) by lia.
  replace (S (S (S (S m))) - 3) with (S m) by lia.
  pose proof (W_omega_bound1 m 1 ltac:(lia)) as Hw.
  set (z := f_omega (S m)) in *.
  set (w := W (S (S (S m))) 1) in *.
  assert (Hdiv : 2 <= a / 2) by (mods; lia).
  split; [lia | split; lia].
Qed.

Lemma Kc_dom2 : forall pa,
  4 <= fst pa -> 4 <= snd pa ->
  4 <= fst (iter 2 Kc pa) /\
  4 <= snd (iter 2 Kc pa) /\
  f_omega (fst pa - 3) <= fst (iter 2 Kc pa) - 3.
Proof.
  intros pa Hp Ha. cbn [iter].
  destruct (Kc_dom1 pa Hp Ha) as [Hp1 [_ Ha1]].
  assert (Ha1' : 4 <= snd (Kc pa)) by lia.
  destruct (Kc_dom1 (Kc pa) ltac:(lia) Ha1') as [Hp2 [Hdiv2 Ha2]].
  assert (Hq : f_omega (fst pa - 3) + 2 <= snd (Kc pa) / 2)
    by (set (z := f_omega (fst pa - 3)) in *; set (s := snd (Kc pa)) in *; mods; lia).
  split; [lia | split; [lia | lia]].
Qed.

Lemma Kc_dom_even : forall k pa,
  4 <= fst pa -> 4 <= snd pa ->
  4 <= fst (iter (2 * k) Kc pa) /\
  4 <= snd (iter (2 * k) Kc pa) /\
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
  4 <= fst pa -> 4 <= snd pa ->
  4 <= fst (iter c' Kc pa) /\
  4 <= snd (iter c' Kc pa) /\
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
    split; [lia | split; [lia | lia]].
Qed.

Definition ok_pa_w (n : nat) (pa : nat * nat) : Prop :=
  n <= fst pa - 3 /\ 4 * n + 6 <= snd pa.

Definition ok_pa (n : nat) (pa : nat * nat) : Prop :=
  n <= fst pa - 5 /\ 4 * n + 6 <= snd pa.

Lemma ok_pa_imp_w : forall n pa, ok_pa n pa -> ok_pa_w n pa.
Proof. intros n [p a] [Hp Ha]. split; lia. Qed.

Lemma ok_pa_mono : forall m n pa,
  m <= n -> ok_pa n pa -> ok_pa m pa.
Proof. intros m n [p a] Hmn [Hp Ha]. split; lia. Qed.

Lemma Kd1_step_dom_w : forall n pa,
  1 <= n -> ok_pa_w n pa -> ok_pa (f_omega1 n) (Kd1_step pa).
Proof.
  intros n [p a] Hn [Hp Ha]. unfold ok_pa_w, ok_pa in *. cbn [fst snd] in *.
  rewrite Kd1_step_unfold.
  assert (Hc : a / 2 - 1 = S (a / 2 - 2)) by (mods; lia).
  assert (Hdiv : n <= (a / 2 - 2) / 2) by (mods; lia).
  rewrite Hc. cbn [iter].
  destruct (Kd1_init_props p ltac:(lia)) as [Hip [Hia _]].
  destruct (Kc_dom_any (a / 2 - 2) (Kd1_init p) ltac:(lia) Hia)
    as [Hp1 [Ha1 Hdom1]].
  destruct (Kc_dom1 (iter (a / 2 - 2) Kc (Kd1_init p)) Hp1 Ha1)
    as [Hp2 [_ Ha2]].
  assert (H1 : f_omega1 n <= iter ((a / 2 - 2) / 2) f_omega (fst (Kd1_init p) - 3)).
  { Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
    transitivity (iter n f_omega (fst (Kd1_init p) - 3)).
    - apply iter_mono_x; [apply f_omega_mono | lia].
    - apply iter_mono_n; [apply f_omega_id | exact Hdiv]. }
  set (pa' := iter (a / 2 - 2) Kc (Kd1_init p)) in *.
  pose proof (f_omega_id (fst pa' - 3)).
  split; lia.
Qed.

Lemma Kd1_step_dom : forall n pa,
  1 <= n -> ok_pa n pa -> ok_pa (f_omega1 n) (Kd1_step pa).
Proof.
  intros n pa Hn Hok.
  apply Kd1_step_dom_w; [exact Hn | apply ok_pa_imp_w, Hok].
Qed.

Lemma Kd1_iter_dom : forall m1 n pa,
  1 <= n -> ok_pa n pa -> ok_pa (iter m1 f_omega1 n) (Kd1_iter m1 pa).
Proof.
  intros m1 n pa. rewrite Kd1_iter_unfold.
  induction m1 as [| m1 IHm1]; intros Hn Hok.
  - cbn [iter]. exact Hok.
  - cbn [iter]. apply Kd1_step_dom.
    + pose proof (iter_ge f_omega1 f_omega1_id m1 n). lia.
    + apply IHm1; assumption.
Qed.

Lemma Kd2_init_w : forall n pa,
  1 <= n -> ok_pa n pa -> ok_pa_w n (fst pa - 2, W (fst pa - 2) 1).
Proof.
  intros n [p a] Hn [Hp Ha]. unfold ok_pa, ok_pa_w in *. cbn [fst snd] in *.
  destruct p as [| [| [| [| [| [| m]]]]]]; try lia.
  replace (S (S (S (S (S (S m))))) - 2) with (S (S (S (S m)))) by lia.
  pose proof (W_omega_bound1 (S m) 1 ltac:(lia)) as Hw.
  pose proof (f_omega_id (S (S m))) as Hid.
  split; lia.
Qed.

Lemma Krel_even_dom : forall k n pa,
  1 <= n -> ok_pa n pa -> ok_pa (f_omega2 n) (Krel_even k pa).
Proof.
  intros k n [p a] Hn Hok.
  pose proof (Kd2_init_w n (p, a) Hn Hok) as Hinit. cbn [fst snd] in Hinit.
  destruct Hok as [Hp Ha]. cbn [fst snd] in Hp, Ha.
  rewrite Krel_even_unfold, Kd1_iter_unfold.
  replace (a / 2 + k + 2) with (S (a / 2 + k + 1)) by lia.
  rewrite iter_S', <- Kd1_iter_unfold.
  pose proof (Kd1_step_dom_w n (p - 2, W (p - 2) 1) Hn Hinit) as Hstep1.
  assert (Hpos1 : 1 <= f_omega1 n) by (pose proof (f_omega1_id n); lia).
  pose proof (Kd1_iter_dom (a / 2 + k + 1) (f_omega1 n) (Kd1_step (p - 2, W (p - 2) 1)) Hpos1 Hstep1) as Hloop.
  rewrite <- iter_S' in Hloop.
  assert (Hdiv : n <= S (a / 2 + k + 1)) by (mods; lia).
  assert (Hle : f_omega2 n <= iter (S (a / 2 + k + 1)) f_omega1 n).
  { Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    apply iter_mono_n; [apply f_omega1_id | exact Hdiv]. }
  eapply ok_pa_mono; [exact Hle | exact Hloop].
Qed.

Lemma Kd2_step_dom : forall n pa,
  1 <= n -> ok_pa n pa -> ok_pa (f_omega2 n) (Kd2_step pa).
Proof.
  intros n pa Hn Hok.
  rewrite Kd2_step_eq_Krel_even.
  apply Krel_even_dom; assumption.
Qed.

Lemma Kd2_iter_dom : forall m2 n pa,
  1 <= n -> ok_pa n pa -> ok_pa (iter m2 f_omega2 n) (Kd2_iter m2 pa).
Proof.
  intros m2 n pa. rewrite Kd2_iter_unfold.
  induction m2 as [| m2 IHm2]; intros Hn Hok.
  - cbn [iter]. exact Hok.
  - cbn [iter]. apply Kd2_step_dom.
    + pose proof (iter_ge f_omega2 f_omega2_id m2 n). lia.
    + apply IHm2; assumption.
Qed.

Lemma Krel_odd_dom : forall n pa,
  1 <= n -> ok_pa n pa -> ok_pa (f_omega2 n) (Krel_odd pa).
Proof.
  intros n [p a] Hn Hok.
  pose proof (Kd2_init_w n (p, a) Hn Hok) as Hinit. cbn [fst snd] in Hinit.
  destruct Hok as [Hp Ha]. cbn [fst snd] in Hp, Ha.
  rewrite Krel_odd_unfold, Kd1_iter_unfold.
  replace (a / 2 + 1) with (S (a / 2)) by lia.
  rewrite iter_S', <- Kd1_iter_unfold.
  pose proof (Kd1_step_dom_w n (p - 2, W (p - 2) 1) Hn Hinit) as Hstep1.
  assert (Hpos1 : 1 <= f_omega1 n) by (pose proof (f_omega1_id n); lia).
  pose proof (Kd1_iter_dom (a / 2) (f_omega1 n) (Kd1_step (p - 2, W (p - 2) 1)) Hpos1 Hstep1) as Hloop.
  rewrite <- iter_S' in Hloop.
  assert (Hdiv : n <= S (a / 2)) by (mods; lia).
  assert (Hle : f_omega2 n <= iter (S (a / 2)) f_omega1 n).
  { Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    apply iter_mono_n; [apply f_omega1_id | exact Hdiv]. }
  eapply ok_pa_mono; [exact Hle | exact Hloop].
Qed.

Lemma Kd1_step_boot : forall pa,
  4 <= fst pa -> 4 <= snd pa -> ok_pa 1 (Kd1_step pa).
Proof.
  intros [p a] Hp Ha. unfold ok_pa. cbn [fst snd] in *.
  rewrite Kd1_step_unfold.
  assert (Hc : a / 2 - 1 = S (a / 2 - 2)) by (mods; lia).
  rewrite Hc. cbn [iter].
  destruct (Kd1_init_props p ltac:(lia)) as [Hip [Hia _]].
  destruct (Kc_dom_any (a / 2 - 2) (Kd1_init p) ltac:(lia) Hia)
    as [Hp1 [Ha1 Hdom1]].
  destruct (Kc_dom1 (iter (a / 2 - 2) Kc (Kd1_init p)) Hp1 Ha1)
    as [Hp2 [_ Ha2]].
  set (pa' := iter (a / 2 - 2) Kc (Kd1_init p)) in *.
  pose proof (iter_ge f_omega f_omega_id ((a / 2 - 2) / 2) (fst (Kd1_init p) - 3)).
  split; lia.
Qed.

Lemma Kd1_iter_22_boot : forall pa0,
  3 <= fst pa0 -> 4 <= snd pa0 -> snd pa0 mod 2 = 0 ->
  ok_pa 1 (Kd1_iter 22 pa0).
Proof.
  intros pa0 Hp0 Ha0 Hm0.
  rewrite Kd1_iter_unfold.
  change 22 with (20 + (1 + 1)).
  rewrite !iter_add, <- Kd1_iter_unfold.
  cbn [iter].
  destruct (Kd1_step_all 0 (const 0)%sym pa0 Hp0 Ha0 Hm0) as [_ [Hp1 [Ha1 _]]].
  pose proof (Kd1_step_boot (Kd1_step pa0) ltac:(lia) Ha1) as Hboot.
  pose proof (Kd1_iter_dom 20 1 (Kd1_step (Kd1_step pa0)) ltac:(lia) Hboot) as Hdom.
  pose proof (iter_ge f_omega1 f_omega1_id 20 1) as Hge.
  eapply ok_pa_mono; [exact Hge | exact Hdom].
Qed.

Lemma pa_dump0_dom : ok_pa 1 pa_dump0.
Proof.
  rewrite pa_dump0_unfold.
  apply Kd1_iter_22_boot.
  - apply Nat.le_refl.
  - exact (W_grow 3 1).
  - exact (W_par 3 1).
Qed.

Lemma iter_f_omega2_ge_f_omega3 : forall n m,
  1 <= n -> 2 * n <= m -> f_omega3 n <= iter m f_omega2 1.
Proof.
  intros n m Hn Hnm.
  transitivity (iter (n + n) f_omega2 1).
  - rewrite iter_add.
    Transparent f_omega3. unfold f_omega3. Opaque f_omega3.
    apply iter_mono_x; [apply f_omega2_mono |].
    pose proof (iter_lin1 f_omega2 ltac:(intros a Ha; pose proof (f_omega2_dbl a Ha); lia) n 1 ltac:(lia)).
    lia.
  - apply iter_mono_n; [apply f_omega2_id | lia].
Qed.

(** ** Score of the halting configuration *)

Lemma Krel_x_dom : forall k n pa,
  1 <= n -> ok_pa n pa -> ok_pa (f_omega2 n) (Krel_x k pa).
Proof.
  intros k n [p a] Hn Hok.
  pose proof (Kd2_init_w n (p, a) Hn Hok) as Hinit. cbn [fst snd] in Hinit.
  destruct Hok as [Hp Ha]. cbn [fst snd] in Hp, Ha.
  rewrite Krel_x_unfold, Kd1_iter_unfold.
  replace (a / 2 + k + 1) with (S (a / 2 + k)) by lia.
  rewrite iter_S', <- Kd1_iter_unfold.
  pose proof (Kd1_step_dom_w n (p - 2, W (p - 2) 1) Hn Hinit) as Hstep1.
  assert (Hpos1 : 1 <= f_omega1 n) by (pose proof (f_omega1_id n); lia).
  pose proof (Kd1_iter_dom (a / 2 + k) (f_omega1 n) (Kd1_step (p - 2, W (p - 2) 1)) Hpos1 Hstep1) as Hloop.
  rewrite <- iter_S' in Hloop.
  assert (Hdiv : n <= S (a / 2 + k)) by (mods; lia).
  assert (Hle : f_omega2 n <= iter (S (a / 2 + k)) f_omega1 n).
  { Transparent f_omega2. unfold f_omega2. Opaque f_omega2.
    apply iter_mono_n; [apply f_omega1_id | exact Hdiv]. }
  eapply ok_pa_mono; [exact Hle | exact Hloop].
Qed.

Lemma Kpass1_dom : forall pa,
  233 <= fst pa -> ok_pa (f_omega2 (f_omega3 114)) (Kpass1 pa).
Proof.
  intros [p a] Hp. rewrite Kpass1_unfold. cbn [fst] in Hp.
  pose proof pa_dump0_dom as Hd0.
  set (d0 := pa_dump0) in *; clearbody d0.
  pose proof (Kd2_iter_dom (p - 4) 1 d0 ltac:(lia) Hd0) as Hd1.
  pose proof (iter_f_omega2_ge_f_omega3 114 (p - 4) ltac:(lia) ltac:(lia)) as Hle1.
  pose proof (ok_pa_mono (f_omega3 114) (iter (p - 4) f_omega2 1) (Kd2_iter (p - 4) d0) Hle1 Hd1) as Hok1.
  assert (Hpos : 1 <= f_omega3 114) by (pose proof (f_omega3_id 114); lia).
  exact (Krel_x_dom (a / 2 + 2) (f_omega3 114) (Kd2_iter (p - 4) d0) Hpos Hok1).
Qed.

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

Lemma ones_c_end : forall p a, ones (c_end p a) (p + a + 5).
Proof.
  intros p a.
  exists RR, ([S0; S0; S1; S1; S1] ++ [S1]^^(a + 2) ++ [S0; S1]^^p), (@nil Sym), S0.
  split.
  - unfold c_end. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

Theorem score_exact :
  exists c, c0 -->* c /\ halted tm c /\
    ones c (fst (Kpass1 pa_init) + snd (Kpass1 pa_init) + 5).
Proof.
  exists (c_end (fst (Kpass1 pa_init)) (snd (Kpass1 pa_init))).
  split; [exact run_end |].
  split; [apply c_end_halted |].
  apply ones_c_end.
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega3 114) < N.
Proof.
  destruct init_pass as [_ [Hp _]].
  destruct (Kpass1_dom pa_init Hp) as [H1 H2].
  exists (c_end (fst (Kpass1 pa_init)) (snd (Kpass1 pa_init))),
         (fst (Kpass1 pa_init) + snd (Kpass1 pa_init) + 5).
  split; [exact run_end |]. split; [apply c_end_halted |]. split; [apply ones_c_end |].
  lia.
Qed.

Corollary sigma_lower_bound_fw3 :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega3 114 < N.
Proof.
  destruct sigma_lower_bound as [c [N [H1 [H2 [H3 H4]]]]].
  exists c, N. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  pose proof (f_omega2_id (f_omega3 114)). lia.
Qed.
