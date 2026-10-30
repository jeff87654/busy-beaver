(** * A 16-state halting Turing machine achieving > f_(omega+2)(f_(omega+3)(9)) *)

(** Machine M16_B (16 states, A..P):
      1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP1RM_1RZ1LI

    This file proves without axioms that M16_B halts from the blank tape [c0]
    and dominates [f_(omega+2)(f_(omega+3)(9))] in the Fast-Growing Hierarchy:
      - Inner cascade: [Ch j b z -->+ Ca j (W j b) z] (achieving f_omega)
      - Level 1 (c-counter): [Kc_loop] (achieving f_(omega+1))
      - Level 2 (d1-counter): [Kd1_loop] and [D1_cycle_all] (achieving f_(omega+2))
      - Level 3 (parity-remainder loop): [Kd2_loop] (achieving f_(omega+3))
      - Bridge + 11th f_(omega+2) cycle + clean halt: [halt] and [halt_f_omega3] *)

From BB8 Require Import Individual162.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1LB1LA_1RC0LA_1RD1RC_1RE1RK_1RF0LJ_1LG1RI_1RM0LM_1LG0RC_0RN0LE_1LA1LE_0LL1LB_0RM1LL_1LF1RH_0RO0LO_1LP1RM_1RZ1LI *)
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
  | I, 0 => Some (0, TM.R, N)  | I, 1 => Some (0, TM.L, E)
  | J, 0 => Some (1, TM.L, A)  | J, 1 => Some (1, TM.L, E)
  | K, 0 => Some (0, TM.L, L)  | K, 1 => Some (1, TM.L, B)
  | L, 0 => Some (0, TM.R, M)  | L, 1 => Some (1, TM.L, L)
  | M, 0 => Some (1, TM.L, F)  | M, 1 => Some (1, TM.R, H)
  | N, 0 => Some (0, TM.R, O)  | N, 1 => Some (0, TM.L, O)
  | O, 0 => Some (1, TM.L, P)  | O, 1 => Some (1, TM.R, M)
  | P, 0 => None               | P, 1 => Some (1, TM.L, I)
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

Lemma E_1100_aux : forall p' m z,
  ([1]^^(2 * m + 2) *> [0; 1]^^(S p') *> const 0) {{E}}> (1 >> 1 >> 0 >> 0 >> z) -->+
  Ch p' 1 ([1; 0]^^(m + 2) *> 0 >> z).
Proof.
  intros p' m z. unfold Ch.
  replace (2 * m + 2)%nat with (1 + (2 * m + 1))%nat by lia.
  replace (m + 2)%nat with (S (m + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] m). cbn [app].
  start_progress.
  follow cr_EL_11_10.
  execute; finish_norm.
Qed.

(** ** Exact hierarchy functions W, Kc, Kd1_step, D1_cycle, Kd2_step *)

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

(** ** Level 1, Level 2, and Level 3 macro transitions *)

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

Lemma E_1100 : forall p' m c r,
  ([1]^^(2 * m + 2) *> [0; 1]^^(S p') *> const 0)%sym {{E}}> (1 >> 1 >> 0 >> 0 >> [1; 0]^^c *> 0 >> r)%sym -->+
  Ce_gen (p' + m + 2) (W p' 1) c r.
Proof.
  intros p' m c r.
  eapply progress_evstep_trans; [apply E_1100_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  follow (CA_SH_iter (m + 2) p' (W p' 1) (0 >> [1; 0]^^c *> 0 >> r)%sym).
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  unfold Ce_gen. replace (p' + (m + 2)) with (p' + m + 2) by lia. finish_norm.
Qed.

Lemma C_REL_aux : forall p' k r,
  Ce_gen (S (S p')) (2 * k + 4) 0 (1 >> 1 >> r)%sym -->+
  Ch p' 1 (0 >> 1 >> 1 >> 0 >> 0 >> [1; 0]^^(S (S k)) *> 0 >> r)%sym.
Proof.
  intros p' k r. unfold Ce_gen, Ch.
  replace (2 * k + 4 + 2) with (2 * k + 6) by lia.
  rewrite lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1]%sym k). cbn [app].
  start_progress.
  follow cr_EL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma C_REL_part1 : forall p' k r,
  Ce_gen (S (S p')) (2 * k + 4) 0 (1 >> 1 >> r)%sym -->+
  ([1]^^(W p' 1 + 2) *> [0; 1]^^p' *> const 0)%sym {{E}}>
    (1 >> 1 >> 0 >> 0 >> [1; 0]^^(S (S k)) *> 0 >> r)%sym.
Proof.
  intros p' k r.
  eapply progress_evstep_trans; [apply C_REL_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma D1_REL_aux : forall p' a r,
  Ce_gen (S (S p')) a 0 (0 >> r)%sym -->+
  Ch p' 1 (0 >> 0 >> [1]^^(a + 3) *> r)%sym.
Proof.
  intros p' a r. unfold Ce_gen, Ch. cbn [lpow Str_app].
  start_progress.
  follow cr_ML_1_1.
  execute; finish_norm.
Qed.

Lemma D1_REL : forall p' a r,
  Ce_gen (S (S p')) a 0 (0 >> r)%sym -->+
  Ce_gen p' (W p' 1) 0 ([1]^^(a + 3) *> r)%sym.
Proof.
  intros p' a r.
  eapply progress_evstep_trans; [apply D1_REL_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  unfold Ce_gen. cbn [lpow Str_app]. finish_norm.
Qed.

Lemma D2_STEP_part1_aux : forall p' k r,
  Ce_gen (S (S p')) (2 * k + 2) 0 (1 >> 0 >> 1 >> 0 >> r)%sym -->+
  Ch p' 1 (0 >> 1 >> 1 >> 0 >> 0 >> [1; 0]^^k *> 0 >> [1]^^2 *> 0 >> 0 >> r)%sym.
Proof.
  intros p' k r. unfold Ce_gen, Ch.
  replace (2 * k + 2 + 2) with (2 + (2 * k + 2)) by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1]%sym k). cbn [app].
  start_progress.
  follow cr_EL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma D2_STEP_part1 : forall p' k r,
  Ce_gen (S (S p')) (2 * k + 2) 0 (1 >> 0 >> 1 >> 0 >> r)%sym -->+
  ([1]^^(W p' 1 + 2) *> [0; 1]^^p' *> const 0)%sym {{E}}>
    (1 >> 1 >> 0 >> 0 >> [1; 0]^^k *> 0 >> [1]^^2 *> 0 >> 0 >> r)%sym.
Proof.
  intros p' k r.
  eapply progress_evstep_trans; [apply D2_STEP_part1_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

Lemma BRIDGE_aux : forall p a r,
  Ce_gen p a 0 (1 >> 0 >> 0 >> 1 >> 0 >> 0 >> r)%sym -->+
  Ch p (a + 2) (blk 1 (0 >> 0 >> r)%sym).
Proof.
  intros p a r. unfold Ce_gen, Ch, blk. cbn [lpow Str_app].
  start_progress.
  follow cr_AL_1_1.
  execute; finish_norm.
Qed.

Lemma BRIDGE : forall p a r,
  Ce_gen p a 0 (1 >> 0 >> 0 >> 1 >> 0 >> 0 >> r)%sym -->+
  Ce_gen (p + 1) (W p (W p (a + 2))) 0 r.
Proof.
  intros p a r.
  eapply progress_evstep_trans; [apply BRIDGE_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, (BLK_iter_aux p (CH_CA p) 1 (W p (a + 2))) |].
  cbn [iter].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  unfold Ce_gen. replace (S p) with (p + 1) by lia. finish_norm.
Qed.

Definition c_end (p a : nat) : Q * tape :=
  (0 >> 0 >> 1 >> 1 >> [1]^^(a + 2) *> [0; 1]^^p *> const 0)%sym <{{P}} (1 >> const 0)%sym.

Lemma c_end_halted : forall p a, halted tm (c_end p a).
Proof. reflexivity. Qed.

Lemma HALT_step : forall p a,
  Ce_gen p a 0 (1 >> const 0)%sym -->+ c_end p a.
Proof.
  intros p a. unfold Ce_gen, c_end. cbn [lpow Str_app].
  do 3 rewrite const_unfold at 2.
  start_progress.
Qed.

(** ** Initial entry and bootstrap from blank tape c0 *)

Lemma init_37 : c0 -->* Ca 0 3 (blk 1 (blk 3 (0 >> const 0)%sym)).
Proof.
  unfold Ca, blk. cbn [lpow Str_app].
  do 37 step. autorewrite with tape_post. finish_norm.
Qed.

Lemma init_ce0 : c0 -->* Ce_gen 0 4 0 ([1]^^230 *> const 0)%sym.
Proof.
  follow init_37.
  eapply evstep_trans; [apply progress_evstep, (BLK_iter_aux 0 (CH_CA 0) 1 3) |].
  change (iter 1 (W 0) 3) with 6.
  eapply evstep_trans; [apply progress_evstep, (BLK_iter_aux 1 (CH_CA 1) 3 6) |].
  change (iter 3 (W 1) 6) with 227.
  do 2 rewrite const_unfold at 1.
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  eapply evstep_trans; [apply progress_evstep, (D1_REL 0 227 (const 0)%sym) |].
  change (W 0 1) with 4. change (227 + 3) with 230.
  apply evstep_refl.
Qed.

Lemma start_38 : forall r,
  Ce_gen 0 4 0 (1 >> 1 >> r)%sym -->+
  Ca 0 3 (blk 1 (blk 1 (0 >> 1 >> 0 >> 1 >> 0 >> 0 >> r)%sym)).
Proof.
  intros r. unfold Ce_gen, Ca, blk. cbn [lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 37 step. autorewrite with tape_post. finish_norm.
Qed.

Lemma start_131 : forall r,
  Ca 2 23 (0 >> 1 >> 0 >> 1 >> 0 >> 0 >> r)%sym -->+
  Ch 2 1 (0 >> 1 >> 1 >> 0 >> 0 >> [1; 0]^^1 *> 0 >> [1; 0]^^10 *> 0 >> 1 >> 0 >> 0 >> r)%sym.
Proof.
  intros r. unfold Ca, Ch. cbn [lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 130 step. autorewrite with tape_post. finish_norm.
Qed.

Lemma W_2_1 : W 2 1 = 38.
Proof. vm_compute. reflexivity. Qed.

Lemma W_1_1 : W 1 1 = 8.
Proof. vm_compute. reflexivity. Qed.

Lemma start_boot : forall r,
  Ce_gen 0 4 0 (1 >> 1 >> r)%sym -->+
  Ce_gen 26 (W 21 1) 0 ([1; 0]^^10 *> 0 >> 1 >> 0 >> 0 >> r)%sym.
Proof.
  intros r.
  eapply progress_evstep_trans; [apply start_38 |].
  eapply evstep_trans; [apply progress_evstep, (BLK_iter_aux 0 (CH_CA 0) 1 3) |].
  change (iter 1 (W 0) 3) with 6.
  eapply evstep_trans; [apply progress_evstep, (BLK_iter_aux 1 (CH_CA 1) 1 6) |].
  change (iter 1 (W 1) 6) with 23.
  eapply evstep_trans; [apply progress_evstep, start_131 |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  rewrite W_2_1.
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  change (38 + 2) with (2 * 19 + 2).
  change 2 with (S 1) at 2.
  eapply evstep_trans; [apply progress_evstep, (E_1100 1 19 1 ([1; 0]^^10 *> 0 >> 1 >> 0 >> 0 >> r)%sym) |].
  change (1 + 19 + 2) with (S 21). rewrite W_1_1. change 8 with (2 * 4).
  eapply evstep_trans; [apply progress_evstep, (CE_EVEN 21 4 0 ([1; 0]^^10 *> 0 >> 1 >> 0 >> 0 >> r)%sym) |].
  change (21 + S 4) with 26.
  apply evstep_refl.
Qed.

Lemma lpow_230_228 :
  ([1]^^230 *> const 0)%sym = (1 >> 1 >> [1]^^228 *> const 0)%sym.
Proof.
  change 230 with (2 + 228). rewrite lpow_add. reflexivity.
Qed.

Lemma init_ce : c0 -->* Ce_gen 26 (W 21 1) 0 ([1; 0]^^10 *> 0 >> 1 >> 0 >> 0 >> [1]^^228 *> const 0)%sym.
Proof.
  eapply evstep_trans; [apply init_ce0 |].
  rewrite lpow_230_228.
  apply progress_evstep, start_boot.
Qed.


(** ** Growth and parity invariants *)

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

Lemma C_REL_full : forall p'' k r,
  Ce_gen (S (S (S p''))) (2 * k + 4) 0 (1 >> 1 >> r)%sym -->+
  Ce_gen (p'' + W (S p'') 1 / 2 + 2) (W p'' 1) (S (S k)) r.
Proof.
  intros p'' k r.
  eapply progress_evstep_trans; [apply C_REL_part1 |].
  pose proof (W_par (S p'') 1) as Hwp.
  assert (Hwev : W (S p'') 1 = 2 * (W (S p'') 1 / 2)) by (mods; lia).
  rewrite Hwev at 1.
  apply progress_evstep, E_1100.
Qed.

Lemma D2_STEP_full : forall p'' k r,
  Ce_gen (S (S (S p''))) (2 * k + 2) 0 (1 >> 0 >> 1 >> 0 >> r)%sym -->+
  Ce_gen (p'' + W (S p'') 1 / 2 + 2) (W p'' 1) k ([1]^^2 *> 0 >> 0 >> r)%sym.
Proof.
  intros p'' k r.
  eapply progress_evstep_trans; [apply D2_STEP_part1 |].
  pose proof (W_par (S p'') 1) as Hwp.
  assert (Hwev : W (S p'') 1 = 2 * (W (S p'') 1 / 2)) by (mods; lia).
  rewrite Hwev at 1.
  apply progress_evstep, E_1100.
Qed.

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

(** *** Level 2: Kd1_loop and D1_cycle (d1-counter) *)

Definition Kd_base (p : nat) : nat * nat :=
  (p - 1 + W (p - 2) 1 / 2, W (p - 3) 1).

Lemma Kd_base_props : forall p,
  3 <= p ->
  p + 1 <= fst (Kd_base p) /\
  4 <= snd (Kd_base p) /\
  snd (Kd_base p) mod 2 = 0.
Proof.
  intros p Hp. unfold Kd_base. cbn [fst snd].
  pose proof (W_grow (p - 2) 1) as Hg1.
  pose proof (W_grow (p - 3) 1) as Hg2.
  pose proof (W_par (p - 3) 1) as Hp2.
  set (w1 := W (p - 2) 1) in *.
  set (w2 := W (p - 3) 1) in *.
  split; [| split]; mods; lia.
Qed.

Definition Kd1_step (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  iter (a / 2) Kc (Kd_base p).

Lemma Kd1_step_all : forall r pa,
  3 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 (1 >> 1 >> r)%sym -->+
    Ce_gen (fst (Kd1_step pa)) (snd (Kd1_step pa)) 0 r /\
  fst pa + 3 <= fst (Kd1_step pa) /\
  4 <= snd (Kd1_step pa) /\
  snd (Kd1_step pa) mod 2 = 0.
Proof.
  intros r [p a] Hp Ha Hev. cbn [fst snd Kd1_step] in *.
  destruct p as [| [| [| p'']]]; try lia.
  assert (Ha_eq : a = 2 * (a / 2 - 2) + 4) by (mods; lia).
  assert (Hc_eq : S (S (a / 2 - 2)) = a / 2) by (mods; lia).
  assert (Hdiv : 2 <= a / 2) by (mods; lia).
  destruct (Kd_base_props (S (S (S p''))) ltac:(lia)) as [Hbp [Hba Hbm]].
  destruct (Kc_loop (a / 2) r (Kd_base (S (S (S p'')))) ltac:(lia) Hba Hbm)
    as [Hrun [Hp1 [Ha1 Hm1]]].
  split; [| split; [| split]].
  - rewrite Ha_eq at 1.
    eapply progress_evstep_trans; [apply C_REL_full |].
    rewrite Hc_eq.
    replace (p'' + W (S p'') 1 / 2 + 2) with (fst (Kd_base (S (S (S p'')))))
      by (unfold Kd_base; cbn [fst]; replace (S (S (S p'')) - 2) with (S p'') by lia; lia).
    replace (W p'' 1) with (snd (Kd_base (S (S (S p'')))))
      by (unfold Kd_base; cbn [snd]; replace (S (S (S p'')) - 3) with p'' by lia; reflexivity).
    exact Hrun.
  - lia.
  - exact Ha1.
  - exact Hm1.
Qed.

Definition Kd1_iter (m1 : nat) (pa : nat * nat) : nat * nat :=
  iter m1 Kd1_step pa.

Lemma lpow_1_2S : forall m1 r,
  ([1]^^(2 * S m1) *> r)%sym = (1 >> 1 >> [1]^^(2 * m1) *> r)%sym.
Proof.
  intros m1 r. replace (2 * S m1) with (2 + 2 * m1) by lia.
  rewrite lpow_add. reflexivity.
Qed.

Lemma Kd1_loop : forall m1 r pa,
  3 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 ([1]^^(2 * m1) *> r)%sym -->*
    Ce_gen (fst (Kd1_iter m1 pa)) (snd (Kd1_iter m1 pa)) 0 r /\
  fst pa + 3 * m1 <= fst (Kd1_iter m1 pa) /\
  4 <= snd (Kd1_iter m1 pa) /\
  snd (Kd1_iter m1 pa) mod 2 = 0.
Proof.
  unfold Kd1_iter.
  induction m1 as [| m1 IHm1]; intros r pa Hp Ha Hev.
  - cbn [iter lpow Str_app].
    split; [finish | split; [lia | split; [lia | exact Hev]]].
  - rewrite iter_S', lpow_1_2S.
    destruct (Kd1_step_all ([1]^^(2 * m1) *> r)%sym pa Hp Ha Hev)
      as [Hstep [Hp1 [Ha1 Hm1]]].
    destruct (IHm1 r (Kd1_step pa) ltac:(lia) Ha1 Hm1)
      as [Hrun [Hp2 [Ha2 Hm2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, Hstep | exact Hrun].
    + lia.
    + exact Ha2.
    + exact Hm2.
Qed.

Definition D1_cycle (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  Kd1_iter (a / 2 + 1) (p - 2, W (p - 2) 1).

Lemma lpow_1_odd : forall k r,
  ([1]^^(2 * k + 1) *> r)%sym = ([1]^^(2 * k) *> 1 >> r)%sym.
Proof.
  intros k r. rewrite lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma D1_cycle_all : forall r pa,
  5 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 (0 >> r)%sym -->+
    Ce_gen (fst (D1_cycle pa)) (snd (D1_cycle pa)) 0 (1 >> r)%sym /\
  fst pa + 7 <= fst (D1_cycle pa) /\
  4 <= snd (D1_cycle pa) /\
  snd (D1_cycle pa) mod 2 = 0.
Proof.
  intros r [p a] Hp Ha Hev. cbn [fst snd D1_cycle] in *.
  destruct p as [| [| p']]; try lia.
  replace (S (S p') - 2) with p' by lia.
  assert (Ha_odd : a + 3 = 2 * (a / 2 + 1) + 1) by (mods; lia).
  assert (Ha_div : 2 <= a / 2) by (mods; lia).
  pose proof (W_grow p' 1) as Hwg.
  pose proof (W_par p' 1) as Hwp.
  assert (Hwm : W p' 1 mod 2 = 0) by (mods; lia).
  destruct (Kd1_loop (a / 2 + 1) (1 >> r)%sym (p', W p' 1) ltac:(cbn; lia) ltac:(cbn; lia) Hwm)
    as [Hrun [Hp1 [Ha1 Hm1]]].
  cbn [fst snd] in *.
  split; [| split; [| split]].
  - eapply progress_evstep_trans; [apply D1_REL |].
    rewrite Ha_odd, lpow_1_odd.
    exact Hrun.
  - lia.
  - exact Ha1.
  - exact Hm1.
Qed.

(** *** Level 3: Kd2_loop (parity-remainder loop, the f_(omega+3) engine) *)

Definition Kd2_part1 (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  Kd1_step (iter (a / 2 - 1) Kc (Kd_base p)).

Lemma Kd2_part1_all : forall r pa,
  3 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 (1 >> 0 >> 1 >> 0 >> r)%sym -->+
    Ce_gen (fst (Kd2_part1 pa)) (snd (Kd2_part1 pa)) 0 (0 >> 0 >> r)%sym /\
  fst pa + 5 <= fst (Kd2_part1 pa) /\
  4 <= snd (Kd2_part1 pa) /\
  snd (Kd2_part1 pa) mod 2 = 0.
Proof.
  intros r [p a] Hp Ha Hev. cbn [fst snd Kd2_part1] in *.
  destruct p as [| [| [| p'']]]; try lia.
  assert (Ha_eq : a = 2 * (a / 2 - 1) + 2) by (mods; lia).
  assert (Hdiv : 2 <= a / 2) by (mods; lia).
  destruct (Kd_base_props (S (S (S p''))) ltac:(lia)) as [Hbp [Hba Hbm]].
  destruct (Kc_loop (a / 2 - 1) ([1]^^2 *> 0 >> 0 >> r)%sym (Kd_base (S (S (S p'')))) ltac:(lia) Hba Hbm)
    as [Hrun1 [Hp1 [Ha1 Hm1]]].
  destruct (Kd1_step_all (0 >> 0 >> r)%sym (iter (a / 2 - 1) Kc (Kd_base (S (S (S p''))))) ltac:(lia) Ha1 Hm1)
    as [Hstep2 [Hp2 [Ha2 Hm2]]].
  split; [| split; [| split]].
  - rewrite Ha_eq at 1.
    eapply progress_evstep_trans; [apply D2_STEP_full |].
    replace (p'' + W (S p'') 1 / 2 + 2) with (fst (Kd_base (S (S (S p'')))))
      by (unfold Kd_base; cbn [fst]; replace (S (S (S p'')) - 2) with (S p'') by lia; lia).
    replace (W p'' 1) with (snd (Kd_base (S (S (S p'')))))
      by (unfold Kd_base; cbn [snd]; replace (S (S (S p'')) - 3) with p'' by lia; reflexivity).
    eapply evstep_trans; [exact Hrun1 |].
    apply progress_evstep, Hstep2.
  - lia.
  - exact Ha2.
  - exact Hm2.
Qed.

Definition Kd2_step (pa : nat * nat) : nat * nat :=
  D1_cycle (Kd2_part1 pa).

Lemma Kd2_step_all : forall r pa,
  3 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 (1 >> 0 >> 1 >> 0 >> r)%sym -->+
    Ce_gen (fst (Kd2_step pa)) (snd (Kd2_step pa)) 0 (1 >> 0 >> r)%sym /\
  fst pa + 12 <= fst (Kd2_step pa) /\
  4 <= snd (Kd2_step pa) /\
  snd (Kd2_step pa) mod 2 = 0.
Proof.
  intros r pa Hp Ha Hev. unfold Kd2_step.
  destruct (Kd2_part1_all r pa Hp Ha Hev) as [Hstep1 [Hp1 [Ha1 Hm1]]].
  destruct (D1_cycle_all (0 >> r)%sym (Kd2_part1 pa) ltac:(lia) Ha1 Hm1)
    as [Hstep2 [Hp2 [Ha2 Hm2]]].
  split; [| split; [| split]].
  - eapply progress_evstep_trans; [exact Hstep1 |].
    apply progress_evstep, Hstep2.
  - lia.
  - exact Ha2.
  - exact Hm2.
Qed.

Definition Kd2_iter (m2 : nat) (pa : nat * nat) : nat * nat :=
  iter m2 Kd2_step pa.

Lemma lpow_10_comm : forall m2 r,
  ([1; 0]^^m2 *> 1 >> 0 >> r)%sym = (1 >> 0 >> [1; 0]^^m2 *> r)%sym.
Proof.
  intros m2 r.
  change (1 >> 0 >> r)%sym with ([1; 0]^^1 *> r)%sym at 1.
  rewrite <- Str_app_assoc, <- lpow_add.
  replace (m2 + 1) with (1 + m2) by lia.
  rewrite lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma lpow_10_S_comm : forall m2 r,
  ([1; 0]^^(S m2) *> 1 >> 0 >> r)%sym = (1 >> 0 >> 1 >> 0 >> [1; 0]^^m2 *> r)%sym.
Proof.
  intros m2 r.
  change (1 >> 0 >> r)%sym with ([1; 0]^^1 *> r)%sym at 1.
  rewrite <- Str_app_assoc, <- lpow_add.
  replace (S m2 + 1) with (2 + m2) by lia.
  rewrite lpow_add, Str_app_assoc. reflexivity.
Qed.

Theorem Kd2_loop : forall m2 r pa,
  3 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 ([1; 0]^^m2 *> 1 >> 0 >> r)%sym -->*
    Ce_gen (fst (Kd2_iter m2 pa)) (snd (Kd2_iter m2 pa)) 0 (1 >> 0 >> r)%sym /\
  fst pa + 12 * m2 <= fst (Kd2_iter m2 pa) /\
  4 <= snd (Kd2_iter m2 pa) /\
  snd (Kd2_iter m2 pa) mod 2 = 0.
Proof.
  unfold Kd2_iter.
  induction m2 as [| m2 IHm2]; intros r pa Hp Ha Hev.
  - cbn [iter lpow Str_app].
    split; [finish | split; [lia | split; [lia | exact Hev]]].
  - rewrite iter_S', lpow_10_S_comm.
    destruct (Kd2_step_all ([1; 0]^^m2 *> r)%sym pa Hp Ha Hev)
      as [Hstep [Hp1 [Ha1 Hm1]]].
    destruct (IHm2 r (Kd2_step pa) ltac:(lia) Ha1 Hm1)
      as [Hrun [Hp2 [Ha2 Hm2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, Hstep |].
      rewrite <- lpow_10_comm. exact Hrun.
    + lia.
    + exact Ha2.
    + exact Hm2.
Qed.

(** ** Bridge, 11th f_(omega+2) cycle, and halting theorem *)

Definition Bridge_pa (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  (p + 1, W p (W p (a + 2))).

Lemma Bridge_all : forall r pa,
  3 <= fst pa -> 4 <= snd pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 (1 >> 0 >> 0 >> 1 >> 0 >> 0 >> r)%sym -->+
    Ce_gen (fst (Bridge_pa pa)) (snd (Bridge_pa pa)) 0 r /\
  fst pa + 1 <= fst (Bridge_pa pa) /\
  4 <= snd (Bridge_pa pa) /\
  snd (Bridge_pa pa) mod 2 = 0.
Proof.
  intros r [p a] Hp Ha Hev. cbn [fst snd Bridge_pa] in *.
  pose proof (W_grow p (a + 2)) as Hg1.
  pose proof (W_grow p (W p (a + 2))) as Hg2.
  pose proof (W_par p (a + 2)) as Hp1.
  pose proof (W_par p (W p (a + 2))) as Hp2.
  set (w1 := W p (a + 2)) in *.
  set (w2 := W p w1) in *.
  split; [| split; [| split]].
  - apply BRIDGE.
  - lia.
  - lia.
  - mods; lia.
Qed.

Lemma Kc_unfold : forall p a,
  Kc (p, a) = (p + a / 2, W (p - 1) 1).
Proof. reflexivity. Qed.

Lemma Kd1_step_unfold : forall p a,
  Kd1_step (p, a) = iter (a / 2) Kc (Kd_base p).
Proof. reflexivity. Qed.

Lemma Kd1_iter_unfold : forall m1 pa,
  Kd1_iter m1 pa = iter m1 Kd1_step pa.
Proof. reflexivity. Qed.

Lemma D1_cycle_unfold : forall p a,
  D1_cycle (p, a) = Kd1_iter (a / 2 + 1) (p - 2, W (p - 2) 1).
Proof. reflexivity. Qed.

Lemma Kd2_part1_unfold : forall p a,
  Kd2_part1 (p, a) = Kd1_step (iter (a / 2 - 1) Kc (Kd_base p)).
Proof. reflexivity. Qed.

Lemma Kd2_step_unfold : forall pa,
  Kd2_step pa = D1_cycle (Kd2_part1 pa).
Proof. reflexivity. Qed.

Lemma Kd2_iter_unfold : forall m2 pa,
  Kd2_iter m2 pa = iter m2 Kd2_step pa.
Proof. reflexivity. Qed.

Lemma Bridge_pa_unfold : forall p a,
  Bridge_pa (p, a) = (p + 1, W p (W p (a + 2))).
Proof. reflexivity. Qed.

Opaque W Kc Kd_base Kd1_step Kd1_iter D1_cycle Kd2_part1 Kd2_step Kd2_iter Bridge_pa.

Definition pa_0  : nat * nat := (26, W 21 1).
Definition pa_9  : nat * nat := Kd2_iter 9 pa_0.
Definition pa_br : nat * nat := Bridge_pa pa_9.
Definition pa_10 : nat * nat := Kd1_iter 114 pa_br.
Definition pa_11 : nat * nat := D1_cycle pa_10.

Lemma pa_0_def  : pa_0  = (26, W 21 1).       Proof. reflexivity. Qed.
Lemma pa_9_def  : pa_9  = Kd2_iter 9 pa_0.    Proof. reflexivity. Qed.
Lemma pa_br_def : pa_br = Bridge_pa pa_9.     Proof. reflexivity. Qed.
Lemma pa_10_def : pa_10 = Kd1_iter 114 pa_br. Proof. reflexivity. Qed.
Lemma pa_11_def : pa_11 = D1_cycle pa_10.     Proof. reflexivity. Qed.

Opaque pa_0 pa_9 pa_br pa_10 pa_11.

Lemma lpow_10_10_9 : forall r,
  ([1; 0]^^10 *> r)%sym = ([1; 0]^^9 *> 1 >> 0 >> r)%sym.
Proof.
  intros r. change 10 with (9 + 1). rewrite lpow_add, Str_app_assoc. reflexivity.
Qed.

Lemma pa_init_props : forall p m,
  5 <= p ->
  5 <= fst (p, W m 1) /\ 4 <= snd (p, W m 1) /\ snd (p, W m 1) mod 2 = 0.
Proof.
  intros p m Hp. cbn [fst snd].
  pose proof (W_grow m 1) as Hg.
  pose proof (W_par m 1) as Hp2.
  split; [lia | split; [lia | exact Hp2]].
Qed.

Lemma pa_0_props :
  5 <= fst pa_0 /\ 4 <= snd pa_0 /\ snd pa_0 mod 2 = 0.
Proof.
  rewrite pa_0_def. apply pa_init_props. lia.
Qed.

Lemma run_to_end : c0 -->* c_end (fst pa_11) (snd pa_11).
Proof.
  destruct pa_0_props as [Hp0 [Ha0 Hm0]].
  destruct (Kd2_loop 9 (0 >> 1 >> 0 >> 0 >> [1]^^228 *> const 0)%sym pa_0 ltac:(lia) Ha0 Hm0)
    as [Hkd2 [Hp9 [Ha9 Hm9]]].
  rewrite <- pa_9_def in Hkd2, Hp9, Ha9, Hm9.
  destruct (Bridge_all ([1]^^228 *> const 0)%sym pa_9 ltac:(lia) Ha9 Hm9)
    as [Hbr [Hpbr [Habr Hmbr]]].
  rewrite <- pa_br_def in Hbr, Hpbr, Habr, Hmbr.
  destruct (Kd1_loop 114 (const 0)%sym pa_br ltac:(lia) Habr Hmbr)
    as [Hkd1 [Hp10 [Ha10 Hm10]]].
  rewrite <- pa_10_def in Hkd1, Hp10, Ha10, Hm10.
  change (2 * 114) with 228 in Hkd1.
  destruct (D1_cycle_all (const 0)%sym pa_10 ltac:(lia) Ha10 Hm10)
    as [Hd1 [Hp11 [Ha11 Hm11]]].
  rewrite <- pa_11_def in Hd1, Hp11, Ha11, Hm11.
  eapply evstep_trans; [apply init_ce |].
  replace 26 with (fst pa_0) by (rewrite pa_0_def; reflexivity).
  replace (W 21 1) with (snd pa_0) by (rewrite pa_0_def; reflexivity).
  rewrite lpow_10_10_9.
  eapply evstep_trans; [exact Hkd2 |].
  eapply evstep_trans; [apply progress_evstep, Hbr |].
  eapply evstep_trans; [exact Hkd1 |].
  rewrite const_unfold at 1.
  eapply evstep_trans; [apply progress_evstep, Hd1 |].
  apply progress_evstep, HALT_step.
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run_to_end) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts, c_end_halted.
Qed.

(** ** Fast-Growing Hierarchy up to f_(omega+3) and domination bounds *)

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | 0 => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega  (n : nat) : nat := f n n.
Definition f_omega1 (n : nat) : nat := iter n f_omega n.
Definition f_omega2 (n : nat) : nat := iter n f_omega1 n.
Definition f_omega3 (n : nat) : nat := iter n f_omega2 n.

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

Lemma f_omega2_id : forall n, n <= f_omega2 n.
Proof. intros n. unfold f_omega2. apply iter_ge, f_omega1_id. Qed.

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

Lemma f_omega3_unfold : forall n, f_omega3 n = iter n f_omega2 n.
Proof. reflexivity. Qed.

Opaque f f_omega f_omega1 f_omega2 f_omega3.

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

(** ** Domination across Kc, Kd1_step, Kd1_iter, D1_cycle, Kd2_step, and Kd2_iter *)

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
  assert (Hc : a / 2 = S (a / 2 - 1)) by (mods; lia).
  assert (Hdiv : n <= (a / 2 - 1) / 2) by (mods; lia).
  rewrite Hc. cbn [iter].
  destruct (Kd_base_props p ltac:(lia)) as [Hbp [Hba _]].
  destruct (Kc_dom_any (a / 2 - 1) (Kd_base p) ltac:(lia) Hba)
    as [Hp1 [Ha1 Hdom1]].
  destruct (Kc_dom1 (iter (a / 2 - 1) Kc (Kd_base p)) Hp1 Ha1)
    as [Hp2 [_ Ha2]].
  assert (H1 : f_omega1 n <= iter ((a / 2 - 1) / 2) f_omega (fst (Kd_base p) - 3)).
  { Transparent f_omega1. unfold f_omega1. Opaque f_omega1.
    transitivity (iter n f_omega (fst (Kd_base p) - 3)).
    - apply iter_mono_x; [apply f_omega_mono | lia].
    - apply iter_mono_n; [apply f_omega_id | exact Hdiv]. }
  set (pa' := iter (a / 2 - 1) Kc (Kd_base p)) in *.
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

Lemma D1_init_w : forall n pa,
  1 <= n -> ok_pa n pa -> ok_pa_w n (fst pa - 2, W (fst pa - 2) 1).
Proof.
  intros n [p a] Hn [Hp Ha]. unfold ok_pa, ok_pa_w in *. cbn [fst snd] in *.
  destruct p as [| [| [| [| [| [| m]]]]]]; try lia.
  replace (S (S (S (S (S (S m))))) - 2) with (S (S (S (S m)))) by lia.
  pose proof (W_omega_bound1 (S m) 1 ltac:(lia)) as Hw.
  pose proof (f_omega_id (S (S m))) as Hid.
  split; lia.
Qed.

Lemma D1_cycle_dom : forall n pa,
  1 <= n -> ok_pa n pa -> ok_pa (f_omega2 n) (D1_cycle pa).
Proof.
  intros n [p a] Hn Hok.
  pose proof (D1_init_w n (p, a) Hn Hok) as Hinit. cbn [fst snd] in Hinit.
  destruct Hok as [Hp Ha]. cbn [fst snd] in Hp, Ha.
  rewrite D1_cycle_unfold, Kd1_iter_unfold.
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

Lemma Kd2_part1_dom : forall n pa,
  1 <= n -> ok_pa n pa -> ok_pa (f_omega1 n) (Kd2_part1 pa).
Proof.
  intros n [p a] Hn [Hp Ha]. unfold ok_pa in *. cbn [fst snd] in *.
  rewrite Kd2_part1_unfold.
  assert (Hc : a / 2 - 1 = S (a / 2 - 2)) by (mods; lia).
  rewrite Hc. cbn [iter].
  destruct (Kd_base_props p ltac:(lia)) as [Hbp [Hba _]].
  destruct (Kc_dom_any (a / 2 - 2) (Kd_base p) ltac:(lia) Hba)
    as [Hp1 [Ha1 Hdom1]].
  destruct (Kc_dom1 (iter (a / 2 - 2) Kc (Kd_base p)) Hp1 Ha1)
    as [Hp2 [_ Ha2]].
  set (pa0 := iter (a / 2 - 2) Kc (Kd_base p)) in *.
  assert (Hge0 : n <= fst pa0 - 3).
  { transitivity (fst (Kd_base p) - 3); [lia |].
    transitivity (iter ((a / 2 - 2) / 2) f_omega (fst (Kd_base p) - 3)); [| exact Hdom1].
    apply iter_ge, f_omega_id. }
  pose proof (f_omega_id (fst pa0 - 3)) as Hid.
  assert (Hok1 : ok_pa_w n (Kc pa0)) by (unfold ok_pa_w; split; lia).
  apply Kd1_step_dom_w; [exact Hn | exact Hok1].
Qed.

Lemma Kd2_step_dom : forall n pa,
  1 <= n -> ok_pa n pa -> ok_pa (f_omega2 n) (Kd2_step pa).
Proof.
  intros n pa Hn Hok.
  rewrite Kd2_step_unfold.
  pose proof (Kd2_part1_dom n pa Hn Hok) as H1.
  pose proof (f_omega1_id n) as Hid.
  pose proof (ok_pa_mono n (f_omega1 n) (Kd2_part1 pa) Hid H1) as H2.
  apply D1_cycle_dom; [exact Hn | exact H2].
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

Theorem Kd2_loop_f_omega3 : forall m2 r n pa,
  1 <= n -> n <= m2 -> ok_pa n pa -> snd pa mod 2 = 0 ->
  Ce_gen (fst pa) (snd pa) 0 ([1; 0]^^m2 *> 1 >> 0 >> r)%sym -->*
    Ce_gen (fst (Kd2_iter m2 pa)) (snd (Kd2_iter m2 pa)) 0 (1 >> 0 >> r)%sym /\
  ok_pa (f_omega3 n) (Kd2_iter m2 pa) /\
  snd (Kd2_iter m2 pa) mod 2 = 0.
Proof.
  intros m2 r n pa Hn Hnm Hok Hev.
  destruct Hok as [Hp Ha].
  destruct (Kd2_loop m2 r pa ltac:(lia) ltac:(lia) Hev) as [Hrun [_ [_ Hm]]].
  pose proof (Kd2_iter_dom m2 n pa Hn (conj Hp Ha)) as Hdom.
  assert (Hle : f_omega3 n <= iter m2 f_omega2 n).
  { Transparent f_omega3. unfold f_omega3. Opaque f_omega3.
    apply iter_mono_n; [apply f_omega2_id | exact Hnm]. }
  split; [exact Hrun | split; [eapply ok_pa_mono; [exact Hle | exact Hdom] | exact Hm]].
Qed.

Lemma Bridge_dom : forall n pa,
  ok_pa n pa -> ok_pa n (Bridge_pa pa).
Proof.
  intros n [p a] [Hp Ha]. unfold ok_pa in *. rewrite Bridge_pa_unfold. cbn [fst snd] in *.
  pose proof (W_grow p (a + 2)).
  pose proof (W_grow p (W p (a + 2))).
  split; lia.
Qed.

Lemma ok_pa_init : forall p m,
  9 <= p - 5 -> 9 <= S m ->
  ok_pa 9 (p, W (S (S (S m))) 1).
Proof.
  intros p m Hp Hm. unfold ok_pa. cbn [fst snd].
  pose proof (W_omega_bound1 m 1 ltac:(lia)) as Hw.
  pose proof (f_omega_id (S m)) as Hid.
  split; lia.
Qed.

Lemma ok_pa_0 : ok_pa 9 pa_0.
Proof.
  rewrite pa_0_def. apply (ok_pa_init 26 18); lia.
Qed.

Theorem halt_f_omega3 :
  c0 -->* c_end (fst pa_11) (snd pa_11) /\
  halted tm (c_end (fst pa_11) (snd pa_11)) /\
  f_omega2 (f_omega3 9) <= fst pa_11 - 5 /\
  4 * f_omega2 (f_omega3 9) + 6 <= snd pa_11.
Proof.
  pose proof (Kd2_iter_dom 9 9 pa_0 ltac:(lia) ok_pa_0) as H9.
  rewrite <- pa_9_def, <- f_omega3_unfold in H9.
  assert (Hpos9 : 1 <= f_omega3 9) by (pose proof (f_omega3_id 9); lia).
  pose proof (Bridge_dom (f_omega3 9) pa_9 H9) as Hbr.
  rewrite <- pa_br_def in Hbr.
  pose proof (Kd1_iter_dom 114 (f_omega3 9) pa_br Hpos9 Hbr) as H10.
  rewrite <- pa_10_def in H10.
  pose proof (iter_ge f_omega1 f_omega1_id 114 (f_omega3 9)) as Hge10.
  pose proof (ok_pa_mono (f_omega3 9) (iter 114 f_omega1 (f_omega3 9)) pa_10 Hge10 H10) as H10'.
  pose proof (D1_cycle_dom (f_omega3 9) pa_10 Hpos9 H10') as [Hp11 Ha11].
  rewrite <- pa_11_def in Hp11, Ha11.
  refine (conj run_to_end (conj (c_end_halted _ _) (conj Hp11 Ha11))).
Qed.

(** ** Score in the repository's standard form (added for publication; the theorems above are Argon's) *)

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
  exists P, ([S0; S1; S1] ++ [S1]^^(a + 2) ++ [S0; S1]^^p), [S1], S0.
  split.
  - unfold c_end. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

Theorem score_exact :
  exists c, c0 -->* c /\ halted tm c /\ ones c (fst pa_11 + snd pa_11 + 5).
Proof.
  exists (c_end (fst pa_11) (snd pa_11)).
  split; [exact run_to_end |].
  split; [apply c_end_halted |].
  apply ones_c_end.
Qed.

Theorem sigma_lower_bound :
  exists c N, c0 -->* c /\ halted tm c /\ ones c N /\ f_omega2 (f_omega3 9) < N.
Proof.
  destruct halt_f_omega3 as [Hrun [Hhalt [Hp Ha]]].
  exists (c_end (fst pa_11) (snd pa_11)), (fst pa_11 + snd pa_11 + 5).
  split; [exact Hrun |]. split; [exact Hhalt |]. split; [apply ones_c_end |].
  lia.
Qed.
