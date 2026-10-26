(** * The 12-state machine M12 halts (main theorem [halt]); its score bounds are in BB12_M12_bound.v *)

From BB8 Require Import Individual122.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LK1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_0LH1LK *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, B)  | A, 1 => Some (1, TM.R, A)
  | B, 0 => Some (1, TM.R, I)  | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)  | C, 1 => Some (1, TM.L, G)
  | D, 0 => Some (0, TM.R, E)  | D, 1 => Some (1, TM.L, D)
  | E, 0 => Some (1, TM.L, K)  | E, 1 => Some (1, TM.R, F)
  | F, 0 => Some (1, TM.R, G)  | F, 1 => Some (0, TM.R, A)
  | G, 0 => Some (1, TM.R, A)  | G, 1 => Some (0, TM.L, H)
  | H, 0 => Some (1, TM.L, G)  | H, 1 => Some (1, TM.L, H)
  | I, 0 => Some (1, TM.R, E)  | I, 1 => Some (0, TM.L, J)
  | J, 0 => Some (1, TM.L, H)  | J, 1 => Some (1, TM.L, I)
  | K, 0 => None               | K, 1 => Some (0, TM.L, L)
  | L, 0 => Some (0, TM.L, H)  | L, 1 => Some (1, TM.L, K)
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

(** ** Halting step at d = 0 *)

Definition c_end (p m : nat) : Q * tape :=
  ([0; 1]^^p *> const 0) <{{K}} ([1; 0]^^(m + 2) *> 1 >> const 0).

Lemma HALT_step : forall p m,
  Cd p (2 * m + 1) 0 -->+ c_end p m.
Proof.
  intros p m. unfold Cd, c_end.
  replace (2 * m + 1 + 2)%nat with (1 + (2 * m + 2))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] m). cbn [app].
  start_progress.
  follow cr_KL_11_10.
  align_tape.
  execute; finish_norm.
Qed.

Lemma c_end_halted : forall p m, halted tm (c_end p m).
Proof. intros [| p'] m; unfold c_end; simpl; reflexivity. Qed.

(** ** Exact hierarchy functions W, Kc, Kd_step *)

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

(** ** Growth, parity, and mod-6 invariants *)

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

Lemma W_1_mod6 : forall b,
  W 1 b mod 6 = (if b mod 2 =? 0 then 5 else 2).
Proof.
  intros b. rewrite W_1.
  destruct (b mod 2 =? 0) eqn:Heq;
    [apply Nat.eqb_eq in Heq | apply Nat.eqb_neq in Heq];
    mods; lia.
Qed.

Lemma W_S_mod6 : forall j b,
  W (S j) b mod 6 = (if b mod 2 =? 0 then 5 else 2).
Proof.
  induction j as [| j IHj]; intros b.
  - apply W_1_mod6.
  - change (W (S (S j)) b) with (iter (S b) (W (S j)) 2).
    cbn [iter].
    rewrite (IHj (iter b (W (S j)) 2)).
    rewrite (iter_par_nat (W (S j)) (W_par (S j)) b 2).
    replace ((2 + b) mod 2) with (b mod 2) by (mods; lia).
    reflexivity.
Qed.

Lemma W_S_1_mod6 : forall j, W (S j) 1 mod 6 = 2.
Proof.
  intros j. rewrite W_S_mod6. reflexivity.
Qed.

Opaque W.

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
  assert (Ha : a = 2 * (a / 2)) by (mods; lia).
  replace (S p' + a / 2) with (p' + S (a / 2)) by lia.
  rewrite Ha at 1.
  apply CE_EVEN.
Qed.

Lemma Kc_props : forall pa,
  1 <= fst pa -> 2 <= snd pa -> snd pa mod 2 = 0 ->
  fst pa + 1 <= fst (Kc pa) /\
  2 <= snd (Kc pa) /\
  snd (Kc pa) mod 2 = 0.
Proof.
  intros [p a] Hp Ha Hev. cbn [fst snd Kc] in *.
  pose proof (W_grow (p - 1) 1).
  pose proof (W_par (p - 1) 1).
  split; [| split]; mods; lia.
Qed.

Lemma Kc_mod6 : forall pa,
  2 <= fst pa -> snd (Kc pa) mod 6 = 2.
Proof.
  intros [p a] Hp. cbn [fst snd Kc] in *.
  destruct p as [| [| p']]; [lia | lia |].
  replace (S (S p') - 1) with (S p') by lia.
  apply W_S_1_mod6.
Qed.

Lemma Kc_loop : forall c d pa,
  1 <= fst pa -> 2 <= snd pa -> snd pa mod 2 = 0 ->
  Ce (fst pa) (snd pa) c d -->* Ce (fst (iter c Kc pa)) (snd (iter c Kc pa)) 0 d /\
  fst pa + c <= fst (iter c Kc pa) /\
  2 <= snd (iter c Kc pa) /\
  snd (iter c Kc pa) mod 2 = 0.
Proof.
  induction c as [| c IHc]; intros d pa Hp Ha Hev.
  - cbn [iter]. split; [finish | split; [lia | split; [lia | exact Hev]]].
  - rewrite iter_S'.
    destruct (Kc_props pa Hp Ha Hev) as [Hp1 [Ha1 Hm1]].
    destruct (IHc d (Kc pa) ltac:(lia) Ha1 Hm1) as [Hrun [Hp2 [Ha2 Hm2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, (Kc_step c d pa Hp Hev) | exact Hrun].
    + lia.
    + exact Ha2.
    + exact Hm2.
Qed.

Lemma Kc_loop_mod6 : forall c pa,
  2 <= fst pa -> 2 <= snd pa -> snd pa mod 2 = 0 ->
  snd (iter (S c) Kc pa) mod 6 = 2.
Proof.
  intros c pa Hp Ha Hev.
  replace (S c) with (1 + c) by lia.
  rewrite iter_add. cbn [iter].
  destruct (Kc_loop c 0 pa ltac:(lia) Ha Hev) as [_ [Hp' _]].
  apply Kc_mod6. lia.
Qed.

Definition Kc_full (pb : nat * nat) : nat * nat :=
  let '(p, b) := pb in
  iter (b / 2) Kc (p - 1, W (p - 1) 3).

Lemma Kc_full_all : forall d pb,
  3 <= fst pb -> 3 <= snd pb -> snd pb mod 2 = 1 ->
  Cd (fst pb) (snd pb) (S d) -->+ Ce (fst (Kc_full pb)) (snd (Kc_full pb)) 0 d /\
  fst pb <= fst (Kc_full pb) /\
  2 <= snd (Kc_full pb) /\
  snd (Kc_full pb) mod 2 = 0 /\
  snd (Kc_full pb) mod 6 = 2.
Proof.
  intros d [p b] Hp Hb Hodd. cbn [fst snd Kc_full] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  assert (Hb_eq : b = 2 * (b / 2) + 1) by (mods; lia).
  assert (Hb_ge : 1 <= b / 2) by (mods; lia).
  pose proof (W_grow p' 3) as Hw3_grow.
  pose proof (W_par p' 3) as Hw3_par.
  assert (Hw3_ev : W p' 3 mod 2 = 0) by (mods; lia).
  destruct (Kc_loop (b / 2) d (p', W p' 3) ltac:(cbn; lia) ltac:(cbn; lia) Hw3_ev)
    as [Hrun [Hp1 [Ha1 Hm1]]].
  assert (Hm6 : snd (iter (b / 2) Kc (p', W p' 3)) mod 6 = 2).
  { replace (b / 2) with (S (b / 2 - 1)) by lia.
    apply Kc_loop_mod6; cbn [fst snd]; [lia | lia | exact Hw3_ev]. }
  cbn [fst snd] in *.
  split; [| split; [| split; [| split]]].
  - rewrite Hb_eq at 1.
    eapply progress_evstep_trans; [apply C_REL | exact Hrun].
  - lia.
  - exact Ha1.
  - exact Hm1.
  - exact Hm6.
Qed.

Definition Kd_step (pb : nat * nat) : nat * nat :=
  let '(p', a') := Kc_full pb in
  (p', W p' (a' + 4)).

Lemma Kd_step_all : forall d pb,
  3 <= fst pb -> 3 <= snd pb -> snd pb mod 2 = 1 ->
  Cd (fst pb) (snd pb) (S (S (S d))) -->+ Cd (fst (Kd_step pb)) (snd (Kd_step pb)) d /\
  fst pb <= fst (Kd_step pb) /\
  3 <= snd (Kd_step pb) /\
  snd (Kd_step pb) mod 2 = 1.
Proof.
  intros d pb Hp Hb Hodd.
  unfold Kd_step.
  destruct (Kc_full_all (S (S d)) pb Hp Hb Hodd) as [Hkc [Hp1 [Ha1 [Hm1 _]]]].
  set (pa' := Kc_full pb) in *.
  destruct pa' as [p' a']. cbn [fst snd] in *.
  pose proof (W_grow p' (a' + 4)) as Hwg.
  pose proof (W_par p' (a' + 4)) as Hwp.
  split; [| split; [| split]].
  - eapply progress_evstep_trans; [exact Hkc | apply progress_evstep, D_STEP].
  - exact Hp1.
  - lia.
  - mods; lia.
Qed.

Definition Kd_iter (m : nat) (pb : nat * nat) : nat * nat :=
  iter m Kd_step pb.

Lemma Kd_loop : forall m r pb,
  3 <= fst pb -> 3 <= snd pb -> snd pb mod 2 = 1 ->
  Cd (fst pb) (snd pb) (3 * m + r) -->* Cd (fst (Kd_iter m pb)) (snd (Kd_iter m pb)) r /\
  fst pb <= fst (Kd_iter m pb) /\
  3 <= snd (Kd_iter m pb) /\
  snd (Kd_iter m pb) mod 2 = 1.
Proof.
  unfold Kd_iter.
  induction m as [| m IHm]; intros r pb Hp Hb Hodd.
  - cbn [iter]. replace (3 * 0 + r) with r by lia.
    split; [finish | split; [lia | split; [exact Hb | exact Hodd]]].
  - rewrite iter_S'.
    replace (3 * S m + r) with (S (S (S (3 * m + r)))) by lia.
    destruct (Kd_step_all (3 * m + r) pb Hp Hb Hodd) as [Hstep [Hp1 [Hb1 Hm1]]].
    destruct (IHm r (Kd_step pb) ltac:(lia) Hb1 Hm1) as [Hrun [Hp2 [Hb2 Hm2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, Hstep | exact Hrun].
    + lia.
    + exact Hb2.
    + exact Hm2.
Qed.

Definition D_reload (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  (p - 1, W (p - 1) 0).

Lemma D_reload_all : forall pa,
  4 <= fst pa -> 2 <= snd pa -> snd pa mod 2 = 0 ->
  Ce (fst pa) (snd pa) 0 0 -->+ Cd (fst (D_reload pa)) (snd (D_reload pa)) (snd pa / 2 + 2) /\
  3 <= fst (D_reload pa) /\
  3 <= snd (D_reload pa) /\
  snd (D_reload pa) mod 2 = 1.
Proof.
  intros [p a] Hp Ha Hev. cbn [fst snd D_reload] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  assert (Ha_eq : a = 2 * (a / 2)) by (mods; lia).
  pose proof (W_grow p' 0) as Hwg.
  pose proof (W_par p' 0) as Hwp.
  split; [| split; [| split]].
  - rewrite Ha_eq at 1. apply D_REL.
  - lia.
  - lia.
  - mods; lia.
Qed.

(** ** The full run of M12 *)

Definition pb1_0 : nat * nat := D_reload (8, 4).
Definition pb1_1 : nat * nat := Kd_step pb1_0.
Definition pa1 : nat * nat := Kc_full pb1_1.
Definition pb2_0 : nat * nat := D_reload pa1.
Definition pb2 : nat * nat := Kd_iter (snd pa1 / 6 + 1) pb2_0.

Lemma pb1_0_def : pb1_0 = D_reload (8, 4). Proof. reflexivity. Qed.
Lemma pb1_1_def : pb1_1 = Kd_step pb1_0. Proof. reflexivity. Qed.
Lemma pa1_def : pa1 = Kc_full pb1_1. Proof. reflexivity. Qed.
Lemma pb2_0_def : pb2_0 = D_reload pa1. Proof. reflexivity. Qed.
Lemma pb2_def : pb2 = Kd_iter (snd pa1 / 6 + 1) pb2_0. Proof. reflexivity. Qed.
Lemma D_reload_8_4_fst : fst (D_reload (8, 4)) = 7. Proof. reflexivity. Qed.

Opaque Kc Kc_full Kd_step Kd_iter D_reload pb1_0 pb1_1 pa1 pb2_0 pb2.

Lemma run_pa1 :
  c0 -->* Ce (fst pa1) (snd pa1) 0 0 /\
  4 <= fst pa1 /\ 2 <= snd pa1 /\ snd pa1 mod 2 = 0 /\ snd pa1 mod 6 = 2.
Proof.
  rewrite pa1_def, pb1_1_def, pb1_0_def.
  destruct (D_reload_all (8, 4) ltac:(cbn; lia) ltac:(cbn; lia) eq_refl)
    as [Hrel1 [Hp0 [Hb0 Hm0]]].
  cbn [fst snd] in Hrel1. change (4 / 2 + 2) with (S (S (S 1))) in Hrel1.
  destruct (Kd_step_all 1 (D_reload (8, 4)) Hp0 Hb0 Hm0)
    as [Hkd1 [Hp1 [Hb1 Hm1]]].
  destruct (Kc_full_all 0 (Kd_step (D_reload (8, 4))) ltac:(lia) Hb1 Hm1)
    as [Hkc1 [Hp2 [Ha2 [Hme2 Hmm6]]]].
  pose proof D_reload_8_4_fst as Hp0_eq.
  split; [| split; [lia | split; [exact Ha2 | split; [exact Hme2 | exact Hmm6]]]].
  follow init_352.
  eapply evstep_trans; [apply progress_evstep, Hrel1 |].
  eapply evstep_trans; [apply progress_evstep, Hkd1 |].
  apply progress_evstep, Hkc1.
Qed.

Lemma run_round2 : forall pa,
  c0 -->* Ce (fst pa) (snd pa) 0 0 /\
  4 <= fst pa /\ 2 <= snd pa /\ snd pa mod 2 = 0 /\ snd pa mod 6 = 2 ->
  c0 -->* c_end (fst (Kd_iter (snd pa / 6 + 1) (D_reload pa)))
                (snd (Kd_iter (snd pa / 6 + 1) (D_reload pa)) / 2).
Proof.
  intros pa [Hrun1 [Hp1 [Ha1 [Hm2 Hm6]]]].
  destruct (D_reload_all pa Hp1 Ha1 Hm2) as [Hrel2 [Hp2_0 [Hb2_0 Hm2_0]]].
  assert (Hd2 : snd pa / 2 + 2 = 3 * (snd pa / 6 + 1) + 0) by (mods; lia).
  destruct (Kd_loop (snd pa / 6 + 1) 0 (D_reload pa) Hp2_0 Hb2_0 Hm2_0)
    as [Hloop2 [_ [_ Hm_end]]].
  set (pb_end := Kd_iter (snd pa / 6 + 1) (D_reload pa)) in *.
  assert (Hb_end : snd pb_end = 2 * (snd pb_end / 2) + 1) by (mods; lia).
  follow Hrun1.
  eapply evstep_trans; [apply progress_evstep, Hrel2 |].
  rewrite Hd2.
  follow Hloop2.
  rewrite Hb_end at 1.
  apply progress_evstep, HALT_step.
Qed.

Lemma run_pb2 :
  c0 -->* c_end (fst pb2) (snd pb2 / 2).
Proof.
  rewrite !pb2_def, !pb2_0_def.
  exact (run_round2 pa1 run_pa1).
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run_pb2) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply c_end_halted.
Qed.
