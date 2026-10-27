(** * The 11-state machine M11b halts (main theorem [halt]); its score bounds are in BB11_M11b_fgh.v *)

From BB8 Require Import Individual112.
From Coq Require Import Lia PeanoNat List Wf_nat.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RG0LH_1RK1RC_0LD1LA_0RE1LD_0LI1RF_---0RG_1RB1RG_1LA1LH_0LK0LJ_1LH1LI_1LJ1RE *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, G)  | A, 1 => Some (0, L, H)
  | B, 0 => Some (1, R, K)  | B, 1 => Some (1, R, C)
  | C, 0 => Some (0, L, D)  | C, 1 => Some (1, L, A)
  | D, 0 => Some (0, R, E)  | D, 1 => Some (1, L, D)
  | E, 0 => Some (0, L, I)  | E, 1 => Some (1, R, F)
  | F, 0 => None            | F, 1 => Some (0, R, G)
  | G, 0 => Some (1, R, B)  | G, 1 => Some (1, R, G)
  | H, 0 => Some (1, L, A)  | H, 1 => Some (1, L, H)
  | I, 0 => Some (0, L, K)  | I, 1 => Some (0, L, J)
  | J, 0 => Some (1, L, H)  | J, 1 => Some (1, L, I)
  | K, 0 => Some (1, L, J)  | K, 1 => Some (1, R, E)
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

Lemma cr_GR_1_1 : forall n l r, l {{G}}> [1]^^n *> r -->* [1]^^n *> l {{G}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_DL_1_1 : forall n l r, [1]^^n *> l <{{D}} r -->* l <{{D}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_HL_1_1 : forall n l r, [1]^^n *> l <{{H}} r -->* l <{{H}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_HL_01_01 : forall n l r, [0; 1]^^n *> l <{{H}} r -->* l <{{H}} [0; 1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_IL_11_10 : forall n l r, [1; 1]^^n *> l <{{I}} r -->* l <{{I}} [1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_JL_11_01 : forall n l r, [1; 1]^^n *> l <{{J}} r -->* l <{{J}} [0; 1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** ** Configurations and inner cascade rules *)

Definition Ca (j b : nat) (z : side) : Q * tape :=
  ([1]^^b *> [0; 1]^^j *> const 0) {{G}}> (0 >> z).

Definition Ch (j b : nat) (z : side) : Q * tape :=
  ([0; 1]^^j *> const 0) <{{H}} (1 >> [1]^^b *> 0 >> z).

Definition Ce (p a c : nat) (z : side) : Q * tape :=
  ([1]^^(a + 2) *> [0; 1]^^p *> const 0) {{K}}> ([1; 0]^^c *> z).

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
  follow cr_GR_1_1.
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
  Ca j b (0 >> z) -->+ ([1]^^(b + 2) *> [0; 1]^^j *> const 0) {{K}}> z.
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
  follow cr_GR_1_1.
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
  ([1]^^(2 * k + 2) *> [0; 1]^^(S p') *> const 0) {{K}}> (1 >> 0 >> r) -->+
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

Lemma K_EVEN_0 : forall p' k r,
  ([1]^^(2 * k + 2) *> [0; 1]^^(S p') *> const 0) {{K}}> (0 >> r) -->+
  Ch p' 1 ([1; 0]^^k *> 1 >> 1 >> r).
Proof.
  intros p' k r. unfold Ch.
  replace (2 * k + 2)%nat with (2 + 2 * k)%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_JL_11_01.
  align_tape.
  execute; finish_norm.
Qed.

Lemma K_ODD_0 : forall p' m,
  ([1]^^(2 * m + 1 + 2) *> [0; 1]^^(S (S p')) *> const 0) {{K}}> (const 0) -->+
  Ch p' 1 (0 >> [1; 0]^^(S m) *> 1 >> 1 >> const 0).
Proof.
  intros p' m. unfold Ch.
  rewrite const_unfold at 2.
  replace (2 * m + 1 + 2)%nat with (2 * S m + 1)%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] (S m)). cbn [app].
  start_progress.
  follow cr_JL_11_01.
  align_tape.
  execute; finish_norm.
Qed.

(** ** Halting configuration *)

Definition c_end (p a : nat) : Q * tape :=
  ([1]^^(a + 4) *> [0; 1]^^p *> const 0) {{F}}> (const 0).

Lemma HALT_step : forall p a,
  Ce p a 0 (1 >> 1 >> const 0) -->+ c_end p a.
Proof.
  intros p a. unfold Ce, c_end. cbn [lpow Str_app].
  start_progress.
  finish_norm.
Qed.

Lemma c_end_halted : forall p a, halted tm (c_end p a).
Proof. intros p a. unfold c_end; simpl; reflexivity. Qed.

(** ** Exact hierarchy functions W and Kc *)

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

Lemma BLK_iter : forall j a b z,
  Ca j b (blk a z) -->+ Ca (S j) (iter a (W j) b) z.
Proof.
  intros j a b z. apply (BLK_iter_aux j (CH_CA j) a b z).
Qed.

Lemma CE_EVEN : forall p' k c z,
  Ce (S p') (2 * k) (S c) z -->+ Ce (p' + S k) (W p' 1) c z.
Proof.
  intros p' k c z. unfold Ce.
  cbn [lpow Str_app].
  eapply progress_evstep_trans; [apply E_EVEN |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  follow (CA_SH_iter (S k) p' (W p' 1) (0 >> [1; 0]^^c *> z)%sym).
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  finish_norm.
Qed.

(** ** Initial steps from blank tape c0 *)

Definition z0 : side := (0 >> [1; 0]^^7 *> 1 >> 1 >> const 0)%sym.

Lemma init_40 : c0 -->* Ch 1 4 (1 >> 0 >> const 0)%sym.
Proof.
  unfold Ch. cbn [lpow Str_app].
  do 40 step. finish_norm.
Qed.

Lemma init_254 : c0 -->* Ca 2 17 (const 0)%sym.
Proof.
  follow init_40.
  eapply evstep_trans; [apply progress_evstep, (CH_CA 1 4 (1 >> 0 >> const 0)%sym) |].
  change (W 1 4) with 17.
  apply progress_evstep, (CA_SH 1 17 (const 0)%sym).
Qed.

Lemma init_361 : c0 -->* Ch 1 1 (0 >> [1; 0]^^3 *> z0)%sym.
Proof.
  follow init_254.
  unfold Ca, Ch, z0. cbn [lpow Str_app].
  do 107 step. finish_norm.
Qed.

Lemma init_424 : c0 -->* Ce 1 8 3 z0.
Proof.
  follow init_361.
  eapply evstep_trans; [apply progress_evstep, (CH_CA 1 1 (0 >> [1; 0]^^3 *> z0)%sym) |].
  change (W 1 1) with 8.
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  unfold Ce. finish_norm.
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

Definition Kc (pa : nat * nat) : nat * nat :=
  let '(p, a) := pa in
  (p + a / 2, W (p - 1) 1).

Lemma Kc_step : forall c z pa,
  1 <= fst pa -> snd pa mod 2 = 0 ->
  Ce (fst pa) (snd pa) (S c) z -->+ Ce (fst (Kc pa)) (snd (Kc pa)) c z.
Proof.
  intros c z [p a] Hp Hev. cbn [fst snd Kc] in *.
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

Lemma Kc_loop : forall c z pa,
  1 <= fst pa -> 2 <= snd pa -> snd pa mod 2 = 0 ->
  Ce (fst pa) (snd pa) c z -->* Ce (fst (iter c Kc pa)) (snd (iter c Kc pa)) 0 z /\
  fst pa + c <= fst (iter c Kc pa) /\
  2 <= snd (iter c Kc pa) /\
  snd (iter c Kc pa) mod 2 = 0.
Proof.
  induction c as [| c IHc]; intros z pa Hp Ha Hev.
  - cbn [iter]. split; [finish | split; [lia | split; [lia | exact Hev]]].
  - rewrite iter_S'.
    destruct (Kc_props pa Hp Ha Hev) as [Hp1 [Ha1 Hm1]].
    destruct (IHc z (Kc pa) ltac:(lia) Ha1 Hm1) as [Hrun [Hp2 [Ha2 Hm2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, (Kc_step c z pa Hp Hev) | exact Hrun].
    + lia.
    + exact Ha2.
    + exact Hm2.
Qed.

(** ** Bridge between Phase 1 (casc 4..6) and Phase 2 (casc 12..end) *)

Lemma z0_blk : forall k,
  ([1; 0]^^k *> 1 >> 1 >> [1; 0]^^7 *> 1 >> 1 >> const 0)%sym =
  ([1; 0]^^k *> blk 2 ([1; 0]^^6 *> blk 1 (const 0)))%sym.
Proof.
  intros k. unfold blk.
  rewrite const_unfold at 1.
  reflexivity.
Qed.

Lemma BRIDGE_step : forall p' k,
  Ce (S p') (2 * k) 0 z0 -->+
  Ch (p' + k + 6) 1 (0 >> [1; 0]^^(W (p' + k + 7) (W (p' + k) (W (p' + k) (W p' 1))) / 2 + 1) *> 1 >> 1 >> const 0)%sym.
Proof.
  intros p' k. unfold Ce, z0. cbn [lpow Str_app].
  eapply progress_evstep_trans; [apply K_EVEN_0 |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  rewrite z0_blk.
  follow (CA_SH_iter k p' (W p' 1) (blk 2 ([1; 0]^^6 *> blk 1 (const 0)))%sym).
  eapply evstep_trans; [apply progress_evstep, BLK_iter |].
  follow (CA_SH_iter 6 (S (p' + k)) (iter 2 (W (p' + k)) (W p' 1)) (blk 1 (const 0))%sym).
  replace (S (p' + k) + 6) with (p' + k + 7) by lia.
  eapply evstep_trans; [apply progress_evstep, BLK_iter |].
  cbn [iter].
  rewrite const_unfold at 1.
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  set (j9 := p' + k + 7).
  set (w9 := W (p' + k) (W (p' + k) (W p' 1))).
  set (w10 := W j9 w9).
  assert (Hw9_par : w9 mod 2 = 0).
  { unfold w9. change (W (p' + k) (W (p' + k) (W p' 1))) with (iter 2 (W (p' + k)) (W p' 1)).
    rewrite (iter_par_nat (W (p' + k)) (W_par (p' + k)) 2 (W p' 1)).
    pose proof (W_par p' 1). mods; lia. }
  assert (Hw10_odd : w10 = 2 * (w10 / 2) + 1).
  { unfold w10. pose proof (W_par j9 w9). mods; lia. }
  replace (S j9) with (S (S (p' + k + 6))) by (unfold j9; lia).
  rewrite Hw10_odd at 1.
  eapply evstep_trans; [apply progress_evstep, K_ODD_0 |].
  replace (S (w10 / 2)) with (w10 / 2 + 1) by lia.
  apply evstep_refl.
Qed.

Definition Bridge (pa : nat * nat) : nat * nat * nat :=
  let '(p, a) := pa in
  let p' := p - 1 in
  let k := a / 2 in
  let j7 := p' + k in
  let j9 := j7 + 7 in
  let w9 := W j7 (W j7 (W p' 1)) in
  let w10 := W j9 w9 in
  let p10 := j7 + 6 in
  (p10, W p10 1, w10 / 2 + 1).

Lemma Bridge_all : forall pa,
  1 <= fst pa -> 2 <= snd pa -> snd pa mod 2 = 0 ->
  let '(p10, a10, c10) := Bridge pa in
  Ce (fst pa) (snd pa) 0 z0 -->+ Ce p10 a10 c10 (1 >> 1 >> const 0)%sym /\
  1 <= p10 /\ 2 <= a10 /\ a10 mod 2 = 0.
Proof.
  intros [p a] Hp Ha Hev. cbn [fst snd Bridge] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  assert (Ha_eq : a = 2 * (a / 2)) by (mods; lia).
  set (k := a / 2) in *.
  set (p10 := p' + k + 6).
  set (c10 := W (p' + k + 7) (W (p' + k) (W (p' + k) (W p' 1))) / 2 + 1).
  pose proof (W_grow p10 1) as Hwg.
  pose proof (W_par p10 1) as Hwp.
  split; [| split; [unfold p10; lia | split; [lia | mods; lia]]].
  rewrite Ha_eq at 1.
  eapply progress_evstep_trans; [apply BRIDGE_step |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  apply evstep_refl.
Qed.

(** ** Full halting trajectory of M11 *)

Definition pa1 : nat * nat := iter 3 Kc (1, 8).
Definition br1 : nat * nat * nat := Bridge pa1.
Definition pa2_0 : nat * nat := fst br1.
Definition c2_0 : nat := snd br1.
Definition pa_end : nat * nat := iter c2_0 Kc pa2_0.

Lemma run_end :
  c0 -->* c_end (fst pa_end) (snd pa_end).
Proof.
  unfold pa_end, pa2_0, c2_0, br1, pa1.
  destruct (Kc_loop 3 z0 (1, 8) ltac:(cbn; lia) ltac:(cbn; lia) eq_refl)
    as [Hkc1 [Hp1 [Ha1 Hm1]]].
  pose proof (Bridge_all (iter 3 Kc (1, 8)) ltac:(lia) Ha1 Hm1) as Hbr.
  destruct (Bridge (iter 3 Kc (1, 8))) as [[p10 a10] c10] eqn:Ebr.
  cbn [fst snd] in *.
  destruct Hbr as [Hbr_step [Hp10 [Ha10 Hm10]]].
  destruct (Kc_loop c10 (1 >> 1 >> const 0)%sym (p10, a10) Hp10 Ha10 Hm10)
    as [Hkc2 _].
  cbn [fst snd] in Hkc2.
  follow init_424.
  follow Hkc1.
  eapply evstep_trans; [apply progress_evstep, Hbr_step |].
  follow Hkc2.
  apply progress_evstep, HALT_step.
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run_end) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply c_end_halted.
Qed.
