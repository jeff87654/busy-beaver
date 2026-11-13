(* machine: 1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_0LM1LK_0LG1LL *)
(** * New BB(13) Champion M13_19: Sigma(13) > f_(omega+2)^19(f_omega(3)) > f_(omega+2)^18(f_(omega+1)^2(3)) *)
(**
   Machine (M12-core form, A-started):
     1RB1RA_1RI1RC_0LD1LG_0RE1LD_0LM1RF_1RG0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LL_0LM1LK_0LG1LL
   Strict first-visit canonical TNF (A-started, all 13 states visited, no symbol flip):
     1RB1RA_1RC1RK_1RD0LM_0LE1RI_0LH1LF_0LE1LG_---0LF_1RA0LJ_1RH0RA_1LH1LJ_0LL1LH_0RD1LL_1LJ1LC

   Beats previous BB(13) champion M13b (> f_(omega+2)^6(f_(omega+1)^2(3))) by 12 full f_(omega+2) levels!
*)

From BB8 Require Import Individual132.
From Coq Require Import ZArith Lia PeanoNat List Ring.
Import ListNotations.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, B)  | A, 1 => Some (1, TM.R, A)
  | B, 0 => Some (1, TM.R, I)  | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)  | C, 1 => Some (1, TM.L, G)
  | D, 0 => Some (0, TM.R, E)  | D, 1 => Some (1, TM.L, D)
  | E, 0 => Some (0, TM.L, M)  | E, 1 => Some (1, TM.R, F)
  | F, 0 => Some (1, TM.R, G)  | F, 1 => Some (0, TM.R, A)
  | G, 0 => Some (1, TM.R, A)  | G, 1 => Some (0, TM.L, H)
  | H, 0 => Some (1, TM.L, G)  | H, 1 => Some (1, TM.L, H)
  | I, 0 => Some (1, TM.R, E)  | I, 1 => Some (0, TM.L, J)
  | J, 0 => Some (1, TM.L, H)  | J, 1 => Some (1, TM.L, I)
  | K, 0 => None               | K, 1 => Some (0, TM.L, L)
  | L, 0 => Some (0, TM.L, M)  | L, 1 => Some (1, TM.L, K)
  | M, 0 => Some (0, TM.L, G)  | M, 1 => Some (1, TM.L, L)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Lemma align_lpow : forall (x : Sym) xs ys n,
  (x::xs)^^n *> x >> ys = x >> (xs ++ [x])^^n *> ys.
Proof.
  induction n; [reflexivity |].
  simpl. repeat rewrite Str_app_assoc. rewrite IHn. reflexivity.
Qed.

Lemma align_lpow_const : forall (x : Sym) xs n,
  (x::xs)^^n *> const x = x >> (xs ++ [x])^^n *> const x.
Proof. intros. rewrite const_unfold at 1. apply align_lpow. Qed.

Ltac align_tape := repeat ((rewrite align_lpow || rewrite align_lpow_const); simpl app).
Ltac norm_nat := repeat progress (rewrite ?Nat.add_succ_r, ?Nat.add_0_r; simpl).
Ltac finish_norm := apply evstep_refl'; norm_nat; align_tape; try reflexivity; lia_refl.

Lemma lpow_double : forall {T} (xs : list T) m, xs^^(2 * m) = (xs ++ xs)^^m.
Proof.
  induction m; [reflexivity |].
  replace (2 * S m)%nat with (S (S (2 * m))) by lia.
  cbn [lpow]. rewrite IHm, app_assoc. reflexivity.
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

Lemma cr_LK_11_01 : forall n l r, [1; 1]^^n *> l <{{L}} r -->* l <{{L}} [0; 1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_LM_01_10 : forall n l r, [0; 1]^^n *> l <{{L}} r -->* l <{{L}} [1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** ** Configurations, push-down stack encoding, and inner cascade rules *)

Definition Ca (j b : nat) (z : side) : Q * tape :=
  ([1]^^b *> [0; 1]^^j *> const 0) {{A}}> (0 >> z).

Definition Ch (j b : nat) (z : side) : Q * tape :=
  ([0; 1]^^j *> const 0) <{{H}} (1 >> [1]^^b *> 0 >> z).

Definition Ci (p a : nat) (z : side) : Q * tape :=
  ([1]^^(a + 2) *> [0; 1]^^p *> const 0) {{I}}> z.

Definition Ce_z (p a c d : nat) (z : side) : Q * tape :=
  Ci p a ([1; 0]^^c *> 0 >> [1; 0]^^d *> z).

Definition Cd_z (p b d : nat) (z : side) : Q * tape :=
  Ci p b ([1; 0]^^d *> z).

Definition blk (a : nat) (z : side) : side :=
  1 >> [1]^^a *> 0 >> z.

Fixpoint stack_tail (us : list nat) : side :=
  match us with
  | [] => const 0
  | u :: rest => [0; 1]^^u *> 1 >> stack_tail rest
  end.

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
  Ca j b (0 >> z) -->+ Ci j b z.
Proof.
  intros j b z. unfold Ca, Ci.
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

Lemma E_EVEN_any : forall p' k y,
  Ci (S p') (2 * k) (1 >> y) -->+ Ch p' 1 ([1; 0]^^(S k) *> y).
Proof.
  intros p' k y. unfold Ci, Ch.
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
  intros p' m d z. unfold Cd_z, Ci, Ch.
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
  intros p a d z. unfold Ce_z, Ci, Ch. norm_nat.
  start_progress.
  follow cr_HL_1_1.
  finish_norm.
Qed.

(** ** Outer push-down stack rules (M_boot_7_3, Ci_even_reload, Rem2_to_Ca, Rem0_to_Ch, Halt_odd_b) *)

Lemma M_boot_7_3_sub : forall y,
  const 0 <{{L}} ([1; 0]^^4 *> y) -->+ Ci 7 3 y.
Proof.
  intros y. unfold Ci.
  apply evstep_progress; [| discriminate].
  cbn [Nat.add lpow Str_app].
  do 173 step; finish_norm.
Qed.

Lemma M_boot_7_3 : forall d z,
  const 0 <{{L}} ([1; 0]^^(d + 4) *> z) -->+ Cd_z 7 3 d z.
Proof.
  intros d z. unfold Cd_z.
  replace (d + 4)%nat with (4 + d)%nat by lia.
  rewrite lpow_add, Str_app_assoc.
  apply M_boot_7_3_sub.
Qed.

Lemma Ci_even_reload_step1 : forall p k w,
  Ci p (2 * k) (0 >> 0 >> w) -->+
  ([0; 1]^^p *> const 0) <{{L}} ([0; 1]^^(S k) *> 1 >> (0 >> w)).
Proof.
  intros p k w. unfold Ci.
  replace (2 * k + 2)%nat with (2 * k + 1 + 1)%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] k). cbn [app].
  start_progress.
  follow cr_LK_11_01.
  align_tape.
  execute; finish_norm.
Qed.

Lemma Ci_even_reload : forall d k w,
  Ci (d + 4) (2 * k) (0 >> 0 >> w) -->+
  Cd_z 7 3 d ([0; 1]^^(S k) *> 1 >> (0 >> w)).
Proof.
  intros d k w.
  eapply progress_evstep_trans; [apply Ci_even_reload_step1 |].
  eapply evstep_trans; [apply cr_LM_01_10 |].
  apply progress_evstep, M_boot_7_3.
Qed.

Lemma Rem2_to_Ca : forall p a u' z,
  Ce_z p a 0 1 ([0; 1]^^(S (S u')) *> 1 >> z) -->+
  Ca p (a + 7) ([1; 0]^^u' *> 1 >> 1 >> z).
Proof.
  intros p a u' z. unfold Ce_z, Ci, Ca.
  apply evstep_progress; [| discriminate].
  cbn [lpow Str_app].
  do 5 step; finish_norm.
Qed.

Lemma Rem0_to_Ch : forall p b v z,
  Cd_z p b 0 ([0; 1]^^(S (S v)) *> 1 >> z) -->+
  Ch p (b + 4) ([0; 1]^^v *> 1 >> z).
Proof.
  intros p b v z. unfold Cd_z, Ci, Ch. norm_nat.
  start_progress.
  follow cr_HL_1_1.
  finish_norm.
Qed.

Definition c_end (p' m : nat) : Q * tape :=
  ([0; 1]^^(S p') *> const 0) <{{K}} (1 >> [0; 1]^^(S m) *> 1 >> const 0).

Lemma Halt_odd_b_aux : forall p' m,
  Ci (S p') (2 * m + 1) (0 >> 0 >> const 0) -->+ c_end p' m.
Proof.
  intros p' m. unfold Ci, c_end.
  replace (2 * m + 1 + 2)%nat with (2 * m + 2 + 1)%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] m). cbn [app].
  start_progress.
  follow cr_LK_11_01.
  align_tape.
  execute; finish_norm.
Qed.

Lemma c_end_halted : forall p' m, halted tm (c_end p' m).
Proof. intros p' m. unfold c_end. reflexivity. Qed.

(** ** Concrete blank-tape boot (388 literal TM steps) *)

Lemma Boot_388 : c0 -->* Cd_z 7 3 2 (stack_tail [3%nat]).
Proof.
  unfold Cd_z, Ci, stack_tail. cbn [Nat.add lpow Str_app].
  do 388 step; finish_norm.
Qed.

(** ** Exact hierarchy function W and inner transitions *)

Close Scope Z_scope.
Local Open Scope nat_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma side_const0 : const S0 = (S0 >> const S0)%sym.
Proof. apply const_unfold. Qed.

Lemma side_const0_2 : const S0 = (S0 >> S0 >> const S0)%sym.
Proof. rewrite side_const0 at 1; rewrite side_const0 at 1; reflexivity. Qed.

Lemma side_11_blk1 : (S1 >> S1 >> const S0)%sym = blk 1 (const S0).
Proof. unfold blk. cbn [lpow app Str_app]. do 2 f_equal. apply const_unfold. Qed.

Lemma Halt_odd_b : forall p' m,
  Ci (S p') (2 * m + 1) (const S0) -->+ c_end p' m.
Proof.
  intros p' m. rewrite side_const0_2. apply Halt_odd_b_aux.
Qed.

Lemma EmptyR_reload : forall d k,
  Ci (d + 4) (2 * k) (const S0) -->+ Cd_z 7 3 d (stack_tail [S k]).
Proof.
  intros d k. rewrite side_const0_2.
  eapply progress_evstep_trans; [apply Ci_even_reload |].
  cbn [stack_tail]. rewrite <- side_const0. finish.
Qed.

Lemma Ca_const0_exit : forall j b,
  Ca j b (const S0) -->+ Ci j b (const S0).
Proof.
  intros j b. rewrite side_const0 at 1. apply CA_EXIT.
Qed.

Fixpoint iter {X : Type} (n : nat) (g : X -> X) (x : X) : X :=
  match n with
  | O => x
  | S n' => g (iter n' g x)
  end.

Lemma iter_S' : forall {X : Type} n (g : X -> X) x, iter (S n) g x = iter n g (g x).
Proof. induction n; intros; simpl; [reflexivity | rewrite <- IHn; reflexivity]. Qed.

Lemma iter_add : forall {X : Type} a b (g : X -> X) x, iter (a + b) g x = iter a g (iter b g x).
Proof. induction a; intros; simpl; [reflexivity | rewrite IHa; reflexivity]. Qed.

Fixpoint W (j : nat) (b : nat) : nat :=
  match j with
  | O => b + 3
  | S j' => iter (S b) (W j') 2
  end.

Lemma W_0 : forall b, W 0 b = b + 3. Proof. reflexivity. Qed.
Lemma W_S : forall j b, W (S j) b = iter (S b) (W j) 2. Proof. reflexivity. Qed.

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
    apply progress_evstep, (BLK_iter_aux j IHj (S b) 2 z).
Qed.

Lemma BLK_1 : forall j b z,
  Ca j b (blk 1 z) -->+ Ca (S j) (W j b) z.
Proof.
  intros j b z. apply (BLK_iter_aux j (CH_CA j) 1 b z).
Qed.

Lemma CI_KC_STEP : forall p' k y,
  Ci (S p') (2 * k) (S1 >> S0 >> y) -->+ Ci (p' + S k) (W p' 1) y.
Proof.
  intros p' k y.
  eapply progress_evstep_trans; [apply E_EVEN_any |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  follow (CA_SH_iter (S k) p' (W p' 1) (S0 >> y)%sym).
  apply progress_evstep, CA_EXIT.
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

(** ** Growth, parity, and 3-adic mod-3^21 invariants of W *)

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
  induction n as [| n IHn]; cbn [iter]; [reflexivity |].
  rewrite W_1. change (S n + 2) with (S (n + 2)). rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma W2_closed : forall b,
  2 * W 2 b + 5 = 3 ^ (b + 3).
Proof.
  intros b. rewrite W_S. replace (b + 3) with (S b + 2) by lia. apply iter_W1_closed.
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

Definition M21 : Z := 10460353203%Z.
Definition R_A_HALF : Z := 7845264901%Z.
Definition R_B_HALF : Z := 2615088299%Z.
Definition R_U : Z := 7845264902%Z.
Definition DELTA_KCFULL : Z := 9806581129%Z.
Definition PB_INIT_P : Z := 7845264907%Z.

Definition is_W_even (a : nat) : Prop :=
  2 <= a /\ a mod 2 = 0 /\ 136 <= a / 2 /\
  (Z.of_nat (a / 2) mod M21 = R_A_HALF)%Z.

Definition is_W_odd (b : nat) : Prop :=
  b = 2 * (b / 2) + 1 /\ 59 <= b / 2 /\
  (Z.of_nat (b / 2) mod M21 = R_B_HALF)%Z.

Definition is_U (u : nat) : Prop :=
  137 <= u /\ (Z.of_nat u mod M21 = R_U)%Z.

Lemma Z_pow_3_21 : Z.of_nat (3 ^ 21) = M21.
Proof. rewrite Nat2Z.inj_pow. reflexivity. Qed.

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
    assert (Hpow : 2 * W 2 y + 5 = 3 ^ (y - 18) * 3 ^ 21).
    { rewrite W2_closed. replace (y + 3) with ((y - 18) + 21) by lia. apply Nat.pow_add_r. }
    set (a := W 2 y) in *; clearbody a; clear Hw Hpar.
    assert (Ha2 : a = 2 * (a / 2) /\ 136 <= a / 2) by (mods; lia).
    destruct Ha2 as [Ha_eq Ha_ge].
    assert (Hpow4 : 4 * (a / 2) + 5 = 3 ^ (y - 18) * 3 ^ 21) by lia.
    pose proof (f_equal Z.of_nat Hpow4) as HZ4.
    rewrite Nat2Z.inj_add, !Nat2Z.inj_mul, Z_pow_3_21 in HZ4.
    change (Z.of_nat 4) with 4%Z in HZ4.
    change (Z.of_nat 5) with 5%Z in HZ4.
    clear Hpow Hpow4.
    set (q := Z.of_nat (3 ^ (y - 18))) in *; clearbody q.
    unfold is_W_even, M21, R_A_HALF in *.
    split; [lia | split; [exact Hev | split; [exact Ha_ge |]]].
    assert (Hz : (Z.of_nat (a / 2) = 7845264901 + (2615088301 * q - Z.of_nat (a / 2) - 2) * 10460353203)%Z) by lia.
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
  assert (Hpow : 2 * W 2 y + 5 = 3 ^ (y - 18) * 3 ^ 21).
  { rewrite W2_closed. replace (y + 3) with ((y - 18) + 21) by lia. apply Nat.pow_add_r. }
  set (w := W 2 y) in *; clearbody w; clear Hw Hpar.
  assert (Hw2 : w = 2 * (w / 2) + 1 /\ 59 <= w / 2) by (mods; lia).
  destruct Hw2 as [Hw_eq Hw_ge].
  assert (Hpow4 : 4 * (w / 2) + 7 = 3 ^ (y - 18) * 3 ^ 21) by lia.
  pose proof (f_equal Z.of_nat Hpow4) as HZ4.
  rewrite Nat2Z.inj_add, !Nat2Z.inj_mul, Z_pow_3_21 in HZ4.
  change (Z.of_nat 4) with 4%Z in HZ4.
  change (Z.of_nat 7) with 7%Z in HZ4.
  clear Hpow Hpow4.
  set (q := Z.of_nat (3 ^ (y - 18))) in *; clearbody q.
  unfold is_W_odd, M21, R_B_HALF in *.
  split; [exact Hw_eq | split; [exact Hw_ge |]].
  assert (Hz : (Z.of_nat (w / 2) = 2615088299 + (2615088301 * q - Z.of_nat (w / 2) - 2) * 10460353203)%Z) by lia.
  rewrite Hz, Z.mod_add by lia. reflexivity.
Qed.

Lemma mod2_even : forall a, a mod 2 = 0 -> a = 2 * (a / 2).
Proof. intros a Ha. pose proof (Nat.div_mod_eq a 2). lia. Qed.

Lemma is_W_even_to_U : forall a, is_W_even a -> is_U (S (a / 2)).
Proof.
  intros a [_ [_ [Hge Hmod]]]. unfold is_U.
  split; [lia |].
  replace (Z.of_nat (S (a / 2))) with (Z.of_nat (a / 2) + 1)%Z by lia.
  rewrite <- Zplus_mod_idemp_l, Hmod. reflexivity.
Qed.

(** ** Fast-growing hierarchy up to omega + 2 and W lower bounds *)

Fixpoint f (k : nat) : nat -> nat :=
  match k with
  | O => S
  | S k' => fun n => iter n (f k') n
  end.

Definition f_omega (n : nat) : nat := f n n.
Definition f_omega1 (n : nat) : nat := iter n f_omega n.
Definition f_omega2 (n : nat) : nat := iter n f_omega1 n.

Lemma iter_mono_x : forall g, (forall a b, a <= b -> g a <= g b) ->
  forall n x y, x <= y -> iter n g x <= iter n g y.
Proof. intros g Hg. induction n; intros; simpl; auto. Qed.

Lemma iter_ge : forall g, (forall a, a <= g a) -> forall n x, x <= iter n g x.
Proof.
  intros g Hg. induction n; intros; simpl; [lia |].
  specialize (IHn x). specialize (Hg (iter n g x)). lia.
Qed.

Lemma iter_mono_n : forall g, (forall a, a <= g a) -> forall n m x, n <= m -> iter n g x <= iter m g x.
Proof.
  intros g Hg n m x Hnm. replace m with ((m - n) + n) by lia.
  rewrite iter_add. apply iter_ge. exact Hg.
Qed.

Lemma iter_lin1 : forall g, (forall a, 1 <= a -> a + 1 <= g a) -> forall n x, 1 <= x -> x + n <= iter n g x.
Proof.
  intros g Hg. induction n; intros x Hx; simpl; [lia |].
  specialize (IHn x Hx). specialize (Hg (iter n g x) ltac:(lia)). lia.
Qed.

Lemma iter_dom : forall K g h, (forall n z, K * n <= z -> K * g n <= h z) ->
  forall m n z, K * n <= z -> K * iter m g n <= iter m h z.
Proof. intros K g h Hd. induction m; intros n z Hz; simpl; auto. Qed.

Lemma f_S : forall k n, f (S k) n = iter n (f k) n. Proof. reflexivity. Qed.

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

Lemma f_id : forall k n, n <= f k n. Proof. intros. apply f_props. Qed.
Lemma f_mono : forall k a b, a <= b -> f k a <= f k b. Proof. intros. apply f_props; assumption. Qed.

Lemma f_gt : forall k n, 1 <= n -> n < f k n.
Proof.
  induction k; intros n Hn; [simpl; lia |].
  rewrite f_S. destruct n as [| n']; [lia |].
  simpl. pose proof (iter_ge (f k) (f_id k) n' (S n')).
  specialize (IHk (iter n' (f k) (S n')) ltac:(lia)). lia.
Qed.

Lemma f_level : forall k n, 1 <= n -> f k n <= f (S k) n.
Proof.
  intros k n Hn. rewrite f_S. destruct n as [| n']; [lia |].
  rewrite iter_S'. apply iter_ge, f_id.
Qed.

Lemma f_level_mono : forall d k n, 1 <= n -> f k n <= f (d + k) n.
Proof.
  induction d; intros k n Hn; [reflexivity |].
  specialize (IHd k n Hn). pose proof (f_level (d + k) n Hn).
  change (S d + k) with (S (d + k)). lia.
Qed.

Lemma iter_succ_add : forall n x, iter n S x = n + x.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma f1 : forall n, f 1 n = 2 * n.
Proof. intros. rewrite f_S, iter_succ_add. lia. Qed.

Lemma f_dbl : forall k n, 1 <= k -> 2 * n <= f k n.
Proof.
  intros k n Hk. destruct n as [| n']; [lia |].
  rewrite <- f1. replace k with ((k - 1) + 1) by lia. apply f_level_mono. lia.
Qed.

Lemma f_omega_id : forall n, n <= f_omega n.
Proof. intros n. unfold f_omega. apply f_id. Qed.

Lemma f_omega_dbl : forall n, 1 <= n -> 2 * n <= f_omega n.
Proof. intros n Hn. unfold f_omega. apply f_dbl. exact Hn. Qed.

Lemma f_omega_mono : forall a b, a <= b -> f_omega a <= f_omega b.
Proof.
  intros [| a'] b Hab.
  - destruct b as [| b']; [reflexivity |].
    change (f_omega 0) with 1. pose proof (f_omega_id (S b')). lia.
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
  pose proof (f_omega_dbl (iter a' f_omega (S a')) ltac:(lia)). lia.
Qed.

Lemma f_omega1_8x : forall n, 3 <= n -> 8 * n <= f_omega1 n.
Proof.
  intros n Hn. unfold f_omega1.
  transitivity (iter 3 f_omega n).
  - cbn [iter].
    pose proof (f_omega_dbl n ltac:(lia)) as H1.
    pose proof (f_omega_dbl (f_omega n) ltac:(lia)) as H2.
    pose proof (f_omega_dbl (f_omega (f_omega n)) ltac:(lia)) as H3.
    lia.
  - apply iter_mono_n; [apply f_omega_id | exact Hn].
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

Lemma W_S' : forall j b, W (S j) b = iter b (W j) (W j 2).
Proof. intros j b. rewrite W_S, iter_S'. reflexivity. Qed.

Lemma W_S_2 : forall j, W (S j) 2 = W j (W j (W j 2)).
Proof. intros j. rewrite W_S. reflexivity. Qed.

Lemma pow2_ge : forall j, j + 2 <= 2 ^ (j + 1).
Proof. induction j; [simpl; lia | change (S j + 1) with (S (j + 1)); rewrite Nat.pow_succ_r'; lia]. Qed.

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
      destruct n as [| n']; [cbn [iter]; lia |].
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
  intros m. rewrite W_S_2.
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
  set (F2 := f (S m) (2 * (m + 1))) in *; set (Z0 := W (S m) (W (S m) (W (S m) 2))) in *.
  nia.
Qed.

Lemma W_omega_bound : forall m,
  4 * f_omega (S m) + 4 <= W (S (S (S m))) 1.
Proof.
  intros m. rewrite W_S. cbn [iter].
  pose proof (W_omega_bound0 m) as H0.
  set (Z0 := W (S (S m)) 2) in *; clearbody Z0.
  rewrite W_S.
  pose proof (iter_lin3 (W (S m)) (W_grow (S m)) (S Z0) 2).
  lia.
Qed.

Lemma W6_3_ge_f_omega_3 : 32 * f_omega 3 <= W 6 3.
Proof.
  assert (HW6 : W 6 3 = W 5 (W 5 (W 5 (W 5 2)))) by (rewrite W_S; reflexivity).
  destruct (W_bound_all 4) as [Hw5 Hx5].
  simpl (2 ^ (4 + 1)) in Hw5.
  simpl (2 ^ (4 + 2) * (4 + 1)) in Hx5.
  assert (H1 : 32 * 10 <= W 5 2) by lia.
  pose proof (Hw5 10 (W 5 2) H1) as H2.
  pose proof (W_grow 5 (W 5 (W 5 2))) as Hg1.
  pose proof (W_grow 5 (W 5 (W 5 (W 5 2)))) as Hg2.
  assert (Hf35 : f_omega 3 <= f 5 10).
  { unfold f_omega.
     transitivity (f 5 3).
     - exact (f_level_mono 2 3 3 ltac:(lia)).
     - apply f_mono; lia. }
  lia.
Qed.

Opaque W.
Strategy opaque [W].
Opaque f.
Strategy opaque [f].
Opaque f_omega f_omega1 f_omega2.
Strategy opaque [f_omega f_omega1 f_omega2].

(** ** Macro-step functions, 3-adic helpers, and unified Kc/Kd loops *)

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
  set (qZ := (Z.of_nat d / (3 * M))%Z) in *; clearbody qZ.
  set (qc := (c / 3)%Z) in *; clearbody qc.
  set (qN := (d - r) / 3) in *; clearbody qN.
  set (rN := (d - r) mod 3) in *; clearbody rN.
  assert (HrN0 : rN = 0) by lia.
  split; [lia |].
  assert (Hq_eq : (Z.of_nat qN = qc + qZ * M)%Z) by lia.
  rewrite Hq_eq, Z.mod_add by lia. reflexivity.
Qed.

Lemma Z_mod_eq_intro : forall (x y M : Z),
  (0 < M)%Z -> (exists k : Z, x - y = k * M)%Z -> (x mod M = y mod M)%Z.
Proof.
  intros x y M HM [k Hk].
  replace x with (y + k * M)%Z by lia.
  apply Z.mod_add. lia.
Qed.

Lemma Z_mod_eq_elim : forall (x y M : Z),
  (0 < M)%Z -> (x mod M = y mod M)%Z -> (exists k : Z, x = y + k * M)%Z.
Proof.
  intros x y M HM Heq.
  pose proof (Z.div_mod x M ltac:(lia)) as Hx.
  pose proof (Z.div_mod y M ltac:(lia)) as Hy.
  rewrite Heq in Hx.
  set (qx := (x / M)%Z) in *; set (qy := (y / M)%Z) in *; set (ry := (y mod M)%Z) in *.
  exists (qx - qy)%Z.
  rewrite Hx, Hy. ring.
Qed.

Lemma Z_mod_const_elim : forall (x c M : Z),
  (0 < M)%Z -> (x mod M = c)%Z -> (exists k : Z, x = c + k * M)%Z.
Proof.
  intros x c M HM Heq.
  pose proof (Z.div_mod x M ltac:(lia)) as Hx.
  rewrite Heq in Hx.
  set (qx := (x / M)%Z) in *.
  exists qx.
  rewrite Hx. ring.
Qed.

Lemma Z_M21_mult : forall M : Z,
  (0 < M)%Z -> (M21 mod M = 0)%Z -> (exists qM : Z, M21 = qM * M)%Z.
Proof.
  intros M HM Hdiv.
  pose proof (Z.div_mod M21 M ltac:(lia)) as H.
  rewrite Hdiv in H.
  set (qM := (M21 / M)%Z) in *.
  exists qM.
  rewrite H. ring.
Qed.

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

Definition pa_7_3 : nat * nat :=
  (6 + W 6 3 / 2, W 5 1).

Definition pb_init : nat * nat :=
  (6 + W 6 3 / 2, W (6 + W 6 3 / 2) (W 5 1 + 4)).

Lemma Kc_unfold : forall p a, Kc (p, a) = (p + a / 2, W (p - 1) 1). Proof. reflexivity. Qed.
Lemma Kc_full_unfold : forall p b, Kc_full (p, b) = iter (b / 2) Kc (p - 1, W (p - 1) 3). Proof. reflexivity. Qed.
Lemma Kd_step_unfold : forall pb, Kd_step pb = let '(p', a') := Kc_full pb in (p', W p' (a' + 4)). Proof. reflexivity. Qed.
Lemma Kd_iter_unfold : forall m pb, Kd_iter m pb = iter m Kd_step pb. Proof. reflexivity. Qed.

Lemma Ci_Kc_step : forall c z pa,
  1 <= fst pa -> snd pa mod 2 = 0 ->
  Ci (fst pa) (snd pa) ([S1; S0]^^(S c) *> z) -->+
  Ci (fst (Kc pa)) (snd (Kc pa)) ([S1; S0]^^c *> z).
Proof.
  intros c z [p a] Hp Hev. cbn [fst snd Kc] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  pose proof (mod2_even a Hev) as Ha.
  replace (S p' + a / 2) with (p' + S (a / 2)) by lia.
  rewrite Ha at 1.
  cbn [lpow app Str_app].
  apply CI_KC_STEP.
Qed.

Lemma Kc_props_mod : forall pa,
  4 <= fst pa -> is_W_even (snd pa) ->
  fst pa + 1 <= fst (Kc pa) /\
  (Z.of_nat (fst (Kc pa)) mod M21 = (Z.of_nat (fst pa) + R_A_HALF) mod M21)%Z /\
  is_W_even (snd (Kc pa)).
Proof.
  intros [p a] Hp Ha. cbn [fst snd Kc] in *.
  assert (Hw : is_W_even (W (p - 1) 1)) by (apply W_ge3_odd; [lia | reflexivity]).
  destruct Ha as [_ [_ [Ha_ge Ha_mod]]].
  split; [lia | split; [| exact Hw]].
  rewrite Nat2Z.inj_add, <- Zplus_mod_idemp_r, Ha_mod. reflexivity.
Qed.

Lemma Ci_Kc_loop : forall c z pa,
  4 <= fst pa -> is_W_even (snd pa) ->
  Ci (fst pa) (snd pa) ([S1; S0]^^c *> z) -->*
  Ci (fst (iter c Kc pa)) (snd (iter c Kc pa)) z /\
  fst pa + c <= fst (iter c Kc pa) /\
  (Z.of_nat (fst (iter c Kc pa)) mod M21 =
    (Z.of_nat (fst pa) + R_A_HALF * Z.of_nat c) mod M21)%Z /\
  is_W_even (snd (iter c Kc pa)).
Proof.
  induction c as [| c IHc]; intros z pa Hp Ha.
  - cbn [iter lpow Str_app]. split; [finish | split; [lia | split; [f_equal; lia | exact Ha]]].
  - rewrite iter_S'.
    destruct Ha as [Ha_ge [Hev [Ha2_ge Ha_mod]]].
    assert (Ha_full : is_W_even (snd pa)) by (exact (conj Ha_ge (conj Hev (conj Ha2_ge Ha_mod)))).
    destruct (Kc_props_mod pa Hp Ha_full) as [Hp1 [Hm1 Ha1]].
    destruct (IHc z (Kc pa) ltac:(lia) Ha1) as [Hrun [Hp2 [Hm2 Ha2]]].
    split; [| split; [| split]].
    + eapply evstep_trans; [apply progress_evstep, (Ci_Kc_step c z pa ltac:(lia) Hev) | exact Hrun].
    + lia.
    + rewrite Hm2, <- Zplus_mod_idemp_l, Hm1, Zplus_mod_idemp_l. f_equal; lia.
    + exact Ha2.
Qed.

Lemma Kc_full_all : forall d z pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) (S d) z -->+ Ce_z (fst (Kc_full pb)) (snd (Kc_full pb)) 0 d z /\
  fst pb + 58 <= fst (Kc_full pb) /\
  (Z.of_nat (fst (Kc_full pb)) mod M21 =
    (Z.of_nat (fst pb) + DELTA_KCFULL) mod M21)%Z /\
  is_W_even (snd (Kc_full pb)).
Proof.
  intros d z [p b] Hp [Hb_eq [Hb_ge Hb_mod]]. cbn [fst snd Kc_full] in *.
  destruct p as [| p']; [lia |].
  replace (S p' - 1) with p' by lia.
  assert (Hw3 : is_W_even (W p' 3)) by (apply W_ge3_odd; [lia | reflexivity]).
  destruct (Ci_Kc_loop (b / 2) (S0 >> [S1; S0]^^d *> z)%sym (p', W p' 3) ltac:(cbn; lia) Hw3)
    as [Hrun [Hp1 [Hm1 Ha1]]].
  cbn [fst snd] in *.
  split; [| split; [| split]].
  - rewrite Hb_eq at 1.
    eapply progress_evstep_trans; [apply C_REL |].
    unfold Ce_z at 1. exact Hrun.
  - lia.
  - rewrite Hm1, <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, Hb_mod, Zplus_mod_idemp_r.
    unfold M21, R_A_HALF, R_B_HALF, DELTA_KCFULL in *.
    replace (Z.of_nat p' + 7845264901 * 2615088299)%Z
      with ((Z.of_nat (S p') + 9806581129) + 1961316223 * 10460353203)%Z by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - exact Ha1.
Qed.

Lemma Kd_step_all : forall d z pb,
  5 <= fst pb -> is_W_odd (snd pb) ->
  Cd_z (fst pb) (snd pb) (S (S (S d))) z -->+ Cd_z (fst (Kd_step pb)) (snd (Kd_step pb)) d z /\
  fst pb + 58 <= fst (Kd_step pb) /\
  (Z.of_nat (fst (Kd_step pb)) mod M21 =
    (Z.of_nat (fst pb) + DELTA_KCFULL) mod M21)%Z /\
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
  (Z.of_nat (fst (Kd_iter m pb)) mod M21 =
    (Z.of_nat (fst pb) + DELTA_KCFULL * Z.of_nat m) mod M21)%Z /\
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
    + rewrite Hm2, <- Zplus_mod_idemp_l, Hm1, Zplus_mod_idemp_l. f_equal; lia.
    + exact Hb2.
Qed.

Lemma step_7_3_kc : forall d z,
  Cd_z 7 3 (S d) z -->+ Ce_z (fst pa_7_3) (snd pa_7_3) 0 d z /\
  142 <= fst pa_7_3 /\
  (Z.of_nat (fst pa_7_3) mod M21 = PB_INIT_P)%Z /\
  is_W_even (snd pa_7_3).
Proof.
  intros d z. unfold pa_7_3. cbn [fst snd].
  assert (Hw6 : is_W_even (W 6 3)) by (apply W_ge3_odd; [lia | reflexivity]).
  assert (Hw5 : is_W_even (W 5 1)) by (apply W_ge3_odd; [lia | reflexivity]).
  destruct Hw6 as [_ [Hev6 [Hge6 Hmod6]]].
  split; [| split; [lia | split; [| exact Hw5]]].
  - eapply progress_evstep_trans; [apply (C_REL 6 1 d z) |].
    unfold Ce_z.
    pose proof (Ci_Kc_step 0 (S0 >> [S1; S0]^^d *> z)%sym (6, W 6 3) ltac:(cbn; lia) Hev6) as Hkc.
    cbn [fst snd Kc lpow Str_app] in Hkc.
    apply progress_evstep, Hkc.
  - rewrite Nat2Z.inj_add, <- Zplus_mod_idemp_r, Hmod6. reflexivity.
Qed.

Lemma step_7_3_kd : forall d z,
  Cd_z 7 3 (S (S (S d))) z -->+ Cd_z (fst pb_init) (snd pb_init) d z /\
  142 <= fst pb_init /\
  (Z.of_nat (fst pb_init) mod M21 = PB_INIT_P)%Z /\
  is_W_odd (snd pb_init).
Proof.
  intros d z. unfold pb_init.
  destruct (step_7_3_kc (S (S d)) z) as [Hkc [Hp [Hmod Ha]]].
  unfold pa_7_3 in Hkc, Hp, Hmod, Ha. cbn [fst snd] in *.
  destruct Ha as [_ [Hev5 _]].
  pose proof (mod2_even (W 5 1) Hev5) as Hw5_eq.
  assert (Hev4 : (W 5 1 + 4) mod 2 = 0).
  { replace (W 5 1 + 4) with (0 + (W 5 1 / 2 + 2) * 2) by lia.
     rewrite Nat.Div0.mod_add. reflexivity. }
  assert (Hodd : is_W_odd (W (6 + W 6 3 / 2) (W 5 1 + 4)))
    by (apply W_ge3_even; [lia | lia | exact Hev4]).
  split; [| split; [exact Hp | split; [exact Hmod | exact Hodd]]].
  eapply progress_evstep_trans; [exact Hkc | apply progress_evstep, D_STEP].
Qed.

(** ** FGH Domination across Kc, Kc_full, Kd_step, Kd_iter *)

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
  n + 6 <= fst pa /\ 6 * n + 2 <= snd pa.

Definition ok_d (n : nat) (d : nat) : Prop :=
  6 * n + 8 <= d.

Lemma ok_pb_mono : forall m n pb, m <= n -> ok_pb n pb -> ok_pb m pb.
Proof. intros m n pb Hmn [H1 H2]. split; lia. Qed.

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

Lemma pb_init_dom3 : ok_pb 3 pb_init.
Proof.
  unfold pb_init, ok_pb. cbn [fst snd].
  destruct (step_7_3_kd 0 (const S0)) as [_ [Hp [_ [Hb_eq [Hb_ge _]]]]].
  unfold pb_init in Hp, Hb_eq, Hb_ge. cbn [fst snd] in *.
  lia.
Qed.

Lemma Kd_loop_7_3_dom : forall m r z N,
  3 <= N ->
  2 * N + 2 <= m ->
  exists p_kd b_kd,
    Cd_z 7 3 (3 * m + r) z -->+ Cd_z p_kd b_kd r z /\
    8 * f_omega2 N + 4 <= p_kd /\
    (Z.of_nat p_kd mod M21 = (PB_INIT_P + DELTA_KCFULL * Z.of_nat (m - 1)) mod M21)%Z /\
    is_W_odd b_kd.
Proof.
  intros m r z N HN Hm.
  destruct (step_7_3_kd (3 * (m - 1) + r) z) as [Hfirst [Hp0 [Hmod0 Hb0]]].
  destruct (Kd_loop (m - 1) r z pb_init ltac:(lia) Hb0) as [Hloop [Hp_kd [Hmod_kd Hb_kd]]].
  pose proof (Kd_iter_dom (m - 1) 3 pb_init ltac:(lia) pb_init_dom3) as [Hdom_p _].
  assert (Hle1 : f_omega1 (f_omega2 N) <= iter (m - 1) f_omega1 3).
  { transitivity (iter (S (2 * N)) f_omega1 3).
     - cbn [iter]. apply f_omega1_mono, f_omega2_le_iter_2n. lia.
     - apply iter_mono_n; [apply f_omega1_id | lia]. }
  pose proof (f_omega2_id N) as Hf2_id.
  pose proof (f_omega1_8x (f_omega2 N) ltac:(lia)) as H8x.
  exists (fst (Kd_iter (m - 1) pb_init)), (snd (Kd_iter (m - 1) pb_init)).
  split; [| split; [lia | split; [| exact Hb_kd]]].
  - replace (3 * m + r) with (S (S (S (3 * (m - 1) + r)))) by lia.
    eapply progress_evstep_trans; [exact Hfirst | exact Hloop].
  - rewrite Hmod_kd, <- Zplus_mod_idemp_l, Hmod0. reflexivity.
Qed.

Opaque Kc Kc_full Kd_step Kd_iter pa_7_3 pb_init.

(** ** Rem0 body and stack-drain lemmas *)

Lemma stack_tail_cons_align : forall u rest,
  (S1 >> stack_tail (u :: rest) = [S1; S0]^^u *> S1 >> S1 >> stack_tail rest)%sym.
Proof.
  intros u rest. cbn [stack_tail].
  symmetry. apply (align_lpow S1 [S0] (S1 >> stack_tail rest) u).
Qed.

Lemma Rem0_body : forall p b u_top rest,
  5 <= p -> is_W_odd b -> is_U u_top ->
  exists j0 b0,
    Cd_z p b 0 (stack_tail (u_top :: rest)) -->+ Ca j0 b0 (S1 >> stack_tail rest) /\
    p + 270 <= j0 /\
    (Z.of_nat j0 mod M21 = (Z.of_nat p + (R_U - 2) * R_A_HALF) mod M21)%Z /\
    is_W_even b0.
Proof.
  intros p b u_top rest Hp [Hb_eq [Hb_ge _]] [Hu_ge Hu_mod].
  set (u'' := u_top - 3).
  assert (Hu_eq : u_top = S (S (S u''))) by (unfold u''; lia).
  assert (Hb4_odd : (b + 4) mod 2 = 1).
  { replace (b + 4) with (1 + (b / 2 + 2) * 2) by lia.
     rewrite Nat.Div0.mod_add. reflexivity. }
  assert (Ha0_ev : is_W_even (W p (b + 4))) by (apply W_ge3_odd; [lia | exact Hb4_odd]).
  destruct (Ci_Kc_loop u'' (S1 >> S1 >> stack_tail rest)%sym (p, W p (b + 4)) ltac:(cbn; lia) Ha0_ev)
    as [Hkc [Hkc_p [Hkc_mod Hkc_ev]]].
  cbn [fst snd] in Hkc, Hkc_p, Hkc_mod.
  set (p_kc := fst (iter u'' Kc (p, W p (b + 4)))) in *.
  set (a_kc := snd (iter u'' Kc (p, W p (b + 4)))) in *.
  destruct Hkc_ev as [_ [Ha_kc_ev [Ha_kc_ge Ha_kc_mod]]].
  pose proof (mod2_even a_kc Ha_kc_ev) as Ha_kc_eq.
  assert (Hb0_ev : is_W_even (W (p_kc - 1) 1)) by (apply W_ge3_odd; [unfold u'' in *; lia | reflexivity]).
  exists (p_kc + a_kc / 2), (W (p_kc - 1) 1).
  split; [| split; [unfold u'' in *; lia | split; [| exact Hb0_ev]]].
  - rewrite Hu_eq. cbn [stack_tail].
    eapply progress_evstep_trans; [apply Rem0_to_Ch |].
    eapply evstep_trans; [apply progress_evstep, CH_CA |].
    change ([S0; S1]^^(S u'') *> S1 >> stack_tail rest)%sym
      with (S0 >> (S1 >> [S0; S1]^^u'' *> S1 >> stack_tail rest))%sym.
    replace (S1 >> [S0; S1]^^u'' *> S1 >> stack_tail rest)%sym
      with ([S1; S0]^^u'' *> S1 >> S1 >> stack_tail rest)%sym
      by (apply (align_lpow S1 [S0] (S1 >> stack_tail rest) u'') ||
          (symmetry; apply (align_lpow S1 [S0] (S1 >> stack_tail rest) u''))).
    eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
    eapply evstep_trans; [exact Hkc |].
    replace p_kc with (S (p_kc - 1)) at 1 by (unfold u'' in *; lia).
    rewrite Ha_kc_eq at 1.
    eapply evstep_trans; [apply progress_evstep, E_EVEN_any |].
    eapply evstep_trans; [apply progress_evstep, CH_CA |].
    follow (CA_SH_iter (S (a_kc / 2)) (p_kc - 1) (W (p_kc - 1) 1) (S1 >> stack_tail rest)%sym).
    replace (p_kc - 1 + S (a_kc / 2)) with (p_kc + a_kc / 2) by (unfold u'' in *; lia).
    finish.
  - assert (HM21 : (0 < M21)%Z) by (unfold M21; lia).
    destruct (Z_mod_eq_elim _ _ M21 HM21 Hkc_mod) as [k1 Hk1].
    destruct (Z_mod_const_elim _ _ M21 HM21 Ha_kc_mod) as [k2 Hk2].
    destruct (Z_mod_const_elim _ _ M21 HM21 Hu_mod) as [k3 Hk3].
    assert (Hu_z : (Z.of_nat u'' = Z.of_nat u_top - 3)%Z) by (unfold u''; lia).
    rewrite Nat2Z.inj_add.
    apply Z_mod_eq_intro; [exact HM21 |].
    exists (k1 + k2 + R_A_HALF * k3)%Z.
    rewrite Hk1, Hk2, Hu_z, Hk3. ring.
Qed.

Lemma Ca_drain_one : forall j b u rest,
  Ca j b (S1 >> stack_tail (u :: rest)) -->+ Ca (j + u) (W (j + u) b) (S1 >> stack_tail rest).
Proof.
  intros j b u rest.
  rewrite stack_tail_cons_align.
  eapply evstep_progress_trans; [apply CA_SH_iter |].
  eapply progress_evstep_trans; [apply CA_CH |].
  apply progress_evstep, CH_CA.
Qed.

Lemma Ca_drain_pair : forall j b u1 u2 rest,
  3 <= j -> is_W_even b -> is_U u1 -> is_U u2 ->
  exists j' b',
    Ca j b (S1 >> stack_tail (u1 :: u2 :: rest)) -->+ Ca j' b' (S1 >> stack_tail rest) /\
    j + 274 <= j' /\
    (Z.of_nat j' mod M21 = (Z.of_nat j + 2 * R_U) mod M21)%Z /\
    is_W_even b'.
Proof.
  intros j b u1 u2 rest Hj [Hb_ge [Hb_ev _]] [Hu1_ge Hu1_mod] [Hu2_ge Hu2_mod].
  assert (Hb1_odd : is_W_odd (W (j + u1) b))
    by (apply W_ge3_even; [lia | lia | exact Hb_ev]).
  destruct Hb1_odd as [Hb1_eq _].
  assert (Hb1_par : W (j + u1) b mod 2 = 1).
  { replace (W (j + u1) b) with (1 + (W (j + u1) b / 2) * 2) by lia.
     rewrite Nat.Div0.mod_add. reflexivity. }
  assert (Hb2_ev : is_W_even (W (j + u1 + u2) (W (j + u1) b)))
    by (apply W_ge3_odd; [lia | exact Hb1_par]).
  exists (j + u1 + u2), (W (j + u1 + u2) (W (j + u1) b)).
  split; [| split; [lia | split; [| exact Hb2_ev]]].
  - eapply progress_evstep_trans; [apply Ca_drain_one |].
    apply progress_evstep, Ca_drain_one.
  - assert (HM21 : (0 < M21)%Z) by (unfold M21; lia).
    destruct (Z_mod_const_elim _ _ M21 HM21 Hu1_mod) as [k1 Hk1].
    destruct (Z_mod_const_elim _ _ M21 HM21 Hu2_mod) as [k2 Hk2].
    replace (Z.of_nat (j + u1 + u2)) with (Z.of_nat j + Z.of_nat u1 + Z.of_nat u2)%Z by lia.
    apply Z_mod_eq_intro; [exact HM21 |].
    exists (k1 + k2)%Z.
    rewrite Hk1, Hk2. ring.
Qed.

Lemma Ca_drain_even : forall K rest j b,
  length rest = 2 * K ->
  Forall is_U rest ->
  3 <= j -> is_W_even b ->
  exists j_exit b_exit,
    Ca j b (S1 >> stack_tail rest) -->+ Ca j_exit b_exit (const S0) /\
    j + 1 <= j_exit /\
    (Z.of_nat j_exit mod M21 = (Z.of_nat j + Z.of_nat (2 * K) * R_U + 1) mod M21)%Z /\
    is_W_even b_exit.
Proof.
  induction K as [| K IHK]; intros rest j b Hlen Hfa Hj Hb.
  - destruct rest as [| x rest']; [| discriminate].
    exists (S j), b.
    split; [| split; [lia | split; [| exact Hb]]].
    + cbn [stack_tail]. rewrite side_const0 at 1. apply CA_SH.
    + f_equal; lia.
  - destruct rest as [| u1 [| u2 rest']]; try (cbn in Hlen; lia).
    inversion Hfa as [| ? ? Hu1 Hfa1]; subst.
    inversion Hfa1 as [| ? ? Hu2 Hfa2]; subst.
    assert (Hlen' : length rest' = 2 * K) by (cbn in Hlen; lia).
    destruct (Ca_drain_pair j b u1 u2 rest' Hj Hb Hu1 Hu2)
      as [j1 [b1 [Hstep [Hj1 [Hmod1 Hb1]]]]].
    destruct (IHK rest' j1 b1 Hlen' Hfa2 ltac:(lia) Hb1)
      as [je [be [Hrest [Hje [Hmode Hbe]]]]].
    exists je, be.
    split; [| split; [lia | split; [| exact Hbe]]].
    + eapply progress_evstep_trans; [exact Hstep | apply progress_evstep, Hrest].
    + assert (HM21 : (0 < M21)%Z) by (unfold M21; lia).
      destruct (Z_mod_eq_elim _ _ M21 HM21 Hmod1) as [k1 Hk1].
      destruct (Z_mod_eq_elim _ _ M21 HM21 Hmode) as [k2 Hk2].
      assert (HK_z : (Z.of_nat (2 * S K) = Z.of_nat (2 * K) + 2)%Z) by lia.
      apply Z_mod_eq_intro; [exact HM21 |].
      exists (k1 + k2)%Z.
      rewrite Hk2, Hk1, HK_z. ring.
Qed.

(** ** Universal RoundState and the 4 round-transition theorems *)

Definition RoundState (M c : Z) (D : nat) (N : nat) : Prop :=
  exists (d : nat) (us : list nat),
    c0 -->* Cd_z 7 3 d (stack_tail us) /\
    length us = D /\
    Forall is_U us /\
    ok_d N d /\
    (Z.of_nat d mod M = c)%Z.

Lemma Boot_Round1 : RoundState M21 7845264905%Z 1 (f_omega 3).
Proof.
  destruct (step_7_3_kc 1 (stack_tail [3])) as [Hkc [Hp0 [Hmod0 Ha0]]].
  set (p0 := fst pa_7_3) in *; set (a0 := snd pa_7_3) in *.
  destruct Ha0 as [_ [Ha0_ev _]].
  pose proof (mod2_even a0 Ha0_ev) as Ha0_eq.
  assert (Ha7_odd : (a0 + 7) mod 2 = 1).
  { replace (a0 + 7) with (1 + (a0 / 2 + 3) * 2) by lia.
     rewrite Nat.Div0.mod_add. reflexivity. }
  assert (Hae_ev : is_W_even (W (p0 + 1) (a0 + 7)))
    by (apply W_ge3_odd; [lia | exact Ha7_odd]).
  destruct Hae_ev as [Hae_ge [Hae_mod2 [Hae_ge2 Hae_mod21]]].
  assert (Hae_full : is_W_even (W (p0 + 1) (a0 + 7)))
    by (exact (conj Hae_ge (conj Hae_mod2 (conj Hae_ge2 Hae_mod21)))).
  pose proof (mod2_even (W (p0 + 1) (a0 + 7)) Hae_mod2) as Hae_eq.
  pose proof (is_W_even_to_U _ Hae_full) as Hu1.
  exists (p0 - 2), [S (W (p0 + 1) (a0 + 7) / 2)].
  split; [| split; [reflexivity | split; [constructor; [exact Hu1 | constructor] | split]]].
  - eapply evstep_trans; [exact Boot_388 |].
    eapply evstep_trans; [apply progress_evstep, Hkc |].
    cbn [stack_tail].
    eapply evstep_trans; [apply progress_evstep, (Rem2_to_Ca p0 a0 1 (const S0)) |].
    rewrite side_11_blk1.
    follow (CA_SH_iter 1 p0 (a0 + 7) (blk 1 (const S0))).
    eapply evstep_trans; [apply progress_evstep, BLK_1 |].
    eapply evstep_trans; [apply progress_evstep, Ca_const0_exit |].
    replace (S (p0 + 1)) with ((p0 - 2) + 4) by lia.
    rewrite Hae_eq at 1.
    apply progress_evstep, EmptyR_reload.
  - unfold ok_d, p0. Transparent pa_7_3. unfold pa_7_3. Opaque pa_7_3. cbn [fst].
    pose proof W6_3_ge_f_omega_3 as HW6.
    pose proof (f_omega_dbl 3 ltac:(lia)) as Hf3.
    set (F3 := f_omega 3) in *; set (X6 := W 6 3) in *.
    mods; lia.
  - replace (Z.of_nat (p0 - 2)) with (Z.of_nat p0 - 2)%Z by lia.
    rewrite <- Zminus_mod_idemp_l, Hmod0. reflexivity.
Qed.

Lemma Step_Rem2 : forall (Mnext c c_next : Z) (N : nat),
  (0 < Mnext)%Z ->
  (M21 mod Mnext = 0)%Z ->
  3 <= N ->
  (c mod 3 = 2)%Z ->
  ((PB_INIT_P + ((c / 3) - 1) * DELTA_KCFULL + DELTA_KCFULL + R_U - 5) mod Mnext = c_next)%Z ->
  RoundState (3 * Mnext) c 1 N ->
  RoundState Mnext c_next 1 (f_omega2 N).
Proof.
  intros Mnext c c_next N HM Hdiv HN Hc_rem Hc_eq [d [us [Hrun [Hlen [Hfa [Hok Hd_mod]]]]]].
  destruct us as [| u [| ? ?]]; try discriminate.
  inversion Hfa as [| x0 l0 [Hu_ge Hu_mod] _]; subst x0 l0; clear Hfa.
  unfold ok_d in Hok.
  destruct (Z_div3_nat d 2 Mnext c HM ltac:(lia) Hd_mod Hc_rem) as [Hd_eq Hm_mod].
  set (m := (d - 2) / 3) in *.
  assert (Hm_ge : 2 * N + 2 <= m) by lia.
  destruct (Kd_loop_7_3_dom m 2 (stack_tail [u]) N HN Hm_ge)
    as [p_kd [b_kd [Hkd [Hp_kd [Hmod_kd Hb_kd]]]]].
  destruct (Kc_full_all 1 (stack_tail [u]) (p_kd, b_kd) ltac:(cbn; pose proof (f_omega2_id N); lia) Hb_kd)
    as [Hkc [Hp_kc [Hmod_kc Ha_kc]]].
  cbn [fst snd] in Hkc, Hp_kc, Hmod_kc.
  set (p_kc := fst (Kc_full (p_kd, b_kd))) in *; set (a_kc := snd (Kc_full (p_kd, b_kd))) in *.
  destruct Ha_kc as [_ [Ha_ev _]].
  pose proof (mod2_even a_kc Ha_ev) as Ha_eq.
  assert (Ha7_odd : (a_kc + 7) mod 2 = 1).
  { replace (a_kc + 7) with (1 + (a_kc / 2 + 3) * 2) by lia.
     rewrite Nat.Div0.mod_add. reflexivity. }
  pose proof (f_omega2_id N) as Hf2_id.
  assert (Hae_ev : is_W_even (W (p_kc + (u - 2)) (a_kc + 7)))
    by (apply W_ge3_odd; [lia | exact Ha7_odd]).
  destruct Hae_ev as [Hae_ge [Hae_m2 [Hae_ge2 Hae_m21]]].
  assert (Hae_full : is_W_even (W (p_kc + (u - 2)) (a_kc + 7)))
    by (exact (conj Hae_ge (conj Hae_m2 (conj Hae_ge2 Hae_m21)))).
  pose proof (mod2_even _ Hae_m2) as Hae_eq.
  pose proof (is_W_even_to_U _ Hae_full) as Hu_new.
  exists (p_kc + u - 5), [S (W (p_kc + (u - 2)) (a_kc + 7) / 2)].
  split; [| split; [reflexivity | split; [constructor; [exact Hu_new | constructor] | split]]].
  - eapply evstep_trans; [exact Hrun |].
    rewrite Hd_eq.
    eapply evstep_trans; [apply progress_evstep, Hkd |].
    eapply evstep_trans; [apply progress_evstep, Hkc |].
    replace u with (S (S (u - 2))) at 1 by lia. cbn [stack_tail].
    eapply evstep_trans; [apply progress_evstep, Rem2_to_Ca |].
    rewrite side_11_blk1.
    follow (CA_SH_iter (u - 2) p_kc (a_kc + 7) (blk 1 (const S0))).
    eapply evstep_trans; [apply progress_evstep, BLK_1 |].
    eapply evstep_trans; [apply progress_evstep, Ca_const0_exit |].
    replace (S (p_kc + (u - 2))) with ((p_kc + u - 5) + 4) by lia.
    rewrite Hae_eq at 1.
    apply progress_evstep, EmptyR_reload.
  - unfold ok_d. lia.
  - assert (HM21 : (0 < M21)%Z) by (unfold M21; lia).
    destruct (Z_M21_mult Mnext HM Hdiv) as [qM HqM].
    destruct (Z_mod_eq_elim _ _ M21 HM21 Hmod_kc) as [k1 Hk1].
    destruct (Z_mod_eq_elim _ _ M21 HM21 Hmod_kd) as [k2 Hk2].
    destruct (Z_mod_const_elim _ _ M21 HM21 Hu_mod) as [k3 Hk3].
    destruct (Z_mod_eq_elim _ _ Mnext HM Hm_mod) as [k4 Hk4].
    assert (Hm_z : (Z.of_nat (m - 1) = Z.of_nat m - 1)%Z) by lia.
    replace (Z.of_nat (p_kc + u - 5)) with (Z.of_nat p_kc + Z.of_nat u - 5)%Z by lia.
    rewrite <- Hc_eq.
    apply Z_mod_eq_intro; [exact HM |].
    exists (k1 * qM + k2 * qM + k3 * qM + DELTA_KCFULL * k4)%Z.
    rewrite Hk1, Hk2, Hk3, Hm_z, Hk4, HqM. ring.
Qed.

Lemma Step_Rem1 : forall (Mnext c c_next : Z) (D N : nat),
  (0 < Mnext)%Z ->
  (M21 mod Mnext = 0)%Z ->
  1 <= D ->
  3 <= N ->
  (c mod 3 = 1)%Z ->
  ((PB_INIT_P + ((c / 3) - 1) * DELTA_KCFULL + DELTA_KCFULL - 4) mod Mnext = c_next)%Z ->
  RoundState (3 * Mnext) c D N ->
  RoundState Mnext c_next (S D) (f_omega2 N).
Proof.
  intros Mnext c c_next D N HM Hdiv HD HN Hc_rem Hc_eq [d [us [Hrun [Hlen [Hfa [Hok Hd_mod]]]]]].
  destruct us as [| u0 rest]; [cbn in Hlen; lia |].
  inversion Hfa as [| x0 l0 [Hu0_ge _] _]; subst x0 l0.
  unfold ok_d in Hok.
  destruct (Z_div3_nat d 1 Mnext c HM ltac:(lia) Hd_mod Hc_rem) as [Hd_eq Hm_mod].
  set (m := (d - 1) / 3) in *.
  assert (Hm_ge : 2 * N + 2 <= m) by lia.
  destruct (Kd_loop_7_3_dom m 1 (stack_tail (u0 :: rest)) N HN Hm_ge)
    as [p_kd [b_kd [Hkd [Hp_kd [Hmod_kd Hb_kd]]]]].
  destruct (Kc_full_all 0 (stack_tail (u0 :: rest)) (p_kd, b_kd) ltac:(cbn; pose proof (f_omega2_id N); lia) Hb_kd)
    as [Hkc [Hp_kc [Hmod_kc Ha_kc]]].
  cbn [fst snd] in Hkc, Hp_kc, Hmod_kc.
  set (p_kc := fst (Kc_full (p_kd, b_kd))) in *; set (a_kc := snd (Kc_full (p_kd, b_kd))) in *.
  destruct Ha_kc as [Ha_ge [Ha_ev [Ha2_ge Ha_m21]]].
  assert (Ha_full : is_W_even a_kc) by (exact (conj Ha_ge (conj Ha_ev (conj Ha2_ge Ha_m21)))).
  pose proof (mod2_even a_kc Ha_ev) as Ha_eq.
  pose proof (is_W_even_to_U _ Ha_full) as Hu_new.
  pose proof (f_omega2_id N) as Hf2_id.
  exists (p_kc - 4), (S (a_kc / 2) :: u0 :: rest).
  split; [| split; [exact (f_equal S Hlen) | split; [constructor; [exact Hu_new | exact Hfa] | split]]].
  - eapply evstep_trans; [exact Hrun |].
    rewrite Hd_eq.
    eapply evstep_trans; [apply progress_evstep, Hkd |].
    eapply evstep_trans; [apply progress_evstep, Hkc |].
    unfold Ce_z. cbn [lpow app Str_app].
    replace p_kc with ((p_kc - 4) + 4) at 1 by lia.
    rewrite Ha_eq at 1.
    replace u0 with (S (u0 - 1)) by lia.
    cbn [stack_tail lpow app Str_app].
    apply progress_evstep, Ci_even_reload.
  - unfold ok_d. lia.
  - assert (HM21 : (0 < M21)%Z) by (unfold M21; lia).
    destruct (Z_M21_mult Mnext HM Hdiv) as [qM HqM].
    destruct (Z_mod_eq_elim _ _ M21 HM21 Hmod_kc) as [k1 Hk1].
    destruct (Z_mod_eq_elim _ _ M21 HM21 Hmod_kd) as [k2 Hk2].
    destruct (Z_mod_eq_elim _ _ Mnext HM Hm_mod) as [k4 Hk4].
    assert (Hm_z : (Z.of_nat (m - 1) = Z.of_nat m - 1)%Z) by lia.
    replace (Z.of_nat (p_kc - 4)) with (Z.of_nat p_kc - 4)%Z by lia.
    rewrite <- Hc_eq.
    apply Z_mod_eq_intro; [exact HM |].
    exists (k1 * qM + k2 * qM + DELTA_KCFULL * k4)%Z.
    rewrite Hk1, Hk2, Hm_z, Hk4, HqM. ring.
Qed.

Lemma Step_Rem0_cont : forall (Mnext c c_next : Z) (K N : nat),
  (0 < Mnext)%Z ->
  (M21 mod Mnext = 0)%Z ->
  3 <= N ->
  (c mod 3 = 0)%Z ->
  ((PB_INIT_P + ((c / 3) - 1) * DELTA_KCFULL + (R_U - 2) * R_A_HALF + Z.of_nat (2 * K) * R_U - 3) mod Mnext = c_next)%Z ->
  RoundState (3 * Mnext) c (S (2 * K)) N ->
  RoundState Mnext c_next 1 (f_omega2 N).
Proof.
  intros Mnext c c_next K N HM Hdiv HN Hc_rem Hc_eq [d [us [Hrun [Hlen [Hfa [Hok Hd_mod]]]]]].
  destruct us as [| u_top rest]; [discriminate |].
  inversion Hfa as [| x0 l0 Hu_top Hfa_rest]; subst x0 l0; clear Hfa.
  assert (Hlen_rest : length rest = 2 * K) by (cbn in Hlen; lia).
  unfold ok_d in Hok.
  destruct (Z_div3_nat d 0 Mnext c HM ltac:(lia) Hd_mod Hc_rem) as [Hd_eq Hm_mod].
  replace (d - 0) with d in * by lia.
  replace (3 * (d / 3) + 0) with (3 * (d / 3) + 0) in Hd_eq by lia.
  set (m := d / 3) in *.
  assert (Hm_ge : 2 * N + 2 <= m) by lia.
  pose proof (f_omega2_id N) as Hf2_id.
  destruct (Kd_loop_7_3_dom m 0 (stack_tail (u_top :: rest)) N HN Hm_ge)
    as [p_kd [b_kd [Hkd [Hp_kd [Hmod_kd Hb_kd]]]]].
  destruct (Rem0_body p_kd b_kd u_top rest ltac:(lia) Hb_kd Hu_top)
    as [j0 [b0 [Hbody [Hj0 [Hmod_j0 Hb0]]]]].
  destruct (Ca_drain_even K rest j0 b0 Hlen_rest Hfa_rest ltac:(lia) Hb0)
    as [j_exit [b_exit [Hdrain [Hje [Hmod_je Hbe]]]]].
  destruct Hbe as [Hbe_ge [Hbe_ev [Hbe_ge2 Hbe_m21]]].
  assert (Hbe_full : is_W_even b_exit) by (exact (conj Hbe_ge (conj Hbe_ev (conj Hbe_ge2 Hbe_m21)))).
  pose proof (mod2_even b_exit Hbe_ev) as Hbe_eq.
  pose proof (is_W_even_to_U _ Hbe_full) as Hu_new.
  exists (j_exit - 4), [S (b_exit / 2)].
  split; [| split; [reflexivity | split; [constructor; [exact Hu_new | constructor] | split]]].
  - eapply evstep_trans; [exact Hrun |].
    rewrite Hd_eq.
    eapply evstep_trans; [apply progress_evstep, Hkd |].
    eapply evstep_trans; [apply progress_evstep, Hbody |].
    eapply evstep_trans; [apply progress_evstep, Hdrain |].
    eapply evstep_trans; [apply progress_evstep, Ca_const0_exit |].
    replace j_exit with ((j_exit - 4) + 4) at 1 by lia.
    rewrite Hbe_eq at 1.
    apply progress_evstep, EmptyR_reload.
  - unfold ok_d. lia.
  - assert (HM21 : (0 < M21)%Z) by (unfold M21; lia).
    destruct (Z_M21_mult Mnext HM Hdiv) as [qM HqM].
    destruct (Z_mod_eq_elim _ _ M21 HM21 Hmod_je) as [k1 Hk1].
    destruct (Z_mod_eq_elim _ _ M21 HM21 Hmod_j0) as [k2 Hk2].
    destruct (Z_mod_eq_elim _ _ M21 HM21 Hmod_kd) as [k3 Hk3].
    destruct (Z_mod_eq_elim _ _ Mnext HM Hm_mod) as [k4 Hk4].
    assert (Hm_z : (Z.of_nat (m - 1) = Z.of_nat m - 1)%Z) by lia.
    replace (Z.of_nat (j_exit - 4)) with (Z.of_nat j_exit - 4)%Z by lia.
    rewrite <- Hc_eq.
    apply Z_mod_eq_intro; [exact HM |].
    exists (k1 * qM + k2 * qM + k3 * qM + DELTA_KCFULL * k4)%Z.
    rewrite Hk1, Hk2, Hk3, Hm_z, Hk4, HqM. ring.
Qed.

(** ** Ones counting and Round 19 halting theorem *)

Definition sym_val (s : Sym) : nat :=
  match s with S0 => 0 | S1 => 1 end.

Fixpoint count1 (xs : list Sym) : nat :=
  match xs with [] => 0 | x :: t => sym_val x + count1 t end.

Definition ones (c : Q * tape) (N : nat) : Prop :=
  exists (q : Q) (L R : list Sym) (s : Sym),
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = count1 L + sym_val s + count1 R.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = count1 xs + count1 ys.
Proof. induction xs; intros; simpl; [reflexivity | rewrite IHxs; lia]. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = n * count1 xs.
Proof. induction n; simpl; [reflexivity | rewrite count1_app, IHn; lia]. Qed.

Lemma ones_c_end : forall p' m, ones (c_end p' m) (p' + m + 4).
Proof.
  intros p' m.
  exists K, (S1 :: [S0; S1]^^p'), ((S1 :: [S0; S1]^^(S m)) ++ [S1]), S0.
  split.
  - unfold c_end. rewrite !Str_app_assoc. cbn [lpow app Str_app Streams.hd Streams.tl]. reflexivity.
  - rewrite !count1_app. cbn [count1]. rewrite !count1_pow. cbn [count1 sym_val]. lia.
Qed.

Lemma Step_Rem0_halt : forall (Mnext c : Z) (N : nat),
  (0 < Mnext)%Z ->
  3 <= N ->
  (c mod 3 = 0)%Z ->
  RoundState (3 * Mnext) c 2 N ->
  exists p_fin m_fin,
    c0 -->* c_end p_fin m_fin /\
    p_fin + m_fin + 4 > f_omega2 N.
Proof.
  intros Mnext c N HM HN Hc_rem [d [us [Hrun [Hlen [Hfa [Hok Hd_mod]]]]]].
  destruct us as [| u_top [| u_bot [| ? ?]]]; try discriminate.
  inversion Hfa as [| x0 l0 Hu_top Hfa1]; subst x0 l0; clear Hfa.
  inversion Hfa1 as [| x1 l1 [Hu_bot_ge _] _]; subst x1 l1; clear Hfa1.
  unfold ok_d in Hok.
  destruct (Z_div3_nat d 0 Mnext c HM ltac:(lia) Hd_mod Hc_rem) as [Hd_eq _].
  replace (d - 0) with d in * by lia.
  set (m := d / 3) in *.
  assert (Hm_ge : 2 * N + 2 <= m) by lia.
  pose proof (f_omega2_id N) as Hf2_id.
  destruct (Kd_loop_7_3_dom m 0 (stack_tail [u_top; u_bot]) N HN Hm_ge)
    as [p_kd [b_kd [Hkd [Hp_kd [_ Hb_kd]]]]].
  destruct (Rem0_body p_kd b_kd u_top [u_bot] ltac:(lia) Hb_kd Hu_top)
    as [j0 [b0 [Hbody [Hj0 [_ [Hb0_ge [Hb0_ev _]]]]]]].
  assert (Hb_fin_odd : is_W_odd (W (j0 + u_bot) b0))
    by (apply W_ge3_even; [lia | lia | exact Hb0_ev]).
  destruct Hb_fin_odd as [Hb_fin_eq [Hb_fin_ge _]].
  exists (j0 + u_bot), (W (j0 + u_bot) b0 / 2).
  split; [| lia].
  eapply evstep_trans; [exact Hrun |].
  rewrite Hd_eq.
  eapply evstep_trans; [apply progress_evstep, Hkd |].
  eapply evstep_trans; [apply progress_evstep, Hbody |].
  eapply evstep_trans; [apply progress_evstep, Ca_drain_one |].
  cbn [stack_tail]. rewrite side_const0 at 1.
  eapply evstep_trans; [apply progress_evstep, CA_SH |].
  eapply evstep_trans; [apply progress_evstep, Ca_const0_exit |].
  rewrite Hb_fin_eq at 1.
  apply progress_evstep, Halt_odd_b.
Qed.

(** ** Chaining all 19 HUGE f_(omega+2) rounds *)

Lemma N_round_ge_3 : forall k, 3 <= iter k f_omega2 (f_omega 3).
Proof.
  intros k.
  pose proof (f_omega_dbl 3 ltac:(lia)) as H0.
  pose proof (iter_ge f_omega2 f_omega2_id k (f_omega 3)) as H1.
  lia.
Qed.

Lemma Reach_Round2 : RoundState 3486784401%Z 3323341382%Z 1 (iter 1 f_omega2 (f_omega 3)).
Proof.
  change (iter 1 f_omega2 (f_omega 3)) with (f_omega2 (f_omega 3)).
  eapply (Step_Rem2 3486784401%Z 7845264905%Z 3323341382%Z (f_omega 3));
    [lia | reflexivity | pose proof (f_omega_dbl 3 ltac:(lia)); lia | reflexivity | reflexivity | exact Boot_Round1].
Qed.

Lemma Reach_Round3 : RoundState 1162261467%Z 1024923929%Z 1 (iter 2 f_omega2 (f_omega 3)).
Proof.
  change (iter 2 f_omega2 (f_omega 3)) with (f_omega2 (iter 1 f_omega2 (f_omega 3))).
  eapply (Step_Rem2 1162261467%Z 3323341382%Z 1024923929%Z (iter 1 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 1) | reflexivity | reflexivity | exact Reach_Round2].
Qed.

Lemma Reach_Round4 : RoundState 387420489%Z 236202590%Z 1 (iter 3 f_omega2 (f_omega 3)).
Proof.
  change (iter 3 f_omega2 (f_omega 3)) with (f_omega2 (iter 2 f_omega2 (f_omega 3))).
  eapply (Step_Rem2 387420489%Z 1024923929%Z 236202590%Z (iter 2 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 2) | reflexivity | reflexivity | exact Reach_Round3].
Qed.

Lemma Reach_Round5 : RoundState 129140163%Z 125781898%Z 1 (iter 4 f_omega2 (f_omega 3)).
Proof.
  change (iter 4 f_omega2 (f_omega 3)) with (f_omega2 (iter 3 f_omega2 (f_omega 3))).
  eapply (Step_Rem2 129140163%Z 236202590%Z 125781898%Z (iter 3 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 3) | reflexivity | reflexivity | exact Reach_Round4].
Qed.

Lemma Reach_Round6 : RoundState 43046721%Z 36336568%Z 2 (iter 5 f_omega2 (f_omega 3)).
Proof.
  change (iter 5 f_omega2 (f_omega 3)) with (f_omega2 (iter 4 f_omega2 (f_omega 3))).
  eapply (Step_Rem1 43046721%Z 125781898%Z 36336568%Z 1 (iter 4 f_omega2 (f_omega 3)));
    [lia | reflexivity | lia | apply (N_round_ge_3 4) | reflexivity | reflexivity | exact Reach_Round5].
Qed.

Lemma Reach_Round7 : RoundState 14348907%Z 6311965%Z 3 (iter 6 f_omega2 (f_omega 3)).
Proof.
  change (iter 6 f_omega2 (f_omega 3)) with (f_omega2 (iter 5 f_omega2 (f_omega 3))).
  eapply (Step_Rem1 14348907%Z 36336568%Z 6311965%Z 2 (iter 5 f_omega2 (f_omega 3)));
    [lia | reflexivity | lia | apply (N_round_ge_3 5) | reflexivity | reflexivity | exact Reach_Round6].
Qed.

Lemma Reach_Round8 : RoundState 4782969%Z 107002%Z 4 (iter 7 f_omega2 (f_omega 3)).
Proof.
  change (iter 7 f_omega2 (f_omega 3)) with (f_omega2 (iter 6 f_omega2 (f_omega 3))).
  eapply (Step_Rem1 4782969%Z 6311965%Z 107002%Z 3 (iter 6 f_omega2 (f_omega 3)));
    [lia | reflexivity | lia | apply (N_round_ge_3 6) | reflexivity | reflexivity | exact Reach_Round7].
Qed.

Lemma Reach_Round9 : RoundState 1594323%Z 939162%Z 5 (iter 8 f_omega2 (f_omega 3)).
Proof.
  change (iter 8 f_omega2 (f_omega 3)) with (f_omega2 (iter 7 f_omega2 (f_omega 3))).
  eapply (Step_Rem1 1594323%Z 107002%Z 939162%Z 4 (iter 7 f_omega2 (f_omega 3)));
    [lia | reflexivity | lia | apply (N_round_ge_3 7) | reflexivity | reflexivity | exact Reach_Round8].
Qed.

Lemma Reach_Round10 : RoundState 531441%Z 371754%Z 1 (iter 9 f_omega2 (f_omega 3)).
Proof.
  change (iter 9 f_omega2 (f_omega 3)) with (f_omega2 (iter 8 f_omega2 (f_omega 3))).
  eapply (Step_Rem0_cont 531441%Z 939162%Z 371754%Z 2 (iter 8 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 8) | reflexivity | reflexivity | exact Reach_Round9].
Qed.

Lemma Reach_Round11 : RoundState 177147%Z 147156%Z 1 (iter 10 f_omega2 (f_omega 3)).
Proof.
  change (iter 10 f_omega2 (f_omega 3)) with (f_omega2 (iter 9 f_omega2 (f_omega 3))).
  eapply (Step_Rem0_cont 177147%Z 371754%Z 147156%Z 0 (iter 9 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 9) | reflexivity | reflexivity | exact Reach_Round10].
Qed.

Lemma Reach_Round12 : RoundState 59049%Z 21347%Z 1 (iter 11 f_omega2 (f_omega 3)).
Proof.
  change (iter 11 f_omega2 (f_omega 3)) with (f_omega2 (iter 10 f_omega2 (f_omega 3))).
  eapply (Step_Rem0_cont 59049%Z 147156%Z 21347%Z 0 (iter 10 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 10) | reflexivity | reflexivity | exact Reach_Round11].
Qed.

Lemma Reach_Round13 : RoundState 19683%Z 4758%Z 1 (iter 12 f_omega2 (f_omega 3)).
Proof.
  change (iter 12 f_omega2 (f_omega 3)) with (f_omega2 (iter 11 f_omega2 (f_omega 3))).
  eapply (Step_Rem2 19683%Z 21347%Z 4758%Z (iter 11 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 11) | reflexivity | reflexivity | exact Reach_Round12].
Qed.

Lemma Reach_Round14 : RoundState 6561%Z 3527%Z 1 (iter 13 f_omega2 (f_omega 3)).
Proof.
  change (iter 13 f_omega2 (f_omega 3)) with (f_omega2 (iter 12 f_omega2 (f_omega 3))).
  eapply (Step_Rem0_cont 6561%Z 4758%Z 3527%Z 0 (iter 12 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 12) | reflexivity | reflexivity | exact Reach_Round13].
Qed.

Lemma Reach_Round15 : RoundState 2187%Z 438%Z 1 (iter 14 f_omega2 (f_omega 3)).
Proof.
  change (iter 14 f_omega2 (f_omega 3)) with (f_omega2 (iter 13 f_omega2 (f_omega 3))).
  eapply (Step_Rem2 2187%Z 3527%Z 438%Z (iter 13 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 13) | reflexivity | reflexivity | exact Reach_Round14].
Qed.

Lemma Reach_Round16 : RoundState 729%Z 359%Z 1 (iter 15 f_omega2 (f_omega 3)).
Proof.
  change (iter 15 f_omega2 (f_omega 3)) with (f_omega2 (iter 14 f_omega2 (f_omega 3))).
  eapply (Step_Rem0_cont 729%Z 438%Z 359%Z 0 (iter 14 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 14) | reflexivity | reflexivity | exact Reach_Round15].
Qed.

Lemma Reach_Round17 : RoundState 243%Z 156%Z 1 (iter 16 f_omega2 (f_omega 3)).
Proof.
  change (iter 16 f_omega2 (f_omega 3)) with (f_omega2 (iter 15 f_omega2 (f_omega 3))).
  eapply (Step_Rem2 243%Z 359%Z 156%Z (iter 15 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 15) | reflexivity | reflexivity | exact Reach_Round16].
Qed.

Lemma Reach_Round18 : RoundState 81%Z 55%Z 1 (iter 17 f_omega2 (f_omega 3)).
Proof.
  change (iter 17 f_omega2 (f_omega 3)) with (f_omega2 (iter 16 f_omega2 (f_omega 3))).
  eapply (Step_Rem0_cont 81%Z 156%Z 55%Z 0 (iter 16 f_omega2 (f_omega 3)));
    [lia | reflexivity | apply (N_round_ge_3 16) | reflexivity | reflexivity | exact Reach_Round17].
Qed.

Lemma Reach_Round19 : RoundState 27%Z 12%Z 2 (iter 18 f_omega2 (f_omega 3)).
Proof.
  change (iter 18 f_omega2 (f_omega 3)) with (f_omega2 (iter 17 f_omega2 (f_omega 3))).
  eapply (Step_Rem1 27%Z 55%Z 12%Z 1 (iter 17 f_omega2 (f_omega 3)));
    [lia | reflexivity | lia | apply (N_round_ge_3 17) | reflexivity | reflexivity | exact Reach_Round18].
Qed.

Lemma Run_Halt_19 :
  exists p_fin m_fin,
    c0 -->* c_end p_fin m_fin /\
    p_fin + m_fin + 4 > iter 19 f_omega2 (f_omega 3).
Proof.
  change (iter 19 f_omega2 (f_omega 3)) with (f_omega2 (iter 18 f_omega2 (f_omega 3))).
  eapply (Step_Rem0_halt 9%Z 12%Z (iter 18 f_omega2 (f_omega 3)));
    [lia | apply (N_round_ge_3 18) | reflexivity | exact Reach_Round19].
Qed.

(** ** Main Halting and Sigma(13) Lower Bound Theorems *)

Theorem halt : halts tm c0.
Proof.
  destruct Run_Halt_19 as [p_fin [m_fin [Hrun _]]].
  destruct (with_counter Hrun) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts, c_end_halted.
Qed.

Theorem sigma_bound :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
  n > iter 19 f_omega2 (f_omega 3).
Proof.
  destruct Run_Halt_19 as [p_fin [m_fin [Hrun Hgt]]].
  exists (c_end p_fin m_fin), (p_fin + m_fin + 4).
  split; [exact Hrun |].
  split; [apply c_end_halted |].
  split; [apply ones_c_end | exact Hgt].
Qed.

Lemma iter18_fw1_le_iter19_fw0 :
  iter 18 f_omega2 (iter 2 f_omega1 3) <= iter 19 f_omega2 (f_omega 3).
Proof.
  rewrite (iter_S' 18 f_omega2 (f_omega 3)).
  apply iter_mono_x; [apply f_omega2_mono |].
  apply f_omega2_ge_iter3.
  transitivity (2 * 3); [lia | exact (f_omega_dbl 3 ltac:(lia))].
Qed.

Theorem sigma_bound_fw1 :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
  n > iter 18 f_omega2 (iter 2 f_omega1 3).
Proof.
  destruct sigma_bound as [c [n [Hrun [Hhalt [Hones Hgt]]]]].
  exists c, n.
  split; [exact Hrun | split; [exact Hhalt | split; [exact Hones |]]].
  exact (Nat.le_lt_trans _ _ _ iter18_fw1_le_iter19_fw0 Hgt).
Qed.

Corollary beats_M13b :
  exists c n, c0 -->* c /\ halted tm c /\ ones c n /\
  n > iter 6 f_omega2 (iter 2 f_omega1 3).
Proof.
  destruct sigma_bound_fw1 as [c [n [Hrun [Hhalt [Hones Hgt]]]]].
  exists c, n.
  split; [exact Hrun | split; [exact Hhalt | split; [exact Hones |]]].
  assert (H6_18 : iter 6 f_omega2 (iter 2 f_omega1 3) <= iter 18 f_omega2 (iter 2 f_omega1 3))
    by (apply iter_mono_n; [apply f_omega2_id | lia]).
  exact (Nat.le_lt_trans _ _ _ H6_18 Hgt).
Qed.

(** ** Strict first-visit canonical TNF isomorphism (tm_tnf) *)

(* Strict first-visit canonical TNF string:
   1RB1RA_1RC1RK_1RD0LM_0LE1RI_0LH1LF_0LE1LG_---0LF_1RA0LJ_1RH0RA_1LH1LJ_0LL1LH_0RD1LL_1LJ1LC *)
Definition tm_tnf : TM := fun '(q, s) =>
  match q, s with
  | A, S0 => Some (S1, TM.R, B) | A, S1 => Some (S1, TM.R, A)
  | B, S0 => Some (S1, TM.R, C) | B, S1 => Some (S1, TM.R, K)
  | C, S0 => Some (S1, TM.R, D) | C, S1 => Some (S0, TM.L, M)
  | D, S0 => Some (S0, TM.L, E) | D, S1 => Some (S1, TM.R, I)
  | E, S0 => Some (S0, TM.L, H) | E, S1 => Some (S1, TM.L, F)
  | F, S0 => Some (S0, TM.L, E) | F, S1 => Some (S1, TM.L, G)
  | G, S0 => None               | G, S1 => Some (S0, TM.L, F)
  | H, S0 => Some (S1, TM.R, A) | H, S1 => Some (S0, TM.L, J)
  | I, S0 => Some (S1, TM.R, H) | I, S1 => Some (S0, TM.R, A)
  | J, S0 => Some (S1, TM.L, H) | J, S1 => Some (S1, TM.L, J)
  | K, S0 => Some (S0, TM.L, L) | K, S1 => Some (S1, TM.L, H)
  | L, S0 => Some (S0, TM.R, D) | L, S1 => Some (S1, TM.L, L)
  | M, S0 => Some (S1, TM.L, J) | M, S1 => Some (S1, TM.L, C)
  end.

Definition perm_f (q : Q) : Q :=
  match q with
  | A => A | B => B | C => K | D => L | E => D | F => I | G => H
  | H => J | I => C | J => M | K => G | L => F | M => E
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
  n > iter 19 f_omega2 (f_omega 3).
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

Theorem beats_M13b_tnf :
  exists c n, c0 -[ tm_tnf ]->* c /\ halted tm_tnf c /\ ones c n /\
  n > iter 6 f_omega2 (iter 2 f_omega1 3).
Proof.
  destruct beats_M13b as [[q t] [n [Hrun [Hhalt [Hones Hgt]]]]].
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
Print Assumptions sigma_bound_fw1.
Print Assumptions beats_M13b.
Print Assumptions halt_tnf.
Print Assumptions sigma_bound_tnf.
Print Assumptions beats_M13b_tnf.
