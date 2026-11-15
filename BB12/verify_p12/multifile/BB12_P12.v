(** * The 12-state machine P12 halts from the blank tape *)

(** P12 = 1RB1RA_1RI1RC_0LD1LG_0RE1LD_---1RF_0LL0RA_1RA0LH_1LG1LH_1RK0LJ_1LH1LI_0LL0RD_0LH1LK   (start A)
    It is the M12/C4 core (states A-D, G, H, J and E1, F1, I1; the f_omega engine Ch -> Ca (W) of BB12_M12.v) with
    E0 = halt, F0 = 0LL, I0 = 1RK, K = 0LL 0RD, L = 0LH 1LK.

    Configurations: Y p u w = [1]^u [0;1]^p 0^inf {I}> w, X p u t = Y p u (0 >> t).
      R_A   X p u ([1;0]^(d+2) t)  -->+ Y p (W p u + 2) ([1;0]^(d+1) t)
      R_Bo  Y (q+1) (2m+3) (1 >> t) -->+ Y q (W q 1 + 2) ([1;0]^(m+1) t)
      R_Be  Y (q+1) (2m+2) (1 0 t)  -->+ Y (q+m+1) (W q 1 + 2) t          (one class-2 pass, map Be)
      BLANK Y p (2m+2) blank        -->+ Y 0 4 ([1;0]^(p+m+2) blank)
      R_H   X p u (1 0 blank) halts (E0) with p + u + 1 ones.
    One round (map Rd) uses two pairs of the base stock and runs (W p u + 1)/2 class-2 passes; a big round (map Big)
    runs (D-2)/2 rounds on a base of D pairs and, if D is even, rebuilds a base of Big D pairs.  The run starts with
    the base D_0 = 9 + W(4,1)/2, the bases D_0..D_6 are even and D_7 is odd: the machine halts in the eighth big
    round.  The parities come from the 2-adic residues of the W tower: W j b mod 2^13 is 3826 (b odd) or 407
    (b even, b >= 1) for j >= 4 (lemmas W2_cong, T_tab, W_res), which gives Big D mod 4096 = 1922 + 1131 (D-2)/2,
    and D_k mod 2^(12-k) = 1922, 194, 930, 370, 106, 62, 12, 25.
    Main results: [halt : halts tm c0] and [score_exact]. *)

From Coq Require Import Lia PeanoNat List ZArith NArith.
From BB8 Require Import Individual122.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB1RA_1RI1RC_0LD1LG_0RE1LD_---1RF_0LL0RA_1RA0LH_1LG1LH_1RK0LJ_1LH1LI_0LL0RD_0LH1LK *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, TM.R, B)  | A, 1 => Some (1, TM.R, A)
  | B, 0 => Some (1, TM.R, I)  | B, 1 => Some (1, TM.R, C)
  | C, 0 => Some (0, TM.L, D)  | C, 1 => Some (1, TM.L, G)
  | D, 0 => Some (0, TM.R, E)  | D, 1 => Some (1, TM.L, D)
  | E, 0 => None               | E, 1 => Some (1, TM.R, F)
  | F, 0 => Some (0, TM.L, L)  | F, 1 => Some (0, TM.R, A)
  | G, 0 => Some (1, TM.R, A)  | G, 1 => Some (0, TM.L, H)
  | H, 0 => Some (1, TM.L, G)  | H, 1 => Some (1, TM.L, H)
  | I, 0 => Some (1, TM.R, K)  | I, 1 => Some (0, TM.L, J)
  | J, 0 => Some (1, TM.L, H)  | J, 1 => Some (1, TM.L, I)
  | K, 0 => Some (0, TM.L, L)  | K, 1 => Some (0, TM.R, D)
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

(** P12's own K/L conversion: a pair of ones on the left becomes a pair [1;0] on the right. *)
Lemma cr_KL_11 : forall n l r, [1; 1]^^n *> l <{{K}} (1 >> 0 >> r) -->* l <{{K}} ([1; 0]^^n *> 1 >> 0 >> r).
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_KL_01 : forall n l r, [0; 1]^^n *> l <{{K}} r -->* l <{{K}} [1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** ** The f_omega engine (BB12_M12.v, unchanged: P12 agrees with M12 on every transition it uses) *)

Definition Ca (j b : nat) (z : side) : Q * tape :=
  ([1]^^b *> [0; 1]^^j *> const 0) {{A}}> (0 >> z).

Definition Ch (j b : nat) (z : side) : Q * tape :=
  ([0; 1]^^j *> const 0) <{{H}} (1 >> [1]^^b *> 0 >> z).

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

Local Close Scope nat_scope.

(** ** P12 configurations and rules *)

Definition Y (p u : nat) (w : side) : Q * tape :=
  ([1]^^u *> [0; 1]^^p *> const 0) {{I}}> w.

Definition X (p u : nat) (t : side) : Q * tape := Y p u (0 >> t).

Lemma lpow_odd : forall (x : Sym) m (l : side), [x]^^(2 * m + 1) *> l = x >> [x; x]^^m *> l.
Proof.
  intros x m l. replace (2 * m + 1)%nat with (S (2 * m)) by lia.
  cbn [lpow app Str_app]. rewrite lpow_double. reflexivity.
Qed.

Lemma lpow_even : forall (x : Sym) m (l : side), [x]^^(2 * m) *> l = [x; x]^^m *> l.
Proof. intros x m l. rewrite lpow_double. reflexivity. Qed.

Lemma R_A_aux : forall p u t,
  X p u (1 >> 0 >> 1 >> 0 >> t) -->+ Ch p u (0 >> 1 >> 0 >> t).
Proof.
  intros p u t. unfold X, Y, Ch.
  start_progress.
  follow cr_HL_1_1.
  finish_norm.
Qed.

Lemma R_A : forall p u t,
  X p u (1 >> 0 >> 1 >> 0 >> t) -->+ Y p (W p u + 2) (1 >> 0 >> t).
Proof.
  intros p u t.
  eapply progress_evstep_trans; [apply R_A_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  apply progress_evstep. unfold Y. apply CA_EXIT.
Qed.

Definition c_end (p u : nat) : Q * tape :=
  (0 >> 0 >> 1 >> [1]^^u *> [0; 1]^^p *> const 0) {{E}}> const 0.

Lemma R_H : forall p u, X p u (1 >> 0 >> const 0) -->+ c_end p u.
Proof.
  intros p u. unfold X, Y, c_end.
  start_progress; try finish_norm.
Qed.

Lemma c_end_halted : forall p u, halted tm (c_end p u).
Proof. intros p u. reflexivity. Qed.

Lemma R_Be_aux : forall q m t,
  Y (S q) (2 * m + 2) (1 >> 0 >> t) -->+ Ch q 1 ([1; 0]^^(S m) *> 0 >> t).
Proof.
  intros q m t. unfold Y, Ch.
  replace (2 * m + 2)%nat with (1 + (2 * m + 1))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] m). cbn [app].
  start_progress.
  follow cr_IL_11_10.
  execute; finish_norm.
Qed.

Lemma R_Be : forall q m t,
  Y (S q) (2 * m + 2) (1 >> 0 >> t) -->+ Y (q + S m) (W q 1 + 2) t.
Proof.
  intros q m t.
  eapply progress_evstep_trans; [apply R_Be_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  follow (CA_SH_iter (S m) q (W q 1) (0 >> t)).
  apply progress_evstep. unfold Y. apply CA_EXIT.
Qed.

Lemma pair_shift : forall n (t : side), [1; 0]^^n *> 1 >> 0 >> t = 1 >> 0 >> [1; 0]^^n *> t.
Proof. intros n t. change (1 >> 0 >> t) with ([1; 0] *> t). rewrite lpow_shift'. reflexivity. Qed.

Lemma R_Bo_aux : forall q m t,
  Y (S q) (2 * m + 3) (1 >> t) -->+ Ch q 1 (0 >> [1; 0]^^(S m) *> t).
Proof.
  intros q m t. unfold Y, Ch.
  replace (2 * m + 3)%nat with (1 + (2 * S m))%nat by lia.
  rewrite !lpow_add. cbn [lpow Str_app].
  rewrite (lpow_double [1] (S m)). cbn [app].
  start_progress.
  follow cr_IL_11_10.
  rewrite !pair_shift.
  execute; finish_norm.
Qed.

Lemma R_Bo : forall q m t,
  Y (S q) (2 * m + 3) (1 >> t) -->+ Y q (W q 1 + 2) ([1; 0]^^(S m) *> t).
Proof.
  intros q m t.
  eapply progress_evstep_trans; [apply R_Bo_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  apply progress_evstep. unfold Y. apply CA_EXIT.
Qed.

Lemma cr_KL_11c : forall n l, [1; 1]^^n *> l <{{K}} (1 >> const 0) -->* l <{{K}} ([1; 0]^^n *> 1 >> const 0).
Proof. intros n l. pose proof (cr_KL_11 n l (const 0)) as H. rewrite <- const_unfold in H. exact H. Qed.

Lemma BLANK_aux : forall p m,
  Y p (2 * m + 2) (const 0) -->+ Y 0 4 ([1; 0]^^p *> [1; 0]^^(S m) *> 1 >> const 0).
Proof.
  intros p m. unfold Y.
  replace (2 * m + 2)%nat with (2 * S m)%nat by lia.
  rewrite lpow_even.
  start_progress.
  follow cr_KL_11.
  follow cr_KL_01.
  execute; try finish_norm.
Qed.

Lemma BLANK : forall p m,
  Y p (2 * m + 2) (const 0) -->+ Y 0 4 ([1; 0]^^(p + m + 2) *> const 0).
Proof.
  intros p m.
  assert (E : [1; 0]^^(p + m + 2) *> const 0 = [1; 0]^^p *> [1; 0]^^(S m) *> 1 >> const 0).
  { replace (p + m + 2)%nat with (p + (S m + 1))%nat by lia.
    rewrite !lpow_add, !Str_app_assoc. cbn [lpow app Str_app]. rewrite <- const_unfold. reflexivity. }
  rewrite E. apply BLANK_aux.
Qed.

Lemma BOOT2 : forall D t,
  Y 0 4 ([1; 0]^^(S (S D)) *> t) -->+ Y 2 5 ([1; 0]^^(S D) *> t).
Proof.
  intros D t. unfold Y. cbn [lpow Str_app app].
  start_progress; try finish_norm.
Qed.

Local Open Scope nat_scope.

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
Proof. intros b. rewrite W_S, iter_W0. lia. Qed.

(** ** W 2 in closed form *)

Lemma W2_closed : forall y, 2 * W 2 y + 5 = 3 ^ (y + 3).
Proof.
  assert (G : forall n, 2 * iter n (W 1) 2 + 5 = 3 ^ (n + 2)).
  { induction n as [| n IHn]; cbn [iter].
    - reflexivity.
    - rewrite W_1. replace (S n + 2) with (S (n + 2)) by lia.
      rewrite Nat.pow_succ_r'. lia. }
  intros y. rewrite W_S. rewrite G. f_equal. lia.
Qed.

(** ** Residues through Z divisibility *)

Lemma natmod_of_Zdiv : forall a b m, m <> 0 ->
  (Z.of_nat m | Z.of_nat a - Z.of_nat b)%Z -> a mod m = b mod m.
Proof.
  intros a b m Hm [k Hk]. apply Nat2Z.inj. rewrite !Nat2Z.inj_mod.
  replace (Z.of_nat a) with (Z.of_nat b + k * Z.of_nat m)%Z by lia.
  rewrite Z.mod_add; [reflexivity | lia].
Qed.

Lemma Zdiv_of_natmod : forall a b m, m <> 0 -> a mod m = b mod m ->
  (Z.of_nat m | Z.of_nat a - Z.of_nat b)%Z.
Proof.
  intros a b m Hm H.
  pose proof (Nat.div_mod a m Hm) as Ha. pose proof (Nat.div_mod b m Hm) as Hb.
  exists (Z.of_nat (a / m) - Z.of_nat (b / m))%Z.
  rewrite H in Ha.
  set (qa := a / m) in *. set (qb := b / m) in *. set (r := b mod m) in *. clearbody qa qb r.
  nia.
Qed.

Lemma Zdiv_pow_sub1 : forall a t, (a - 1 | a ^ Z.of_nat t - 1)%Z.
Proof.
  intros a t. induction t as [| t IHt].
  - simpl. apply Z.divide_0_r.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    replace (a * a ^ Z.of_nat t - 1)%Z with (a * (a ^ Z.of_nat t - 1) + (a - 1))%Z by ring.
    apply Z.divide_add_r; [apply Z.divide_mul_r; exact IHt | apply Z.divide_refl].
Qed.

(** 3 has order 2^(n+1) modulo 2^(n+3). *)
Lemma ord3 : forall n, (2 ^ (Z.of_nat n + 3) | 3 ^ (2 ^ (Z.of_nat n + 1)) - 1)%Z.
Proof.
  induction n as [| n IHn].
  - exists 1%Z. reflexivity.
  - rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat n) + 3)%Z with ((Z.of_nat n + 3) + 1)%Z by lia.
    replace (Z.succ (Z.of_nat n) + 1)%Z with ((Z.of_nat n + 1) + 1)%Z by lia.
    rewrite (Z.pow_add_r 2 (Z.of_nat n + 3) 1) by lia.
    rewrite (Z.pow_add_r 2 (Z.of_nat n + 1) 1) by lia.
    rewrite Z.pow_mul_r by (try apply Z.pow_nonneg; lia).
    set (a := (3 ^ 2 ^ (Z.of_nat n + 1))%Z) in *. clearbody a.
    change (2 ^ 1)%Z with 2%Z.
    destruct IHn as [k Hk].
    assert (E : (2 ^ (Z.of_nat n + 3) = 2 * 2 ^ (Z.of_nat n + 2))%Z).
    { replace (Z.of_nat n + 3)%Z with (Z.succ (Z.of_nat n + 2)) by lia.
      rewrite Z.pow_succ_r by lia. reflexivity. }
    rewrite E in Hk |- *.
    exists (k * (k * 2 ^ (Z.of_nat n + 2) + 1))%Z.
    replace a with (k * (2 * 2 ^ (Z.of_nat n + 2)) + 1)%Z by lia.
    ring.
Qed.

Lemma W2_shift : forall n x t,
  W 2 (x + 2 ^ (S n) * t) mod 2 ^ (S (S n)) = W 2 x mod 2 ^ (S (S n)).
Proof.
  intros n x t.
  apply natmod_of_Zdiv; [apply Nat.pow_nonzero; discriminate |].
  set (a := 3 ^ 2 ^ S n).
  assert (E1 : 2 * W 2 (x + 2 ^ S n * t) + 5 = 3 ^ (x + 3) * a ^ t).
  { rewrite W2_closed. unfold a. rewrite <- Nat.pow_mul_r, <- Nat.pow_add_r. f_equal. lia. }
  pose proof (W2_closed x) as E2.
  assert (Ha : (2 ^ (Z.of_nat n + 3) | Z.of_nat a - 1)%Z).
  { unfold a. rewrite !Nat2Z.inj_pow.
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1)%Z by lia.
    change (Z.of_nat 3) with 3%Z. change (Z.of_nat 2) with 2%Z. apply ord3. }
  assert (Ht : (2 ^ (Z.of_nat n + 3) | Z.of_nat (a ^ t) - 1)%Z).
  { rewrite Nat2Z.inj_pow. eapply Z.divide_trans; [exact Ha | apply Zdiv_pow_sub1]. }
  assert (Hd : (2 ^ (Z.of_nat n + 3) | 2 * (Z.of_nat (W 2 (x + 2 ^ S n * t)) - Z.of_nat (W 2 x)))%Z).
  { replace (2 * (Z.of_nat (W 2 (x + 2 ^ S n * t)) - Z.of_nat (W 2 x)))%Z
      with (Z.of_nat (3 ^ (x + 3)) * (Z.of_nat (a ^ t) - 1))%Z.
    - apply Z.divide_mul_r. exact Ht.
    - apply (f_equal Z.of_nat) in E1, E2. rewrite Nat2Z.inj_mul in E1.
      set (P := Z.of_nat (3 ^ (x + 3))) in *. set (At := Z.of_nat (a ^ t)) in *.
      clearbody P At. nia. }
  replace (Z.of_nat n + 3)%Z with (Z.succ (Z.of_nat n + 2)) in Hd by lia.
  rewrite Z.pow_succ_r in Hd by lia.
  apply Z.mul_divide_cancel_l in Hd; [| lia].
  rewrite Nat2Z.inj_pow. replace (Z.of_nat (S (S n))) with (Z.of_nat n + 2)%Z by lia.
  change (Z.of_nat 2) with 2%Z. exact Hd.
Qed.

Lemma W2_cong : forall n x y, x mod 2 ^ (S n) = y mod 2 ^ (S n) ->
  W 2 x mod 2 ^ (S (S n)) = W 2 y mod 2 ^ (S (S n)).
Proof.
  intros n x y H.
  assert (HM : 2 ^ (S n) <> 0) by (apply Nat.pow_nonzero; discriminate).
  rewrite (Nat.div_mod x (2 ^ (S n)) HM), (Nat.div_mod y (2 ^ (S n)) HM).
  rewrite !(Nat.add_comm (2 ^ S n * _)).
  rewrite !W2_shift, H. reflexivity.
Qed.

(** ** The tower T h = W2^h 2 modulo 2^(k+1) depends only on h mod 2 once h >= k *)

Definition T (h : nat) : nat := iter h (W 2) 2.

Lemma T_S : forall h, T (S h) = W 2 (T h).
Proof. reflexivity. Qed.

Lemma T_par : forall h, T h mod 2 = h mod 2.
Proof.
  intros h. unfold T. rewrite (iter_par_nat (W 2) (W_par 2)). mods; lia.
Qed.

Lemma T_lin : forall h, 2 + 3 * h <= T h.
Proof. intros h. unfold T. apply (iter_lin3 (W 2) (W_grow 2)). Qed.

Definition tabE : list nat := [0; 2; 2; 2; 18; 50; 114; 242; 242; 754; 1778; 3826; 3826].
Definition tabO : list nat := [1; 3; 7; 7; 23; 23; 23; 151; 407; 407; 407; 407; 407].
Definition tabv (k par : nat) : nat := nth k (if par =? 0 then tabE else tabO) 0.

Lemma W2_mod_N : forall r M v, M <> 0 -> v < M ->
  (N.of_nat 3 ^ N.of_nat (r + 3) mod N.of_nat (2 * M) = N.of_nat (2 * v + 5) mod N.of_nat (2 * M))%N ->
  W 2 r mod M = v.
Proof.
  intros r M v HM Hv HN.
  rewrite <- Nat2N.inj_pow, <- !Nat2N.inj_mod in HN. apply Nat2N.inj in HN.
  rewrite <- W2_closed in HN.
  apply Zdiv_of_natmod in HN; [| lia].
  assert (H2 : (Z.of_nat M | Z.of_nat (W 2 r) - Z.of_nat v)%Z).
  { rewrite Nat2Z.inj_mul in HN. change (Z.of_nat 2) with 2%Z in HN.
    replace (Z.of_nat (2 * W 2 r + 5) - Z.of_nat (2 * v + 5))%Z
      with (2 * (Z.of_nat (W 2 r) - Z.of_nat v))%Z in HN by lia.
    apply Z.mul_divide_cancel_l in HN; [exact HN | lia]. }
  apply natmod_of_Zdiv in H2; [| exact HM].
  rewrite H2. apply Nat.mod_small. exact Hv.
Qed.

Ltac tabcase := apply W2_mod_N;
  [apply Nat.pow_nonzero; discriminate | apply Nat.ltb_lt; vm_compute; reflexivity | vm_compute; reflexivity].

Lemma tab_step : forall k par, k < 12 -> par < 2 ->
  W 2 (tabv k par) mod 2 ^ (S (S k)) = tabv (S k) (1 - par).
Proof.
  intros k par Hk Hp.
  do 12 (destruct k as [| k]; [destruct par as [| [| par]]; [tabcase | tabcase | lia] |]).
  lia.
Qed.

Lemma tab_lt : forall k par, k <= 12 -> tabv k par < 2 ^ (S k).
Proof.
  intros k par Hk. unfold tabv.
  destruct (par =? 0); do 13 (destruct k as [| k]; [apply Nat.ltb_lt; vm_compute; reflexivity |]); lia.
Qed.

Lemma T_tab : forall k h, k <= 12 -> k <= h -> T h mod 2 ^ (S k) = tabv k (h mod 2).
Proof.
  induction k as [| k IHk]; intros h Hk Hh.
  - rewrite T_par. assert (h mod 2 < 2) by (apply Nat.mod_upper_bound; discriminate).
    destruct (h mod 2) as [| [| x]]; [reflexivity | reflexivity | lia].
  - destruct h as [| h]; [lia |].
    rewrite T_S.
    assert (IH : T h mod 2 ^ (S k) = tabv k (h mod 2) mod 2 ^ (S k)).
    { rewrite IHk by lia. symmetry. apply Nat.mod_small. apply tab_lt; lia. }
    rewrite (W2_cong k _ _ IH).
    rewrite tab_step by (try lia; apply Nat.mod_upper_bound; discriminate).
    f_equal.
    assert (h mod 2 < 2) by (apply Nat.mod_upper_bound; discriminate).
    replace (S h) with (h + 1) by lia. mods; lia.
Qed.

Lemma T_mod : forall h, 12 <= h -> T h mod (2 * 4096) = if h mod 2 =? 0 then 3826 else 407.
Proof.
  intros h Hh.
  replace (2 * 4096) with (2 ^ (S 12)) by reflexivity.
  rewrite T_tab by lia.
  assert (h mod 2 < 2) by (apply Nat.mod_upper_bound; discriminate).
  destruct (h mod 2) as [| [| x]]; [reflexivity | reflexivity | lia].
Qed.

(** ** Every W j b (j >= 3) is a tower T h with h >= b+1 *)

Lemma W_T : forall j b, exists h, S b <= h /\ W (3 + j) b = T h.
Proof.
  induction j as [| j IHj]; intros b.
  - exists (S b). split; [lia | reflexivity].
  - destruct (IHj (iter b (W (3 + j)) 2)) as [h [Hh E]].
    exists h. split.
    + pose proof (iter_lin3 (W (3 + j)) (W_grow (3 + j)) b 2) as Hl. lia.
    + rewrite <- E. reflexivity.
Qed.

Lemma W_big : forall j b, 4 <= j -> 1 <= b -> exists h, 12 <= h /\ W j b = T h.
Proof.
  intros j b Hj Hb.
  destruct j as [| [| [| [| j]]]]; try lia.
  destruct b as [| b]; [lia |].
  pose proof (iter_lin3 (W (3 + j)) (W_grow (3 + j)) b 2) as Hy.
  destruct (W_T j (iter b (W (3 + j)) 2)) as [h1 [Hh1 E1]].
  pose proof (T_lin h1) as Hx. rewrite <- E1 in Hx.
  destruct (W_T j (W (3 + j) (iter b (W (3 + j)) 2))) as [h [Hh E]].
  exists h. split.
  - lia.
  - rewrite <- E. reflexivity.
Qed.

(** Residues used by the run: for j >= 4 and b >= 1, W j b mod 2^13 is 3826 (b odd) or 407 (b even). *)
Lemma W_res : forall j b, 4 <= j -> 1 <= b ->
  W j b mod (2 * 4096) = if b mod 2 =? 0 then 407 else 3826.
Proof.
  intros j b Hj Hb.
  destruct (W_big j b Hj Hb) as [h [Hh E]].
  pose proof (W_par j b) as Hp. rewrite E in Hp |- *. rewrite T_par in Hp.
  rewrite T_mod by exact Hh.
  assert (Hc : (b mod 2 = 0 /\ h mod 2 = 1) \/ (b mod 2 = 1 /\ h mod 2 = 0)) by (clear E; mods; lia).
  destruct Hc as [[-> ->] | [-> ->]]; reflexivity.
Qed.

Lemma W_res1 : forall j, 4 <= j -> W j 1 mod (2 * 4096) = 3826.
Proof. intros j Hj. rewrite (W_res j 1 Hj) by lia. reflexivity. Qed.

Lemma W_res_even : forall j b, 4 <= j -> 1 <= b -> b mod 2 = 0 -> W j b mod (2 * 4096) = 407.
Proof. intros j b Hj Hb He. rewrite (W_res j b Hj Hb), He. reflexivity. Qed.

Local Close Scope nat_scope.

(** ** Loop maps *)

Local Open Scope nat_scope.

(** one class-2 pass:  Y q u (1 0 T) -> Y (q-1+u/2) (W (q-1) 1 + 2) T *)
Definition Be (qu : nat * nat) : nat * nat :=
  let '(q, u) := qu in (q - 1 + u / 2, W (q - 1) 1 + 2).

(** one class-3 pass (round): two pairs of the base stock *)
Definition Rd (pu : nat * nat) : nat * nat :=
  let '(p, u) := pu in iter ((W p u + 1) / 2) Be (p - 1, W (p - 1) 1 + 2).

(** one big round: base D -> next base *)
Definition BigP (D : nat) : nat * nat := iter ((D - 2) / 2) Rd (7, W 4 1 + 2).
Definition Big (D : nat) : nat := fst (BigP D) + snd (BigP D) / 2 + 1.

Lemma Be_eq : forall q u, Be (q, u) = (q - 1 + u / 2, W (q - 1) 1 + 2).
Proof. reflexivity. Qed.

Lemma Rd_eq : forall p u, Rd (p, u) = iter ((W p u + 1) / 2) Be (p - 1, W (p - 1) 1 + 2).
Proof. reflexivity. Qed.

Lemma Big_eq : forall D, Big D = fst (iter ((D - 2) / 2) Rd (7, W 4 1 + 2)) + snd (iter ((D - 2) / 2) Rd (7, W 4 1 + 2)) / 2 + 1.
Proof. reflexivity. Qed.

Lemma half2 : forall m, (2 * m + 2) / 2 = S m.
Proof. intros m. replace (2 * m + 2) with (S m * 2) by lia. apply Nat.div_mul. lia. Qed.

Lemma W_even1 : forall j, (W j 1 + 2) mod 2 = 0.
Proof. intros j. pose proof (W_par j 1). mods; lia. Qed.

(** ** Invariants (sizes, parity) *)

Lemma Be_ok : forall q u, 1 <= q -> 4 <= u -> u mod 2 = 0 ->
  1 <= fst (Be (q, u)) /\ 4 <= snd (Be (q, u)) /\ snd (Be (q, u)) mod 2 = 0 /\ q + 1 <= fst (Be (q, u)).
Proof.
  intros q u Hq Hu He. rewrite Be_eq. cbn [fst snd].
  pose proof (W_grow (q - 1) 1). pose proof (W_even1 (q - 1)).
  assert (2 <= u / 2) by (mods; lia).
  repeat split; lia.
Qed.

Lemma iter_Be_ok : forall n q u, 1 <= q -> 4 <= u -> u mod 2 = 0 ->
  1 <= fst (iter n Be (q, u)) /\ 4 <= snd (iter n Be (q, u)) /\ snd (iter n Be (q, u)) mod 2 = 0 /\
  q + n <= fst (iter n Be (q, u)).
Proof.
  induction n as [| n IHn]; intros q u Hq Hu He.
  - cbn [iter fst snd]. repeat split; lia.
  - cbn [iter]. destruct (IHn q u Hq Hu He) as [H1 [H2 [H3 H4]]].
    destruct (iter n Be (q, u)) as [q2 u2]. cbn [fst snd] in *.
    destruct (Be_ok q2 u2 H1 H2 H3) as [G1 [G2 [G3 G4]]].
    repeat split; lia.
Qed.

Lemma Rd_ok : forall p u, 2 <= p -> u mod 2 = 0 ->
  2 <= fst (Rd (p, u)) /\ snd (Rd (p, u)) mod 2 = 0 /\ 4 <= snd (Rd (p, u)).
Proof.
  intros p u Hp Hu. rewrite Rd_eq.
  pose proof (W_grow p u).
  assert (Hm : 1 <= (W p u + 1) / 2) by (mods; lia).
  pose proof (W_grow (p - 1) 1).
  destruct (iter_Be_ok ((W p u + 1) / 2) (p - 1) (W (p - 1) 1 + 2)) as [H1 [H2 [H3 H4]]];
    [lia | lia | apply W_even1 |].
  repeat split; lia.
Qed.

Lemma iter_Rd_ok : forall r p u, 2 <= p -> u mod 2 = 0 -> 4 <= u ->
  2 <= fst (iter r Rd (p, u)) /\ snd (iter r Rd (p, u)) mod 2 = 0 /\ 4 <= snd (iter r Rd (p, u)).
Proof.
  induction r as [| r IHr]; intros p u Hp Hu Hu4.
  - cbn [iter fst snd]. repeat split; lia.
  - cbn [iter]. destruct (IHr p u Hp Hu Hu4) as [H1 [H2 H3]].
    destruct (iter r Rd (p, u)) as [p2 u2]. cbn [fst snd] in *.
    apply Rd_ok; assumption.
Qed.

(** ** Residues along the loops (moduli 2^13 = 2 * 4096 and 2^12 = 4096) *)

Lemma Be_mod : forall q u, 5 <= q -> u mod (2 * 4096) = 3828 ->
  fst (Be (q, u)) mod 4096 = (q + 1913) mod 4096 /\ snd (Be (q, u)) mod (2 * 4096) = 3828 /\
  q + 1 <= fst (Be (q, u)).
Proof.
  intros q u Hq Hu. rewrite Be_eq. cbn [fst snd].
  pose proof (W_res1 (q - 1) ltac:(lia)) as HW.
  set (w := W (q - 1) 1) in *. clearbody w.
  repeat split; mods; lia.
Qed.

Lemma iter_Be_mod : forall n q u, 5 <= q -> u mod (2 * 4096) = 3828 ->
  fst (iter n Be (q, u)) mod 4096 = (q + n * 1913) mod 4096 /\
  snd (iter n Be (q, u)) mod (2 * 4096) = 3828 /\ q + n <= fst (iter n Be (q, u)).
Proof.
  induction n as [| n IHn]; intros q u Hq Hu.
  - cbn [iter fst snd]. repeat split; [f_equal; lia | exact Hu | lia].
  - cbn [iter]. destruct (IHn q u Hq Hu) as [H1 [H2 H3]].
    destruct (iter n Be (q, u)) as [q2 u2]. cbn [fst snd] in *.
    destruct (Be_mod q2 u2 ltac:(lia) H2) as [G1 [G2 G3]].
    repeat split; [| exact G2 | lia].
    rewrite G1. clear G2 G3 H2 Hu. mods; lia.
Qed.

Lemma Rd_mod : forall p u, 6 <= p -> u mod (2 * 4096) = 3828 ->
  fst (Rd (p, u)) mod 4096 = (p + 1131) mod 4096 /\ snd (Rd (p, u)) mod (2 * 4096) = 3828 /\
  6 <= fst (Rd (p, u)).
Proof.
  intros p u Hp Hu. rewrite Rd_eq.
  assert (Hu1 : 1 <= u) by (mods; lia).
  assert (Hue : u mod 2 = 0) by (mods; lia).
  pose proof (W_res_even p u ltac:(lia) Hu1 Hue) as HW.
  pose proof (W_res1 (p - 1) ltac:(lia)) as HW1.
  assert (HW1' : (W (p - 1) 1 + 2) mod (2 * 4096) = 3828) by (clear HW; mods; lia).
  destruct (iter_Be_mod ((W p u + 1) / 2) (p - 1) (W (p - 1) 1 + 2) ltac:(lia) HW1') as [H1 [H2 H3]].
  set (m := (W p u + 1) / 2) in *.
  assert (Hm : m mod 4096 = 204 /\ 1 <= m) by (unfold m; clear H1 H2 H3 HW1 HW1'; mods; lia).
  set (F := fst (iter m Be (p - 1, W (p - 1) 1 + 2))) in *.
  set (G := snd (iter m Be (p - 1, W (p - 1) 1 + 2))) in *.
  clearbody F G m.
  repeat split; [| exact H2 | lia].
  rewrite H1. clear H2 HW HW1 HW1' Hu Hue. destruct Hm as [Hm Hm1]. mods; lia.
Qed.

Lemma iter_Rd_mod : forall r p u, 6 <= p -> u mod (2 * 4096) = 3828 ->
  fst (iter r Rd (p, u)) mod 4096 = (p + r * 1131) mod 4096 /\
  snd (iter r Rd (p, u)) mod (2 * 4096) = 3828 /\ 6 <= fst (iter r Rd (p, u)).
Proof.
  induction r as [| r IHr]; intros p u Hp Hu.
  - cbn [iter fst snd]. repeat split; [f_equal; lia | exact Hu | lia].
  - cbn [iter]. destruct (IHr p u Hp Hu) as [H1 [H2 H3]].
    destruct (iter r Rd (p, u)) as [p2 u2]. cbn [fst snd] in *.
    destruct (Rd_mod p2 u2 H3 H2) as [G1 [G2 G3]].
    repeat split; [| exact G2 | exact G3].
    rewrite G1. clear G2 G3 H2 Hu. mods; lia.
Qed.

Lemma W41_mod : (W 4 1 + 2) mod (2 * 4096) = 3828.
Proof. pose proof (W_res1 4 ltac:(lia)) as H. set (w := W 4 1) in *. clearbody w. mods; lia. Qed.

Lemma Big_mod : forall D, Big D mod 4096 = (1922 + ((D - 2) / 2) * 1131) mod 4096.
Proof.
  intros D. rewrite Big_eq.
  destruct (iter_Rd_mod ((D - 2) / 2) 7 (W 4 1 + 2) ltac:(lia) W41_mod) as [H1 [H2 H3]].
  set (r := (D - 2) / 2) in *.
  set (P := iter r Rd (7, W 4 1 + 2)) in *. clearbody P r.
  destruct P as [a b]. cbn [fst snd] in *.
  clear H3. mods; lia.
Qed.

(** The base sequence: residues lose one bit per big round. *)
Ltac bigstep := intros D HD; pose proof (Big_mod D) as HB; set (B := Big D) in *; clearbody B; mods; lia.

Lemma Big1 : forall D, D mod 4096 = 1922 -> Big D mod 2048 = 194. Proof. bigstep. Qed.
Lemma Big2 : forall D, D mod 2048 = 194 -> Big D mod 1024 = 930. Proof. bigstep. Qed.
Lemma Big3 : forall D, D mod 1024 = 930 -> Big D mod 512 = 370. Proof. bigstep. Qed.
Lemma Big4 : forall D, D mod 512 = 370 -> Big D mod 256 = 106. Proof. bigstep. Qed.
Lemma Big5 : forall D, D mod 256 = 106 -> Big D mod 128 = 62. Proof. bigstep. Qed.
Lemma Big6 : forall D, D mod 128 = 62 -> Big D mod 64 = 12. Proof. bigstep. Qed.
Lemma Big7 : forall D, D mod 64 = 12 -> Big D mod 32 = 25. Proof. bigstep. Qed.

Lemma chain : forall D, D mod 4096 = 1922 ->
  (forall i, i < 7 -> 2 <= iter i Big D /\ iter i Big D mod 2 = 0) /\ iter 7 Big D mod 32 = 25.
Proof.
  intros D H0.
  pose proof (Big1 _ H0) as H1. pose proof (Big2 _ H1) as H2. pose proof (Big3 _ H2) as H3.
  pose proof (Big4 _ H3) as H4. pose proof (Big5 _ H4) as H5. pose proof (Big6 _ H5) as H6.
  pose proof (Big7 _ H6) as H7.
  split.
  - intros i Hi.
    destruct i as [| [| [| [| [| [| [| i]]]]]]]; cbn [iter].
    1: clear - H0. 2: clear - H1. 3: clear - H2. 4: clear - H3. 5: clear - H4. 6: clear - H5. 7: clear - H6.
    all: try (mods; lia).
    all: lia.
  - cbn [iter]. exact H7.
Qed.

Local Close Scope nat_scope.

(** ** Machine level: loops *)

Lemma LOOP2 : forall n q u t, (1 <= q)%nat -> (4 <= u)%nat -> (u mod 2 = 0)%nat ->
  Y q u ([1; 0]^^n *> t) -->* Y (fst (iter n Be (q, u))) (snd (iter n Be (q, u))) t.
Proof.
  induction n as [| n IHn]; intros q u t Hq Hu He.
  - cbn [iter fst snd lpow Str_app]. finish.
  - rewrite iter_S'.
    destruct q as [| q']; [lia |].
    assert (Hm : u = (2 * (u / 2 - 1) + 2)%nat) by (mods; lia).
    set (m := (u / 2 - 1)%nat) in Hm. clearbody m. subst u.
    assert (EB : Be (S q', 2 * m + 2)%nat = (q' + S m, W q' 1 + 2)%nat).
    { rewrite Be_eq. replace (S q' - 1)%nat with q' by lia. rewrite half2. reflexivity. }
    rewrite EB. cbn [lpow app Str_app].
    eapply evstep_trans; [apply progress_evstep, R_Be |].
    apply IHn; [lia | pose proof (W_grow q' 1); lia | apply W_even1].
Qed.

Lemma ROUND : forall p u d t, (2 <= p)%nat -> (u mod 2 = 0)%nat ->
  X p u ([1; 0]^^(S (S d)) *> t) -->+ X (fst (Rd (p, u))) (snd (Rd (p, u))) ([1; 0]^^d *> t).
Proof.
  intros p u d t Hp Hu.
  cbn [lpow app Str_app].
  eapply progress_evstep_trans; [apply R_A |].
  pose proof (W_par p u) as Hw. pose proof (W_grow p u) as Hg.
  assert (Ho : (W p u + 2 = 2 * ((W p u + 1) / 2 - 1) + 3)%nat) by (mods; lia).
  assert (Hs : (S ((W p u + 1) / 2 - 1) = (W p u + 1) / 2)%nat) by (mods; lia).
  rewrite Ho.
  destruct p as [| p']; [lia |].
  eapply evstep_trans; [apply progress_evstep, R_Bo |].
  rewrite Hs, Rd_eq. replace (S p' - 1)%nat with p' by lia.
  unfold X. apply LOOP2; [lia | pose proof (W_grow p' 1); lia | apply W_even1].
Qed.

Lemma ROUNDS : forall r p u t, (2 <= p)%nat -> (u mod 2 = 0)%nat ->
  X p u ([1; 0]^^(2 * r) *> t) -->* X (fst (iter r Rd (p, u))) (snd (iter r Rd (p, u))) t.
Proof.
  induction r as [| r IHr]; intros p u t Hp Hu.
  - cbn [iter fst snd]. finish.
  - replace (2 * S r)%nat with (S (S (2 * r))) by lia.
    eapply evstep_trans; [apply progress_evstep, ROUND; assumption |].
    rewrite iter_S'.
    destruct (Rd_ok p u Hp Hu) as [H1 [H2 _]].
    destruct (Rd (p, u)) as [p2 u2]. cbn [fst snd] in *.
    apply IHr; assumption.
Qed.

(** From the start of a big round to the first round configuration. *)
Lemma BOOT : forall D t,
  Y 0 4 ([1; 0]^^(S (S D)) *> t) -->+ X 7 (W 4 1 + 2) ([1; 0]^^D *> t).
Proof.
  intros D t.
  eapply progress_evstep_trans; [apply BOOT2 |].
  cbn [lpow app Str_app].
  eapply evstep_trans; [apply progress_evstep, (R_Bo 1 1) |].
  cbn [lpow app Str_app].
  change (W 1 1 + 2)%nat with (2 * 4 + 2)%nat.
  eapply evstep_trans; [apply progress_evstep, (R_Be 0 4) |].
  change (0 + S 4)%nat with (S 4). change (W 0 1 + 2)%nat with (2 * 2 + 2)%nat.
  eapply evstep_trans; [apply progress_evstep, (R_Be 4 2) |].
  unfold X. finish.
Qed.

Lemma ROUNDS_BLANK : forall r p u, (2 <= p)%nat -> (u mod 2 = 0)%nat -> (4 <= u)%nat ->
  X p u ([1; 0]^^(2 * r) *> const 0) -->+
  Y 0 4 ([1; 0]^^(fst (iter r Rd (p, u)) + snd (iter r Rd (p, u)) / 2 + 1) *> const 0).
Proof.
  intros r p u Hp Hu Hu4.
  eapply evstep_progress_trans; [apply ROUNDS; assumption |].
  destruct (iter_Rd_ok r p u Hp Hu Hu4) as [H1 [H2 H3]].
  destruct (iter r Rd (p, u)) as [P U]. cbn [fst snd] in *.
  assert (HU : U = (2 * (U / 2 - 1) + 2)%nat) by (mods; lia).
  assert (HP : (P + U / 2 + 1 = P + (U / 2 - 1) + 2)%nat) by (mods; lia).
  rewrite HP. unfold X. rewrite <- const_unfold. rewrite HU at 1. apply BLANK.
Qed.

Lemma BIG_EVEN : forall D, (2 <= D)%nat -> (D mod 2 = 0)%nat ->
  Y 0 4 ([1; 0]^^D *> const 0) -->+ Y 0 4 ([1; 0]^^(Big D) *> const 0).
Proof.
  intros D HD He. rewrite Big_eq.
  set (r := ((D - 2) / 2)%nat).
  assert (Er : D = S (S (2 * r))) by (unfold r; mods; lia).
  clearbody r. subst D.
  eapply progress_evstep_trans; [apply BOOT |].
  apply progress_evstep. apply ROUNDS_BLANK; [lia | apply W_even1 | pose proof (W_grow 4 1); lia].
Qed.

Lemma BIG_ODD : forall E, (3 <= E)%nat -> (E mod 2 = 1)%nat ->
  Y 0 4 ([1; 0]^^E *> const 0) -->+
  c_end (fst (iter ((E - 3) / 2) Rd (7, W 4 1 + 2)%nat)) (snd (iter ((E - 3) / 2) Rd (7, W 4 1 + 2)%nat)).
Proof.
  intros E HE Ho.
  set (r := ((E - 3) / 2)%nat).
  assert (Er : E = S (S (2 * r + 1))) by (unfold r; mods; lia).
  clearbody r. subst E.
  eapply progress_evstep_trans; [apply BOOT |].
  rewrite lpow_add, Str_app_assoc. cbn [lpow app Str_app].
  eapply evstep_trans; [apply ROUNDS; [lia | apply W_even1] |].
  apply progress_evstep. apply R_H.
Qed.

Lemma RUN_EVENS : forall k D, (forall i, (i < k)%nat -> (2 <= iter i Big D)%nat /\ (iter i Big D mod 2 = 0)%nat) ->
  Y 0 4 ([1; 0]^^D *> const 0) -->* Y 0 4 ([1; 0]^^(iter k Big D) *> const 0).
Proof.
  induction k as [| k IHk]; intros D H.
  - cbn [iter]. finish.
  - eapply evstep_trans; [apply IHk; intros i Hi; apply H; lia |].
    destruct (H k ltac:(lia)) as [H1 H2].
    cbn [iter]. apply progress_evstep. apply BIG_EVEN; assumption.
Qed.

Lemma RUN_GEN : forall D, (D mod 4096 = 1922)%nat ->
  Y 0 4 ([1; 0]^^D *> const 0) -->*
  c_end (fst (iter ((iter 7 Big D - 3) / 2) Rd (7, W 4 1 + 2)%nat))
        (snd (iter ((iter 7 Big D - 3) / 2) Rd (7, W 4 1 + 2)%nat)).
Proof.
  intros D HD.
  destruct (chain D HD) as [Hev Hodd].
  eapply evstep_trans; [apply (RUN_EVENS 7 D Hev) |].
  apply progress_evstep. apply BIG_ODD.
  - clear Hev. set (x := iter 7 Big D) in *. clearbody x. mods; lia.
  - clear Hev. set (x := iter 7 Big D) in *. clearbody x. mods; lia.
Qed.

(** ** From the blank tape *)

Lemma even_half : forall w, (w mod 2 = 0)%nat -> (w + 2 = 2 * (w / 2) + 2)%nat.
Proof. intros w H. mods; lia. Qed.

Lemma D0_mod : forall w, (w mod (2 * 4096) = 3826)%nat -> ((7 + w / 2 + 2) mod 4096 = 1922)%nat.
Proof. intros w H. mods; lia. Qed.

Lemma W_even : forall j, (W j 1 mod 2 = 0)%nat.
Proof. intros j. rewrite W_par. reflexivity. Qed.

Lemma boot : c0 -->* Y 0 4 ([1; 0]^^(7 + W 4 1 / 2 + 2) *> const 0).
Proof.
  eapply evstep_trans.
  { do 248 step. apply evstep_refl. }
  eapply evstep_trans; [apply progress_evstep, (CH_CA 4 1) |].
  follow (CA_SH_iter 2 4 (W 4 1) (1 >> const 0)).
  assert (E1 : Ca (4 + 2) (W 4 1) (1 >> const 0) = Ca 6 (W 4 1) (1 >> 0 >> const 0)).
  { rewrite <- const_unfold. reflexivity. }
  rewrite E1.
  eapply evstep_trans; [apply progress_evstep, CA_SH |].
  assert (E2 : Ca 7 (W 4 1) (const 0) = Ca 7 (W 4 1) (0 >> const 0)).
  { rewrite <- const_unfold. reflexivity. }
  rewrite E2.
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  change (([1]^^(W 4 1 + 2) *> [0; 1]^^7 *> const 0) {{I}}> const 0) with (Y 7 (W 4 1 + 2) (const 0)).
  rewrite (even_half (W 4 1) (W_even 4)).
  apply progress_evstep. apply BLANK.
Qed.

Opaque W Be Rd Big.

(** Names for the numbers of the run (notations: everything stays syntactic). *)
Notation nD0 := (7 + W 4 1 / 2 + 2)%nat.
Notation nD7 := (iter 7 Big nD0).
Notation nP := (iter ((nD7 - 3) / 2) Rd (7, W 4 1 + 2)%nat).

Lemma D0_res : (nD0 mod 4096 = 1922)%nat.
Proof. exact (D0_mod (W 4 1) (W_res1 4 ltac:(lia))). Qed.

Lemma run_FIN : c0 -->* c_end (fst nP) (snd nP).
Proof.
  eapply evstep_trans; [apply boot |].
  exact (RUN_GEN nD0 D0_res).
Qed.

Theorem halt : halts tm c0.
Proof.
  destruct (with_counter run_FIN) as [n Hn].
  eapply halts_multistep; [| exact Hn].
  apply halted_halts. apply c_end_halted.
Qed.

(** ** Exact score *)

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
    c = (q, (L *> const S0, s, R *> const S0)) /\ N = (count1 L + sym_val s + count1 R)%nat.

Lemma count1_app : forall xs ys, count1 (xs ++ ys) = (count1 xs + count1 ys)%nat.
Proof. induction xs; intros; simpl. - reflexivity. - rewrite IHxs. lia. Qed.

Lemma count1_pow : forall xs n, count1 (xs ^^ n) = (n * count1 xs)%nat.
Proof. induction n; simpl. - reflexivity. - rewrite count1_app, IHn. lia. Qed.

Lemma ones_c_end : forall p u, ones (c_end p u) (u + p + 1).
Proof.
  intros p u. exists E, ([0; 0; 1] ++ [1]^^u ++ [0; 1]^^p), (@nil Sym), S0. split.
  - unfold c_end. rewrite !Str_app_assoc. reflexivity.
  - rewrite !count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

Theorem score_exact :
  exists c, c0 -->* c /\ halted tm c /\ ones c (snd nP + fst nP + 1).
Proof.
  exists (c_end (fst nP) (snd nP)).
  split; [exact run_FIN |].
  split; [apply c_end_halted |].
  apply ones_c_end.
Qed.
