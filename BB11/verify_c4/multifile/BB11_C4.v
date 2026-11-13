(** * The 11-state machine C4 halts from the blank tape *)

(** C4 is the 12-state machine M12 with state L removed.  The table below is the start-A relabelling of
    1RB1RA_1RI1RC_0LD1LG_0RE1LD_1LJ1RF_1RK0RA_1RA0LH_1LG1LH_1RE0LJ_1LH1LI_---0LI  (start B), with the map
    A>G B>A C>H D>I E>C F>J G>F H>E I>B J>D K>K.  The lemmas Ca, Ch, CA_SH, ..., CH_CA are those of
    BB12_M12.v with the states renamed by this map. *)

From BB8 Require Import Individual112.
From Coq Require Import Lia PeanoNat List.
Import ListNotations.
Set Default Goal Selector "!".

(* machine: 1RB1RH_1RC0LD_1LD1RJ_1LE1LB_1LF1LE_1RG0LE_1RA1RG_0LI1LF_0RC1LI_1RK0RG_---0LB *)
Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, R, H)
  | B, 0 => Some (1, R, C)  | B, 1 => Some (0, L, D)
  | C, 0 => Some (1, L, D)  | C, 1 => Some (1, R, J)
  | D, 0 => Some (1, L, E)  | D, 1 => Some (1, L, B)
  | E, 0 => Some (1, L, F)  | E, 1 => Some (1, L, E)
  | F, 0 => Some (1, R, G)  | F, 1 => Some (0, L, E)
  | G, 0 => Some (1, R, A)  | G, 1 => Some (1, R, G)
  | H, 0 => Some (0, L, I)  | H, 1 => Some (1, L, F)
  | I, 0 => Some (0, R, C)  | I, 1 => Some (1, L, I)
  | J, 0 => Some (1, R, K)  | J, 1 => Some (0, R, G)
  | K, 0 => None            | K, 1 => Some (0, L, B)
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

(** [x]^(2m+1) read from the near end: a single x first, or the pairs first. *)
Lemma lpow_odd : forall (x : Sym) m (l : side), [x]^^(2 * m + 1) *> l = x >> [x; x]^^m *> l.
Proof.
  intros x m l. replace (2 * m + 1)%nat with (S (2 * m)) by lia.
  cbn [lpow app Str_app]. rewrite lpow_double. reflexivity.
Qed.

Lemma lpow_odd' : forall (x : Sym) m (l : side), [x]^^(2 * m + 1) *> l = [x; x]^^m *> x >> l.
Proof.
  intros x m l.
  rewrite lpow_add, Str_app_assoc, lpow_double. reflexivity.
Qed.

(** ** Basic shift lemmas *)

Lemma cr_GR_1_1 : forall n l r, l {{G}}> [1]^^n *> r -->* [1]^^n *> l {{G}}> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_IL_1_1 : forall n l r, [1]^^n *> l <{{I}} r -->* l <{{I}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_EL_1_1 : forall n l r, [1]^^n *> l <{{E}} r -->* l <{{E}} [1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_EL_01_01 : forall n l r, [0; 1]^^n *> l <{{E}} r -->* l <{{E}} [0; 1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_BL_11_10 : forall n l r, [1; 1]^^n *> l <{{B}} r -->* l <{{B}} [1; 0]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

Lemma cr_DL_11_01 : forall n l r, [1; 1]^^n *> l <{{D}} r -->* l <{{D}} [0; 1]^^n *> r.
Proof. induction n; intros. - finish. - execute. follow IHn. finish_norm. Qed.

(** ** The f_omega engine (BB12_M12.v, renamed) *)

Definition Ca (j b : nat) (z : side) : Q * tape :=
  ([1]^^b *> [0; 1]^^j *> const 0) {{G}}> (0 >> z).

Definition Ch (j b : nat) (z : side) : Q * tape :=
  ([0; 1]^^j *> const 0) <{{E}} (1 >> [1]^^b *> 0 >> z).

Definition blk (a : nat) (z : side) : side :=
  1 >> [1]^^a *> 0 >> z.

Lemma CA_SH : forall j b z,
  Ca j b (1 >> 0 >> z) -->+ Ca (S j) b z.
Proof.
  intros j b z. unfold Ca.
  start_progress.
  follow cr_IL_1_1.
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
  Ca j b (0 >> z) -->+ ([1]^^(b + 2) *> [0; 1]^^j *> const 0) {{B}}> z.
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
  follow cr_EL_1_1.
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
  follow cr_EL_01_01.
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

(** ** Number theory: parity (W_par) and the residue lemma L4 *)

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

(** W j (j >= 1) swaps the residues 2 and 3 mod 4. *)
Lemma W_swap23 : forall j, 1 <= j -> forall x,
  (x mod 4 = 2 -> W j x mod 4 = 3) /\ (x mod 4 = 3 -> W j x mod 4 = 2).
Proof.
  intros j Hj. induction j as [| j IHj]; [lia |].
  destruct j as [| j].
  - intros x. rewrite W_1. split; intros Hx; mods; lia.
  - assert (Halt : forall n, iter n (W (S j)) 2 mod 4 = 2 + n mod 2).
    { induction n as [| n IHn]; cbn [iter]; [reflexivity |].
      destruct (IHj ltac:(lia) (iter n (W (S j)) 2)) as [H2 H3].
      assert (Hn : n mod 2 = 0 \/ n mod 2 = 1) by (mods; lia).
      destruct Hn as [Hn | Hn].
      - rewrite H2 by lia. mods; lia.
      - rewrite H3 by lia. mods; lia. }
    intros x. rewrite W_S, Halt. split; intros Hx; mods; lia.
Qed.

(** L4: for j >= 2, W j b mod 4 = 3 if b is even, 2 if b is odd. *)
Lemma W_mod4 : forall j b, 2 <= j -> W j b mod 4 = 3 - b mod 2.
Proof.
  intros j b Hj. destruct j as [| [| j]]; [lia | lia |].
  assert (Halt : forall n, iter n (W (S j)) 2 mod 4 = 2 + n mod 2).
  { induction n as [| n IHn]; cbn [iter]; [reflexivity |].
    destruct (W_swap23 (S j) ltac:(lia) (iter n (W (S j)) 2)) as [H2 H3].
    assert (Hn : n mod 2 = 0 \/ n mod 2 = 1) by (mods; lia).
    destruct Hn as [Hn | Hn].
    - rewrite H2 by lia. mods; lia.
    - rewrite H3 by lia. mods; lia. }
  rewrite W_S, Halt. mods; lia.
Qed.

Opaque W.

Local Close Scope nat_scope.

(** ** Configurations of C4 *)

(** Y: the engine has exited into state B (M12 name I) facing the stock side w. *)
Definition Y (p u : nat) (w : side) : Q * tape :=
  ([1]^^u *> [0; 1]^^p *> const 0) {{B}}> w.

Definition X (p u : nat) (S : side) : Q * tape := Y p u (0 >> S).

Definition Z (j b k : nat) (y : side) : Q * tape := Y j (b + 2) ([0]^^k *> y).

(** V: conversion of the left block (V' of the finder's report; V p 0 is his V p 2). *)
Definition V (p k : nat) (y : side) : Q * tape :=
  ([0; 1]^^p *> const 0) <{{B}} ([1; 0]^^2 *> [0; 0]^^k *> y).

Lemma STOCK : forall p m S,
  X p (2 * m + 1) ([1; 0]^^2 *> S) -->+ V p 0 ([1; 0]^^m *> 0 >> 0 >> S).
Proof.
  intros p m S. unfold X, Y, V. rewrite lpow_odd.
  start_progress.
  follow cr_BL_11_10.
  finish_norm.
Qed.

Lemma CONV : forall p k y, V (S p) k y -->+ V p (S k) y.
Proof.
  intros p k y. unfold V. cbn [lpow app Str_app].
  start_progress.
Qed.

Lemma CONV_iter : forall p k y, V p k y -->* V 0 (p + k) y.
Proof.
  induction p as [| p IHp]; intros k y.
  - finish.
  - eapply evstep_trans; [apply progress_evstep, CONV |].
    follow (IHp (S k) y). replace (p + S k)%nat with (S p + k)%nat by lia. finish.
Qed.

Lemma RESTART : forall k y, V 0 k y -->+ Z 1 3 (2 * k + 1) y.
Proof.
  intros k y. unfold V, Z, Y. rewrite lpow_odd. cbn [lpow app Str_app].
  start_progress.
Qed.

Lemma ZCORE_aux : forall j m z,
  Y (S j) (2 * m + 3) (0 >> 0 >> 0 >> z) -->+ Ch j 1 ([1; 0]^^(S m) *> 1 >> 1 >> 0 >> z).
Proof.
  intros j m z. unfold Y, Ch.
  replace (2 * m + 3)%nat with (2 * S m + 1)%nat by lia. rewrite lpow_odd.
  start_progress.
  follow cr_DL_11_01.
  execute.
  finish_norm.
Qed.

Lemma ZCORE : forall j m z,
  Y (S j) (2 * m + 3) (0 >> 0 >> 0 >> z) -->+ Ca (j + m + 2) (W (j + m + 1) (W j 1)) z.
Proof.
  intros j m z.
  eapply progress_evstep_trans; [apply ZCORE_aux |].
  eapply evstep_trans; [apply progress_evstep, CH_CA |].
  follow (CA_SH_iter (S m) j (W j 1) (1 >> 1 >> 0 >> z)).
  apply progress_evstep.
  replace (j + m + 2)%nat with (S (j + S m)) by lia.
  replace (j + m + 1)%nat with (j + S m)%nat by lia.
  change (1 >> 1 >> 0 >> z) with (blk 1 z).
  exact (BLK_iter_aux (j + S m) (CH_CA (j + S m)) 1 (W j 1) z).
Qed.

(** ** The f_(omega+1) loop: one Z step eats four zeros *)

Definition Zs (jb : nat * nat) : nat * nat :=
  let '(j, b) := jb in ((j + b / 2 + 1)%nat, W (j + b / 2) (W (j - 1) 1)).

Lemma ZSTEP : forall j b k y, (1 <= j)%nat -> (b mod 2 = 1)%nat ->
  Z j b (4 + k) y -->+ Z (fst (Zs (j, b))) (snd (Zs (j, b))) k y.
Proof.
  intros j b k y Hj Hb. destruct j as [| j]; [lia |].
  cbn [Zs fst snd].
  assert (Hb2 : b = (2 * (b / 2) + 1)%nat) by (mods; lia).
  set (m := (b / 2)%nat) in *. clearbody m. subst b.
  replace (S j - 1)%nat with j by lia.
  replace (S j + m + 1)%nat with (j + m + 2)%nat by lia.
  replace (S j + m)%nat with (j + m + 1)%nat by lia.
  unfold Z. replace (2 * m + 1 + 2)%nat with (2 * m + 3)%nat by lia.
  cbn [lpow app Str_app Nat.add].
  eapply progress_evstep_trans; [apply ZCORE |].
  apply progress_evstep. unfold Y. apply CA_EXIT.
Qed.

Lemma ZEND : forall j b m w, (1 <= j)%nat -> (b mod 2 = 1)%nat ->
  Z j b 3 ([1; 0]^^m *> 0 >> w) -->+ Y (fst (Zs (j, b)) + m) (snd (Zs (j, b)) + 2) w.
Proof.
  intros j b m w Hj Hb. destruct j as [| j]; [lia |].
  cbn [Zs fst snd].
  assert (Hb2 : b = (2 * (b / 2) + 1)%nat) by (mods; lia).
  set (n := (b / 2)%nat) in *. clearbody n. subst b.
  replace (S j - 1)%nat with j by lia.
  replace (S j + n + 1 + m)%nat with (j + n + 2 + m)%nat by lia.
  replace (S j + n)%nat with (j + n + 1)%nat by lia.
  unfold Z. replace (2 * n + 1 + 2)%nat with (2 * n + 3)%nat by lia.
  cbn [lpow app Str_app].
  eapply progress_evstep_trans; [apply ZCORE |].
  follow (CA_SH_iter m (j + n + 2) (W (j + n + 1) (W j 1)) (0 >> w)).
  apply progress_evstep. unfold Y. apply CA_EXIT.
Qed.

Lemma Zs_odd : forall jb, (1 <= fst jb)%nat -> (snd jb mod 2 = 1)%nat ->
  (1 <= fst (Zs jb))%nat /\ (snd (Zs jb) mod 2 = 1)%nat.
Proof.
  intros [j b] Hj Hb. cbn [Zs fst snd] in *.
  pose proof (W_par (j + b / 2) (W (j - 1) 1)) as H1.
  pose proof (W_par (j - 1) 1) as H2.
  split; [lia |]. mods; lia.
Qed.

Lemma ZLOOP : forall t r y jb, (1 <= fst jb)%nat -> (snd jb mod 2 = 1)%nat ->
  Z (fst jb) (snd jb) (4 * t + r) y -->* Z (fst (iter t Zs jb)) (snd (iter t Zs jb)) r y.
Proof.
  induction t as [| t IHt]; intros r y jb Hj Hb.
  - cbn [iter]. replace (4 * 0 + r)%nat with r by lia. finish.
  - rewrite iter_S'.
    replace (4 * S t + r)%nat with (4 + (4 * t + r))%nat by lia.
    destruct jb as [j b].
    eapply evstep_trans; [apply progress_evstep, ZSTEP; assumption |].
    destruct (Zs_odd (j, b) Hj Hb) as [Hj' Hb'].
    exact (IHt r y (Zs (j, b)) Hj' Hb').
Qed.

(** Residues along the Z loop started from (1, 3): j stays odd, b stays 3 mod 4 (uses L4). *)
Lemma Zs_inv4 : forall jb, (fst jb mod 2 = 1)%nat -> (snd jb mod 4 = 3)%nat ->
  (fst (Zs jb) mod 2 = 1)%nat /\ (snd (Zs jb) mod 4 = 3)%nat.
Proof.
  intros [j b] Hj Hb. cbn [Zs fst snd] in *.
  pose proof (W_par (j - 1) 1) as H2.
  rewrite W_mod4 by (mods; lia).
  split; mods; lia.
Qed.

Lemma iter_Zs_inv : forall t,
  (fst (iter t Zs (1, 3)%nat) mod 2 = 1)%nat /\ (snd (iter t Zs (1, 3)%nat) mod 4 = 3)%nat.
Proof.
  induction t as [| t IHt]; cbn [iter].
  - split; reflexivity.
  - apply Zs_inv4; tauto.
Qed.

(** ** One f_(omega+2) round: two pairs of the stock *)

Definition Rnd (pu : nat * nat) : nat * nat :=
  let '(p, u) := pu in
  ((fst (iter (p / 2 + 1) Zs (1, 3)) + u / 2)%nat, (snd (iter (p / 2 + 1) Zs (1, 3)) + 2)%nat).

Lemma ROUND : forall p u w, (p mod 2 = 1)%nat -> (u mod 2 = 1)%nat ->
  X p u (1 >> 0 >> 1 >> 0 >> w) -->+ X (fst (Rnd (p, u))) (snd (Rnd (p, u))) w.
Proof.
  intros p u w Hp Hu. cbn [Rnd fst snd].
  assert (Hu2 : u = (2 * (u / 2) + 1)%nat) by (mods; lia).
  assert (Hp2 : p = (2 * (p / 2) + 1)%nat) by (mods; lia).
  set (m := (u / 2)%nat) in *. set (t := (p / 2)%nat) in *. clearbody m t. subst u p.
  change (1 >> 0 >> 1 >> 0 >> w) with ([1; 0]^^2 *> w).
  eapply progress_evstep_trans; [apply STOCK |].
  eapply evstep_trans; [apply CONV_iter |].
  eapply evstep_trans; [apply progress_evstep, RESTART |].
  replace (2 * (2 * t + 1 + 0) + 1)%nat with (4 * t + 3)%nat by lia.
  eapply evstep_trans; [apply (ZLOOP t 3 _ (1, 3)%nat); cbn; lia |].
  destruct (iter_Zs_inv t) as [H1 H2].
  replace (t + 1)%nat with (S t) by lia. cbn [iter].
  set (jb := iter t Zs (1, 3)%nat) in *. clearbody jb. destruct jb as [j b]. cbn [fst snd] in *.
  apply progress_evstep. unfold X. apply ZEND; mods; lia.
Qed.

Lemma Rnd_inv : forall pu, (fst pu mod 2 = 1)%nat -> (snd pu mod 4 = 1)%nat ->
  (fst (Rnd pu) mod 2 = 1)%nat /\ (snd (Rnd pu) mod 4 = 1)%nat.
Proof.
  intros [p u] Hp Hu. cbn [Rnd fst snd] in *.
  destruct (iter_Zs_inv (p / 2 + 1)) as [H1 H2].
  split; mods; lia.
Qed.

Lemma ROUNDS : forall a pu w, (fst pu mod 2 = 1)%nat -> (snd pu mod 4 = 1)%nat ->
  X (fst pu) (snd pu) ([1; 0; 1; 0]^^a *> w) -->* X (fst (iter a Rnd pu)) (snd (iter a Rnd pu)) w.
Proof.
  induction a as [| a IHa]; intros pu w Hp Hu.
  - finish.
  - rewrite iter_S'. cbn [lpow app Str_app].
    destruct pu as [p u]. cbn [fst snd] in *.
    eapply evstep_trans; [apply progress_evstep, ROUND; mods; lia |].
    destruct (Rnd_inv (p, u) Hp Hu) as [Hp' Hu'].
    exact (IHa (Rnd (p, u)) w Hp' Hu').
Qed.

(** ** The transitions that make the two stocks, and the halt *)

Lemma lpow_even2 : forall (x : Sym) m (l : side), [x]^^(2 * m + 2) *> l = x >> [x; x]^^m *> x >> l.
Proof.
  intros x m l. replace (2 * m + 2)%nat with (S (2 * m + 1)) by lia.
  cbn [lpow app Str_app]. rewrite lpow_odd'. reflexivity.
Qed.

(** Bootstrap: the engine exits onto the blank tape; the J-phase makes stock 1 behind the sentinel 1 1. *)
Lemma JPH0 : forall p m,
  Y p (2 * m + 4) (const 0) -->+ V p 0 ([1; 0]^^m *> 1 >> 1 >> const 0).
Proof.
  intros p m. unfold Y, V.
  replace (2 * m + 4)%nat with (2 * S m + 2)%nat by lia. rewrite lpow_even2.
  start_progress.
  follow cr_DL_11_01.
  execute.
  finish_norm.
Qed.

(** Stock 1 exhausted on the sentinel 1 1: a new sentinel 0 1 and a block of m+3 pairs. *)
Lemma T2 : forall p m,
  X p (2 * m + 1) (1 >> 1 >> const 0) -->+ V p 0 ([1; 0]^^(S m) *> 0 >> 1 >> const 0).
Proof.
  intros p m. unfold X, Y, V. rewrite lpow_odd'.
  start_progress.
  follow cr_DL_11_01.
  execute.
  finish_norm.
Qed.

(** The engine exits onto the sentinel's 1: the J-phase makes stock 2. *)
Lemma T3 : forall p m,
  Y p (2 * m + 5) (1 >> const 0) -->+ V p 0 ([1; 0]^^(S m) *> const 0).
Proof.
  intros p m. unfold Y, V.
  replace (2 * m + 5)%nat with (2 * (m + 2) + 1)%nat by lia. rewrite lpow_odd'.
  start_progress.
  follow cr_DL_11_01.
  execute.
  finish_norm.
Qed.

Definition c_end (p u : nat) : Q * tape :=
  ([1]^^(u + 3) *> [0; 1]^^p *> const 0) {{K}}> const 0.

Lemma HALT : forall p u, X p u (1 >> 0 >> const 0) -->+ c_end p u.
Proof.
  intros p u. unfold X, Y, c_end.
  start_progress.
  finish_norm.
Qed.

Lemma c_end_halted : forall p u, halted tm (c_end p u).
Proof. intros p u. reflexivity. Qed.

(** ** Generic forms of the stages (all numbers are variables here) *)

Lemma lpow_S_double : forall c (l : side), [1; 0]^^(S (2 * c)) *> l = [1; 0; 1; 0]^^c *> 1 >> 0 >> l.
Proof.
  intros c l. cbn [lpow]. rewrite <- lpow_shift, Str_app_assoc, lpow_double. reflexivity.
Qed.

Lemma ROUNDS' : forall a p u w, (p mod 2 = 1)%nat -> (u mod 4 = 1)%nat ->
  X p u ([1; 0; 1; 0]^^a *> w) -->* X (fst (iter a Rnd (p, u))) (snd (iter a Rnd (p, u))) w.
Proof.
  intros a p u w Hp Hu. exact (ROUNDS a (p, u) w Hp Hu).
Qed.

Lemma iter_Rnd_inv : forall a p u, (p mod 2 = 1)%nat -> (u mod 4 = 1)%nat ->
  (fst (iter a Rnd (p, u)) mod 2 = 1)%nat /\ (snd (iter a Rnd (p, u)) mod 4 = 1)%nat.
Proof.
  induction a as [| a IHa]; intros p u Hp Hu; cbn [iter].
  - split; assumption.
  - destruct (IHa p u Hp Hu) as [H1 H2].
    apply Rnd_inv; assumption.
Qed.

Lemma plus2_mod4 : forall b, (b mod 4 = 3)%nat -> ((b + 2) mod 4 = 1)%nat.
Proof. intros b Hb. mods; lia. Qed.

Lemma boot_ca : c0 -->* Ca 5 (W 5 (W 2 4)) (1 >> const 0).
Proof.
  eapply evstep_trans.
  { unfold Ch. cbn [lpow Str_app app]. do 150 step. apply evstep_refl. }
  eapply evstep_trans; [apply progress_evstep, (CH_CA 2 4) |].
  follow (CA_SH_iter 3 2 (W 2 4) (1 >> 1 >> const 0)).
  replace (2 + 3)%nat with 5%nat by reflexivity.
  eapply evstep_trans; [apply progress_evstep, CA_CH |].
  apply progress_evstep. apply CH_CA.
Qed.

Lemma boot_gen : forall a,
  Ca 5 (4 * a + 2) (1 >> const 0) -->*
  X (fst (iter 3 Zs (1, 3)%nat)) (snd (iter 3 Zs (1, 3)%nat) + 2) ([1; 0; 1; 0]^^a *> 1 >> 1 >> const 0).
Proof.
  intros a.
  assert (E1 : Ca 5 (4 * a + 2) (1 >> const 0) = Ca 5 (4 * a + 2) (1 >> 0 >> const 0))
    by (f_equal; f_equal; apply const_unfold).
  rewrite E1.
  eapply evstep_trans; [apply progress_evstep, CA_SH |].
  assert (E2 : Ca 6 (4 * a + 2) (const 0) = Ca 6 (4 * a + 2) (0 >> const 0)) by (f_equal; apply const_unfold).
  rewrite E2.
  eapply evstep_trans; [apply progress_evstep, CA_EXIT |].
  replace (4 * a + 2 + 2)%nat with (2 * (2 * a) + 4)%nat by lia.
  eapply evstep_trans; [apply progress_evstep, (JPH0 6 (2 * a)) |].
  eapply evstep_trans; [apply CONV_iter |].
  eapply evstep_trans; [apply progress_evstep, RESTART |].
  replace (2 * (6 + 0) + 1)%nat with (4 * 3 + 1)%nat by reflexivity.
  eapply evstep_trans; [apply (ZLOOP 3 1 _ (1, 3)%nat); cbn; lia |].
  rewrite lpow_double. unfold Z, X. apply evstep_refl.
Qed.

(** From stock 1 exhausted to stock 2 (finder's macro steps 2378-2900). *)
Lemma MID : forall p u, (p mod 2 = 1)%nat -> (u mod 4 = 1)%nat ->
  X p u (1 >> 1 >> const 0) -->*
  X (fst (iter ((fst (iter (p / 2 + 1) Zs (1, 3)%nat) + u / 2 + 1) / 2) Zs (1, 3)%nat))
    (snd (iter ((fst (iter (p / 2 + 1) Zs (1, 3)%nat) + u / 2 + 1) / 2) Zs (1, 3)%nat) + 2)
    ([1; 0; 1; 0]^^(snd (iter (p / 2 + 1) Zs (1, 3)%nat) / 4) *> 1 >> 0 >> const 0).
Proof.
  intros p u Hp Hu.
  assert (Hu2 : u = (2 * (u / 2) + 1)%nat) by (mods; lia).
  assert (Hm : ((u / 2) mod 2 = 0)%nat) by (mods; lia).
  assert (Hp2 : p = (2 * (p / 2) + 1)%nat) by (mods; lia).
  set (m := (u / 2)%nat) in *. set (t := (p / 2)%nat) in *. clearbody m t. subst u p.
  eapply evstep_trans; [apply progress_evstep, T2 |].
  eapply evstep_trans; [apply CONV_iter |].
  eapply evstep_trans; [apply progress_evstep, RESTART |].
  replace (2 * (2 * t + 1 + 0) + 1)%nat with (4 * t + 3)%nat by lia.
  eapply evstep_trans; [apply (ZLOOP t 3 _ (1, 3)%nat); cbn; lia |].
  destruct (iter_Zs_inv t) as [H1 H2].
  destruct (iter_Zs_inv (S t)) as [H3 H4]. cbn [iter] in H3, H4.
  replace (t + 1)%nat with (S t) by lia. cbn [iter].
  set (jb := iter t Zs (1, 3)%nat) in *. clearbody jb. destruct jb as [j b]. cbn [fst snd] in *.
  eapply evstep_trans; [apply progress_evstep, ZEND; mods; lia |].
  set (JB := Zs (j, b)) in *. clearbody JB. destruct JB as [J B]. cbn [fst snd] in *.
  assert (HB : (B + 2 = 2 * (2 * (B / 4)) + 5)%nat) by (mods; lia).
  assert (HP : (J + S m = 2 * ((J + m + 1) / 2))%nat) by (mods; lia).
  rewrite HB, HP.
  set (c := (B / 4)%nat). set (s := ((J + m + 1) / 2)%nat). clearbody c s.
  eapply evstep_trans; [apply progress_evstep, T3 |].
  eapply evstep_trans; [apply CONV_iter |].
  eapply evstep_trans; [apply progress_evstep, RESTART |].
  replace (2 * (2 * s + 0) + 1)%nat with (4 * s + 1)%nat by lia.
  eapply evstep_trans; [apply (ZLOOP s 1 _ (1, 3)%nat); cbn; lia |].
  rewrite lpow_S_double. unfold Z, X. apply evstep_refl.
Qed.

Lemma W5_mod : W 5 (W 2 4) = (4 * (W 5 (W 2 4) / 4) + 2)%nat.
Proof.
  assert (G : forall v x, (v mod 4 = 3 - x mod 2)%nat -> (x mod 2 = 1)%nat -> v = (4 * (v / 4) + 2)%nat)
    by (intros; mods; lia).
  apply (G _ (W 2 4)).
  - apply W_mod4. lia.
  - rewrite W_par. reflexivity.
Qed.

Opaque Zs Rnd.

(** ** The halting run *)

(** Names for the numbers of the run (notations only: no new constants, everything stays syntactic). *)
Notation nT3 := (iter 3 Zs (1, 3)%nat).
Notation na1 := (W 5 (W 2 4) / 4)%nat.
Notation nQ1 := (iter na1 Rnd (fst nT3, snd nT3 + 2)%nat).
Notation nM1 := (iter (fst nQ1 / 2 + 1) Zs (1, 3)%nat).
Notation ns2 := ((fst nM1 + snd nQ1 / 2 + 1) / 2)%nat.
Notation nc2 := (snd nM1 / 4)%nat.
Notation nT4 := (iter ns2 Zs (1, 3)%nat).
Notation nFIN := (iter nc2 Rnd (fst nT4, snd nT4 + 2)%nat).

Lemma run_Q1 : c0 -->* X (fst nQ1) (snd nQ1) (1 >> 1 >> const 0) /\
  (fst nQ1 mod 2 = 1)%nat /\ (snd nQ1 mod 4 = 1)%nat.
Proof.
  destruct (iter_Zs_inv 3) as [H1 H2].
  pose proof (plus2_mod4 _ H2) as H3.
  split; [| exact (iter_Rnd_inv _ _ _ H1 H3)].
  eapply evstep_trans; [apply boot_ca |].
  rewrite W5_mod at 1.
  eapply evstep_trans; [apply boot_gen |].
  apply ROUNDS'; assumption.
Qed.

Lemma run_FIN : c0 -->* c_end (fst nFIN) (snd nFIN).
Proof.
  destruct run_Q1 as [Hrun [H1 H2]].
  destruct (iter_Zs_inv ns2) as [H3 H4].
  pose proof (plus2_mod4 _ H4) as H5.
  eapply evstep_trans; [exact Hrun |].
  eapply evstep_trans; [apply MID; assumption |].
  eapply evstep_trans; [apply ROUNDS'; assumption |].
  apply progress_evstep, HALT.
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

Lemma ones_c_end : forall p u, ones (c_end p u) (u + 3 + p).
Proof.
  intros p u. exists K, ([1]^^(u + 3) ++ [0; 1]^^p), (@nil Sym), S0. split.
  - unfold c_end. rewrite Str_app_assoc. reflexivity.
  - rewrite count1_app, !count1_pow. cbn [count1 sym_val]. lia.
Qed.

Theorem score_exact :
  exists c, c0 -->* c /\ halted tm c /\ ones c (snd nFIN + 3 + fst nFIN).
Proof.
  exists (c_end (fst nFIN) (snd nFIN)).
  split; [exact run_FIN |].
  split; [apply c_end_halted |].
  apply ones_c_end.
Qed.
